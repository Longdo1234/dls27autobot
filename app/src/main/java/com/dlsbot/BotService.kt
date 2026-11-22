package com.dlsbot

import android.accessibilityservice.AccessibilityService
import android.accessibilityservice.GestureDescription
import android.graphics.*
import android.os.Handler
import android.os.Looper
import android.util.Base64
import android.view.*
import android.view.accessibility.AccessibilityEvent
import android.widget.Button
import android.widget.LinearLayout
import android.widget.TextView
import org.json.JSONArray
import org.json.JSONObject
import java.io.ByteArrayOutputStream
import java.net.HttpURLConnection
import java.net.URL
import java.util.concurrent.CopyOnWriteArrayList
import java.util.concurrent.CountDownLatch
import java.util.concurrent.Executors
import java.util.concurrent.atomic.AtomicInteger
import kotlin.math.*
import kotlin.random.Random

class BotService : AccessibilityService() {
    // Khoảng cách (ms) giữa 2 lần chụp + hỏi AI. 600 = khoảng 100 lượt/phút (cần key có bật thanh toán).
    // Gói miễn phí: đổi thành 4300L.
    private val GAP_MS = 600L
    private val io = Executors.newSingleThreadExecutor()
    private val pool = Executors.newFixedThreadPool(4)
    private val ui = Handler(Looper.getMainLooper())
    private var tv: TextView? = null
    private var panel: View? = null
    @Volatile private var running = false
    @Volatile private var gen = 0L
    private val inflight = AtomicInteger(0)
    private val sides = CopyOnWriteArrayList<String>()
    private lateinit var wm: WindowManager
    private val prefs get() = getSharedPreferences("cfg", MODE_PRIVATE)
    private val D = arrayOf(.12f to .72f, .72f to .82f, .82f to .68f, .9f to .86f)

    private fun status(s: String) { ui.post { tv?.text = s } }
    private fun hide(h: Boolean) { ui.post { panel?.visibility = if (h) View.INVISIBLE else View.VISIBLE } }
    private fun side(): String {
        val l = sides.count { it == "left" }; val r = sides.count { it == "right" }
        return if (l > r) "left" else if (r > l) "right" else "unknown"
    }

    override fun onServiceConnected() {
        wm = getSystemService(WINDOW_SERVICE) as WindowManager
        val l = LinearLayout(this).apply { setBackgroundColor(0x99000000.toInt()) }
        val go = Button(this).apply { text = "▶" }
        go.setOnClickListener {
            running = !running
            go.text = if (running) "⏹" else "▶"
            if (running) io.execute { loop() }
        }
        l.addView(go)
        l.addView(Button(this).apply { text = "⚙"; setOnClickListener { showSetup() } })
        tv = TextView(this).apply { setTextColor(Color.WHITE); textSize = 11f; maxLines = 2; maxWidth = 600; text = "Sẵn sàng" }
        l.addView(tv)
        panel = l
        wm.addView(l, WindowManager.LayoutParams(-2, -2, WindowManager.LayoutParams.TYPE_ACCESSIBILITY_OVERLAY,
            WindowManager.LayoutParams.FLAG_NOT_FOCUSABLE, PixelFormat.TRANSLUCENT).apply { gravity = Gravity.TOP or Gravity.START })
    }
    override fun onAccessibilityEvent(e: AccessibilityEvent?) {}
    override fun onInterrupt() { running = false }

    private fun bounds() = wm.currentWindowMetrics.bounds
    private fun pt(i: Int): Pair<Float, Float> = bounds().let {
        prefs.getFloat("x$i", it.width() * D[i].first) to prefs.getFloat("y$i", it.height() * D[i].second)
    }
    private fun jrad() = min(bounds().width(), bounds().height()) * 0.12f
    private fun rn(x: Float) = Random.nextFloat() * 2 * x - x

    private fun showSetup() {
        val names = arrayOf("JOY", "A", "B", "C")
        val pts = FloatArray(8) { if (it % 2 == 0) pt(it / 2).first else pt(it / 2).second }
        val jr = jrad()
        val v = object : View(this) {
            val p = Paint(Paint.ANTI_ALIAS_FLAG)
            var sel = -1
            override fun onDraw(c: Canvas) {
                c.drawColor(0x55000000)
                p.textSize = 40f; p.textAlign = Paint.Align.CENTER
                for (i in 0..3) {
                    p.color = 0x99FF9800.toInt()
                    c.drawCircle(pts[i * 2], pts[i * 2 + 1], if (i == 0) jr else jr * .5f, p)
                    p.color = Color.WHITE; c.drawText(names[i], pts[i * 2], pts[i * 2 + 1] + 14, p)
                }
                p.color = 0xFF4CAF50.toInt(); c.drawRect(width / 2f - 120, 20f, width / 2f + 120, 110f, p)
                p.color = Color.WHITE; c.drawText("LƯU", width / 2f, 80f, p)
            }
            override fun onTouchEvent(e: MotionEvent): Boolean {
                when (e.action) {
                    MotionEvent.ACTION_DOWN -> {
                        if (e.y < 110 && abs(e.x - width / 2f) < 120) {
                            prefs.edit().apply { for (i in 0..3) { putFloat("x$i", pts[i * 2]); putFloat("y$i", pts[i * 2 + 1]) } }.apply()
                            wm.removeView(this); return true
                        }
                        sel = (0..3).minByOrNull { hypot(pts[it * 2] - e.x, pts[it * 2 + 1] - e.y) } ?: -1
                    }
                    MotionEvent.ACTION_MOVE -> if (sel >= 0) { pts[sel * 2] = e.x; pts[sel * 2 + 1] = e.y; invalidate() }
                }
                return true
            }
        }
        wm.addView(v, WindowManager.LayoutParams(-1, -1, WindowManager.LayoutParams.TYPE_ACCESSIBILITY_OVERLAY,
            WindowManager.LayoutParams.FLAG_NOT_FOCUSABLE or WindowManager.LayoutParams.FLAG_LAYOUT_IN_SCREEN or
                WindowManager.LayoutParams.FLAG_LAYOUT_NO_LIMITS, PixelFormat.TRANSLUCENT))
    }

    // Chụp liên tục, mỗi ảnh hỏi AI song song; lệnh của ảnh mới nhất ghi đè lệnh cũ
    private fun loop() {
        var t0 = 0L
        var seq = 0L
        gen = 0; sides.clear()
        while (running) {
            val wait = GAP_MS - (System.currentTimeMillis() - t0)
            if (wait > 0) Thread.sleep(wait)
            t0 = System.currentTimeMillis()
            if (inflight.get() >= 4) continue
            val img = shoot()
            if (img == null) { status("Chụp màn hình lỗi"); Thread.sleep(500); continue }
            val my = ++seq
            val key = prefs.getString("key", "") ?: ""
            val hint = side()
            inflight.incrementAndGet()
            pool.execute {
                try {
                    val (d, msg) = Ai.decide(key, img, hint)
                    if (d == null) { status(msg); return@execute }
                    if (!running || my < gen) return@execute
                    gen = my
                    val a = d.optString("attack", "unknown")
                    if (a == "left" || a == "right") { sides.add(a); while (sides.size > 6) sides.removeAt(0) }
                    status("${d.optString("act")} | tấn công: ${side()}")
                    act(d)
                } catch (e: Exception) {
                    status(("Lỗi: " + e.message).take(80))
                } finally {
                    inflight.decrementAndGet()
                }
            }
        }
        status("Đã dừng")
    }

    private fun shoot(): String? {
        var out: String? = null
        hide(true)
        try {
            Thread.sleep(90) // chờ menu ẩn hẳn rồi mới chụp
            val latch = CountDownLatch(1)
            takeScreenshot(Display.DEFAULT_DISPLAY, mainExecutor, object : TakeScreenshotCallback {
                override fun onSuccess(r: ScreenshotResult) {
                    try {
                        val sw = Bitmap.wrapHardwareBuffer(r.hardwareBuffer, r.colorSpace)!!.copy(Bitmap.Config.ARGB_8888, false)
                        r.hardwareBuffer.close()
                        val sc = Bitmap.createScaledBitmap(sw, 800, sw.height * 800 / sw.width, true)
                        val bo = ByteArrayOutputStream(); sc.compress(Bitmap.CompressFormat.JPEG, 55, bo)
                        out = Base64.encodeToString(bo.toByteArray(), Base64.NO_WRAP)
                    } catch (e: Exception) {}
                    latch.countDown()
                }
                override fun onFailure(code: Int) { status("Chụp lỗi, mã $code"); latch.countDown() }
            })
            latch.await(3, java.util.concurrent.TimeUnit.SECONDS)
        } finally {
            hide(false)
        }
        return out
    }

    // AI trả vị trí (me, to) theo % màn hình; app tự tính hướng joystick rồi thao tác
    private fun act(d: JSONObject) {
        val b = bounds(); val W = b.width().toFloat(); val H = b.height().toFloat()
        val me = d.optJSONArray("me"); val to = d.optJSONArray("to")
        if (me == null || to == null || me.length() < 2 || to.length() < 2) return
        val dx = ((to.optDouble(0) - me.optDouble(0)) / 100.0 * W).toFloat()
        val dy = ((me.optDouble(1) - to.optDouble(1)) / 100.0 * H).toFloat()
        val a0 = atan2(dy, dx).toDouble()
        val pw = if (hypot(dx, dy) > H * .15f) 1f else .6f
        val (jx, jy) = pt(0); val jr = jrad()
        val kind = d.optString("act", "run")
        val ms = (1100 + Random.nextInt(-100, 150)).toLong()
        val path = Path().apply {
            val sx = jx + rn(8f); val sy = jy + rn(8f)
            moveTo(sx, sy)
            for (i in 1..(if (kind == "dribble") 6 else 3)) {
                val a = a0 + Math.toRadians(rn(6f).toDouble() + if (kind == "dribble") (if (i % 2 == 0) 35.0 else -35.0) else 0.0)
                val r = jr * pw * (.9f + Random.nextFloat() * .1f)
                lineTo(sx + (cos(a) * r).toFloat(), sy - (sin(a) * r).toFloat())
            }
        }
        val g = GestureDescription.Builder().addStroke(GestureDescription.StrokeDescription(path, 0, ms))
        fun press(i: Int, start: Long, hold: Long) {
            val (bx, by) = pt(i)
            g.addStroke(GestureDescription.StrokeDescription(
                Path().apply { moveTo(bx + rn(6f), by + rn(6f)) }, start, hold.coerceAtLeast(40)))
        }
        when (kind) {
            "pass", "tackle" -> press(1, Random.nextLong(60, 250), 50L + Random.nextLong(40))
            "shoot" -> press(2, Random.nextLong(60, 200), Random.nextLong(200, 450))
        }
        if (d.optBoolean("sprint")) press(3, 0, ms - 100)
        if (!dispatchGesture(g.build(), null, null)) status("Hệ thống từ chối cử chỉ")
    }
}

object Ai {
    private val MODELS = arrayOf("gemini-2.5-flash-lite", "gemini-flash-lite-latest", "gemini-2.5-flash")
    @Volatile private var mi = 0
    private const val SYS = """You play Dream League Soccer on a phone from one landscape screenshot. Ignore the small play/gear overlay buttons at the top-left corner and any on-screen touch controls.
All coordinates are percentages of the screenshot: [x from 0 (left) to 100 (right), y from 0 (top) to 100 (bottom)].
me = the center of the player I control (he has an arrow or ring marker). His teammates wear his shirt color; players in the other color are opponents; goalkeepers wear a different color. Teams swap sides at half time, so decide the attack direction from THIS screenshot: the goal I attack is the one defended by the opponents' goalkeeper. A recent estimate is given as a hint: keep it unless the screenshot clearly shows otherwise.
Choose ONE move for the next second:
- I do not have the ball: act "run" with to = the ball and sprint true; use "tackle" (to = the ball carrier) when an opponent with the ball is very close.
- I have the ball: carry it toward the goal I attack (act "run", or "dribble" when a defender is close and ahead, to = a point ahead toward that goal); "pass" (to = a free teammate) when a defender blocks the way; "shoot" (to = a corner of the goal) when near the penalty box with a clear angle.
Reply ONLY with JSON: {"me":[x,y],"to":[x,y],"act":"run"|"dribble"|"pass"|"shoot"|"tackle","sprint":true|false,"attack":"left"|"right"|"unknown"}"""

    fun decide(key: String, b64: String, hint: String): Pair<JSONObject?, String> {
        if (key.isBlank()) return null to "Chưa nhập API key"
        return try {
            val img = JSONObject().put("inline_data", JSONObject().put("mime_type", "image/jpeg").put("data", b64))
            val txt = JSONObject().put("text", "Recent attack-side estimate: $hint. Decide the next move.")
            val body = JSONObject()
                .put("system_instruction", JSONObject().put("parts", JSONArray().put(JSONObject().put("text", SYS))))
                .put("contents", JSONArray().put(JSONObject().put("role", "user").put("parts", JSONArray().put(img).put(txt))))
                .put("generationConfig", JSONObject().put("maxOutputTokens", 200).put("temperature", 0.3).put("responseMimeType", "application/json"))
            val c = URL("https://generativelanguage.googleapis.com/v1beta/models/${MODELS[mi]}:generateContent").openConnection() as HttpURLConnection
            c.requestMethod = "POST"; c.doOutput = true; c.connectTimeout = 5000; c.readTimeout = 10000
            c.setRequestProperty("x-goog-api-key", key)
            c.setRequestProperty("content-type", "application/json")
            c.outputStream.use { it.write(body.toString().toByteArray()) }
            val code = c.responseCode
            if (code != 200) {
                val err = (c.errorStream?.bufferedReader()?.readText() ?: "").replace("\n", " ").take(60)
                val tried = MODELS[mi]
                if ((code == 404 || code == 400) && err.contains("model", true) && mi < MODELS.size - 1) mi++
                return null to "HTTP $code $tried: $err"
            }
            val t = JSONObject(c.inputStream.bufferedReader().readText()).getJSONArray("candidates").getJSONObject(0)
                .getJSONObject("content").getJSONArray("parts").getJSONObject(0).getString("text")
            JSONObject(t.substring(t.indexOf('{'), t.lastIndexOf('}') + 1)) to "OK"
        } catch (e: Exception) { null to ("Lỗi: " + e.message).take(80) }
    }
}
