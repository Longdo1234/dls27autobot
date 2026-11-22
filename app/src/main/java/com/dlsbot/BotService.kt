package com.dlsbot

import android.accessibilityservice.AccessibilityService
import android.accessibilityservice.GestureDescription
import android.graphics.*
import android.util.Base64
import android.view.*
import android.view.accessibility.AccessibilityEvent
import android.widget.Button
import android.widget.LinearLayout
import org.json.JSONArray
import org.json.JSONObject
import java.io.ByteArrayOutputStream
import java.net.HttpURLConnection
import java.net.URL
import java.util.concurrent.CountDownLatch
import java.util.concurrent.Executors
import kotlin.math.*
import kotlin.random.Random

// Tool nhận diện màn hình + gọi AI + điều khiển cảm ứng như người thật
class BotService : AccessibilityService() {
    private val io = Executors.newSingleThreadExecutor()
    @Volatile private var running = false
    private lateinit var wm: WindowManager
    private val prefs get() = getSharedPreferences("cfg", MODE_PRIVATE)
    // vị trí mặc định (tỉ lệ màn hình) của JOY, A, B, C
    private val D = arrayOf(.12f to .72f, .72f to .82f, .82f to .68f, .9f to .86f)

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

    // ---- Tool setup: kéo JOY/A/B/C đè lên nút thật trong game ----
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

    // ---- Vòng lặp: chụp màn hình -> AI quyết định -> thao tác ----
    private fun loop() {
        var last = "start"
        while (running) {
            val img = shoot()
            val p = if (img != null) Ai.decide(prefs.getString("key", "") ?: "", img, last) else null
            if (p != null) { act(p); last = p.toString() } else Thread.sleep(700)
            Thread.sleep(Random.nextLong(30, 150)) // độ trễ phản xạ ngẫu nhiên
        }
    }

    private fun shoot(): String? {
        var out: String? = null
        val latch = CountDownLatch(1)
        takeScreenshot(Display.DEFAULT_DISPLAY, mainExecutor, object : TakeScreenshotCallback {
            override fun onSuccess(r: ScreenshotResult) {
                try {
                    val sw = Bitmap.wrapHardwareBuffer(r.hardwareBuffer, r.colorSpace)!!.copy(Bitmap.Config.ARGB_8888, false)
                    r.hardwareBuffer.close()
                    val sc = Bitmap.createScaledBitmap(sw, 960, sw.height * 960 / sw.width, true)
                    val bo = ByteArrayOutputStream(); sc.compress(Bitmap.CompressFormat.JPEG, 60, bo)
                    out = Base64.encodeToString(bo.toByteArray(), Base64.NO_WRAP)
                } catch (e: Exception) {}
                latch.countDown()
            }
            override fun onFailure(code: Int) { latch.countDown() }
        })
        latch.await(3, java.util.concurrent.TimeUnit.SECONDS)
        return out
    }

    // Joystick = 1 nét kéo liên tục (có rung nhẹ, rê dắt thì zigzag); nút A/B/C = nét chạm/giữ cùng lúc (đa điểm chạm)
    private fun act(p: JSONObject) {
        val (jx, jy) = pt(0); val jr = jrad()
        val ms = p.optLong("ms", 900).coerceIn(500, 1500)
        val dr = p.optBoolean("dribble")
        val pw = p.optDouble("power", .8).toFloat().coerceIn(.3f, 1f)
        val a0 = Math.toRadians(p.optDouble("angle", 0.0))
        val path = Path().apply {
            val sx = jx + rn(8f); val sy = jy + rn(8f)
            moveTo(sx, sy)
            for (i in 1..(if (dr) 6 else 3)) {
                val a = a0 + Math.toRadians(rn(7f).toDouble() + if (dr) (if (i % 2 == 0) 40.0 else -40.0) else 0.0)
                val r = jr * pw * (.85f + Random.nextFloat() * .15f)
                lineTo(sx + (cos(a) * r).toFloat(), sy - (sin(a) * r).toFloat())
            }
        }
        val g = GestureDescription.Builder().addStroke(GestureDescription.StrokeDescription(path, 0, ms))
        val btn = when (p.optString("btn")) { "A" -> 1; "B" -> 2; "C" -> 3; else -> -1 }
        if (btn >= 0) {
            val (bx, by) = pt(btn)
            val hold = when (btn) { 3 -> ms - 100; 2 -> p.optLong("hold", 150).coerceIn(80, 700); else -> 50L + Random.nextLong(40) }
            g.addStroke(GestureDescription.StrokeDescription(
                Path().apply { moveTo(bx + rn(6f), by + rn(6f)) }, Random.nextLong(60, 250), hold.coerceAtLeast(40)))
        }
        dispatchGesture(g.build(), null, null)
    }
}

object Ai {
    private const val MODEL = "claude-haiku-5-5" // nhanh nhất; đổi sang claude-sonnet-5-5 nếu muốn AI "thông minh" hơn
    private const val SYS = """You play Dream League Soccer on a phone through screenshots. Find the ball, the player you control (highlighted), teammates, opponents and both goals; work out which way your team attacks and which part of the pitch you are in.
Controls: joystick moves the player. A = short pass, B = shoot (hold longer = more power / long ball), C = sprint. When defending: chase the ball carrier, hold C to sprint, tap A to switch player or tackle. When attacking: carry the ball toward goal, dribble (zigzag) past defenders, pass to a free teammate, shoot when near the box with a clear angle.
Reply ONLY with JSON: {"angle":0-359 screen direction for the joystick (0=right,90=up,180=left,270=down),"power":0.3-1,"dribble":true/false,"btn":"A"|"B"|"C"|"none","hold":0-600 ms (for B),"ms":600-1400 how long to keep this move,"note":"3-word tactic"}"""

    fun decide(key: String, b64: String, last: String): JSONObject? = try {
        val img = JSONObject().put("type", "image").put("source",
            JSONObject().put("type", "base64").put("media_type", "image/jpeg").put("data", b64))
        val txt = JSONObject().put("type", "text").put("text", "Previous move: $last. Next move?")
        val body = JSONObject().put("model", MODEL).put("max_tokens", 120).put("system", SYS).put("messages",
            JSONArray().put(JSONObject().put("role", "user").put("content", JSONArray().put(img).put(txt))))
        val c = URL("https://api.anthropic.com/v1/messages").openConnection() as HttpURLConnection
        c.requestMethod = "POST"; c.doOutput = true; c.connectTimeout = 5000; c.readTimeout = 8000
        c.setRequestProperty("x-api-key", key)
        c.setRequestProperty("anthropic-version", "2023-06-01")
        c.setRequestProperty("content-type", "application/json")
        c.outputStream.use { it.write(body.toString().toByteArray()) }
        val t = JSONObject(c.inputStream.bufferedReader().readText()).getJSONArray("content").getJSONObject(0).getString("text")
        JSONObject(t.substring(t.indexOf('{'), t.lastIndexOf('}') + 1))
    } catch (e: Exception) { null }
}
