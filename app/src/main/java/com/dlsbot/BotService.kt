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
    private val TICK = 380L   // chu kỳ chụp + đọc minimap
    private val SEG = 1000L   // độ dài mỗi đoạn kéo joystick
    private val RAD = Math.PI / 180

    private val io = Executors.newSingleThreadExecutor()
    private val pool = Executors.newFixedThreadPool(3)
    private val ui = Handler(Looper.getMainLooper())
    private var tv: TextView? = null
    private var panel: View? = null
    private var spBtn: Button? = null
    private lateinit var wm: WindowManager
    private val prefs get() = getSharedPreferences("cfg", MODE_PRIVATE)
    // JOY, A, B, C, MAP1, MAP2 (tỉ lệ màn hình)
    private val D = arrayOf(.12f to .72f, .72f to .82f, .82f to .68f, .9f to .86f, .40f to .03f, .60f to .22f)

    @Volatile private var running = false
    @Volatile private var fast = false
    @Volatile private var pauseUntil = 0L
    // kết quả AI (chậm): vị trí % trên màn hình
    @Volatile private var aiStamp = 0L
    @Volatile private var aiHas = false
    @Volatile private var aiBall: DoubleArray? = null
    @Volatile private var aiMe: DoubleArray? = null
    @Volatile private var aiTo: DoubleArray? = null
    @Volatile private var aiAct = "run"
    @Volatile private var aiFresh = false
    @Volatile private var aiMsg = "chờ AI"
    // kết quả đọc minimap (nhanh)
    @Volatile private var attack = 0          // -1 tấn công trái, +1 tấn công phải, 0 chưa rõ
    @Volatile private var advance = 0.5f      // 0 = sát khung thành nhà, 1 = sát khung thành đối thủ
    @Volatile private var mapMsg = "chưa đặt"
    private val votes = CopyOnWriteArrayList<Int>()
    private val inflight = AtomicInteger(0)
    // trạng thái điều khiển (chỉ vòng lặp chính dùng)
    private var tac: Tactic? = null
    private var tacStart = 0L
    private var tacBase = 0.0
    private var lastHas = true
    private var segEnd = 0L

    private class Tactic(
        val name: String,
        val dur: Long,
        val off: (Float) -> Double = { 0.0 },
        val pw: (Float) -> Float = { 1f },
        val taps: List<Triple<Int, Long, Long>> = emptyList(),  // (nút 1=A 2=B 3=C, bắt đầu ms, giữ ms)
        val sprint: Boolean = false,
        val press: Boolean = false
    )

    private fun status(s: String) { ui.post { tv?.text = s } }
    private fun hide(h: Boolean) { ui.post { panel?.visibility = if (h) View.INVISIBLE else View.VISIBLE } }

    @Synchronized private fun addVote(v: Int, n: Int) {
        repeat(n) { votes.add(v) }
        while (votes.size > 12) votes.removeAt(0)
        val s = votes.sum()
        attack = if (s >= 3) 1 else if (s <= -3) -1 else 0
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
        val sp = Button(this).apply { text = "🐢" }
        sp.setOnClickListener { fast = !fast; sp.text = if (fast) "⚡" else "🐢" }
        spBtn = sp
        l.addView(sp)
        tv = TextView(this).apply { setTextColor(Color.WHITE); textSize = 10f; maxLines = 3; maxWidth = 650; text = "Sẵn sàng" }
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

    // ---- Tool setup: JOY, A, B, C và khung minimap (MAP1 góc trên-trái, MAP2 góc dưới-phải) ----
    private fun showSetup() {
        val names = arrayOf("JOY", "A", "B", "C", "MAP1", "MAP2")
        val pts = FloatArray(12) { if (it % 2 == 0) pt(it / 2).first else pt(it / 2).second }
        val jr = jrad()
        val v = object : View(this) {
            val p = Paint(Paint.ANTI_ALIAS_FLAG)
            var sel = -1
            override fun onDraw(c: Canvas) {
                c.drawColor(0x55000000)
                p.style = Paint.Style.STROKE; p.strokeWidth = 4f; p.color = 0xFF00E5FF.toInt()
                c.drawRect(min(pts[8], pts[10]), min(pts[9], pts[11]), max(pts[8], pts[10]), max(pts[9], pts[11]), p)
                p.style = Paint.Style.FILL
                p.textSize = 40f; p.textAlign = Paint.Align.CENTER
                for (i in 0..5) {
                    p.color = 0x99FF9800.toInt()
                    c.drawCircle(pts[i * 2], pts[i * 2 + 1], if (i == 0) jr else if (i < 4) jr * .5f else 26f, p)
                    p.color = Color.WHITE; c.drawText(names[i], pts[i * 2], pts[i * 2 + 1] + 14, p)
                }
                p.textSize = 30f
                c.drawText("Kéo MAP1, MAP2 phủ khung minimap rồi bấm LƯU", width / 2f, height - 30f, p)
                p.textSize = 40f
                p.color = 0xFF4CAF50.toInt(); c.drawRect(width / 2f - 120, 20f, width / 2f + 120, 110f, p)
                p.color = Color.WHITE; c.drawText("LƯU", width / 2f, 80f, p)
            }
            override fun onTouchEvent(e: MotionEvent): Boolean {
                when (e.action) {
                    MotionEvent.ACTION_DOWN -> {
                        if (e.y < 110 && abs(e.x - width / 2f) < 120) {
                            prefs.edit().apply { for (i in 0..5) { putFloat("x$i", pts[i * 2]); putFloat("y$i", pts[i * 2 + 1]) } }.apply()
                            wm.removeView(this); return true
                        }
                        sel = (0..5).minByOrNull { hypot(pts[it * 2] - e.x, pts[it * 2 + 1] - e.y) } ?: -1
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

    // ---- Vòng lặp chính: chụp -> đọc minimap -> (thỉnh thoảng) hỏi AI -> điều khiển ----
    private fun loop() {
        votes.clear(); attack = 0; aiStamp = 0; aiFresh = false; aiHas = false
        aiBall = null; aiMe = null; aiTo = null; aiMsg = "chờ AI"
        tac = null; segEnd = 0; lastHas = true
        var lastAi = 0L
        while (running) {
            val t0 = System.currentTimeMillis()
            val bmp = shoot()
            if (bmp == null) { status("Chụp màn hình lỗi"); Thread.sleep(400); continue }
            try {
                readMap(bmp)
                val now = System.currentTimeMillis()
                if (now >= pauseUntil && now - lastAi >= (if (fast) 800L else 4400L) && inflight.get() < 3) {
                    lastAi = now
                    val key = prefs.getString("key", "") ?: ""
                    val b64 = jpeg(bmp)
                    val hint = when (attack) { 1 -> "right"; -1 -> "left"; else -> "unknown" }
                    inflight.incrementAndGet()
                    pool.execute {
                        try {
                            val (d, msg) = Ai.decide(key, b64, hint)
                            aiMsg = msg
                            if (d == null) {
                                if (msg.startsWith("HTTP 429")) {
                                    pauseUntil = System.currentTimeMillis() + 6000
                                    if (fast) { fast = false; ui.post { spBtn?.text = "🐢" } }
                                }
                                return@execute
                            }
                            if (!running) return@execute
                            aiBall = arr(d, "ball"); aiMe = arr(d, "me"); aiTo = arr(d, "to")
                            aiHas = d.optBoolean("hasBall")
                            aiAct = d.optString("act", "run")
                            aiStamp = System.currentTimeMillis()
                            aiFresh = true
                            when (d.optString("attack")) { "right" -> addVote(1, 2); "left" -> addVote(-1, 2) }
                        } catch (e: Exception) {
                            aiMsg = ("Lỗi: " + e.message).take(40)
                        } finally {
                            inflight.decrementAndGet()
                        }
                    }
                }
                if (now >= segEnd - TICK || aiFresh) { control(now); segEnd = now + SEG }
            } finally {
                bmp.recycle()
            }
            val el = System.currentTimeMillis() - t0
            if (el < TICK) Thread.sleep(TICK - el)
        }
        status("Đã dừng")
    }

    private fun arr(d: JSONObject, k: String): DoubleArray? =
        d.optJSONArray(k)?.let { if (it.length() >= 2) doubleArrayOf(it.optDouble(0), it.optDouble(1)) else null }

    private fun shoot(): Bitmap? {
        var out: Bitmap? = null
        hide(true) // ẩn menu để không lọt vào ảnh
        try {
            Thread.sleep(80)
            val latch = CountDownLatch(1)
            takeScreenshot(Display.DEFAULT_DISPLAY, mainExecutor, object : TakeScreenshotCallback {
                override fun onSuccess(r: ScreenshotResult) {
                    try {
                        out = Bitmap.wrapHardwareBuffer(r.hardwareBuffer, r.colorSpace)!!.copy(Bitmap.Config.ARGB_8888, false)
                        r.hardwareBuffer.close()
                    } catch (e: Exception) {}
                    latch.countDown()
                }
                override fun onFailure(code: Int) { latch.countDown() }
            })
            latch.await(2, java.util.concurrent.TimeUnit.SECONDS)
        } finally {
            hide(false)
        }
        return out
    }

    private fun jpeg(bmp: Bitmap): String {
        val sc = Bitmap.createScaledBitmap(bmp, 960, bmp.height * 960 / bmp.width, true)
        val bo = ByteArrayOutputStream(); sc.compress(Bitmap.CompressFormat.JPEG, 60, bo)
        return Base64.encodeToString(bo.toByteArray(), Base64.NO_WRAP)
    }

    // ---- Đọc minimap: chấm đỏ = đội mình, chấm màu khác (không xám/xanh lá) = đối thủ ----
    private fun readMap(bmp: Bitmap) {
        val sx = bmp.width / bounds().width().toFloat()
        val sy = bmp.height / bounds().height().toFloat()
        val (x1, y1) = pt(4); val (x2, y2) = pt(5)
        val l = (min(x1, x2) * sx).toInt().coerceIn(0, bmp.width - 2)
        val r = (max(x1, x2) * sx).toInt().coerceIn(l + 1, bmp.width)
        val t = (min(y1, y2) * sy).toInt().coerceIn(0, bmp.height - 2)
        val b = (max(y1, y2) * sy).toInt().coerceIn(t + 1, bmp.height)
        val w = r - l; val h = b - t
        if (w < 30 || h < 15) { mapMsg = "kéo MAP1/MAP2 phủ minimap"; return }
        val px = IntArray(w * h)
        bmp.getPixels(px, 0, w, l, t, w, h)
        var rMin = w; var rMax = -1; var rSum = 0L; var rN = 0
        var oMin = w; var oMax = -1; var oSum = 0L; var oN = 0
        for (y in 0 until h) for (x in 0 until w) {
            val c = px[y * w + x]
            val cr = (c shr 16) and 255; val cg = (c shr 8) and 255; val cb = c and 255
            if (max(cr, max(cg, cb)) - min(cr, min(cg, cb)) < 80) continue
            if (cr >= 150 && cg <= 100 && cb <= 100) {
                if (x < rMin) rMin = x
                if (x > rMax) rMax = x
                rSum += x; rN++
            } else if (!(cg > cr && cg > cb)) {
                if (x < oMin) oMin = x
                if (x > oMax) oMax = x
                oSum += x; oN++
            }
        }
        if (rN < 6 || oN < 6) { mapMsg = "không thấy chấm đỏ/đối thủ"; return }
        val tol = w * 0.03
        val left = if (rMin < oMin - tol) 1 else if (oMin < rMin - tol) -1 else 0
        val right = if (rMax > oMax + tol) 1 else if (oMax > rMax + tol) -1 else 0
        val mr = rSum.toDouble() / rN; val mo = oSum.toDouble() / oN
        if (left == 1 && right == -1) addVote(1, 2)         // thủ môn nhà bên trái -> tấn công phải
        else if (left == -1 && right == 1) addVote(-1, 2)   // thủ môn nhà bên phải -> tấn công trái
        else if (abs(mr - mo) > w * 0.08) addVote(if (mr < mo) 1 else -1, 1)
        val cx = (mr / w).toFloat()
        advance = if (attack >= 0) cx else 1f - cx
        mapMsg = "đỏ $rN / đối thủ $oN"
    }

    // ---- Thư viện chiến thuật (d = hướng tấn công: +1 phải, -1 trái) ----
    private fun library(d: Int, adv: Float, meY: Double): List<Pair<Int, Tactic>> {
        val side = if (meY < 50) 1.0 else -1.0
        val w = side * d * 45 * RAD   // lệch về phía mép sân gần nhất
        fun zig(t: Float) = (if ((t * 3.5f).toInt() % 2 == 0) 1.0 else -1.0) * 38 * RAD
        val straight = Tactic("Thẳng tiến", 2000, sprint = true)
        val zigzag = Tactic("Zigzag", 2200, off = { t -> zig(t) })
        val slalom = Tactic("Slalom", 2200, off = { t -> sin(t * 7.0) * 35 * RAD })
        val wing = Tactic("Rê cánh", 2400, off = { t -> if (t < 1.3f) w else w / 4 }, sprint = true)
        val cross = Tactic("Tạt cánh", 2400, off = { t -> if (t < 1.3f) w else w / 4 },
            taps = listOf(Triple(1, 1700L, 60L)), sprint = true)
        val cut = Tactic("Cắt vào trong", 1800, off = { t -> if (t < 0.9f) -w * 0.9 else 0.0 })
        val oneTwo = Tactic("Một-hai", 1800, taps = listOf(Triple(1, 250L, 60L)))
        val feint = Tactic("Nhử rồi bứt", 2000, pw = { t -> if (t in 0.7f..1.0f) 0.25f else 1f }, sprint = true)
        val shot = Tactic("Sút xa", 1400, taps = listOf(Triple(2, 400L, 380L)))
        return when {
            adv < .35f -> listOf(3 to straight, 3 to wing, 2 to oneTwo, 1 to zigzag, 1 to slalom)
            adv < .65f -> listOf(2 to zigzag, 2 to slalom, 2 to cut, 2 to wing, 2 to feint, 1 to oneTwo, 1 to straight)
            else -> listOf(3 to shot, 2 to cut, 2 to feint, 2 to cross, 1 to zigzag, 1 to straight)
        }
    }

    private fun pick(l: List<Pair<Int, Tactic>>): Tactic {
        var r = Random.nextInt(l.sumOf { it.first })
        for ((w, t) in l) { r -= w; if (r < 0) return t }
        return l[0].second
    }

    // ---- Quyết định: mất bóng -> ép sát; AI báo sút/chuyền -> làm ngay; còn lại -> chiến thuật theo minimap ----
    private fun control(now: Long) {
        val fresh = aiFresh
        aiFresh = false
        val act = if (fresh) aiAct else "run"
        val me = aiMe; val ball = aiBall; val to = aiTo
        val ok = now - aiStamp < (if (fast) 4000L else 14000L)
        val has = aiHas
        val W = bounds().width().toFloat(); val H = bounds().height().toFloat()
        fun ang(a: DoubleArray, b: DoubleArray) = atan2((a[1] - b[1]) / 100.0 * H, (b[0] - a[0]) / 100.0 * W)
        val d = if (attack != 0) attack else if ((me?.get(0) ?: 50.0) < 50.0) 1 else -1
        val head = if (d > 0) "→" else "←"

        if (ok && !has && ball != null && me != null) {
            val far = hypot((ball[0] - me[0]) / 100.0 * W, (ball[1] - me[1]) / 100.0 * H) > H * .25
            val p = Tactic("Ép sát (đè B)", 1000, sprint = far, press = true)
            lastHas = false
            status("${p.name}\nMAP ${mapMsg} | AI ${aiMsg}")
            emit(p, ang(me, ball), 0)
            return
        }
        if (ok && has && me != null && to != null && (act == "shoot" || act == "pass")) {
            val t2 = if (act == "shoot") Tactic("SÚT", 900, taps = listOf(Triple(2, 120L, 380L)))
                     else Tactic("CHUYỀN", 800, taps = listOf(Triple(1, 120L, 60L)))
            tac = t2; tacStart = now; tacBase = ang(me, to); lastHas = true
            status("${t2.name}\nMAP ${mapMsg} | AI ${aiMsg}")
            emit(t2, tacBase, 0)
            return
        }
        val cur = tac
        if (cur == null || now - tacStart > cur.dur || !lastHas) {
            tac = pick(library(d, advance, me?.get(1) ?: 50.0))
            tacStart = now
            tacBase = if (d > 0) 0.0 else Math.PI
        }
        lastHas = true
        val tt = tac!!
        status("${tt.name} $head\nMAP ${mapMsg} | AI ${aiMsg}")
        emit(tt, tacBase, now - tacStart)
    }

    // Một đoạn cử chỉ: joystick kéo theo đường cong của chiến thuật + các nút bấm cùng lúc (đa điểm chạm)
    private fun emit(tc: Tactic, base: Double, rel: Long) {
        val (jx, jy) = pt(0); val jr = jrad()
        val path = Path()
        path.moveTo(jx + rn(8f), jy + rn(8f))
        for (k in 1..5) {
            val t = (rel + k * SEG / 5) / 1000f
            val a = base + tc.off(t) + Math.toRadians(rn(4f).toDouble())
            val r = jr * tc.pw(t) * (.92f + Random.nextFloat() * .08f)
            path.lineTo(jx + (cos(a) * r).toFloat(), jy - (sin(a) * r).toFloat())
        }
        val g = GestureDescription.Builder()
        g.addStroke(GestureDescription.StrokeDescription(path, 0, SEG))
        fun btn(i: Int, start: Long, hold: Long) {
            val (bx, by) = pt(i)
            g.addStroke(GestureDescription.StrokeDescription(
                Path().apply { moveTo(bx + rn(6f), by + rn(6f)) }, start, hold.coerceAtLeast(40)))
        }
        for ((b, s, h) in tc.taps) if (s >= rel && s < rel + SEG) btn(b, s - rel, h + Random.nextLong(-20, 40))
        if (tc.sprint) btn(3, 0, SEG - 80)
        if (tc.press) btn(2, Random.nextLong(40, 120), SEG - 160)
        if (!dispatchGesture(g.build(), null, null)) status("Hệ thống từ chối cử chỉ")
    }
}

object Ai {
    private val MODELS = arrayOf("gemini-2.5-flash-lite", "gemini-flash-lite-latest", "gemini-2.5-flash")
    @Volatile private var mi = 0
    private const val SYS = """You play Dream League Soccer on a phone from one landscape screenshot. Ignore the small overlay buttons at the top-left corner and the on-screen touch controls.
All coordinates are percentages of the screenshot: [x from 0 (left) to 100 (right), y from 0 (top) to 100 (bottom)].
My team wears RED shirts (red dots on the small radar/minimap); the other color is the opponent. Goalkeepers wear a different color from their team.
Locate carefully:
- ball = the center of the ball.
- me = the center of the player I control (he wears red and has an arrow or ring marker).
- hasBall = true only if the ball is at his feet.
- attack = the side of the screen ("left" or "right") of the goal my red team attacks, i.e. the goal defended by the opponents' goalkeeper. Teams swap sides at half time, so decide from THIS screenshot; a recent estimate is given as a hint, keep it unless the screenshot clearly shows otherwise; "unknown" if unsure.
Then choose act:
- hasBall false: act "run", to = the ball.
- hasBall true: act "run" (default, to = a point ahead toward the goal I attack), "dribble" when a defender is close and ahead, "pass" (to = a free red teammate) when a defender blocks the way, "shoot" (to = a corner of the goal I attack) only near the penalty box with a clear angle.
Reply ONLY with JSON in this order: {"ball":[x,y],"me":[x,y],"hasBall":true|false,"to":[x,y],"act":"run"|"dribble"|"pass"|"shoot","attack":"left"|"right"|"unknown"}"""

    fun decide(key: String, b64: String, hint: String): Pair<JSONObject?, String> {
        if (key.isBlank()) return null to "Chưa nhập API key"
        return try {
            val img = JSONObject().put("inline_data", JSONObject().put("mime_type", "image/jpeg").put("data", b64))
            val txt = JSONObject().put("text", "Recent attack-side estimate: $hint. Decide the next move.")
            val body = JSONObject()
                .put("system_instruction", JSONObject().put("parts", JSONArray().put(JSONObject().put("text", SYS))))
                .put("contents", JSONArray().put(JSONObject().put("role", "user").put("parts", JSONArray().put(img).put(txt))))
                .put("generationConfig", JSONObject().put("maxOutputTokens", 250).put("temperature", 0.2).put("responseMimeType", "application/json"))
            val c = URL("https://generativelanguage.googleapis.com/v1beta/models/${MODELS[mi]}:generateContent").openConnection() as HttpURLConnection
            c.requestMethod = "POST"; c.doOutput = true; c.connectTimeout = 5000; c.readTimeout = 10000
            c.setRequestProperty("x-goog-api-key", key)
            c.setRequestProperty("content-type", "application/json")
            c.outputStream.use { it.write(body.toString().toByteArray()) }
            val code = c.responseCode
            if (code != 200) {
                val err = (c.errorStream?.bufferedReader()?.readText() ?: "").replace("\n", " ").take(40)
                val tried = MODELS[mi]
                if ((code == 404 || code == 400) && err.contains("model", true) && mi < MODELS.size - 1) mi++
                return null to "HTTP $code $tried: $err"
            }
            val
