package com.dlsbot

import android.accessibilityservice.AccessibilityService
import android.accessibilityservice.GestureDescription
import android.content.Context
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

// Một biểu tượng cầu thủ trên minimap (toạ độ trong ảnh đã cắt đúng vùng minimap)
class Blob(val x: Float, val y: Float, val n: Int, val x0: Int, val x1: Int, val y0: Int, val y1: Int)

// Kết quả đọc minimap
class Radar(
    val w: Int, val h: Int,
    val reds: List<Blob>,              // cầu thủ áo đỏ (đội mình)
    val opps: List<Blob>,              // cầu thủ đội kia
    val mine: Blob?,                   // áo đỏ có vầng sáng = đội mình đang cầm bóng
    val foreign: Pair<Float, Float>?,  // vầng sáng không dính áo đỏ = đối phương cầm bóng hoặc bóng lỏng
    val oppHas: Boolean                // vầng sáng đó dính vào cầu thủ đội kia = đối phương đang cầm bóng
)

// Dải xanh lơ ở mép màn hình = phía khung thành đối thủ (không đụng vào vùng minimap)
class Hud(ctx: Context) : View(ctx) {
    @Volatile var attack = 0
    private val p = Paint(Paint.ANTI_ALIAS_FLAG)
    override fun onDraw(c: Canvas) {
        if (attack == 0) return
        p.style = Paint.Style.FILL; p.color = 0x8800E5FF.toInt()
        val bw = width * 0.05f
        if (attack > 0) {
            c.drawRect(width - bw, height * 0.2f, width.toFloat(), height * 0.8f, p)
        } else {
            c.drawRect(0f, height * 0.2f, bw, height * 0.8f, p)
        }
    }
}

class BotService : AccessibilityService() {
    private val TICK = 380L        // chu kỳ chụp + đọc minimap
    private val SEG = 800L         // độ dài mỗi cử chỉ
    private val RAD = Math.PI / 180
    private val PASS_MIN = 70L     // chuyền gần: chạm nhẹ (ms giữ B). Chuyền yếu quá thì tăng
    private val PASS_MAX = 520L    // chuyền xa: giữ lâu nhất (ms). Chuyền mạnh quá thì giảm
    private val SHOOT_ADV = 0.78f  // người cầm bóng tiến quá 78% sân (tính theo minimap) = trong tầm sút/vòng cấm
    private val BOX_ADV = 0.62f    // quá 62% sân = bắt đầu áp sát vòng cấm

    private val io = Executors.newSingleThreadExecutor()
    private val pool = Executors.newFixedThreadPool(3)
    private val ui = Handler(Looper.getMainLooper())
    private var tv: TextView? = null
    private var panel: View? = null
    private var panelLp: WindowManager.LayoutParams? = null
    private var hud: Hud? = null
    private var spBtn: Button? = null
    private lateinit var wm: WindowManager
    private val prefs get() = getSharedPreferences("cfg", MODE_PRIVATE)
    // JOY, A, B, C, MAP1, MAP2 (tỉ lệ màn hình)
    private val D = arrayOf(.12f to .72f, .72f to .82f, .82f to .68f, .9f to .86f, .40f to .03f, .60f to .22f)

    @Volatile private var running = false
    @Volatile private var fast = false
    @Volatile private var pauseUntil = 0L
    @Volatile private var aiMsg = "chờ AI"
    @Volatile private var attack = 0          // -1 tấn công trái, +1 tấn công phải, 0 chưa rõ
    private val votes = CopyOnWriteArrayList<Int>()
    private val inflight = AtomicInteger(0)
    // trạng thái điều khiển (chỉ vòng lặp chính dùng)
    private var tac: Tactic? = null
    private var tacStart = 0L
    private var tacBase = 0.0
    private var segEnd = 0L
    private var shotUntil = 0L
    private var crossUntil = 0L
    private var switchUntil = 0L
    private var slideUntil = 0L
    private var noPressUntil = 0L
    private var hasBall = true
    private var lostTicks = 0
    private var justLost = false
    private var lastCarrier: Pair<Float, Float>? = null
    // hàng đợi cử chỉ: chỉ 1 cử chỉ chạy một lúc, không bao giờ ngắt giữa chừng (tránh kẹt/liệt nút)
    @Volatile private var busy = false
    @Volatile private var busySince = 0L
    private var pendingG: GestureDescription? = null

    private class Tactic(
        val name: String,
        val dur: Long,
        val off: (Float) -> Double = { 0.0 },
        val pw: (Float) -> Float = { 1f },
        val taps: List<Triple<Int, Long, Long>> = emptyList(),  // (nút 1=A xoạc/sút, 2=B chuyền/kèm, 3=C tạt/đổi người; bắt đầu ms, giữ ms)
        val steady: Boolean = false,   // true = joystick giữ thẳng, không rung (để chuyền chính xác)
        val press: Boolean = false
    )

    private fun status(s: String) { ui.post { tv?.text = s } }

    @Synchronized private fun addVote(v: Int, n: Int) {
        repeat(n) { votes.add(v) }
        while (votes.size > 12) votes.removeAt(0)
        val s = votes.sum()
        attack = if (s >= 3) 1 else if (s <= -3) -1 else 0
    }

    override fun onServiceConnected() {
        wm = getSystemService(WINDOW_SERVICE) as WindowManager
        val h = Hud(this)
        hud = h
        wm.addView(h, WindowManager.LayoutParams(-1, -1, WindowManager.LayoutParams.TYPE_ACCESSIBILITY_OVERLAY,
            WindowManager.LayoutParams.FLAG_NOT_FOCUSABLE or WindowManager.LayoutParams.FLAG_NOT_TOUCHABLE or
                WindowManager.LayoutParams.FLAG_LAYOUT_IN_SCREEN or WindowManager.LayoutParams.FLAG_LAYOUT_NO_LIMITS,
            PixelFormat.TRANSLUCENT))
        fun mk(t: String) = Button(this).apply { text = t; textSize = 18f; minWidth = 120; minHeight = 100; setPadding(10, 0, 10, 0) }
        val l = LinearLayout(this).apply { setBackgroundColor(0xAA000000.toInt()) }
        val go = mk("▶")
        go.setOnClickListener {
            running = !running
            go.text = if (running) "⏹" else "▶"
            if (running) io.execute { loop() }
        }
        l.addView(go)
        l.addView(mk("⚙").apply { setOnClickListener { showSetup() } })
        val sp = mk("🐢")
        sp.setOnClickListener { fast = !fast; sp.text = if (fast) "⚡" else "🐢" }
        spBtn = sp
        l.addView(sp)
        tv = TextView(this).apply { setTextColor(Color.WHITE); textSize = 10f; maxLines = 3; maxWidth = 600; text = "Sẵn sàng" }
        l.addView(tv)
        panel = l
        val lp = WindowManager.LayoutParams(-2, -2, WindowManager.LayoutParams.TYPE_ACCESSIBILITY_OVERLAY,
            WindowManager.LayoutParams.FLAG_NOT_FOCUSABLE, PixelFormat.TRANSLUCENT)
        lp.gravity = Gravity.TOP or Gravity.START
        panelLp = lp
        wm.addView(l, lp)
        placePanel()
    }
    override fun onAccessibilityEvent(e: AccessibilityEvent?) {}
    override fun onInterrupt() { running = false }

    private fun bounds() = wm.currentWindowMetrics.bounds
    private fun pt(i: Int): Pair<Float, Float> = bounds().let {
        prefs.getFloat("x$i", it.width() * D[i].first) to prefs.getFloat("y$i", it.height() * D[i].second)
    }
    private fun jrad() = min(bounds().width(), bounds().height()) * 0.12f
    private fun rn(x: Float) = Random.nextFloat() * 2 * x - x

    // Đặt thanh điều khiển ở góc đối diện minimap để không che minimap
    private fun placePanel() {
        val lp = panelLp ?: return
        val (x1, _) = pt(4); val (x2, _) = pt(5)
        lp.gravity = if ((x1 + x2) / 2f < bounds().width() / 2f) Gravity.TOP or Gravity.END else Gravity.TOP or Gravity.START
        ui.post { panel?.let { wm.updateViewLayout(it, lp) } }
    }

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
                c.drawText("Kéo MAP1, MAP2 ôm sát sân trong minimap (bot chỉ đọc vùng này); A, B, C đúng nút trong game", width / 2f, height - 30f, p)
                p.textSize = 40f
                p.color = 0xFF4CAF50.toInt(); c.drawRect(width / 2f - 120, 20f, width / 2f + 120, 110f, p)
                p.color = Color.WHITE; c.drawText("LƯU", width / 2f, 80f, p)
            }
            override fun onTouchEvent(e: MotionEvent): Boolean {
                when (e.action) {
                    MotionEvent.ACTION_DOWN -> {
                        if (e.y < 110 && abs(e.x - width / 2f) < 120) {
                            prefs.edit().apply { for (i in 0..5) { putFloat("x$i", pts[i * 2]); putFloat("y$i", pts[i * 2 + 1]) } }.apply()
                            wm.removeView(this)
                            placePanel()
                            return true
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

    // ---- Vòng lặp chính: chụp CHỈ vùng minimap -> đọc -> (thỉnh thoảng) hỏi AI -> điều khiển ----
    private fun loop() {
        votes.clear(); attack = 0; aiMsg = "chờ AI"
        tac = null; segEnd = 0; shotUntil = 0; crossUntil = 0; switchUntil = 0; slideUntil = 0; noPressUntil = 0
        hasBall = true; lostTicks = 0; lastCarrier = null; justLost = false
        var lastAi = 0L
        while (running) {
            val t0 = System.currentTimeMillis()
            val map = grabMap()
            if (map == null) { status("Chưa chụp được minimap (bấm ⚙ đặt MAP1/MAP2)"); Thread.sleep(500); continue }
            try {
                val now = System.currentTimeMillis()
                val rd = scan(map)
                voteAttack(rd)
                hud?.let { it.attack = attack; it.postInvalidate() }
                val prev = hasBall
                if (rd.mine != null) {
                    hasBall = true; lostTicks = 0
                } else {
                    lostTicks++
                    if (rd.foreign != null || lostTicks >= 2) hasBall = false
                }
                if (prev && !hasBall) justLost = true
                if (now >= pauseUntil && now - lastAi >= (if (fast) 800L else 4400L) && inflight.get() < 3) {
                    lastAi = now
                    val key = prefs.getString("key", "") ?: ""
                    val b64 = jpeg(map)
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
                            when (d.optString("attack")) { "right" -> addVote(1, 2); "left" -> addVote(-1, 2) }
                        } catch (e: Exception) {
                            aiMsg = ("Lỗi: " + e.message).take(40)
                        } finally {
                            inflight.decrementAndGet()
                        }
                    }
                }
                // mất/được bóng thì quyết định lại NGAY, còn lại đổi đoạn mỗi ~0,8 giây
                if (hasBall != prev || now >= segEnd - TICK) {
                    control(now, rd)
                    segEnd = now + SEG
                }
            } finally {
                map.recycle()
            }
            val el = System.currentTimeMillis() - t0
            if (el < TICK) Thread.sleep(TICK - el)
        }
        hud?.let { it.attack = 0; it.postInvalidate() }
        synchronized(this) { pendingG = null }
        status("Đã dừng")
    }

    // Chụp màn hình rồi CẮT NGAY vùng minimap, bỏ phần còn lại
    private fun grabMap(): Bitmap? {
        val (x1, y1) = pt(4); val (x2, y2) = pt(5)
        var out: Bitmap? = null
        val latch = CountDownLatch(1)
        takeScreenshot(Display.DEFAULT_DISPLAY, mainExecutor, object : TakeScreenshotCallback {
            override fun onSuccess(r: ScreenshotResult) {
                try {
                    val full = Bitmap.wrapHardwareBuffer(r.hardwareBuffer, r.colorSpace)!!.copy(Bitmap.Config.ARGB_8888, false)
                    r.hardwareBuffer.close()
                    val sx = full.width / bounds().width().toFloat()
                    val sy = full.height / bounds().height().toFloat()
                    val l = (min(x1, x2) * sx).toInt().coerceIn(0, full.width - 2)
                    val rr = (max(x1, x2) * sx).toInt().coerceIn(l + 1, full.width)
                    val t = (min(y1, y2) * sy).toInt().coerceIn(0, full.height - 2)
                    val b = (max(y1, y2) * sy).toInt().coerceIn(t + 1, full.height)
                    if (rr - l >= 30 && b - t >= 15) {
                        val crop = Bitmap.createBitmap(full, l, t, rr - l, b - t)
                        if (crop !== full) full.recycle()
                        out = crop
                    } else {
                        full.recycle()
                    }
                } catch (e: Exception) {}
                latch.countDown()
            }
            override fun onFailure(code: Int) { latch.countDown() }
        })
        latch.await(2, java.util.concurrent.TimeUnit.SECONDS)
        return out
    }

    private fun jpeg(bmp: Bitmap): String {
        val sw = 480
        val sh = max(1, bmp.height * sw / bmp.width)
        val sc = Bitmap.createScaledBitmap(bmp, sw, sh, true)
        val bo = ByteArrayOutputStream(); sc.compress(Bitmap.CompressFormat.JPEG, 80, bo)
        return Base64.encodeToString(bo.toByteArray(), Base64.NO_WRAP)
    }

    // ---- Đọc minimap: áo đỏ = đội mình, màu khác = đối thủ, vầng sáng trắng/hồng = người cầm bóng ----
    private fun scan(bmp: Bitmap): Radar {
        val w = bmp.width; val h = bmp.height
        val px = IntArray(w * h)
        bmp.getPixels(px, 0, w, 0, 0, w, h)
        val red = BooleanArray(w * h); val opp = BooleanArray(w * h); val glw = BooleanArray(w * h)
        for (i in px.indices) {
            val c = px[i]
            val cr = (c shr 16) and 255; val cg = (c shr 8) and 255; val cb = c and 255
            if (cr >= 215 && cg >= 130 && cb >= 130) { glw[i] = true; continue }
            if (cr >= 140 && cg <= 110 && cb <= 110 && cr - cg >= 70) { red[i] = true; continue }
            val top = max(cr, max(cg, cb)); val low = min(cr, min(cg, cb))
            if (top - low < 80) continue
            val redDom = cr == top && cg * 4 <= cr * 3 && cb * 4 <= cr * 3
            val greenDom = cg == top && cg > cr && cg > cb
            if (!redDom && !greenDom) opp[i] = true
        }
        val reds = blobsOf(red, w, h, 5)
        val opps = blobsOf(opp, w, h, 5)
        // vầng sáng dính vào áo đỏ nào nhiều nhất -> đội mình đang cầm bóng
        var mine: Blob? = null
        var bestG = 0
        val attached = BooleanArray(w * h)
        for (r in reds) {
            val ex = ((r.x1 - r.x0 + 1) * 0.6f).toInt() + 2
            val ey = ((r.y1 - r.y0 + 1) * 0.6f).toInt() + 2
            var cnt = 0
            for (y in max(0, r.y0 - ey)..min(h - 1, r.y1 + ey)) for (x in max(0, r.x0 - ex)..min(w - 1, r.x1 + ex)) {
                if (glw[y * w + x]) { cnt++; attached[y * w + x] = true }
            }
            if (cnt > bestG) { bestG = cnt; mine = r }
        }
        if (bestG < 4) mine = null
        var fN = 0; var fx = 0L; var fy = 0L
        for (i in glw.indices) if (glw[i] && !attached[i]) { fN++; fx += i % w; fy += i / w }
        val foreign = if (fN >= 4) Pair(fx.toFloat() / fN, fy.toFloat() / fN) else null
        var oppHas = false
        if (foreign != null) {
            for (o in opps) {
                val ex = ((o.x1 - o.x0 + 1) * 0.6f).toInt() + 2
                val ey = ((o.y1 - o.y0 + 1) * 0.6f).toInt() + 2
                if (foreign.first >= o.x0 - ex && foreign.first <= o.x1 + ex && foreign.second >= o.y0 - ey && foreign.second <= o.y1 + ey) { oppHas = true; break }
            }
        }
        return Radar(w, h, reds, opps, mine, foreign, oppHas)
    }

    private fun blobsOf(mask: BooleanArray, w: Int, h: Int, minN: Int): List<Blob> {
        val seen = BooleanArray(w * h)
        val stack = IntArray(w * h)
        val out = ArrayList<Blob>()
        for (s in mask.indices) {
            if (!mask[s] || seen[s]) continue
            var sp = 0
            stack[sp++] = s; seen[s] = true
            var n = 0; var sx = 0L; var sy = 0L
            var x0 = w; var x1 = 0; var y0 = h; var y1 = 0
            while (sp > 0) {
                val i = stack[--sp]
                val x = i % w; val y = i / w
                n++; sx += x; sy += y
                if (x < x0) x0 = x
                if (x > x1) x1 = x
                if (y < y0) y0 = y
                if (y > y1) y1 = y
                for (dy in -1..1) for (dx in -1..1) {
                    val nx = x + dx; val ny = y + dy
                    if (nx < 0 || ny < 0 || nx >= w || ny >= h) continue
                    val j = ny * w + nx
                    if (mask[j] && !seen[j]) { seen[j] = true; stack[sp++] = j }
                }
            }
            if (n >= minN) out.add(Blob(sx.toFloat() / n, sy.toFloat() / n, n, x0, x1, y0, y1))
        }
        return out
    }

    // Hướng tấn công: đội nào có người sát mép trái/phải minimap (thủ môn) là đội phòng ngự bên đó
    private fun voteAttack(rd: Radar) {
        if (rd.reds.size < 2 || rd.opps.size < 2) return
        val w = rd.w
        val rMin = rd.reds.minOf { it.x0 }; val rMax = rd.reds.maxOf { it.x1 }
        val oMin = rd.opps.minOf { it.x0 }; val oMax = rd.opps.maxOf { it.x1 }
        val tol = w * 0.03
        val left = if (rMin < oMin - tol) 1 else if (oMin < rMin - tol) -1 else 0
        val right = if (rMax > oMax + tol) 1 else if (oMax > rMax + tol) -1 else 0
        val mr = rd.reds.map { it.x.toDouble() }.average()
        val mo = rd.opps.map { it.x.toDouble() }.average()
        if (left == 1 && right == -1) {
            addVote(1, 2)        // thủ môn nhà bên trái -> tấn công phải
        } else if (left == -1 && right == 1) {
            addVote(-1, 2)       // thủ môn nhà bên phải -> tấn công trái
        } else if (abs(mr - mo) > w * 0.08) {
            addVote(if (mr < mo) 1 else -1, 1)
        }
    }

    // ---- Thư viện rê bóng (d = hướng tấn công: +1 phải, -1 trái) ----
    private fun library(d: Int, side: Double): List<Pair<Int, Tactic>> {
        val w = side * d * 45 * RAD   // lệch về phía mép sân gần nhất
        fun zig(t: Float) = (if ((t * 3.5f).toInt() % 2 == 0) 1.0 else -1.0) * 38 * RAD
        val straight = Tactic("Thẳng tiến", 1600)
        val zigzag = Tactic("Zigzag", 2000, off = { t -> zig(t) })
        val slalom = Tactic("Slalom", 2000, off = { t -> sin(t * 7.0) * 35 * RAD })
        val wing = Tactic("Rê cánh", 2000, off = { t -> if (t < 1.1f) w else w / 4 })
        val cut = Tactic("Cắt vào trong", 1600, off = { t -> if (t < 0.9f) -w * 0.9 else 0.0 })
        val feint = Tactic("Nhử rồi bứt", 1800, pw = { t -> if (t in 0.7f..1.0f) 0.25f else 1f })
        return listOf(3 to zigzag, 3 to slalom, 2 to cut, 2 to wing, 2 to feint, 1 to straight)
    }

    private fun pick(l: List<Pair<Int, Tactic>>): Tactic {
        var r = Random.nextInt(l.sumOf { it.first })
        for ((w, t) in l) { r -= w; if (r < 0) return t }
        return l[0].second
    }

    // Lực chuyền = thời gian giữ B: đồng đội gần thì chạm nhẹ, xa thì giữ lâu hơn (PASS_MIN..PASS_MAX ms)
    private fun passHold(dist: Float, W: Float, H: Float): Long {
        val f = ((dist - H * .1f) / (W * .4f - H * .1f)).coerceIn(0f, 1f)
        return PASS_MIN + (f * (PASS_MAX - PASS_MIN)).toLong()
    }

    // Chọn đồng đội (áo đỏ khác) để chuyền: ưu tiên người ở phía trước, gần trục ngang, không quá xa
    private fun pickMate(me: Blob, all: List<Blob>, d: Int, W: Float, H: Float): Blob? {
        var best: Blob? = null
        var bs = -1e9f
        for (m in all) {
            if (m === me) continue
            val dist = hypot(m.x - me.x, m.y - me.y)
            if (dist < H * .08f || dist > W * .45f) continue
            val fwd = (m.x - me.x) * d
            val s = fwd * 0.6f - abs(m.y - me.y) * 0.25f - dist * 0.1f - (if (dist > W * .3f) 200f else 0f) - (if (fwd < 0) 100f else 0f)
            if (s > bs) { bs = s; best = m }
        }
        return best
    }

    // ---- Quyết định: mất bóng -> ĐÈ B + joystick (+C đổi người, +A xoạc); trong tầm sút -> sút (A) / tạt (C); còn lại chuyền ban bật (B) / rê ----
    private fun control(now: Long, rd: Radar) {
        val w = rd.w.toFloat(); val h = rd.h.toFloat()
        val d = if (attack != 0) attack else 1
        val head = if (d > 0) "→" else "←"
        val who = if (hasBall) "mình" else if (rd.oppHas) "kia" else if (rd.foreign != null) "lỏng" else "?"
        val me = rd.mine
        val adv = if (me == null) -1f else if (d > 0) me.x / w else 1f - me.x / w   // 0 = sát khung thành nhà, 1 = sát khung thành đối thủ
        val zone = if (me == null) "" else " | tiến ${(adv * 100).toInt()}% ngang ${(me.y / h * 100).toInt()}%"
        val info = "đỏ ${rd.reds.size} | kia ${rd.opps.size} | bóng $who$zone | AI $aiMsg"
        if (rd.reds.isEmpty()) { status("Không thấy áo đỏ trên minimap\n$info"); return }
        val carrier: Pair<Float, Float>? = if (me != null) Pair(me.x, me.y) else (rd.foreign ?: lastCarrier)
        if (carrier != null) lastCarrier = carrier

        // 1) MẤT BÓNG: đè B + kéo joystick (kèm bóng). Vừa mất bóng thì bấm C đổi sang cầu thủ gần bóng nhất;
        //    sát người giữ bóng thì bấm A xoạc để cướp.
        if (!hasBall || me == null) {
            if (carrier == null) { status("Chưa thấy bóng\n$info"); return }
            val chaser = rd.reds.minByOrNull { hypot(it.x - carrier.first, it.y - carrier.second) } ?: return
            val a = atan2((chaser.y - carrier.second).toDouble(), (carrier.first - chaser.x).toDouble())
            val dist = hypot(chaser.x - carrier.first, chaser.y - carrier.second) / w
            tac = null
            if (now <= noPressUntil && !rd.oppHas) {   // vừa chuyền/sút/tạt: bóng đang bay, chưa ép (trừ khi đối thủ đã cầm bóng)
                status("Theo bóng\n$info")
                emit(Tactic("Theo bóng", 800), a, 0)
                return
            }
            val taps = ArrayList<Triple<Int, Long, Long>>()
            if ((justLost || dist > .22f) && now > switchUntil) {
                taps.add(Triple(3, 30L, 60L)); switchUntil = now + 2500
            }
            justLost = false
            if (dist < .10f && now > slideUntil && Random.nextFloat() < .6f) {
                taps.add(Triple(1, 250L, 60L)); slideUntil = now + 1400
            }
            val extra = (if (taps.any { it.first == 3 }) " + đổi người (C)" else "") + (if (taps.any { it.first == 1 }) " + xoạc (A)" else "")
            status("Ép sát: đè B$extra\n$info")
            emit(Tactic("Ép sát", 1000, taps = taps, press = true), a, 0)
            return
        }

        val up = me.y < h / 2f
        val side = if (up) 1.0 else -1.0
        val central = abs(me.y - h / 2f) <= h * .28f
        val veryWide = abs(me.y - h / 2f) > h * .4f
        // hướng tới khung thành đối thủ (nhắm góc xa)
        val tx = if (d > 0) w else 0f
        val ty = if (up) h * .53f else h * .47f
        val aim = atan2((me.y - ty).toDouble(), (tx - me.x).toDouble())

        // 2) TRONG TẦM SÚT / VÒNG CẤM
        if (adv >= SHOOT_ADV) {
            if (now > shotUntil) {
                val t1: Tactic
                if (veryWide) {
                    t1 = Tactic("Tạt từ sát biên ngang", 900, taps = listOf(Triple(3, 200L, 200L)))
                } else {
                    val shotAt = if (central) 150L else 650L    // lệch cánh thì vào góc tốt hơn rồi mới sút
                    t1 = Tactic(if (central) "SÚT" else "Vào góc rồi sút", shotAt + 600, taps = listOf(Triple(1, shotAt, 350L)))
                }
                tac = t1; tacStart = now; tacBase = aim; shotUntil = now + 1800; noPressUntil = now + 1500
                status("${t1.name} $head\n$info")
                emit(t1, tacBase, 0)
                return
            }
            // đang chờ sau cú sút: cứ áp sát khung thành, không chuyền vòng vo
            val k0 = tac
            if (k0 != null && now - tacStart <= k0.dur) {
                status("${k0.name} $head\n$info")
                emit(k0, tacBase, now - tacStart)
                return
            }
            val t5 = Tactic("Áp sát khung thành", 1000, off = { t -> sin(t * 5.0) * 12 * RAD })
            tac = t5; tacStart = now; tacBase = aim
            status("${t5.name} $head\n$info")
            emit(t5, tacBase, 0)
            return
        }
        // 3) đang chạy dở một chiến thuật thì làm tiếp
        val k1 = tac
        if (k1 != null && now - tacStart <= k1.dur) {
            status("${k1.name} $head\n$info")
            emit(k1, tacBase, now - tacStart)
            return
        }
        // 4) DẠT CÁNH (sát biên minimap, chưa tới vòng cấm): chạy dọc biên rồi tạt (C)
        if ((me.y < h * .2f || me.y > h * .8f) && adv > .45f && now > crossUntil) {
            val inward = -side * d * 38 * RAD
            val t2 = Tactic("Tạt cánh", 1800, off = { t -> if (t < 0.9f) 0.0 else inward },
                taps = listOf(Triple(3, 1000L, 200L)))
            tac = t2; tacStart = now; tacBase = if (d > 0) 0.0 else Math.PI; crossUntil = now + 3000; noPressUntil = now + 2800
            status("${t2.name} $head\n$info")
            emit(t2, tacBase, 0)
            return
        }
        // 4b) gần vòng cấm: một nửa số lần đi thẳng vào khung thành
        if (adv >= BOX_ADV && Random.nextFloat() < .5f) {
            val t6 = Tactic("Áp sát vòng cấm", 1200, off = { t -> sin(t * 5.0) * 15 * RAD })
            tac = t6; tacStart = now; tacBase = aim
            status("${t6.name} $head\n$info")
            emit(t6, tacBase, 0)
            return
        }
        // 5) CHUYỀN BAN BẬT liên tục (B), lực theo khoảng cách
        val mate = pickMate(me, rd.reds, d, w, h)
        if (mate != null && Random.nextFloat() < .65f) {
            val a = atan2((me.y - mate.y).toDouble(), (mate.x - me.x).toDouble())
            val hold = passHold(hypot(mate.x - me.x, mate.y - me.y), w, h)
            val t3 = Tactic("Chuyền ${hold}ms", 900, taps = listOf(Triple(2, 220L, hold)), steady = true)
            tac = t3; tacStart = now; tacBase = a; noPressUntil = now + 1000
            status("${t3.name} $head\n$info")
            emit(t3, tacBase, 0)
            return
        }
        // 6) RÊ BÓNG
        val t4 = pick(library(d, side))
        tac = t4; tacStart = now; tacBase = if (d > 0) 0.0 else Math.PI
        status("${t4.name} $head\n$info")
        emit(t4, tacBase, 0)
    }

    // Dựng một cử chỉ: joystick kéo theo đường cong của chiến thuật + các nút bấm cùng lúc (đa điểm chạm)
    private fun emit(tc: Tactic, base: Double, rel: Long) {
        val (jx, jy) = pt(0); val jr = jrad()
        val path = Path()
        val jit = if (tc.steady) 2f else 8f
        path.moveTo(jx + rn(jit), jy + rn(jit))
        for (k in 1..5) {
            val t = (rel + k * SEG / 5) / 1000f
            val a = base + tc.off(t) + (if (tc.steady) 0.0 else Math.toRadians(rn(4f).toDouble()))
            val r = jr * tc.pw(t) * (if (tc.steady) 1f else .92f + Random.nextFloat() * .08f)
            path.lineTo(jx + (cos(a) * r).toFloat(), jy - (sin(a) * r).toFloat())
        }
        val g = GestureDescription.Builder()
        g.addStroke(GestureDescription.StrokeDescription(path, 0, SEG))
        fun btn(i: Int, start: Long, hold: Long) {
            val (bx, by) = pt(i)
            g.addStroke(GestureDescription.StrokeDescription(
                Path().apply { moveTo(bx + rn(6f), by + rn(6f)) }, start, hold.coerceAtLeast(40)))
        }
        for ((b, s, hd) in tc.taps) if (s >= rel && s < rel + SEG) btn(b, s - rel, if (tc.steady) hd else hd + Random.nextLong(-20, 40))
        if (tc.press) btn(2, Random.nextLong(40, 120), SEG - 160)
        send(g.build())
    }

    // Chỉ một cử chỉ chạy một lúc. Lệnh mới đến lúc đang bận thì xếp hàng (giữ lệnh mới nhất),
    // chờ cử chỉ trước kết thúc + nghỉ 40ms cho ngón nhả hẳn. Không bao giờ ngắt giữa chừng -> không kẹt nút.
    @Synchronized private fun send(g: GestureDescription) {
        val now = System.currentTimeMillis()
        if (busy && now - busySince > 3000) busy = false   // phòng khi hệ thống không báo kết thúc
        if (busy) { pendingG = g; return }
        busy = true; busySince = now
        val ok = dispatchGesture(g, object : GestureResultCallback() {
            override fun onCompleted(d: GestureDescription?) { release() }
            override fun onCancelled(d: GestureDescription?) { release() }
        }, null)
        if (!ok) { busy = false; status("Hệ thống từ chối cử chỉ") }
    }

    private fun release() {
        ui.postDelayed({
            var n: GestureDescription? = null
            synchronized(this) { busy = false; n = pendingG; pendingG = null }
            val next = n
            if (next != null && running) send(next)
        }, 40)
    }
}

object Ai {
    private val MODELS = arrayOf("gemini-2.5-flash-lite", "gemini-flash-lite-latest", "gemini-2.5-flash")
    @Volatile private var mi = 0
    private const val SYS = """You see a cropped image of the small radar/minimap of a Dream League Soccer match (a top-down view of the pitch). My team's players are RED icons; the other team's players have another color. A bright white or pink glow on an icon marks the player holding the ball. Goalkeepers stand near the two short ends of the pitch.
Answer one thing: attack = the side of the image ("left" or "right") toward which my red team attacks, i.e. the end of the pitch where the opponents' goalkeeper stands. Teams swap ends at half time. A recent estimate is given as a hint: keep it unless the image clearly shows otherwise; "unknown" if unsure.
Reply ONLY with JSON: {"attack":"left"|"right"|"unknown"}"""

    fun decide(key: String, b64: String, hint: String): Pair<JSONObject?, String> {
        if (key.isBlank()) return null to "Chưa nhập API key"
        return try {
            val img = JSONObject().put("inline_data", JSONObject().put("mime_type", "image/jpeg").put("data", b64))
            val txt = JSONObject().put("text", "Recent attack-side estimate: $hint. Answer now.")
            val body = JSONObject()
                .put("system_instruction", JSONObject().put("parts", JSONArray().put(JSONObject().put("text", SYS))))
                .put("contents", JSONArray().put(JSONObject().put("role", "user").put("parts", JSONArray().put(img).put(txt))))
                .put("generationConfig", JSONObject().put("maxOutputTokens", 60).put("temperature", 0.1).put("responseMimeType", "application/json"))
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
            val t = JSONObject(c.inputStream.bufferedReader().readText()).getJSONArray("candidates").getJSONObject(0)
                .getJSONObject("content").getJSONArray("parts").getJSONObject(0).getString("text")
            JSONObject(t.substring(t.indexOf('{'), t.lastIndexOf('}') + 1)) to "OK"
        } catch (e: Exception) { null to ("Lỗi: " + e.message).take(40) }
    }
}
