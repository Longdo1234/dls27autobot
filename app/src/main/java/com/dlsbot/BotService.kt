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

// Một cụm điểm ảnh đỏ = một cầu thủ đội mình (toạ độ pixel màn hình)
class Blob(val x: Float, val y: Float, val n: Int)

// Lớp phủ trong suốt: vòng xanh lá = cầu thủ đang điều khiển, vòng vàng = đồng đội áo đỏ,
// chấm trắng = điểm bóng, dải xanh lơ = phía khung thành đối thủ. Nó cũng lọt vào ảnh gửi AI.
class Hud(ctx: Context) : View(ctx) {
    @Volatile var blobs: List<Blob> = emptyList()
    @Volatile var me: Blob? = null
    @Volatile var ref: Pair<Float, Float>? = null
    @Volatile var attack = 0
    private val p = Paint(Paint.ANTI_ALIAS_FLAG)
    override fun onDraw(c: Canvas) {
        p.style = Paint.Style.STROKE
        for (b in blobs) {
            val isMe = b === me
            p.strokeWidth = if (isMe) 10f else 6f
            p.color = if (isMe) 0xFF00FF00.toInt() else 0xFFFFEB3B.toInt()
            c.drawCircle(b.x, b.y, if (isMe) 75f else 55f, p)
        }
        ref?.let { p.strokeWidth = 5f; p.color = Color.WHITE; c.drawCircle(it.first, it.second, 16f, p) }
        if (attack != 0) {
            p.style = Paint.Style.FILL; p.color = 0x8800E5FF.toInt()
            val bw = width * 0.05f
            if (attack > 0) {
                c.drawRect(width - bw, height * 0.2f, width.toFloat(), height * 0.8f, p)
            } else {
                c.drawRect(0f, height * 0.2f, bw, height * 0.8f, p)
            }
        }
    }
}

class BotService : AccessibilityService() {
    private val TICK = 380L        // chu kỳ chụp + đọc màn hình
    private val SEG = 1000L        // độ dài mỗi đoạn kéo joystick
    private val RAD = Math.PI / 180
    private val HOLD_IN = 0.08f    // cầu thủ cách điểm bóng < 8% chiều cao màn hình -> coi là có bóng
    private val HOLD_OUT = 0.11f   // xa hơn 11% -> coi là mất bóng
    private val PASS_MIN = 70L     // chuyền gần: chạm nhẹ (ms giữ B). Chuyền yếu quá thì tăng
    private val PASS_MAX = 520L    // chuyền xa: giữ lâu nhất (ms). Chuyền mạnh quá thì giảm
    private val MIN_N = 20         // số điểm ảnh đỏ tối thiểu của một cầu thủ (ảnh đã thu nhỏ 1/2)

    private val io = Executors.newSingleThreadExecutor()
    private val pool = Executors.newFixedThreadPool(3)
    private val ui = Handler(Looper.getMainLooper())
    private var tv: TextView? = null
    private var panel: View? = null
    private var hud: Hud? = null
    private var spBtn: Button? = null
    private lateinit var wm: WindowManager
    private val prefs get() = getSharedPreferences("cfg", MODE_PRIVATE)
    // JOY, A, B, C, MAP1, MAP2 (tỉ lệ màn hình)
    private val D = arrayOf(.12f to .72f, .72f to .82f, .82f to .68f, .9f to .86f, .40f to .03f, .60f to .22f)

    @Volatile private var running = false
    @Volatile private var fast = false
    @Volatile private var pauseUntil = 0L
    // AI (chậm): chỉ báo vùng sân + hướng tấn công
    @Volatile private var aiStamp = 0L
    @Volatile private var aiZone = "mid"
    @Volatile private var aiMsg = "chờ AI"
    // minimap (nhanh)
    @Volatile private var attack = 0          // -1 tấn công trái, +1 tấn công phải, 0 chưa rõ
    @Volatile private var advance = 0.5f      // 0 = sát khung thành nhà, 1 = sát khung thành đối thủ
    @Volatile private var mapMsg = "chưa đặt"
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
    private var hasLocal = true

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
    private fun hide(h: Boolean) { ui.post { panel?.visibility = if (h) View.INVISIBLE else View.VISIBLE } }

    @Synchronized private fun addVote(v: Int, n: Int) {
        repeat(n) { votes.add(v) }
        while (votes.size > 12) votes.removeAt(0)
        val s = votes.sum()
        attack = if (s >= 3) 1 else if (s <= -3) -1 else 0
    }

    override fun onServiceConnected() {
        wm = getSystemService(WINDOW_SERVICE) as WindowManager
        // lớp phủ HUD (không nhận chạm)
        val h = Hud(this)
        hud = h
        wm.addView(h, WindowManager.LayoutParams(-1, -1, WindowManager.LayoutParams.TYPE_ACCESSIBILITY_OVERLAY,
            WindowManager.LayoutParams.FLAG_NOT_FOCUSABLE or WindowManager.LayoutParams.FLAG_NOT_TOUCHABLE or
                WindowManager.LayoutParams.FLAG_LAYOUT_IN_SCREEN or WindowManager.LayoutParams.FLAG_LAYOUT_NO_LIMITS,
            PixelFormat.TRANSLUCENT))
        // thanh điều khiển: nút to, không còn bị ẩn liên tục nên bấm dễ hơn
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
        // 🎯: bấm khi cầu thủ bạn đang cầm bóng để bot nhớ vị trí "cầm bóng" trên màn hình
        l.addView(mk("🎯").apply {
            setOnClickListener {
                pool.execute {
                    val b = shoot(true)
                    if (b == null) status("Chụp lỗi") else { saveRef(b); b.recycle() }
                }
            }
        })
        tv = TextView(this).apply { setTextColor(Color.WHITE); textSize = 10f; maxLines = 3; maxWidth = 600; text = "Sẵn sàng" }
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
    private fun refPoint(): Pair<Float, Float> =
        prefs.getFloat("rx", bounds().width() / 2f) to prefs.getFloat("ry", bounds().height() / 2f)

    private fun saveRef(bmp: Bitmap) {
        val cx = bounds().width() / 2f; val cy = bounds().height() / 2f
        val b = findRed(bmp).minByOrNull { hypot(it.x - cx, it.y - cy) }
        if (b == null) { status("Không thấy áo đỏ để lưu"); return }
        prefs.edit().putFloat("rx", b.x).putFloat("ry", b.y).apply()
        status("Đã lưu điểm cầm bóng")
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
                c.drawText("Kéo MAP1, MAP2 phủ khung minimap; B phải nằm đúng nút B trong game", width / 2f, height - 30f, p)
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

    // ---- Vòng lặp chính: chụp -> nhận diện (minimap + áo đỏ) -> (thỉnh thoảng) hỏi AI -> điều khiển ----
    private fun loop() {
        votes.clear(); attack = 0; aiStamp = 0; aiZone = "mid"; aiMsg = "chờ AI"
        tac = null; segEnd = 0; shotUntil = 0; crossUntil = 0; hasLocal = true; switchUntil = 0; slideUntil = 0; noPressUntil = 0
        var lastAi = 0L
        while (running) {
            val t0 = System.currentTimeMillis()
            val needAi = t0 >= pauseUntil && t0 - lastAi >= (if (fast) 800L else 4400L) && inflight.get() < 3
            val bmp = shoot(needAi)   // chỉ ẩn thanh điều khiển khi chụp ảnh gửi AI
            if (bmp == null) { status("Chụp màn hình lỗi"); Thread.sleep(400); continue }
            try {
                val now = System.currentTimeMillis()
                val H = bounds().height().toFloat()
                readMap(bmp)
                val blobs = findRed(bmp)
                val ref = refPoint()
                val me = blobs.minByOrNull { hypot(it.x - ref.first, it.y - ref.second) }
                val dist = if (me == null) 9999f else hypot(me.x - ref.first, me.y - ref.second)
                val prevHas = hasLocal
                if (me != null) hasLocal = if (prevHas) dist <= H * HOLD_OUT else dist <= H * HOLD_IN
                hud?.let { it.blobs = blobs; it.me = me; it.ref = ref; it.attack = attack; it.postInvalidate() }

                if (needAi) {
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
                            aiZone = d.optString("zone", "mid")
                            aiStamp = System.currentTimeMillis()
                            when (d.optString("attack")) { "right" -> addVote(1, 2); "left" -> addVote(-1, 2) }
                        } catch (e: Exception) {
                            aiMsg = ("Lỗi: " + e.message).take(40)
                        } finally {
                            inflight.decrementAndGet()
                        }
                    }
                }
                // mất/được bóng thì quyết định lại NGAY, còn lại đổi đoạn mỗi ~0,8 giây
                if (hasLocal != prevHas || now >= segEnd - TICK) {
                    control(now, me, blobs, ref, hasLocal, dist)
                    segEnd = now + SEG
                }
            } finally {
                bmp.recycle()
            }
            val el = System.currentTimeMillis() - t0
            if (el < TICK) Thread.sleep(TICK - el)
        }
        hud?.let { it.blobs = emptyList(); it.me = null; it.attack = 0; it.postInvalidate() }
        status("Đã dừng")
    }

    private fun shoot(hidePanel: Boolean): Bitmap? {
        var out: Bitmap? = null
        if (hidePanel) { hide(true); Thread.sleep(80) }
        try {
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
            if (hidePanel) hide(false)
        }
        return out
    }

    private fun jpeg(bmp: Bitmap): String {
        val sc = Bitmap.createScaledBitmap(bmp, 960, bmp.height * 960 / bmp.width, true)
        val bo = ByteArrayOutputStream(); sc.compress(Bitmap.CompressFormat.JPEG, 60, bo)
        return Base64.encodeToString(bo.toByteArray(), Base64.NO_WRAP)
    }

    // ---- Tìm cầu thủ áo đỏ trên màn hình (bỏ qua vùng HUD trên cùng, minimap và các nút điều khiển) ----
    private fun findRed(bmp: Bitmap): List<Blob> {
        val st = 2
        val sw = bmp.width / st; val sh = bmp.height / st
        val sm = Bitmap.createScaledBitmap(bmp, sw, sh, false)
        val px = IntArray(sw * sh)
        sm.getPixels(px, 0, sw, 0, 0, sw, sh)
        sm.recycle()
        val kx = bounds().width().toFloat() / bmp.width
        val top = bounds().height() * 0.12f
        val (m1x, m1y) = pt(4); val (m2x, m2y) = pt(5)
        val jr = jrad()
        val zones = (0..3).map { i ->
            val z = pt(i)
            Triple(z.first, z.second, if (i == 0) jr * 1.5f else jr * .9f)
        }
        fun excluded(x: Float, y: Float): Boolean {
            if (y < top) return true
            if (x >= min(m1x, m2x) - 10 && x <= max(m1x, m2x) + 10 && y >= min(m1y, m2y) - 10 && y <= max(m1y, m2y) + 10) return true
            for (z in zones) if (hypot(x - z.first, y - z.second) < z.third) return true
            return false
        }
        val cell = 8
        val gw = sw / cell + 1; val gh = sh / cell + 1
        val cnt = IntArray(gw * gh); val sxs = LongArray(gw * gh); val sys = LongArray(gw * gh)
        for (y in 0 until sh) for (x in 0 until sw) {
            val c = px[y * sw + x]
            val cr = (c shr 16) and 255; val cg = (c shr 8) and 255; val cb = c and 255
            if (cr < 140 || cg > 110 || cb > 110 || cr - cg < 70) continue
            if (excluded(x * st * kx, y * st * kx)) continue
            val i = (y / cell) * gw + (x / cell)
            cnt[i]++; sxs[i] += x.toLong(); sys[i] += y.toLong()
        }
        val seen = BooleanArray(gw * gh)
        val stack = IntArray(gw * gh)
        val out = ArrayList<Blob>()
        for (s in 0 until gw * gh) {
            if (cnt[s] < 3 || seen[s]) continue
            var sp = 0
            stack[sp++] = s; seen[s] = true
            var n = 0; var tx = 0L; var ty = 0L
            while (sp > 0) {
                val i = stack[--sp]
                n += cnt[i]; tx += sxs[i]; ty += sys[i]
                val cx = i % gw; val cy = i / gw
                for (dy in -1..1) for (dx in -1..1) {
                    val nx = cx + dx; val ny = cy + dy
                    if (nx < 0 || ny < 0 || nx >= gw || ny >= gh) continue
                    val j = ny * gw + nx
                    if (!seen[j] && cnt[j] >= 3) { seen[j] = true; stack[sp++] = j }
                }
            }
            if (n >= MIN_N) out.add(Blob(tx.toFloat() / n * st * kx, ty.toFloat() / n * st * kx, n))
        }
        return out
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
        if (left == 1 && right == -1) {
            addVote(1, 2)         // thủ môn nhà bên trái -> tấn công phải
        } else if (left == -1 && right == 1) {
            addVote(-1, 2)        // thủ môn nhà bên phải -> tấn công trái
        } else if (abs(mr - mo) > w * 0.08) {
            addVote(if (mr < mo) 1 else -1, 1)
        }
        val cx = (mr / w).toFloat()
        advance = if (attack >= 0) cx else 1f - cx
        mapMsg = "đỏ $rN / đối thủ $oN"
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

    // ---- Quyết định: mất bóng -> ĐÈ B + kéo joystick; gần khung thành -> sút; dạt cánh -> tạt; còn lại chuyền ban bật / rê ----
    private fun control(now: Long, me: Blob?, blobs: List<Blob>, ref: Pair<Float, Float>, has: Boolean, dist: Float) {
        val W = bounds().width().toFloat(); val H = bounds().height().toFloat()
        val d = if (attack != 0) attack else 1
        val head = if (d > 0) "→" else "←"
        val info = "MAP $mapMsg | AI $aiMsg | d=${(dist / H * 100).toInt()}%"
        if (me == null) {
            status("Không thấy áo đỏ\n$info")
            val k0 = tac
            if (k0 != null && now - tacStart <= k0.dur) emit(k0, tacBase, now - tacStart)
            return
        }
        // 1) MẤT BÓNG: đè B + kéo joystick (kèm bóng); xa bóng thì bấm C đổi cầu thủ, sát người giữ bóng thì A xoạc
        if (!has) {
            val a = atan2((me.y - ref.second).toDouble(), (ref.first - me.x).toDouble())
            tac = null
            if (now <= noPressUntil) {          // vừa chuyền/sút/tạt: bóng rời chân là bình thường, chưa ép
                status("Theo bóng\n$info")
                emit(Tactic("Theo bóng", 800), a, 0)
                return
            }
            val taps = ArrayList<Triple<Int, Long, Long>>()
            if (dist > H * .2f && now > switchUntil) {
                taps.add(Triple(3, 30L, 60L)); switchUntil = now + 2500
            } else if (dist < H * .16f && now > slideUntil && Random.nextFloat() < .3f) {
                taps.add(Triple(1, 250L, 60L)); slideUntil = now + 2500
            }
            val extra = if (taps.isEmpty()) "" else if (taps[0].first == 3) " + đổi người (C)" else " + xoạc (A)"
            status("Ép sát: đè B$extra\n$info")
            emit(Tactic("Ép sát", 1000, taps = taps, press = true), a, 0)
            return
        }
        val fresh = now - aiStamp < (if (fast) 3000L else 6500L)
        val zone = if (fresh) aiZone else "mid"
        val up = me.y < H / 2f
        val side = if (up) 1.0 else -1.0
        // 2) GẦN KHUNG THÀNH: sút
        if ((zone == "goal" || advance >= .8f) && now > shotUntil) {
            val tilt = (if (up) -d else d) * 12 * RAD
            val t1 = Tactic("SÚT gần khung thành", 900, taps = listOf(Triple(1, 150L, 350L)))
            tac = t1; tacStart = now; tacBase = (if (d > 0) 0.0 else Math.PI) + tilt; shotUntil = now + 1800; noPressUntil = now + 2000
            status("${t1.name} $head\n$info")
            emit(t1, tacBase, 0)
            return
        }
        // 3) đang chạy dở một chiến thuật thì làm tiếp
        val k1 = tac
        if (k1 != null && now - tacStart <= k1.dur) {
            status("${k1.name} $head\n$info")
            emit(k1, tacBase, now - tacStart)
            return
        }
        // 4) DẠT CÁNH: chạy dọc biên rồi tạt vào
        if (zone == "wing" && now > crossUntil) {
            val inward = -side * d * 38 * RAD
            val t2 = Tactic("Tạt cánh", 1800, off = { t -> if (t < 0.9f) 0.0 else inward },
                taps = listOf(Triple(3, 1000L, 200L)))
            tac = t2; tacStart = now; tacBase = if (d > 0) 0.0 else Math.PI; crossUntil = now + 3000; noPressUntil = now + 2800
            status("${t2.name} $head\n$info")
            emit(t2, tacBase, 0)
            return
        }
        // 5) CHUYỀN BAN BẬT liên tục
        val mate = pickMate(me, blobs, d, W, H)
        if (mate != null && Random.nextFloat() < .65f) {
            val a = atan2((me.y - mate.y).toDouble(), (mate.x - me.x).toDouble())
            val hold = passHold(hypot(mate.x - me.x, mate.y - me.y), W, H)
            val t3 = Tactic("Chuyền ${hold}ms", 900, taps = listOf(Triple(2, 220L, hold)), steady = true)
            tac = t3; tacStart = now; tacBase = a; noPressUntil = now + 1500
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

    // Một đoạn cử chỉ: joystick kéo theo đường cong của chiến thuật + các nút bấm cùng lúc (đa điểm chạm)
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
        for ((b, s, h) in tc.taps) if (s >= rel && s < rel + SEG) btn(b, s - rel, if (tc.steady) h else h + Random.nextLong(-20, 40))
        if (tc.press) btn(2, Random.nextLong(40, 120), SEG - 160)
        if (!dispatchGesture(g.build(), null, null)) status("Hệ thống từ chối cử chỉ")
    }
}

object Ai {
    private val MODELS = arrayOf("gemini-2.5-flash-lite", "gemini-flash-lite-latest", "gemini-2.5-flash")
    @Volatile private var mi = 0
    private const val SYS = """You watch one landscape screenshot of Dream League Soccer. Ignore the small overlay buttons at the top-left corner and the on-screen touch controls.
My team wears RED shirts; the other color is the opponent. I added markings: a GREEN ring = the red player I control (he holds or chases the ball), YELLOW rings = my other red players, a small white circle = where the ball usually is, a CYAN bar on the left or right screen edge = the side of the opponents' goal that my team attacks (it may be missing).
Answer two things:
- attack: the side of the screen ("left" or "right") of the goal my red team attacks, i.e. the goal defended by the opponents' goalkeeper. Teams swap sides at half time, so decide from THIS screenshot; a recent estimate is given as a hint, keep it unless the screenshot clearly shows otherwise; "unknown" if unsure.
- zone: where the green-ring player is: "goal" = inside or right at the edge of the opponent penalty area (shooting range); "wing" = close to the touchline in the attacking half (a cross is possible); "mid" = anywhere else in the attacking half or midfield; "own" = in my own half.
Reply ONLY with JSON: {"attack":"left"|"right"|"unknown","zone":"own"|"mid"|"wing"|"goal"}"""

    fun decide(key: String, b64: String, hint: String): Pair<JSONObject?, String> {
        if (key.isBlank()) return null to "Chưa nhập API key"
        return try {
            val img = JSONObject().put("inline_data", JSONObject().put("mime_type", "image/jpeg").put("data", b64))
            val txt = JSONObject().put("text", "Recent attack-side estimate: $hint. Answer now.")
            val body = JSONObject()
                .put("system_instruction", JSONObject().put("parts", JSONArray().put(JSONObject().put("text", SYS))))
                .put("contents", JSONArray().put(JSONObject().put("role", "user").put("parts", JSONArray().put(img).put(txt))))
                .put("generationConfig", JSONObject().put("maxOutputTokens", 100).put("temperature", 0.2).put("responseMimeType", "application/json"))
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
