package com.dlsbot

import android.accessibilityservice.AccessibilityService
import android.accessibilityservice.GestureDescription
import android.content.ContentValues
import android.content.Context
import android.graphics.*
import android.os.Handler
import android.os.Looper
import android.provider.MediaStore
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
    val mine: Blob?,                   // áo đỏ có vầng sáng/bóng = đội mình đang cầm bóng
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
    private val SEG = 500L         // độ dài mỗi đoạn cử chỉ (joystick liền mạch nên ngắn cũng không khựng)
    private val RAD = Math.PI / 180
    // ---- lực chuyền / sút (chỉ dùng nút B để chuyền) ----
    private val SHORT_PASS_MS = 400L   // chuyền ngắn: nhấp B 0,4 giây
    private val LONG_PASS_MIN = 700L   // chuyền dài: đè B, từ ... (ms)
    private val LONG_PASS_MAX = 1200L  // ... đến ... (ms), xa hơn thì đè lâu hơn
    private val SHORT_MAX_M = 20f      // đồng đội cách <= 20m thì chuyền ngắn, xa hơn thì chuyền dài
    // ---- lực sút theo thanh lực (Calibrated Shot Power Curve): 0,4s ≈ 45% => thanh đầy ≈ 0,89s ----
    private val FULL_BAR_MS = 890L         // thời gian đè A để đầy thanh lực; nếu cú sút luôn yếu/mạnh quá thì chỉnh số này
    private fun pct(p: Int): Long = FULL_BAR_MS * p / 100
    private val SHOT_MS = pct(45)          // A1 sút căng/cứa lòng góc xa: 40-50% lực (= 0,4s)
    private val SHOT_LOW_MS = pct(20)      // A2 sút sệt chìm khi thủ môn lao ra: 15-25% lực
    private val SHOT_LONG_MS = pct(60)     // sút xa ngoài vòng cấm: 55-65% lực
    private val SHOT_MAX_BOX_MS = pct(65)  // trong vòng cấm 16m50 không bao giờ vượt 65% (quá tay dễ vọt xà)
    private val SHOT_MAX_MS = pct(75)      // nơi khác không vượt 75%
    // kích thước sân thật để tính góc joystick đúng (minimap kéo dãn không làm lệch hướng)
    private val PITCH_L = 105f
    private val PITCH_W = 68f
    private val VF = 1f                // hệ số hướng dọc; nếu chuyền/sút luôn lệch lên/xuống thì chỉnh số này
    // ---- theo tài liệu chiến thuật DLS Offline ----
    private val GK_RUSH = true          // đối thủ đối mặt trong vòng cấm nhà: giữ C gọi thủ môn lao ra
    // vùng vuốt màn hình cho kỹ thuật cá nhân (tỉ lệ màn hình), chỉ dùng khi bật nút ✨
    private val SW_X = 0.62f
    private val SW_Y = 0.42f
    private val SW_LEN = 0.10f
    private val SW_MS = 160L

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
    @Volatile private var hasBall = true
    private var lostTicks = 0
    private var gainTicks = 0
    private var justLost = false
    @Volatile private var swipesOn = false
    private var swipeUntil = 0L
    private var gkUntil = 0L
    private val recent = ArrayList<String>()        // các chiến thuật vừa dùng (để không lặp, AI máy hay bắt bài)
    private val crossSides = ArrayList<Int>()       // các lần tạt gần nhất từ cánh nào
    private var lastPassFrom: Pair<Float, Float>? = null
    private var lastPassAt = 0L
    private var lastCarrier: Pair<Float, Float>? = null
    // ---- cử chỉ liền mạch ----
    // Joystick là MỘT nét chạm duy nhất được nối dài qua nhiều cử chỉ (continueStroke): ngón không nhả, không về tâm,
    // đổi hướng theo cung cong nên không bị khựng. Chỉ một cử chỉ chạy một lúc và không bao giờ bị ngắt giữa chừng.
    private class Step(val tc: Tactic, val base: Double, val rel: Long, val hold: Boolean = false, val release: Boolean = false)
    @Volatile private var busy = false
    @Volatile private var busySince = 0L
    private val queue = ArrayList<Step>()
    private var lastStep: Step? = null
    private var lastEnd = 0L
    private var lastTotal = 0L
    private var buildCont = false
    private var replays = 0
    private var joyStroke: GestureDescription.StrokeDescription? = null
    private var btnStroke: GestureDescription.StrokeDescription? = null
    private var joyX = 0f
    private var joyY = 0f
    private var joyA = 0.0
    private var btnX = 0f
    private var btnY = 0f
    @Volatile private var cont = true      // false = chế độ cũ (nhả ngón mỗi đoạn); tự chuyển sang khi chế độ liền mạch bị lỗi 3 lần
    private var contFails = 0

    private class Tactic(
        val name: String,
        val dur: Long,
        val off: (Float) -> Double = { 0.0 },
        val pw: (Float) -> Float = { 1f },
        val taps: List<Triple<Int, Long, Long>> = emptyList(),  // (nút 1=A xoạc/sút, 2=B chuyền/kèm, 3=C tạt/đổi người; bắt đầu ms, giữ ms)
        val steady: Boolean = false,   // true = joystick giữ thẳng, không rung (để chuyền/sút chính xác)
        val seg: Long = 0L,            // độ dài cử chỉ (0 = mặc định)
        val swipe: Triple<Int, Int, Long>? = null,   // vuốt màn hình (dx, dy, bắt đầu ms): dx=±1 ngang, dy=+1 xuống, -1 lên
        val press: Boolean = false
    ) {
        fun withSwipe(sw: Triple<Int, Int, Long>) = Tactic(name + " + vuốt", dur, off, pw, taps, steady, seg, sw, press)
        fun noTaps() = Tactic(name, dur, off, pw, emptyList(), steady, seg, null, press)
    }

    private class PassPick(val m: Blob, val score: Float, val progress: Float, val dist: Float)

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
        // 📷: lưu ảnh minimap hiện tại vào Thư viện > DLSBot (để gửi cho mình chỉnh nhận diện)
        l.addView(mk("📷").apply { setOnClickListener { pool.execute { saveShot() } } })
        // ✨: bật/tắt kỹ thuật vuốt màn hình (đẩy bóng dài, giật gót, gắp bóng). Mặc định TẮT, bật khi đã chỉnh SW_X/SW_Y đúng vùng vuốt của game
        val swb = mk("✨")
        swb.alpha = 0.5f
        swb.setOnClickListener { swipesOn = !swipesOn; swb.alpha = if (swipesOn) 1f else 0.5f }
        l.addView(swb)
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
    override fun onDestroy() { running = false; releaseChain(); super.onDestroy() }

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

    private fun saveShot() {
        val bmp = grabMap()
        if (bmp == null) { status("Chưa chụp được minimap (đặt MAP1/MAP2 trước)"); return }
        try {
            val tag = if (hasBall) "mine" else "lost"
            val v = ContentValues()
            v.put(MediaStore.Images.Media.DISPLAY_NAME, "mm_" + tag + "_" + System.currentTimeMillis() + ".png")
            v.put(MediaStore.Images.Media.MIME_TYPE, "image/png")
            v.put(MediaStore.Images.Media.RELATIVE_PATH, "Pictures/DLSBot")
            val uri = contentResolver.insert(MediaStore.Images.Media.EXTERNAL_CONTENT_URI, v)
            if (uri != null) contentResolver.openOutputStream(uri)?.use { bmp.compress(Bitmap.CompressFormat.PNG, 100, it) }
            status(if (uri != null) "Đã lưu ảnh minimap: Thư viện > DLSBot" else "Không lưu được ảnh")
        } catch (e: Exception) {
            status(("Lỗi lưu ảnh: " + e.message).take(60))
        }
        bmp.recycle()
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
        hasBall = true; lostTicks = 0; gainTicks = 0; lastCarrier = null; justLost = false
        swipeUntil = 0; gkUntil = 0; recent.clear(); crossSides.clear(); lastPassFrom = null; lastPassAt = 0
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
                    // được bóng lại phải thấy 2 lần liên tiếp để khỏi chập chờn
                    gainTicks++; lostTicks = 0
                    if (hasBall || gainTicks >= 2) hasBall = true
                } else {
                    gainTicks = 0; lostTicks++
                    if (rd.oppHas || lostTicks >= 2) hasBall = false
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
        synchronized(this) { queue.clear(); replays = 99 }
        releaseChain()
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

    // ---- Đọc minimap: áo đỏ = đội mình, màu khác = đối thủ, vầng sáng sáng/trắng = bóng/người cầm bóng ----
    private fun scan(bmp: Bitmap): Radar {
        val w = bmp.width; val h = bmp.height
        val px = IntArray(w * h)
        bmp.getPixels(px, 0, w, 0, 0, w, h)
        val red = BooleanArray(w * h); val opp = BooleanArray(w * h); val glw = BooleanArray(w * h)
        for (i in px.indices) {
            val c = px[i]
            val cr = (c shr 16) and 255; val cg = (c shr 8) and 255; val cb = c and 255
            val top = max(cr, max(cg, cb)); val low = min(cr, min(cg, cb))
            if (top >= 215 && low >= 130) { glw[i] = true; continue }
            if (cr >= 140 && cg <= 110 && cb <= 110 && cr - cg >= 70) { red[i] = true; continue }
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

    // ---- Hình học theo mét thật của sân (minimap bị kéo dãn cũng không lệch) ----
    private fun dm(ax: Float, ay: Float, bx: Float, by: Float, w: Float, h: Float): Float =
        hypot((bx - ax) / w * PITCH_L, (by - ay) / h * PITCH_W)

    // góc joystick (0 = phải, 90 = lên) từ A tới B
    private fun pang(ax: Float, ay: Float, bx: Float, by: Float, w: Float, h: Float): Double =
        atan2(((ay - by) / h * PITCH_W * VF).toDouble(), ((bx - ax) / w * PITCH_L).toDouble())

    // (t, khoảng cách vuông góc tính bằng mét) của điểm P so với đoạn AB; t trong 0..1 nghĩa là P nằm giữa A và B
    private fun segInfo(ax: Float, ay: Float, bx: Float, by: Float, px: Float, py: Float, w: Float, h: Float): Pair<Float, Float> {
        val kx = PITCH_L / w; val ky = PITCH_W / h
        val abx = (bx - ax) * kx; val aby = (by - ay) * ky
        val apx = (px - ax) * kx; val apy = (py - ay) * ky
        val len2 = abx * abx + aby * aby
        if (len2 < 1e-6f) return Pair(0f, 99f)
        val t = (apx * abx + apy * aby) / len2
        val tc = t.coerceIn(0f, 1f)
        return Pair(t, hypot(apx - abx * tc, apy - aby * tc))
    }

    // Chọn đồng đội để chuyền (chỉ nút B): tiến về phía trước, đường chuyền không bị chặn, người nhận không bị kèm.
    // Thưởng thêm: ban bật trả ngược cho người vừa chuyền, chọc khe sau lưng hàng thủ, đổi cánh khi bị vây.
    // cutBack = chỉ xét đồng đội gần chấm phạt đền (chuyền ngược tuyến hai từ sát biên ngang).
    private fun choosePass(me: Blob, reds: List<Blob>, opps: List<Blob>, d: Int, w: Float, h: Float, cutBack: Boolean, tight: Boolean): PassPick? {
        var best: PassPick? = null
        val crowd = opps.count { dm(me.x, me.y, it.x, it.y, w, h) < 12f }
        // hàng thủ thứ hai từ cuối (bỏ thủ môn) = đường lưng hậu vệ
        val xs = opps.map { it.x }.sortedBy { if (d > 0) -it else it }
        val line = if (xs.size >= 2) xs[1] else (if (d > 0) w else 0f)
        val spx = (if (d > 0) w else 0f) - d * w * (14f / PITCH_L)
        val from = lastPassFrom
        for (m in reds) {
            if (m === me) continue
            val dist = dm(me.x, me.y, m.x, m.y, w, h)
            if (dist < 6f || dist > 45f) continue
            if (cutBack && dm(m.x, m.y, spx, h / 2f, w, h) > 14f) continue
            val progress = (m.x - me.x) / w * PITCH_L * d
            var pen = 0f
            for (o in opps) {
                val si = segInfo(me.x, me.y, m.x, m.y, o.x, o.y, w, h)
                if (si.first > 0.05f && si.first < 0.95f) {
                    if (si.second < 2.5f) pen += 1000f else if (si.second < 5f) pen += 25f * (5f - si.second)
                }
            }
            val near = opps.minOfOrNull { dm(m.x, m.y, it.x, it.y, w, h) } ?: 99f
            if (near < 4f) pen += 30f * (4f - near)
            var s = progress.coerceIn(-15f, 30f) * 0.8f - dist * 0.35f - pen + min(near, 10f) * 2f
            val behind = (m.x - line) * d / w * PITCH_L            // mét phía sau lưng hàng thủ
            if (behind >= 0f && behind <= 8f && near > 5f) s += 15f  // chọc khe
            if (from != null && System.currentTimeMillis() - lastPassAt < 2500 &&
                dm(m.x, m.y, from.first, from.second, w, h) < 15f) s += 18f   // ban bật trả ngược
            if (crowd >= 3 && abs(m.y - me.y) / h * PITCH_W > 25f && near > 8f) s += 25f   // bị vây: đổi cánh
            if (tight && dist < 18f) s += 12f                                              // bị ép sát: chuyền một chạm cho người gần
            if (s > (best?.score ?: -1e9f)) best = PassPick(m, s, progress, dist)
        }
        return best?.takeIf { it.score > -10f }
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

    private fun remember(n: String) { recent.add(n); while (recent.size > 6) recent.removeAt(0) }

    private fun pick(l: List<Pair<Int, Tactic>>): Tactic {
        // AI máy bắt bài khi mình lặp lại: giảm trọng số các kiểu vừa dùng trong 2 lần gần nhất
        val last2 = recent.takeLast(2)
        val ws = l.map { (wt, t) -> if (last2.contains(t.name)) max(1, wt / 3) else wt }
        var r = Random.nextInt(ws.sum())
        for (i in l.indices) {
            r -= ws[i]
            if (r < 0) { remember(l[i].second.name); return l[i].second }
        }
        return l[0].second
    }

    // ---- Quyết định: mất bóng -> ĐÈ B + joystick (+C đổi người/gọi thủ môn, +A xoạc ngoài vòng cấm);
    //      có bóng -> sút / cắt ngược / tạt / vào vị trí sút / chuyền thông minh / rê (+vuốt) ----
    private fun control(now: Long, rd: Radar) {
        val w = rd.w.toFloat(); val h = rd.h.toFloat()
        val d = if (attack != 0) attack else 1
        val head = if (d > 0) "→" else "←"
        val who = if (hasBall) "mình" else if (rd.oppHas) "kia" else if (rd.foreign != null) "lỏng" else "?"
        val me = rd.mine
        val adv = if (me == null) -1f else if (d > 0) me.x / w else 1f - me.x / w   // 0 = sát khung thành nhà, 1 = sát khung thành đối thủ
        val zone = if (me == null) "" else " | tiến ${(adv * 100).toInt()}% ngang ${(me.y / h * 100).toInt()}%"
        var info = "đỏ ${rd.reds.size} | kia ${rd.opps.size} | bóng $who$zone | AI $aiMsg" + (if (cont) "" else " | chế độ cũ")
        if (rd.reds.isEmpty()) { status("Không thấy áo đỏ trên minimap\n$info"); return }
        val carrier: Pair<Float, Float>? = if (me != null) Pair(me.x, me.y) else (rd.foreign ?: lastCarrier)
        if (carrier != null) lastCarrier = carrier

        // 1) MẤT BÓNG: đè B + kéo joystick (kèm bóng) về phía người giữ bóng.
        //    Vừa mất bóng: C đổi sang cầu thủ gần bóng nhất. Đối thủ đối mặt trong vòng cấm nhà: giữ C gọi thủ môn lao ra.
        //    Sát người giữ bóng: A xoạc, nhưng KHÔNG xoạc trong vòng cấm nhà (dễ bị phạt đền/thẻ).
        if (!hasBall || me == null) {
            if (carrier == null) { status("Chưa thấy bóng\n$info"); return }
            val chaser = rd.reds.minByOrNull { dm(it.x, it.y, carrier.first, carrier.second, w, h) } ?: return
            val a = pang(chaser.x, chaser.y, carrier.first, carrier.second, w, h)
            val dist = dm(chaser.x, chaser.y, carrier.first, carrier.second, w, h)   // mét
            val ownGx = if (d > 0) 0f else w
            val inMyBox = abs(carrier.first - ownGx) / w * PITCH_L <= 16.5f && abs(carrier.second - h / 2f) / h * PITCH_W <= 20.2f
            val centralMyBox = inMyBox && abs(carrier.second - h / 2f) / h * PITCH_W <= 12f
            tac = null
            if (now <= noPressUntil && !rd.oppHas) {   // vừa chuyền/sút/tạt: bóng đang bay, chưa ép (trừ khi đối thủ đã cầm bóng)
                status("Theo bóng\n$info")
                emit(Tactic("Theo bóng", 800), a, 0)
                return
            }
            val taps = ArrayList<Triple<Int, Long, Long>>()
            var rush = false
            if (GK_RUSH && centralMyBox && rd.oppHas && dist > 10f && now > gkUntil) {
                taps.add(Triple(3, 30L, 700L)); gkUntil = now + 3000; rush = true
            } else if ((justLost || dist > 22f) && now > switchUntil) {
                taps.add(Triple(3, 30L, 60L)); switchUntil = now + 2500
            }
            justLost = false
            if (!inMyBox && dist < 8f && now > slideUntil && Random.nextFloat() < .6f) {
                taps.add(Triple(1, 250L, 60L)); slideUntil = now + 1400
            }
            val extra = (if (rush) " + gọi thủ môn (giữ C)" else if (taps.any { it.first == 3 }) " + đổi người (C)" else "") +
                (if (taps.any { it.first == 1 }) " + xoạc (A)" else "")
            status("Ép sát: đè B$extra (${dist.toInt()}m)\n$info")
            emit(Tactic("Ép sát", 600, taps = taps, press = true, seg = 600L), a, 0)
            return
        }

        val up = me.y < h / 2f
        val side = if (up) 1.0 else -1.0
        val tx = if (d > 0) w else 0f
        val dGoal = dm(me.x, me.y, tx, h / 2f, w, h)
        val lateral = abs(me.y - h / 2f) / h * PITCH_W
        val nearOpp = rd.opps.minOfOrNull { dm(me.x, me.y, it.x, it.y, w, h) } ?: 99f
        val pressured = nearOpp < 6f
        // góc nhìn khung thành giữa hai cột dọc (độ): dưới 15 độ là góc hẹp -> không sút, mở góc hoặc chuyền
        val halfGoal = h * (3.66f / PITCH_W)
        val pa = pang(me.x, me.y, tx, h / 2f - halfGoal, w, h)
        val pb = pang(me.x, me.y, tx, h / 2f + halfGoal, w, h)
        var da = abs(pa - pb)
        if (da > Math.PI) da = 2 * Math.PI - da
        val narrow = Math.toDegrees(da) < 15.0
        if (narrow && dGoal <= 24f) info += " [GÓC HẸP]"
        val canShoot = dGoal <= 24f && lateral <= 20f && !narrow
        val goodShot = dGoal <= 20f && lateral <= 14f && !narrow
        // nhắm góc xa, tránh thủ môn: thủ môn lệch bên nào thì sút bên kia
        val gk = rd.opps.filter { dm(it.x, it.y, tx, h / 2f, w, h) < 14f }.minByOrNull { dm(it.x, it.y, tx, h / 2f, w, h) }
        val gkOut = gk != null && abs(gk.x - tx) / w * PITCH_L > 6f     // thủ môn đã lao ra khỏi vạch vôi
        val postOff = h * 0.03f
        val ty = if (gk != null) (if (gk.y >= h / 2f) h / 2f - postOff else h / 2f + postOff) else (if (up) h / 2f + postOff else h / 2f - postOff)
        val aim = pang(me.x, me.y, tx, ty, w, h)
        val spx = tx - d * w * (14f / PITCH_L)               // chấm phạt đền
        val toSpot = pang(me.x, me.y, spx, h / 2f, w, h)

        // chuyền bằng nút B: nhấp 0,4s = ngắn; đồng đội xa thì đè B lâu hơn = dài
        fun doPass(pk: PassPick, tag: String) {
            val short = pk.dist <= SHORT_MAX_M
            val hold = if (short) SHORT_PASS_MS else LONG_PASS_MIN + (((pk.dist - SHORT_MAX_M) / 25f).coerceIn(0f, 1f) * (LONG_PASS_MAX - LONG_PASS_MIN)).toLong()
            val a = pang(me.x, me.y, pk.m.x, pk.m.y, w, h)
            val t3 = Tactic(tag + (if (short) "ngắn " else "dài ") + hold + "ms", 200L + hold + 100L,
                taps = listOf(Triple(2, 200L, hold)), steady = true)
            tac = t3; tacStart = now; tacBase = a; noPressUntil = now + 600L + hold
            lastPassFrom = Pair(me.x, me.y); lastPassAt = now
            status("${t3.name} (${pk.dist.toInt()}m) $head\n$info")
            emit(t3, tacBase, 0)
        }

        // 2) SÚT (nút A). Pha 1 xoay joystick về góc khung thành, pha 2 giữ nguyên hướng rồi mới bấm A.
        //    Thủ môn lao ra: sút sệt A2 (20% lực). Sút xa: 60% lực. Còn lại A1: 45% lực (= 0,4s). Không bao giờ vượt ngưỡng quá lực.
        val inBox = dGoal <= 16.5f
        if (canShoot && now > shotUntil && (goodShot || pressured)) {
            var hold = if (gkOut) SHOT_LOW_MS else if (dGoal > 20f) SHOT_LONG_MS else SHOT_MS
            hold = min(hold, if (inBox) SHOT_MAX_BOX_MS else SHOT_MAX_MS)
            val nm = if (gkOut) "SÚT sệt A2" else if (dGoal > 20f) "SÚT xa" else "SÚT A1"
            val t1 = Tactic("$nm ${hold * 100 / FULL_BAR_MS}% (${hold}ms)", 200L + hold + 100L, taps = listOf(Triple(1, 200L, hold)), steady = true)
            tac = t1; tacStart = now; tacBase = aim; shotUntil = now + 1800; noPressUntil = now + 1200
            status("${t1.name} $head\n$info")
            emit(t1, tacBase, 0)
            return
        }
        // sút xa chính diện (20-30m, thoáng): đôi khi tung cú 60% lực
        if (dGoal > 20f && dGoal <= 30f && lateral <= 12f && !narrow && !pressured && now > shotUntil && Random.nextFloat() < .3f) {
            val hold = min(SHOT_LONG_MS, SHOT_MAX_MS)
            val t8 = Tactic("SÚT xa ${hold * 100 / FULL_BAR_MS}% (${hold}ms)", 200L + hold + 100L, taps = listOf(Triple(1, 200L, hold)), steady = true)
            tac = t8; tacStart = now; tacBase = aim; shotUntil = now + 1800; noPressUntil = now + 1200
            status("${t8.name} $head\n$info")
            emit(t8, tacBase, 0)
            return
        }
        // 3) đang chạy dở một chiến thuật thì làm tiếp
        val k1 = tac
        if (k1 != null && now - tacStart <= k1.dur) {
            status("${k1.name} $head\n$info")
            emit(k1, tacBase, now - tacStart)
            return
        }
        // 4) SÁT BIÊN NGANG / DẠT CÁNH: gần đáy biên thì cắt ngược về chấm phạt đền (nút B), không thì tạt (nút C).
        //    Không tạt mãi một cánh vì AI máy sẽ dồn người kèm cánh đó.
        val sInt = if (up) 1 else -1
        val repeatCross = crossSides.size >= 2 && crossSides.takeLast(2).all { it == sInt } && Random.nextFloat() < .6f
        if (lateral > 22f && dGoal <= 45f && now > crossUntil && !repeatCross) {
            val near = dGoal <= 32f
            if (near) {
                val cb = choosePass(me, rd.reds, rd.opps, d, w, h, true, false)
                if (cb != null && cb.score > 0f) {
                    crossUntil = now + 3000
                    doPass(cb, "Cắt ngược ")
                    return
                }
            }
            val inward = -side * d * 38 * RAD
            val t2 = if (near) {
                Tactic("Tạt từ biên", 800, taps = listOf(Triple(3, 200L, 200L)), steady = true)
            } else {
                Tactic("Tạt cánh", 1800, off = { t -> if (t < 0.9f) 0.0 else inward }, taps = listOf(Triple(3, 1000L, 200L)))
            }
            tac = t2; tacStart = now; tacBase = if (near) toSpot else (if (d > 0) 0.0 else Math.PI)
            crossUntil = now + 3000; noPressUntil = now + 2000
            crossSides.add(sInt); while (crossSides.size > 3) crossSides.removeAt(0)
            remember(t2.name)
            status("${t2.name} $head\n$info")
            emit(t2, tacBase, 0)
            return
        }
        // 5) trong tầm nhưng chưa phải góc đẹp: chạy vào vị trí sút (không bị kèm)
        if (dGoal <= 30f && !pressured) {
            val t5 = Tactic("Vào vị trí sút", 1000, steady = true)
            tac = t5; tacStart = now; tacBase = toSpot
            status("${t5.name} $head\n$info")
            emit(t5, tacBase, 0)
            return
        }
        // 6) CHUYỀN THÔNG MINH: chọc khe sau lưng hàng thủ, ban bật trả ngược, đổi cánh khi bị vây, tránh đường bị chặn
        val pk = choosePass(me, rd.reds, rd.opps, d, w, h, false, nearOpp < 4f)
        val oneTwo = System.currentTimeMillis() - lastPassAt < 2500 && Random.nextFloat() < .6f
        val wantPass = pk != null && ((pressured && Random.nextFloat() < .9f) || oneTwo || (pk.progress >= 8f && Random.nextFloat() < .5f) || Random.nextFloat() < .25f)
        if (pk != null && wantPass) {
            doPass(pk, "Chuyền ")
            return
        }
        // 7) RÊ BÓNG (+ vuốt màn hình nếu bật ✨): đẩy bóng dài khi thoáng, giật gót/gắp bóng khi bị ép sát
        var t4 = pick(library(d, side))
        if (swipesOn && now > swipeUntil && Random.nextFloat() < .35f) {
            val sw: Triple<Int, Int, Long>? =
                if (nearOpp < 3.5f) Triple(0, if (Random.nextBoolean()) 1 else -1, 300L)
                else if (dGoal > 30f && nearOpp > 10f) Triple(d, 0, 300L)
                else null
            if (sw != null) { t4 = t4.withSwipe(sw); swipeUntil = now + 4000 }
        }
        tac = t4; tacStart = now; tacBase = if (d > 0) 0.0 else Math.PI
        status("${t4.name} $head\n$info")
        emit(t4, tacBase, 0)
    }

    // ======================= CỬ CHỈ LIỀN MẠCH =======================
    // Control gọi emit() để đặt kế hoạch (thay thế hàng đợi); mỗi cử chỉ chỉ được dựng và gửi khi cử chỉ trước đã xong.
    private fun emit(tc: Tactic, base: Double, rel: Long) {
        val steps = ArrayList<Step>()
        if (cont && tc.steady && tc.taps.isNotEmpty()) {
            // chuyền/sút: pha 1 xoay joystick về đúng hướng (160ms), pha 2 giữ nguyên hướng rồi mới bấm nút
            if (rel == 0L) steps.add(Step(Tactic(tc.name, 160L, steady = true, seg = 160L), base, 0L))
            steps.add(Step(tc, base, rel, hold = true))
        } else {
            steps.add(Step(tc, base, rel))
        }
        synchronized(this) { queue.clear(); queue.addAll(steps); replays = 0 }
        dispatchNext(false)
    }

    // nhả hẳn ngón khi dừng bot
    private fun releaseChain() {
        synchronized(this) {
            if (joyStroke == null && btnStroke == null) return
            queue.clear(); queue.add(Step(Tactic("nhả", 0L), 0.0, 0L, release = true))
        }
        dispatchNext(false)
    }

    @Synchronized private fun dispatchNext(fromCallback: Boolean) {
        val now = System.currentTimeMillis()
        if (busy && now - busySince > 3000) { busy = false; joyStroke = null; btnStroke = null }   // phòng khi hệ thống không báo kết thúc
        if (busy) return
        var next: Step? = if (queue.isEmpty()) null else queue.removeAt(0)
        if (next == null) {
            if (!fromCallback) return
            if (joyStroke == null && btnStroke == null) return
            val lt = lastStep
            next = if (running && lt != null && replays < 2) {
                replays++
                Step(lt.tc.noTaps(), lt.base, lastEnd, hold = lt.hold)      // chưa có lệnh mới: giữ/kéo tiếp joystick, không bấm lại nút
            } else {
                Step(Tactic("nhả", 0L), 0.0, 0L, release = true)            // hết lệnh: nhả ngón
            }
        }
        val step = next!!
        val g = try { build(step) } catch (e: Exception) { null }
        if (g == null) {
            if (!step.release) { joyStroke = null; btnStroke = null; contFails++; if (contFails >= 3) cont = false }
            return
        }
        if (!step.release) { lastStep = step; lastEnd = step.rel + lastTotal }
        val isCont = buildCont
        busy = true; busySince = now
        val ok = dispatchGesture(g, object : GestureResultCallback() {
            override fun onCompleted(d: GestureDescription?) { finished(true, isCont) }
            override fun onCancelled(d: GestureDescription?) { finished(false, isCont) }
        }, null)
        if (!ok) {
            busy = false; joyStroke = null; btnStroke = null
            if (isCont) { contFails++; if (contFails >= 3) cont = false }
            status("Hệ thống từ chối cử chỉ")
        }
    }

    private fun finished(ok: Boolean, wasCont: Boolean) {
        synchronized(this) {
            busy = false
            if (ok) {
                if (wasCont) contFails = 0
            } else {
                joyStroke = null; btnStroke = null
                if (wasCont) {
                    contFails++
                    if (contFails >= 3) { cont = false; status("Chế độ liền mạch lỗi: chuyển sang chế độ cũ") }
                }
            }
        }
        dispatchNext(true)
    }

    // Dựng một cử chỉ. Joystick: nét nối dài từ điểm cuối của đoạn trước, đổi hướng theo cung (giới hạn tốc độ xoay);
    // nút bấm: các nét riêng trong cùng cử chỉ (đa điểm chạm); nút B khi ép sát cũng được nối dài để giữ liên tục.
    private fun build(st: Step): GestureDescription? {
        val tc = st.tc
        val (cx, cy) = pt(0); val jr = jrad()
        val g = GestureDescription.Builder()
        val prevJ = if (cont) joyStroke else null
        val prevB = if (cont) btnStroke else null
        buildCont = prevJ != null
        if (st.release) {
            if (prevJ == null && prevB == null) return null
            if (prevJ != null) { val p = Path(); p.moveTo(joyX, joyY); g.addStroke(prevJ.continueStroke(p, 0, 40, false)) }
            if (prevB != null) { val p = Path(); p.moveTo(btnX, btnY); g.addStroke(prevB.continueStroke(p, 0, 40, false)) }
            joyStroke = null; btnStroke = null
            lastTotal = 40L
            return g.build()
        }
        val rel = st.rel
        var total = if (tc.seg > 0) tc.seg else SEG
        for ((_, s, hd) in tc.taps) if (s >= rel && s < rel + total) total = max(total, (s - rel) + hd + 120)
        lastTotal = total
        val path = Path()
        var curX: Float
        var curY: Float
        var curA: Double
        if (prevJ != null) { curX = joyX; curY = joyY; curA = joyA } else { curX = cx + rn(3f); curY = cy + rn(3f); curA = st.base }
        path.moveTo(curX, curY)
        if (!(st.hold && prevJ != null)) {
            val n = if (tc.steady) 3 else 5
            val maxTurn = (if (tc.steady) 1080.0 else 540.0) * RAD * (total / 1000.0 / n)
            for (k in 1..n) {
                val t = (rel + k * total / n) / 1000f
                val tgt = st.base + tc.off(t) + (if (tc.steady) 0.0 else Math.toRadians(rn(4f).toDouble()))
                var diff = tgt - curA
                while (diff > Math.PI) diff -= 2 * Math.PI
                while (diff < -Math.PI) diff += 2 * Math.PI
                curA += diff.coerceIn(-maxTurn, maxTurn)
                val r = jr * tc.pw(t) * (if (tc.steady) 1f else .92f + Random.nextFloat() * .08f)
                curX = cx + (cos(curA) * r).toFloat(); curY = cy - (sin(curA) * r).toFloat()
                path.lineTo(curX, curY)
            }
        }
        val js = if (prevJ != null) prevJ.continueStroke(path, 0, total, cont) else GestureDescription.StrokeDescription(path, 0, total, cont)
        g.addStroke(js)
        if (cont) { joyStroke = js; joyX = curX; joyY = curY; joyA = curA } else { joyStroke = null }

        fun btn(i: Int, start: Long, hold: Long) {
            val (bx, by) = pt(i)
            g.addStroke(GestureDescription.StrokeDescription(
                Path().apply { moveTo(bx + rn(6f), by + rn(6f)) }, start, hold.coerceAtLeast(40)))
        }
        if (prevB != null && !tc.press) {
            // rời chế độ ép sát: nhả B
            val p = Path(); p.moveTo(btnX, btnY)
            g.addStroke(prevB.continueStroke(p, 0, 40, false)); btnStroke = null
        }
        for ((b, s, hd) in tc.taps) if (s >= rel && s < rel + total) btn(b, s - rel, if (tc.steady) hd else hd + Random.nextLong(-20, 40))
        if (tc.press) {
            if (cont) {
                val bs: GestureDescription.StrokeDescription
                if (prevB != null) {
                    val p = Path(); p.moveTo(btnX, btnY)
                    bs = prevB.continueStroke(p, 0, total, true)
                } else {
                    val (bx, by) = pt(2)
                    btnX = bx + rn(6f); btnY = by + rn(6f)
                    val p = Path(); p.moveTo(btnX, btnY)
                    val s0 = Random.nextLong(40, 120)
                    bs = GestureDescription.StrokeDescription(p, s0, total - s0, true)
                }
                g.addStroke(bs); btnStroke = bs
            } else {
                btn(2, Random.nextLong(40, 120), total - 200)
            }
        }
        val swp = tc.swipe
        if (swp != null && swp.third >= rel && swp.third < rel + total) {
            val bw = bounds().width().toFloat(); val bh = bounds().height().toFloat()
            val sx0 = bw * SW_X; val sy0 = bh * SW_Y
            val sp = Path()
            sp.moveTo(sx0, sy0)
            sp.lineTo(sx0 + swp.first * SW_LEN * bw, sy0 + swp.second * SW_LEN * bw)
            g.addStroke(GestureDescription.StrokeDescription(sp, swp.third - rel, SW_MS))
        }
        return g.build()
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
