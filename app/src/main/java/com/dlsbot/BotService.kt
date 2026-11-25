package com.dlsbot

import android.accessibilityservice.AccessibilityService
import android.accessibilityservice.GestureDescription
import android.content.ContentValues
import android.content.Context
import android.content.Intent
import android.graphics.*
import android.graphics.drawable.GradientDrawable
import android.os.Handler
import android.os.Looper
import android.provider.MediaStore
import android.util.Base64
import android.view.*
import android.view.accessibility.AccessibilityEvent
import android.widget.Button
import android.widget.ImageView
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
class Blob(val x: Float, val y: Float, val n: Int, val x0: Int, val x1: Int, val y0: Int, val y1: Int) {
    var vx = 0f   // vận tốc (m/s theo mét sân) để chuyền đón đầu chỗ đồng đội sẽ chạy tới
    var vy = 0f
}

// Kết quả đọc minimap
class Radar(
    val w: Int, val h: Int,
    val reds: List<Blob>,              // cầu thủ áo đỏ (đội mình)
    val opps: List<Blob>,              // cầu thủ đội kia
    val mine: Blob?,                   // áo đỏ có vầng sáng/bóng = đội mình đang cầm bóng
    val foreign: Pair<Float, Float>?,  // vầng sáng không dính áo đỏ = đối phương cầm bóng hoặc bóng lỏng
    val oppHas: Boolean,               // vầng sáng đó dính vào cầu thủ đội kia = đối phương đang cầm bóng
    val myRed: Boolean                 // true = đội mình mặc đỏ/cam (mặc định), false = đội mình xanh dương/cyan
)

// Cửa trao đổi khung hình minimap giữa CaptureService (15-20 FPS, tùy chọn) và BotService.
// Không có CaptureService thì BotService tự chụp bằng takeScreenshot (~3 ảnh/giây).
object CaptureHub {
    @Volatile var frame: Bitmap? = null
    @Volatile var stamp = 0L
    @Volatile var rect = floatArrayOf(0f, 0f, 0f, 0f)   // trái, trên, phải, dưới (pixel màn hình) của vùng minimap
    fun active(): Boolean = android.os.SystemClock.uptimeMillis() - stamp < 700L
    fun take(): Bitmap? { val f = frame; frame = null; return f }
}

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
    // ---- lực chuyền / sút: chỉnh trực tiếp bằng nút − / + trên bảng điều khiển (được lưu lại, áp dụng ngay) ----
    private val PASS_LO_MS = 300L       // chuyền ngắn, đồng đội sát (nhân với hệ số "Chuyền")
    private val PASS_HI_MS = 480L       // chuyền ngắn, đồng đội cách ~20m
    private val SLIDE_ENABLED = false   // false = KHÔNG xoạc bằng A khi mất bóng (dễ hở sườn/phạt đền), chỉ đè B ép sát + C đổi người
    private val LONG_PASS_MIN = 700L    // chuyền dài: đè B từ ... (ms)
    private val LONG_PASS_MAX = 1200L   // ... đến ... (ms), đồng đội càng xa càng đè lâu
    private val SHORT_MAX_M = 20f       // đồng đội cách <= 20m thì chuyền ngắn, xa hơn thì chuyền dài
    private fun shotBase() = prefs.getInt("shotMs", 120)          // giữ A khi sút trong vòng cấm (ms): 120ms ~ 20% thanh lực
    private fun passScale() = prefs.getFloat("passScale", 1f)     // hệ số lực chuyền (1.0 = 100%)
    // sút ngoài vòng cấm (> 16m50) cần lực gấp 2,5 lần: 300ms ~ 50% thanh lực
    private fun shotHold(long: Boolean): Long = (shotBase() * (if (long) 2.5f else 1f) * (0.95f + Random.nextFloat() * 0.1f)).toLong()
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
    private var miniBtn: TextView? = null
    private var fullView: LinearLayout? = null
    private var previewIv: ImageView? = null
    @Volatile private var previewOn = false
    @Volatile private var gkNote = ""
    @Volatile private var gkMark: Blob? = null
    private var lastVoteT = 0L
    private var goBtn: Button? = null
    private var body: LinearLayout? = null
    private var shotTv: TextView? = null
    private var passTv: TextView? = null
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
    private var sideStreak = 0                       // số lần chuyền ngang/lùi liên tiếp (tối đa 2)
    private var snapMine: List<Blob> = emptyList()
    private var snapOpp: List<Blob> = emptyList()
    private var snapMineT = 0L
    private var snapOppT = 0L
    private var gainSince = 0L                       // thời điểm bắt đầu thấy lại bóng (để chống chập chờn)
    private var lostSince = 0L                       // thời điểm bắt đầu mất vầng sáng
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
        val taps: List<Triple<Int, Long, Long>> = emptyList(),  // (nút 1=A sút, 2=B chuyền/kèm, 3=C tạt/đổi người; bắt đầu ms, giữ ms)
        val steady: Boolean = false,   // true = joystick giữ thẳng, không rung (để chuyền/sút chính xác)
        val seg: Long = 0L,            // độ dài cử chỉ (0 = mặc định)
        val swipe: Triple<Int, Int, Long>? = null,   // vuốt màn hình (dx, dy, bắt đầu ms): dx=±1 ngang, dy=+1 xuống, -1 lên
        val press: Boolean = false
    ) {
        val fired = BooleanArray(taps.size)   // mỗi cú bấm chỉ bắn ĐÚNG MỘT LẦN (tránh bấm đúp/hụt khi kế hoạch được gửi lại)
        fun withSwipe(sw: Triple<Int, Int, Long>) = Tactic(name + " + vuốt", dur, off, pw, taps, steady, seg, sw, press)
        fun noTaps() = Tactic(name, dur, off, pw, emptyList(), steady, seg, null, press)
    }

    private class PassPick(val m: Blob, val score: Float, val progress: Float, val dist: Float, val tx: Float, val ty: Float)

    private fun status(s: String) { ui.post { tv?.text = s } }

    @Synchronized private fun addVote(v: Int, n: Int) {
        val now = System.currentTimeMillis()
        if (now - lastVoteT < 200) return            // tối đa ~5 lượt phiếu/giây dù quét nhanh
        lastVoteT = now
        repeat(n) { votes.add(v) }
        while (votes.size > 15) votes.removeAt(0)
        val s = votes.sum()
        if (s >= 6) attack = 1 else if (s <= -6) attack = -1   // chưa đủ bằng chứng ngược lại thì GIỮ hướng cũ
    }

    override fun onServiceConnected() {
        wm = getSystemService(WINDOW_SERVICE) as WindowManager
        val h = Hud(this)
        hud = h
        wm.addView(h, WindowManager.LayoutParams(-1, -1, WindowManager.LayoutParams.TYPE_ACCESSIBILITY_OVERLAY,
            WindowManager.LayoutParams.FLAG_NOT_FOCUSABLE or WindowManager.LayoutParams.FLAG_NOT_TOUCHABLE or
                WindowManager.LayoutParams.FLAG_LAYOUT_IN_SCREEN or WindowManager.LayoutParams.FLAG_LAYOUT_NO_LIMITS,
            PixelFormat.TRANSLUCENT))
        // ===== Bảng điều khiển nổi: thu nhỏ = CHỈ 1 nút bật/tắt (kéo để dời, giữ lâu rồi thả để mở menu) =====
        val root = LinearLayout(this).apply { orientation = LinearLayout.VERTICAL }
        val mini = TextView(this).apply {
            text = "▶"; textSize = 20f; gravity = Gravity.CENTER; setTextColor(Color.WHITE)
            background = bg(0xCC2E7D32.toInt(), 24)
            layoutParams = LinearLayout.LayoutParams(dp(48), dp(48))
        }
        miniBtn = mini
        attachDrag(mini, { toggle() }, { setExpanded(true) })
        root.addView(mini)

        val full = LinearLayout(this).apply {
            orientation = LinearLayout.VERTICAL
            background = bg(0xE60F1720.toInt(), 14)
            setPadding(dp(4), dp(4), dp(4), dp(4))
            visibility = View.GONE
        }
        fullView = full
        val head = LinearLayout(this).apply { orientation = LinearLayout.HORIZONTAL; gravity = Gravity.CENTER_VERTICAL }
        val grip = TextView(this).apply { text = "✥"; textSize = 20f; setTextColor(0xFF9FB3C8.toInt()); setPadding(dp(6), 0, dp(8), 0) }
        attachDrag(grip, {}, null)
        head.addView(grip)
        val go = mkBtn("▶", 0xFF2E7D32.toInt(), 44, 40, 18f) { toggle() }
        goBtn = go
        head.addView(go)
        head.addView(mkBtn("⚙", 0xFF37474F.toInt(), 40, 40, 16f) { showSetup() })
        // 👁: xem trực tiếp bot đang "nhìn" gì trên toàn bộ minimap (vòng xanh = đội mình, ô cyan = đội kia, vòng vàng = người cầm bóng)
        val eye = mkBtn("👁", 0xFF37474F.toInt(), 40, 40, 16f) {}
        eye.alpha = 0.5f
        eye.setOnClickListener {
            previewOn = !previewOn
            eye.alpha = if (previewOn) 1f else 0.5f
            previewIv?.visibility = if (previewOn) View.VISIBLE else View.GONE
        }
        head.addView(eye)
        head.addView(mkBtn("▾", 0xFF37474F.toInt(), 40, 40, 16f) { setExpanded(false) })
        full.addView(head)

        val modes = LinearLayout(this).apply { orientation = LinearLayout.HORIZONTAL }
        val sp = mkBtn("🐢", 0xFF455A64.toInt(), 38, 34, 14f) {}
        sp.setOnClickListener { fast = !fast; sp.text = if (fast) "⚡" else "🐢" }
        spBtn = sp
        modes.addView(sp)
        // ✨: kỹ thuật vuốt màn hình (đẩy bóng dài, giật gót, gắp bóng). Mặc định TẮT
        val swb = mkBtn("✨", 0xFF455A64.toInt(), 38, 34, 14f) {}
        swb.alpha = 0.5f
        swb.setOnClickListener { swipesOn = !swipesOn; swb.alpha = if (swipesOn) 1f else 0.5f }
        modes.addView(swb)
        modes.addView(mkBtn("📷", 0xFF455A64.toInt(), 38, 34, 14f) { pool.execute { saveShot() } })
        modes.addView(mkBtn("🎥", 0xFF455A64.toInt(), 38, 34, 14f) { startFastCapture() })
        val aib = mkBtn("🌐", 0xFF455A64.toInt(), 38, 34, 14f) {}
        aib.alpha = if (aiOn()) 1f else 0.5f
        aib.setOnClickListener {
            val v = !aiOn()
            prefs.edit().putBoolean("aiOn", v).apply()
            aib.alpha = if (v) 1f else 0.5f
            status(if (v) "AI trực tuyến BẬT (cần API key)" else "Chế độ offline hoàn toàn")
        }
        modes.addView(aib)
        full.addView(modes)
        full.addView(powerRow({ shotTv = it }, { adjustShot(-10) }, { adjustShot(10) }))
        full.addView(powerRow({ passTv = it }, { adjustPass(-0.1f) }, { adjustPass(0.1f) }))
        val iv = ImageView(this)
        iv.visibility = View.GONE
        iv.adjustViewBounds = true
        iv.layoutParams = LinearLayout.LayoutParams(dp(236), -2)
        previewIv = iv
        full.addView(iv)
        tv = TextView(this).apply {
            setTextColor(0xFFE0E6EC.toInt()); textSize = 10f; minLines = 2; maxLines = 4
            setPadding(dp(6), dp(3), dp(6), dp(2)); text = "Sẵn sàng"
            layoutParams = LinearLayout.LayoutParams(dp(236), -2)
        }
        full.addView(tv)
        root.addView(full)
        panel = root
        val lp = WindowManager.LayoutParams(-2, -2, WindowManager.LayoutParams.TYPE_ACCESSIBILITY_OVERLAY,
            WindowManager.LayoutParams.FLAG_NOT_FOCUSABLE, PixelFormat.TRANSLUCENT)
        lp.gravity = Gravity.TOP or Gravity.START
        panelLp = lp
        wm.addView(root, lp)
        refreshPower()
        syncGo()
        placePanel()
    }

    // kéo để dời; chạm nhẹ = onTap; giữ > 0,55s rồi thả (không kéo) = onLong
    private fun attachDrag(v: View, onTap: () -> Unit, onLong: (() -> Unit)?) {
        var gx = 0f; var gy = 0f; var sx = 0; var sy = 0; var moved = false; var t0 = 0L
        v.setOnTouchListener { _, e ->
            val lp = panelLp
            if (lp != null) {
                when (e.action) {
                    MotionEvent.ACTION_DOWN -> { gx = e.rawX; gy = e.rawY; sx = lp.x; sy = lp.y; moved = false; t0 = System.currentTimeMillis() }
                    MotionEvent.ACTION_MOVE -> {
                        if (abs(e.rawX - gx) > 12f || abs(e.rawY - gy) > 12f) moved = true
                        if (moved) {
                            lp.x = sx + (e.rawX - gx).toInt(); lp.y = sy + (e.rawY - gy).toInt()
                            panel?.let { wm.updateViewLayout(it, lp) }
                        }
                    }
                    MotionEvent.ACTION_UP -> {
                        if (moved) {
                            prefs.edit().putInt("px", lp.x).putInt("py", lp.y).apply()
                        } else if (onLong != null && System.currentTimeMillis() - t0 > 550) {
                            onLong()
                        } else {
                            onTap()
                        }
                    }
                }
            }
            true
        }
    }

    private fun setExpanded(b: Boolean) {
        fullView?.visibility = if (b) View.VISIBLE else View.GONE
        miniBtn?.visibility = if (b) View.GONE else View.VISIBLE
        val lp = panelLp
        if (b && lp != null) {
            lp.x = lp.x.coerceIn(0, max(0, bounds().width() - dp(244)))
            panel?.let { wm.updateViewLayout(it, lp) }
        }
    }

    // xem trước toàn bộ minimap bot đang quét, kèm kết quả nhận diện
    private fun makePreview(map: Bitmap, rd: Radar): Bitmap {
        val pw = dp(236)
        val ph = max(1, map.height * pw / map.width)
        val out = Bitmap.createScaledBitmap(map, pw, ph, false).copy(Bitmap.Config.ARGB_8888, true)
        val f = pw / map.width.toFloat()
        val c = Canvas(out)
        val p = Paint(Paint.ANTI_ALIAS_FLAG)
        p.style = Paint.Style.STROKE
        p.strokeWidth = 3f
        p.color = 0xFF00FF00.toInt()
        for (b in rd.reds) c.drawCircle(b.x * f, b.y * f, 9f, p)
        p.color = 0xFF00E5FF.toInt()
        for (b in rd.opps) c.drawRect(b.x * f - 8f, b.y * f - 8f, b.x * f + 8f, b.y * f + 8f, p)
        val m = rd.mine
        if (m != null) { p.color = 0xFFFFEB3B.toInt(); p.strokeWidth = 5f; c.drawCircle(m.x * f, m.y * f, 13f, p) }
        val fo = rd.foreign
        if (fo != null) { p.style = Paint.Style.FILL; p.color = Color.WHITE; c.drawCircle(fo.first * f, fo.second * f, 5f, p) }
        p.style = Paint.Style.FILL
        p.color = Color.WHITE
        p.textSize = 22f
        c.drawText(if (attack > 0) "tấn công →" else if (attack < 0) "← tấn công" else "hướng ?", 6f, 24f, p)
        val gm = gkMark
        if (gm != null) { p.color = 0xFFFF5252.toInt(); c.drawText("GK", gm.x * f - 10f, gm.y * f - 12f, p) }
        return out
    }

    // ---- hàm phụ cho giao diện ----
    private fun dp(v: Int) = (v * resources.displayMetrics.density).toInt()

    private fun bg(color: Int, r: Int): GradientDrawable {
        val g = GradientDrawable()
        g.setColor(color)
        g.cornerRadius = dp(r).toFloat()
        return g
    }

    private fun mkBtn(t: String, color: Int, w: Int, h: Int, size: Float, click: () -> Unit): Button {
        val b = Button(this)
        b.text = t; b.textSize = size; b.setTextColor(Color.WHITE); b.background = bg(color, 12)
        b.minWidth = 0; b.minHeight = 0; b.minimumWidth = 0; b.minimumHeight = 0
        b.isAllCaps = false
        b.setPadding(dp(4), 0, dp(4), 0)
        val p = LinearLayout.LayoutParams(dp(w), dp(h))
        p.setMargins(dp(3), dp(3), dp(3), dp(3))
        b.layoutParams = p
        b.setOnClickListener { click() }
        return b
    }

    // một hàng: nhãn giá trị + nút − / +
    private fun powerRow(setLabel: (TextView) -> Unit, minus: () -> Unit, plus: () -> Unit): LinearLayout {
        val row = LinearLayout(this)
        row.orientation = LinearLayout.HORIZONTAL
        row.gravity = Gravity.CENTER_VERTICAL
        val lab = TextView(this)
        lab.textSize = 12f; lab.setTextColor(Color.WHITE); lab.setPadding(dp(8), 0, 0, 0)
        lab.layoutParams = LinearLayout.LayoutParams(0, -2, 1f)
        setLabel(lab)
        row.addView(lab)
        row.addView(mkBtn("−", 0xFF5D4037.toInt(), 40, 34, 18f) { minus() })
        row.addView(mkBtn("+", 0xFF2E7D32.toInt(), 40, 34, 18f) { plus() })
        return row
    }

    private fun refreshPower() {
        shotTv?.text = "Lực sút: giữ A ${shotBase()}ms (xa ×2.5)"
        passTv?.text = "Lực chuyền: ${(passScale() * 100).toInt()}%"
    }
    private fun adjustShot(delta: Int) {
        prefs.edit().putInt("shotMs", (shotBase() + delta).coerceIn(40, 400)).apply()
        refreshPower()
    }
    private fun adjustPass(delta: Float) {
        val v = Math.round((passScale() + delta) * 10f) / 10f
        prefs.edit().putFloat("passScale", v.coerceIn(0.5f, 1.6f)).apply()
        refreshPower()
    }

    private fun toggle() {
        running = !running
        syncGo()
        if (running) io.execute { loop() }
    }
    private fun syncGo() {
        goBtn?.text = if (running) "⏹" else "▶"
        goBtn?.background = bg(if (running) 0xFFC62828.toInt() else 0xFF2E7D32.toInt(), 12)
        miniBtn?.text = if (running) "⏹" else "▶"
        miniBtn?.background = bg(if (running) 0xCCC62828.toInt() else 0xCC2E7D32.toInt(), 24)
    }

    override fun onAccessibilityEvent(e: AccessibilityEvent?) {}
    override fun onInterrupt() { running = false; ui.post { syncGo() } }
    override fun onDestroy() { running = false; releaseChain(); super.onDestroy() }

    // nhịp quét: nhanh (~15 ảnh/giây) khi có CaptureService, không thì ~3 ảnh/giây
    private fun tick() = if (CaptureHub.active()) 66L else 380L
    private fun segLen() = if (CaptureHub.active()) 250L else 500L
    private fun aiOn() = prefs.getBoolean("aiOn", false)
    private fun myRed() = true   // đội mình luôn áo đỏ
    private fun publishRect() {
        val (x1, y1) = pt(4); val (x2, y2) = pt(5)
        CaptureHub.rect = floatArrayOf(min(x1, x2), min(y1, y2), max(x1, x2), max(y1, y2))
    }
    private fun startFastCapture() {
        try {
            val i = Intent().setClassName(packageName, "com.dlsbot.CaptureRequestActivity")
            i.addFlags(Intent.FLAG_ACTIVITY_NEW_TASK)
            startActivity(i)
            status("Chọn \"Bắt đầu ngay\" ở hộp thoại ghi màn hình rồi quay lại game")
        } catch (e: Exception) {
            status("Chưa có chụp nhanh (thiếu CaptureService.kt). Bot vẫn chạy ~3 ảnh/giây")
        }
    }

    private fun bounds() = wm.currentWindowMetrics.bounds
    private fun pt(i: Int): Pair<Float, Float> = bounds().let {
        prefs.getFloat("x$i", it.width() * D[i].first) to prefs.getFloat("y$i", it.height() * D[i].second)
    }
    private fun jrad() = min(bounds().width(), bounds().height()) * 0.12f
    private fun rn(x: Float) = Random.nextFloat() * 2 * x - x

    // Vị trí ban đầu: góc đối diện minimap (không che minimap). Kéo ✥ để dời, vị trí được nhớ lại.
    private fun placePanel() {
        val lp = panelLp ?: return
        publishRect()
        if (prefs.contains("px")) {
            lp.x = prefs.getInt("px", 0); lp.y = prefs.getInt("py", 0)
        } else {
            val (x1, _) = pt(4); val (x2, _) = pt(5)
            val bw = bounds().width()
            lp.x = if ((x1 + x2) / 2f < bw / 2f) bw - dp(60) else dp(12)
            lp.y = dp(8)
        }
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
        votes.clear(); attack = 0; aiMsg = if (aiOn()) "chờ AI" else "offline"
        tac = null; segEnd = 0; shotUntil = 0; crossUntil = 0; switchUntil = 0; slideUntil = 0; noPressUntil = 0
        hasBall = true; gainSince = 0L; lostSince = 0L; lastCarrier = null; justLost = false
        swipeUntil = 0; gkUntil = 0; recent.clear(); crossSides.clear(); lastPassFrom = null; lastPassAt = 0
        sideStreak = 0; snapMine = emptyList(); snapOpp = emptyList(); snapMineT = 0; snapOppT = 0
        var lastAi = 0L
        var lastPrev = 0L
        lastVoteT = 0L
        while (running) {
            val t0 = System.currentTimeMillis()
            publishRect()
            val map = grabMap()
            if (map == null) {
                if (CaptureHub.active()) { Thread.sleep(6); continue }   // chờ khung hình kế tiếp (chụp nhanh)
                status("Chưa chụp được minimap (bấm ⚙ đặt MAP1/MAP2)"); Thread.sleep(500); continue
            }
            try {
                val now = System.currentTimeMillis()
                val rd = scan(map)
                voteAttack(rd)
                trackVel(rd.reds, true, now, rd.w.toFloat(), rd.h.toFloat())
                trackVel(rd.opps, false, now, rd.w.toFloat(), rd.h.toFloat())
                hud?.let { it.attack = attack; it.postInvalidate() }
                val prev = hasBall
                if (rd.mine != null) {
                    // được bóng lại phải thấy liên tục >= 0,25s để khỏi chập chờn
                    if (gainSince == 0L) gainSince = now
                    lostSince = 0L
                    if (hasBall || now - gainSince >= 250) hasBall = true
                } else {
                    gainSince = 0L
                    if (lostSince == 0L) lostSince = now
                    if (rd.oppHas || now - lostSince >= 500) hasBall = false
                }
                if (prev && !hasBall) { justLost = true; sideStreak = 0 }
                // AI trực tuyến chỉ chạy khi bật nút 🌐 (mặc định TẮT = offline hoàn toàn)
                if (aiOn() && now >= pauseUntil && now - lastAi >= (if (fast) 800L else 4400L) && inflight.get() < 3) {
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
                if (previewOn && now - lastPrev >= 250) {
                    lastPrev = now
                    val pv = makePreview(map, rd)
                    ui.post { previewIv?.setImageBitmap(pv) }
                }
                // mất/được bóng thì quyết định lại NGAY, còn lại đổi đoạn theo nhịp quét
                if (hasBall != prev || now >= segEnd - tick()) {
                    control(now, rd)
                    segEnd = now + segLen()
                }
            } finally {
                map.recycle()
            }
            val el = System.currentTimeMillis() - t0
            if (el < tick()) Thread.sleep(tick() - el)
        }
        hud?.let { it.attack = 0; it.postInvalidate() }
        synchronized(this) { queue.clear(); replays = 99 }
        releaseChain()
        status("Đã dừng")
        ui.post { syncGo() }
    }

    // Chụp màn hình rồi CẮT NGAY vùng minimap, bỏ phần còn lại
    private fun grabMap(): Bitmap? {
        if (CaptureHub.active()) return CaptureHub.take()     // khung hình 15-20 FPS từ CaptureService
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
    // Đội mình = áo ĐỎ/cam. Đội kia = bất kỳ cụm màu nào khác sân và khác đỏ (xanh, vàng, tím, xám, đen, trắng...).
    private fun scan(bmp: Bitmap): Radar {
        val w = bmp.width; val h = bmp.height
        val px = IntArray(w * h)
        bmp.getPixels(px, 0, w, 0, 0, w, h)
        // màu sân = trung vị từng kênh màu của cả vùng minimap (sân chiếm phần lớn diện tích)
        val hr = IntArray(256); val hg = IntArray(256); val hb = IntArray(256)
        for (c in px) { hr[(c shr 16) and 255]++; hg[(c shr 8) and 255]++; hb[c and 255]++ }
        val half = px.size / 2
        fun med(hh: IntArray): Int { var acc = 0; for (i in 0..255) { acc += hh[i]; if (acc >= half) return i }; return 128 }
        val pr = med(hr); val pg = med(hg); val pb = med(hb)
        val red = BooleanArray(w * h); val oth = BooleanArray(w * h); val glw = BooleanArray(w * h)
        for (i in px.indices) {
            val c = px[i]
            val cr = (c shr 16) and 255; val cg = (c shr 8) and 255; val cb = c and 255
            val top = max(cr, max(cg, cb)); val low = min(cr, min(cg, cb))
            val sat = top - low
            if (top >= 215 && low >= 130) { glw[i] = true; continue }               // vầng sáng / quả bóng / áo trắng
            val redDom = cr == top && cr >= 140 && cg * 4 <= cr * 3 && cb * 4 <= cr * 3
            if (redDom && sat >= 70) { red[i] = true; continue }                   // ĐỘI MÌNH: đỏ / cam
            val greenDom = cg == top && cg > cr && cg > cb
            if (greenDom && sat < 110) continue                                     // cỏ sân, vạch kẻ sẫm
            if (sat >= 80) { oth[i] = true; continue }                             // áo xanh/vàng/tím/hồng... màu nào cũng được
            val dr = cr - pr; val dg = cg - pg; val db = cb - pb
            if (dr * dr + dg * dg + db * db > 5625) oth[i] = true                   // áo xám/đen: khác màu sân rõ rệt
        }
        // viền khử răng cưa quanh áo đỏ không phải cầu thủ khác: bỏ các điểm "khác" nằm sát điểm đỏ (<= 2px)
        val nearRed = BooleanArray(w * h)
        for (i in red.indices) if (red[i]) {
            val x = i % w; val y = i / w
            for (yy in max(0, y - 2)..min(h - 1, y + 2)) for (xx in max(0, x - 2)..min(w - 1, x + 2)) nearRed[yy * w + xx] = true
        }
        for (i in oth.indices) if (oth[i] && nearRed[i]) oth[i] = false
        val reds = blobsOf(red, w, h, 5)
        val othB = ArrayList(blobsOf(oth, w, h, 5))
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
        // điểm sáng không dính áo đỏ: cụm to bằng cả cầu thủ = đối thủ mặc áo trắng; cụm nhỏ = quả bóng
        val free = BooleanArray(w * h)
        for (i in glw.indices) free[i] = glw[i] && !attached[i]
        val medN = if (reds.isEmpty()) 0 else reds.map { it.n }.sorted()[reds.size / 2]
        var ball: Blob? = null
        for (g in blobsOf(free, w, h, 3, 1)) {
            if (medN > 0 && g.n >= medN * 0.6f && (g.x1 - g.x0 + 1) >= 3 && (g.y1 - g.y0 + 1) >= 3) {
                othB.add(g)
            } else if (ball == null || g.n > ball.n) {
                ball = g
            }
        }
        val opps: List<Blob> = othB
        var foreign = if (ball != null) Pair(ball.x, ball.y) else null
        // quả bóng nằm sát một cầu thủ đội mình (cách < 6px) -> cầu thủ đó đang cầm bóng
        if (mine == null && foreign != null) {
            val fr = foreign
            val near = reds.minByOrNull { hypot(it.x - fr.first, it.y - fr.second) }
            if (near != null && hypot(near.x - fr.first, near.y - fr.second) <= max(6f, h * 0.06f)) { mine = near; foreign = null }
        }
        var oppHas = false
        if (foreign != null) {
            for (o in opps) {
                val ex = ((o.x1 - o.x0 + 1) * 0.6f).toInt() + 2
                val ey = ((o.y1 - o.y0 + 1) * 0.6f).toInt() + 2
                if (foreign.first >= o.x0 - ex && foreign.first <= o.x1 + ex && foreign.second >= o.y0 - ey && foreign.second <= o.y1 + ey) { oppHas = true; break }
            }
        }
        return Radar(w, h, reds, opps, mine, foreign, oppHas, true)
    }

    private fun blobsOf(mask: BooleanArray, w: Int, h: Int, minN: Int, minDim: Int = 3): List<Blob> {
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
            val bw = x1 - x0 + 1; val bh = y1 - y0 + 1
            // cầu thủ là cụm tròn đặc; vạch kẻ lưới là đường mảnh (bề ngang/dọc nhỏ hoặc rỗng) nên bị loại
            if (n >= minN && bw >= minDim && bh >= minDim && n >= 0.3f * bw * bh) out.add(Blob(sx.toFloat() / n, sy.toFloat() / n, n, x0, x1, y0, y1))
        }
        return out
    }

    // Hướng tấn công theo THỦ MÔN ÁO ĐỎ. Thủ môn đỏ = cầu thủ đỏ nằm sát một đầu sân hơn hẳn đầu kia (>= 12% bề ngang)
    // và gần giữa chiều dọc (thủ môn đứng giữa khung thành). Đỏ phòng ngự bên nào thì tấn công sang phía ngược lại.
    // Tiền đạo ép cao làm cả hai đầu đều có người đỏ -> chênh lệch nhỏ -> không bỏ phiếu bừa.
    private fun voteAttack(rd: Radar) {
        val w = rd.w.toFloat(); val h = rd.h.toFloat()
        gkNote = ""; gkMark = null
        if (rd.reds.size >= 3) {
            val l = rd.reds.minByOrNull { it.x }
            val r = rd.reds.maxByOrNull { it.x }
            if (l != null && r != null) {
                val dl = l.x / w
                val dr = 1f - r.x / w
                val lc = abs(l.y - h / 2f) <= 0.25f * h
                val rc = abs(r.y - h / 2f) <= 0.25f * h
                if (dl <= 0.22f && dr - dl >= 0.12f) { gkNote = "GK đỏ bên trái"; gkMark = l; addVote(1, if (lc) 3 else 2); return }
                if (dr <= 0.22f && dl - dr >= 0.12f) { gkNote = "GK đỏ bên phải"; gkMark = r; addVote(-1, if (rc) 3 else 2); return }
            }
        }
        // chưa rõ thủ môn đỏ: xét thủ môn đội kia (người kia sát mép nhất) rồi đến vị trí trung bình
        if (rd.opps.size >= 2) {
            val odl = rd.opps.minOf { it.x } / w
            val odr = 1f - rd.opps.maxOf { it.x } / w
            if (odl <= 0.22f && odr - odl >= 0.12f) { gkNote = "GK kia bên trái"; addVote(-1, 2); return }
            if (odr <= 0.22f && odl - odr >= 0.12f) { gkNote = "GK kia bên phải"; addVote(1, 2); return }
        }
        if (rd.reds.size >= 2 && rd.opps.size >= 2) {
            val mr = rd.reds.map { it.x.toDouble() }.average()
            val mo = rd.opps.map { it.x.toDouble() }.average()
            if (abs(mr - mo) > w * 0.08) addVote(if (mr < mo) 1 else -1, 1)
        }
    }

    // Vận tốc từng cầu thủ (m/s). Cứ >= 0,25s lại tính lại từ ảnh chụp cũ; các lần quét giữa chừng chép vận tốc từ cầu thủ gần nhất.
    private fun trackVel(list: List<Blob>, mineTeam: Boolean, now: Long, w: Float, h: Float) {
        val snap = if (mineTeam) snapMine else snapOpp
        val t0 = if (mineTeam) snapMineT else snapOppT
        val dt = (now - t0) / 1000f
        for (b in list) {
            val p = snap.minByOrNull { dm(it.x, it.y, b.x, b.y, w, h) } ?: continue
            if (dm(p.x, p.y, b.x, b.y, w, h) >= 8f) continue
            if (dt >= 0.25f && dt < 1.5f) {
                b.vx = 0.6f * ((b.x - p.x) / w * PITCH_L / dt) + 0.4f * p.vx
                b.vy = 0.6f * ((b.y - p.y) / h * PITCH_W / dt) + 0.4f * p.vy
            } else if (dt < 0.25f) {
                b.vx = p.vx; b.vy = p.vy
            }
        }
        if (dt >= 0.25f || snap.isEmpty()) {
            if (mineTeam) { snapMine = list; snapMineT = now } else { snapOpp = list; snapOppT = now }
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

    // Chọn đồng đội để chuyền (chỉ nút B): ưu tiên chuyền THẲNG LÊN, đường chuyền không bị chặn, người nhận không bị kèm.
    // Chuyền vào chân chỗ đồng đội SẼ chạy tới (đón đầu theo vận tốc). Thưởng: chọc khe sau lưng hàng thủ, người đang bứt chạy chỗ,
    // ban bật trả ngược, đổi cánh khi bị vây. noSide = đã chuyền ngang/lùi 2 nhịp liên tiếp -> chỉ xét đường chuyền tiến lên.
    // cutBack = chỉ xét đồng đội gần chấm phạt đền.
    private fun choosePass(me: Blob, reds: List<Blob>, opps: List<Blob>, d: Int, w: Float, h: Float,
                           cutBack: Boolean, tight: Boolean, noSide: Boolean): PassPick? {
        var best: PassPick? = null
        val crowd = opps.count { dm(me.x, me.y, it.x, it.y, w, h) < 12f }
        // hàng thủ thứ hai từ cuối (bỏ thủ môn) = đường lưng hậu vệ
        val xs = opps.map { it.x }.sortedBy { if (d > 0) -it else it }
        val line = if (xs.size >= 2) xs[1] else (if (d > 0) w else 0f)
        val spx = (if (d > 0) w else 0f) - d * w * (14f / PITCH_L)
        val from = lastPassFrom
        val myAdv = if (d > 0) me.x / w else 1f - me.x / w
        for (m in reds) {
            if (m === me) continue
            // đón đầu: bóng bay ~18 m/s, đồng đội chạy tiếp trong lúc đó
            val d0 = dm(me.x, me.y, m.x, m.y, w, h)
            val speed = hypot(m.vx, m.vy)
            var lx = m.x
            var ly = m.y
            if (speed > 1.5f) {
                val tf = d0 / 18f
                lx = (m.x + m.vx * tf / PITCH_L * w).coerceIn(w * 0.02f, w * 0.98f)   // không để bóng trượt ra biên
                ly = (m.y + m.vy * tf / PITCH_W * h).coerceIn(h * 0.02f, h * 0.98f)
            }
            val dist = dm(me.x, me.y, lx, ly, w, h)
            if (dist < 6f || dist > 45f) continue
            if (cutBack && dm(lx, ly, spx, h / 2f, w, h) > 14f) continue
            val progress = (lx - me.x) / w * PITCH_L * d
            if (noSide && progress < 4f) continue
            var pen = 0f
            for (o in opps) {
                val si = segInfo(me.x, me.y, lx, ly, o.x, o.y, w, h)
                if (si.first > 0.05f && si.first < 0.95f) {
                    if (si.second < 2.5f) pen += 1000f else if (si.second < 5f) pen += 25f * (5f - si.second)
                }
            }
            val near = opps.minOfOrNull { dm(lx, ly, it.x, it.y, w, h) } ?: 99f
            if (near < 4f) pen += 30f * (4f - near)
            var s = progress.coerceIn(-15f, 30f) * 1.0f - dist * 0.35f - pen + min(near, 10f) * 2f
            val behind = (lx - line) * d / w * PITCH_L              // mét phía sau lưng hàng thủ
            if (behind >= 0f && behind <= 8f && near > 5f) s += 15f   // chọc khe
            if (m.vx * d > 3f && myAdv > .45f) s += 12f              // đang bứt chạy chỗ về phía khung thành
            if (from != null && System.currentTimeMillis() - lastPassAt < 2500 &&
                dm(m.x, m.y, from.first, from.second, w, h) < 15f) s += 18f   // ban bật trả ngược
            if (crowd >= 3 && abs(ly - me.y) / h * PITCH_W > 25f && near > 8f) s += 25f   // bị vây: đổi cánh
            if (tight && dist < 18f) s += 12f                         // bị ép sát: chuyền một chạm cho người gần
            if (s > (best?.score ?: -1e9f)) best = PassPick(m, s, progress, dist, lx, ly)
        }
        return best?.takeIf { it.score > -10f }
    }

    // ---- Thư viện rê bóng (tacBase = hướng tới khung thành; side = +1 nếu đang ở nửa trên minimap) ----
    private fun library(d: Int, side: Double): List<Pair<Int, Tactic>> {
        val w = side * d * 45 * RAD   // lệch về phía mép sân gần nhất
        fun zig(t: Float) = (if ((t * 3.5f).toInt() % 2 == 0) 1.0 else -1.0) * 38 * RAD
        val straight = Tactic("Thẳng tiến", 1600, steady = true)
        val zigzag = Tactic("Zigzag", 2000, off = { t -> zig(t) })
        val slalom = Tactic("Slalom", 2000, off = { t -> sin(t * 7.0) * 35 * RAD })
        val wing = Tactic("Rê cánh", 2000, off = { t -> if (t < 1.1f) w else w / 4 })
        val cut = Tactic("Cắt vào trong", 1600, off = { t -> if (t < 0.9f) -w * 0.9 else 0.0 })
        val feint = Tactic("Nhử rồi bứt", 1800, pw = { t -> if (t in 0.7f..1.0f) 0.25f else 1f })
        return listOf(4 to straight, 2 to zigzag, 1 to slalom, 2 to cut, 2 to wing, 2 to feint)
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

    private fun nearOppOf(rd: Radar, p: Pair<Float, Float>?): Pair<Float, Float>? {
        if (p == null) return null
        val w = rd.w.toFloat(); val h = rd.h.toFloat()
        val o = rd.opps.minByOrNull { dm(it.x, it.y, p.first, p.second, w, h) } ?: return null
        return if (dm(o.x, o.y, p.first, p.second, w, h) < 15f) Pair(o.x, o.y) else null
    }

    // ---- Quyết định ----
    // Mất bóng: đè B + joystick (+C đổi người/gọi thủ môn). Có bóng: sút khi có cơ hội -> tạt/cắt ngược -> vào vị trí sút ->
    // chuyền CHỈ khi bị ép hoặc có đường chuyền tiến lên rất tốt -> còn lại DỐC BÓNG thẳng về khung thành.
    private fun control(now: Long, rd: Radar) {
        val w = rd.w.toFloat(); val h = rd.h.toFloat()
        val known = attack != 0
        var d = attack
        if (d == 0) {   // chưa đủ phiếu GK: tạm hướng về phía đội kia đang đứng
            d = if (rd.opps.size >= 2 && rd.reds.size >= 2) {
                if (rd.opps.map { it.x.toDouble() }.average() >= rd.reds.map { it.x.toDouble() }.average()) 1 else -1
            } else 1
        }
        val head = if (!known) "?" else if (d > 0) "→" else "←"
        val who = if (hasBall) "mình" else if (rd.oppHas) "kia" else if (rd.foreign != null) "lỏng" else "?"
        val me = rd.mine
        val adv = if (me == null) -1f else if (d > 0) me.x / w else 1f - me.x / w   // 0 = sát khung thành nhà, 1 = sát khung thành đối thủ
        val zone = if (me == null) "" else " | tiến ${(adv * 100).toInt()}% ngang ${(me.y / h * 100).toInt()}%"
        var info = "đỏ ${rd.reds.size} | kia ${rd.opps.size} | bóng $who$zone" +
            (if (gkNote.isEmpty()) "" else " | $gkNote") + (if (cont) " | liền mạch" else " | chế độ cũ")
        if (rd.reds.isEmpty()) { status("Không thấy áo đỏ trên minimap\n$info"); return }
        val carrier: Pair<Float, Float>? = if (me != null) Pair(me.x, me.y) else (rd.foreign ?: nearOppOf(rd, lastCarrier) ?: lastCarrier)
        if (carrier != null) lastCarrier = carrier

        // 1) MẤT BÓNG: đè B + kéo joystick (kèm bóng) về phía người giữ bóng, đón đầu hướng họ chạy.
        //    Vừa mất bóng / bóng vượt về nửa sân nhà: bấm C đổi người. Đối thủ đối mặt trong vòng cấm nhà: giữ C gọi thủ môn.
        if (!hasBall || me == null) {
            if (carrier == null) { status("Chưa thấy bóng\n$info"); return }
            val chaser = rd.reds.minByOrNull { dm(it.x, it.y, carrier.first, carrier.second, w, h) } ?: return
            val oc = rd.opps.minByOrNull { dm(it.x, it.y, carrier.first, carrier.second, w, h) }
            var ix = carrier.first
            var iy = carrier.second
            if (oc != null && hypot(oc.vx, oc.vy) > 1.5f) {
                val tI = (dm(chaser.x, chaser.y, carrier.first, carrier.second, w, h) / 7f).coerceAtMost(1.2f)
                ix = (carrier.first + oc.vx * tI / PITCH_L * w).coerceIn(0f, w)
                iy = (carrier.second + oc.vy * tI / PITCH_W * h).coerceIn(0f, h)
            }
            val a = pang(chaser.x, chaser.y, ix, iy, w, h)
            val dist = dm(chaser.x, chaser.y, carrier.first, carrier.second, w, h)   // mét
            val ownGx = if (d > 0) 0f else w
            val inMyBox = abs(carrier.first - ownGx) / w * PITCH_L <= 16.5f && abs(carrier.second - h / 2f) / h * PITCH_W <= 20.2f
            val centralMyBox = inMyBox && abs(carrier.second - h / 2f) / h * PITCH_W <= 12f
            val inMyHalf = (if (d > 0) carrier.first / w else 1f - carrier.first / w) < 0.5f
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
            } else if ((justLost || dist > 22f || (inMyHalf && dist > 12f)) && now > switchUntil) {
                taps.add(Triple(3, 30L, 60L)); switchUntil = now + 2500
            }
            justLost = false
            if (SLIDE_ENABLED && !inMyBox && dist < 8f && now > slideUntil && Random.nextFloat() < .6f) {
                taps.add(Triple(1, 250L, 60L)); slideUntil = now + 1400
            }
            val extra = (if (rush) " + gọi thủ môn (giữ C)" else if (taps.any { it.first == 3 }) " + đổi người (C)" else "") +
                (if (taps.any { it.first == 1 }) " + xoạc (A)" else "")
            status("Ép sát: đè B$extra (${dist.toInt()}m)\n$info")
            emit(Tactic("Ép sát", 600, taps = taps, press = true, seg = 600L), a, 0)
            return
        }

        // ---- CÓ BÓNG ----
        val up = me.y < h / 2f
        val side = if (up) 1.0 else -1.0
        val tx = if (d > 0) w else 0f
        val dGoal = dm(me.x, me.y, tx, h / 2f, w, h)
        val lateral = abs(me.y - h / 2f) / h * PITCH_W
        val nearOpp = rd.opps.minOfOrNull { dm(me.x, me.y, it.x, it.y, w, h) } ?: 99f
        val pressured = nearOpp < 6f
        // góc nhìn khung thành giữa hai cột dọc (độ): dưới 15 độ là góc hẹp -> không sút, mở góc
        val halfGoal = h * (3.66f / PITCH_W)
        val pa = pang(me.x, me.y, tx, h / 2f - halfGoal, w, h)
        val pb = pang(me.x, me.y, tx, h / 2f + halfGoal, w, h)
        var da = abs(pa - pb)
        if (da > Math.PI) da = 2 * Math.PI - da
        val narrow = Math.toDegrees(da) < 15.0
        if (narrow && dGoal <= 24f) info += " [GÓC HẸP]"
        val canShoot = known && dGoal <= 25f && lateral <= 20f && !narrow
        val goodShot = dGoal <= 20f && lateral <= 14f
        val backing = me.vx * d < -1.5f           // đang chạy lùi xa khung thành -> không sút
        val gk = rd.opps.filter { dm(it.x, it.y, tx, h / 2f, w, h) < 14f }.minByOrNull { dm(it.x, it.y, tx, h / 2f, w, h) }
        val postOff = halfGoal * 0.4f             // ngắm gần chính giữa khung thành, chỉ lệch nhẹ khỏi thủ môn
        var ty = if (gk != null) (if (gk.y >= h / 2f) h / 2f - postOff else h / 2f + postOff) else h / 2f
        // không sút thẳng vào thủ môn: thủ môn nằm trên đường sút thì đổi sang bên kia; cả hai bị chắn thì thôi
        var gkBlocked = false
        if (gk != null) {
            val s1 = segInfo(me.x, me.y, tx, ty, gk.x, gk.y, w, h)
            val s2 = segInfo(me.x, me.y, tx, h - ty, gk.x, gk.y, w, h)
            val b1 = s1.first >= 0f && s1.first <= 1f && s1.second < 2.0f
            val b2 = s2.first >= 0f && s2.first <= 1f && s2.second < 2.0f
            if (b1 && !b2) ty = h - ty else if (b1 && b2) gkBlocked = true
        }
        val squeezed = rd.opps.count { it !== gk && dm(me.x, me.y, it.x, it.y, w, h) < 5f } >= 2   // bị 2 hậu vệ kẹp sát
        val aim = pang(me.x, me.y, tx, ty, w, h)               // góc joystick ngắm THẲNG vào khung thành
        val toGoal = pang(me.x, me.y, tx, h / 2f, w, h)
        val inBoxArea = abs(me.x - tx) / w * PITCH_L <= 16.5f && lateral <= 20.2f
        var frontBlocked = false
        for (o in rd.opps) {
            if (o === gk) continue
            val si = segInfo(me.x, me.y, tx, ty, o.x, o.y, w, h)
            if (si.first > 0f && si.first < 1f && si.second < 2.5f && dm(me.x, me.y, o.x, o.y, w, h) < 7f) { frontBlocked = true; break }
        }
        val spx = tx - d * w * (14f / PITCH_L)               // chấm phạt đền
        val toSpot = pang(me.x, me.y, spx, h / 2f, w, h)

        // chuyền bằng nút B: nhấp ~0,4s = ngắn; đồng đội xa thì đè B lâu hơn = dài (lực chỉnh bằng nút − / + trên menu)
        fun doPass(pk: PassPick, tag: String) {
            val short = pk.dist <= SHORT_MAX_M
            val baseMs = if (short) PASS_LO_MS + ((pk.dist - 6f) / (SHORT_MAX_M - 6f)).coerceIn(0f, 1f) * (PASS_HI_MS - PASS_LO_MS)
                else LONG_PASS_MIN + ((pk.dist - SHORT_MAX_M) / 25f).coerceIn(0f, 1f) * (LONG_PASS_MAX - LONG_PASS_MIN)
            val hold = (baseMs * passScale()).toLong().coerceAtLeast(80L)
            val a = pang(me.x, me.y, pk.tx, pk.ty, w, h)
            val t3 = Tactic(tag + (if (short) "ngắn " else "dài ") + hold + "ms", 200L + hold + 100L,
                taps = listOf(Triple(2, 200L, hold)), steady = true)
            val t3s = if (swipesOn && lateral > 20f) t3.withSwipe(Triple(d, 0, 300L)) else t3   // ban bật sát biên + đẩy bóng bứt tốc
            tac = t3s; tacStart = now; tacBase = a; noPressUntil = now + 300L + hold
            lastPassFrom = Pair(me.x, me.y); lastPassAt = now
            if (pk.progress < 4f) sideStreak++ else sideStreak = 0
            status("${t3.name} (${pk.dist.toInt()}m) $head\n$info")
            emit(t3s, tacBase, 0)
        }

        // 2) SÚT (nút A): pha 1 xoay joystick thẳng vào khung thành (giữ thẳng), pha 2 giữ nguyên hướng rồi mới bấm A.
        //    Vào vòng cấm 16m50 mà không có hậu vệ chắn trước mặt -> sút NGAY. Không sút thẳng vào thủ môn, không sút khi đang chạy lùi.
        val shootOnSight = inBoxArea && !frontBlocked
        if (canShoot && now > shotUntil && (!gkBlocked || squeezed) && (!backing || pressured) && (goodShot || pressured || shootOnSight)) {
            val hold = shotHold(dGoal > 16.5f)
            val nm = if (shootOnSight) "SÚT ngay (vòng cấm trống)" else if (gkOut(gk, tx, w)) "SÚT thẳng khung thành (thủ môn ra)" else "SÚT thẳng khung thành"
            val t1 = Tactic("$nm ${hold}ms", 220L + hold + 100L, taps = listOf(Triple(1, 220L, hold)), steady = true)
            tac = t1; tacStart = now; tacBase = aim; shotUntil = now + 1800; noPressUntil = now + 700; sideStreak = 0
            status("${t1.name} $head\n$info")
            emit(t1, tacBase, 0)
            return
        }
        // sút xa chính diện (16m50 - 25m, thoáng)
        if (known && dGoal > 16.5f && dGoal <= 25f && lateral <= 14f && !narrow && !frontBlocked && !gkBlocked && !backing && now > shotUntil && Random.nextFloat() < .5f) {
            val hold = shotHold(true)
            val t8 = Tactic("SÚT xa ${hold}ms", 220L + hold + 100L, taps = listOf(Triple(1, 220L, hold)), steady = true)
            tac = t8; tacStart = now; tacBase = aim; shotUntil = now + 1800; noPressUntil = now + 700; sideStreak = 0
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
        // 4) SÁT BIÊN NGANG / DẠT CÁNH: gần đáy biên thì cắt ngược về chấm phạt đền (nút B), không thì tạt (nút C)
        val sInt = if (up) 1 else -1
        val repeatCross = crossSides.size >= 2 && crossSides.takeLast(2).all { it == sInt } && Random.nextFloat() < .6f
        if (known && lateral > 22f && dGoal <= 45f && now > crossUntil && !repeatCross) {
            val near = dGoal <= 32f
            if (near) {
                val cb = choosePass(me, rd.reds, rd.opps, d, w, h, true, false, sideStreak >= 2)
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
            tac = t2; tacStart = now; tacBase = if (near) toSpot else toGoal
            crossUntil = now + 3000; noPressUntil = now + 1200
            crossSides.add(sInt); while (crossSides.size > 3) crossSides.removeAt(0)
            remember(t2.name)
            status("${t2.name} $head\n$info")
            emit(t2, tacBase, 0)
            return
        }
        // 5) trong tầm nhưng chưa phải góc đẹp / góc hẹp: chạy vào vị trí sút để mở góc (không bị kèm)
        if (known && dGoal <= 30f && !pressured) {
            val t5 = Tactic("Vào vị trí sút", 1000, steady = true)
            tac = t5; tacStart = now; tacBase = toSpot
            status("${t5.name} $head\n$info")
            emit(t5, tacBase, 0)
            return
        }
        // 6) CHUYỀN: chỉ khi bị ép sát, hoặc có đường chuyền TIẾN LÊN rất tốt (>= 10m) và đã quá 2,5s kể từ lần chuyền trước.
        //    Không chuyền ngang qua lại; trong vòng cấm không chuyền ngang.
        val pk = choosePass(me, rd.reds, rd.opps, d, w, h, false, nearOpp < 4f, sideStreak >= 2)
        val recentPass = now - lastPassAt < 2500
        val wantPass = pk != null && !(inBoxArea && pk.progress < 3f) &&
            ((pressured && Random.nextFloat() < .85f) || (!recentPass && pk.progress >= 10f && Random.nextFloat() < .35f))
        if (pk != null && wantPass) {
            doPass(pk, "Chuyền ")
            return
        }
        // 7) DỐC BÓNG thẳng về khung thành nếu đường phía trước thoáng; không thì rê (+ vuốt nếu bật ✨)
        var laneClear = true
        for (o in rd.opps) {
            val si = segInfo(me.x, me.y, tx, h / 2f, o.x, o.y, w, h)
            if (si.first > 0f && si.first < 0.6f && si.second < 4f && dm(me.x, me.y, o.x, o.y, w, h) < 16f) { laneClear = false; break }
        }
        if (known && laneClear && !pressured) {
            val t6 = Tactic("Dốc bóng thẳng khung thành", 1200, steady = true)
            tac = t6; tacStart = now; tacBase = toGoal
            status("${t6.name} $head\n$info")
            emit(t6, tacBase, 0)
            return
        }
        var t4 = pick(library(d, side))
        if (swipesOn && now > swipeUntil && Random.nextFloat() < .35f) {
            val sw: Triple<Int, Int, Long>? =
                if (nearOpp < 3.5f) Triple(0, if (Random.nextBoolean()) 1 else -1, 300L)
                else if (dGoal > 30f && nearOpp > 10f) Triple(d, 0, 300L)
                else null
            if (sw != null) { t4 = t4.withSwipe(sw); swipeUntil = now + 4000 }
        }
        tac = t4; tacStart = now; tacBase = toGoal
        status("${t4.name} $head\n$info")
        emit(t4, tacBase, 0)
    }

    // thủ môn đã lao ra khỏi vạch vôi (> 6m)?
    private fun gkOut(gk: Blob?, tx: Float, w: Float): Boolean = gk != null && abs(gk.x - tx) / w * PITCH_L > 6f

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
        var total = if (tc.seg > 0) tc.seg else segLen()
        for (i in tc.taps.indices) {
            val (_, s, hd) = tc.taps[i]
            if (!tc.fired[i] && s < rel + total) total = max(total, max(0L, s - rel) + hd + 120)
        }
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
                val tgt = st.base + tc.off(t) + (if (tc.steady) 0.0 else Math.toRadians(rn(2f).toDouble()))
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
        for (i in tc.taps.indices) {
            val (b, s, hd) = tc.taps[i]
            if (!tc.fired[i] && s < rel + total) {
                tc.fired[i] = true
                btn(b, max(0L, s - rel), if (tc.steady) hd else hd + Random.nextLong(-20, 40))
            }
        }
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
