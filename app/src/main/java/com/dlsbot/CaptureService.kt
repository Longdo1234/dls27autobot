package com.dlsbot

import android.app.Activity
import android.app.Notification
import android.app.NotificationChannel
import android.app.NotificationManager
import android.app.Service
import android.content.Context
import android.content.Intent
import android.content.pm.ServiceInfo
import android.graphics.Bitmap
import android.graphics.PixelFormat
import android.hardware.display.DisplayManager
import android.hardware.display.VirtualDisplay
import android.media.ImageReader
import android.media.projection.MediaProjection
import android.media.projection.MediaProjectionManager
import android.os.Bundle
import android.os.Handler
import android.os.HandlerThread
import android.os.IBinder
import android.os.SystemClock
import android.util.DisplayMetrics
import android.view.Display
import kotlin.math.max

// Hộp thoại xin quyền ghi màn hình (nền trong suốt). Chọn "Bắt đầu ngay" rồi quay lại game.
class CaptureRequestActivity : Activity() {
    override fun onCreate(savedInstanceState: Bundle?) {
        super.onCreate(savedInstanceState)
        val mpm = getSystemService(Context.MEDIA_PROJECTION_SERVICE) as MediaProjectionManager
        startActivityForResult(mpm.createScreenCaptureIntent(), 7)
    }

    override fun onActivityResult(requestCode: Int, resultCode: Int, data: Intent?) {
        super.onActivityResult(requestCode, resultCode, data)
        if (resultCode == RESULT_OK && data != null) {
            val i = Intent(this, CaptureService::class.java)
            i.putExtra("code", resultCode)
            i.putExtra("data", data)
            startForegroundService(i)
        }
        finish()
    }
}

// Đọc màn hình 15-20 khung hình/giây trên luồng nền (HandlerThread), chỉ cắt đúng vùng minimap rồi đưa cho BotService qua CaptureHub.
class CaptureService : Service() {
    private var proj: MediaProjection? = null
    private var vd: VirtualDisplay? = null
    private var reader: ImageReader? = null
    private var ht: HandlerThread? = null
    private var handler: Handler? = null
    private var curW = 0
    private var curH = 0
    private var scrW = 1
    private var scrH = 1
    private val scale = 0.6f   // thu nhỏ ảnh để nhẹ máy; minimap vẫn đủ rõ

    override fun onBind(intent: Intent?): IBinder? = null

    override fun onStartCommand(intent: Intent?, flags: Int, startId: Int): Int {
        if (proj != null) return START_NOT_STICKY
        val nm = getSystemService(NotificationManager::class.java)
        nm.createNotificationChannel(NotificationChannel("dls_cap", "Đọc minimap", NotificationManager.IMPORTANCE_LOW))
        val n = Notification.Builder(this, "dls_cap")
            .setContentTitle("DLS Bot đang đọc minimap")
            .setSmallIcon(android.R.drawable.ic_menu_camera)
            .build()
        startForeground(1, n, ServiceInfo.FOREGROUND_SERVICE_TYPE_MEDIA_PROJECTION)
        val code = intent?.getIntExtra("code", 0) ?: 0
        @Suppress("DEPRECATION")
        val data = intent?.getParcelableExtra<Intent>("data")
        if (data == null) { stopSelf(); return START_NOT_STICKY }
        val t = HandlerThread("dls-capture")
        t.start()
        ht = t
        val hd = Handler(t.looper)
        handler = hd
        val mpm = getSystemService(Context.MEDIA_PROJECTION_SERVICE) as MediaProjectionManager
        val p = mpm.getMediaProjection(code, data)
        proj = p
        p.registerCallback(object : MediaProjection.Callback() {
            override fun onStop() { stopSelf() }
        }, hd)
        rebuild()
        // xoay màn hình thì dựng lại màn hình ảo cho khớp kích thước mới
        getSystemService(DisplayManager::class.java).registerDisplayListener(object : DisplayManager.DisplayListener {
            override fun onDisplayAdded(displayId: Int) {}
            override fun onDisplayRemoved(displayId: Int) {}
            override fun onDisplayChanged(displayId: Int) { if (displayId == Display.DEFAULT_DISPLAY) rebuild() }
        }, hd)
        return START_NOT_STICKY
    }

    @Synchronized
    private fun rebuild() {
        val p = proj ?: return
        val m = DisplayMetrics()
        @Suppress("DEPRECATION")
        getSystemService(DisplayManager::class.java).getDisplay(Display.DEFAULT_DISPLAY).getRealMetrics(m)
        scrW = m.widthPixels
        scrH = m.heightPixels
        val w = max(64, (scrW * scale).toInt())
        val h = max(64, (scrH * scale).toInt())
        if (w == curW && h == curH && vd != null) return
        val old = reader
        val r = ImageReader.newInstance(w, h, PixelFormat.RGBA_8888, 2)
        r.setOnImageAvailableListener({ rd -> onFrame(rd) }, handler)
        reader = r
        val v = vd
        if (v == null) {
            vd = p.createVirtualDisplay("dls-minimap", w, h, m.densityDpi,
                DisplayManager.VIRTUAL_DISPLAY_FLAG_AUTO_MIRROR, r.surface, null, handler)
        } else {
            v.resize(w, h, m.densityDpi)
            v.surface = r.surface
        }
        curW = w
        curH = h
        try { old?.close() } catch (e: Exception) {}
    }

    // Mỗi khung hình: chỉ chép vùng minimap (toạ độ do BotService đặt trong CaptureHub.rect) ra một Bitmap nhỏ
    private fun onFrame(rd: ImageReader) {
        try {
            val img = rd.acquireLatestImage() ?: return
            try {
                val rc = CaptureHub.rect
                if (rc[2] - rc[0] < 10f || rc[3] - rc[1] < 5f) return
                val sx = img.width / scrW.toFloat()
                val sy = img.height / scrH.toFloat()
                val l = (rc[0] * sx).toInt().coerceIn(0, img.width - 2)
                val r = (rc[2] * sx).toInt().coerceIn(l + 1, img.width)
                val t = (rc[1] * sy).toInt().coerceIn(0, img.height - 2)
                val b = (rc[3] * sy).toInt().coerceIn(t + 1, img.height)
                val cw = r - l
                val ch = b - t
                if (cw < 20 || ch < 10) return
                val pl = img.planes[0]
                val buf = pl.buffer
                val rs = pl.rowStride
                val ps = pl.pixelStride
                val px = IntArray(cw * ch)
                var k = 0
                for (y in 0 until ch) {
                    var pos = (t + y) * rs + l * ps
                    for (x in 0 until cw) {
                        val rr = buf.get(pos).toInt() and 255
                        val gg = buf.get(pos + 1).toInt() and 255
                        val bb = buf.get(pos + 2).toInt() and 255
                        px[k++] = (255 shl 24) or (rr shl 16) or (gg shl 8) or bb
                        pos += ps
                    }
                }
                CaptureHub.frame = Bitmap.createBitmap(px, cw, ch, Bitmap.Config.ARGB_8888)
                CaptureHub.stamp = SystemClock.uptimeMillis()
            } finally {
                img.close()
            }
        } catch (e: Exception) {
        }
    }

    override fun onDestroy() {
        CaptureHub.stamp = 0L
        CaptureHub.frame = null
        try { vd?.release() } catch (e: Exception) {}
        try { reader?.close() } catch (e: Exception) {}
        try { proj?.stop() } catch (e: Exception) {}
        ht?.quitSafely()
        super.onDestroy()
    }
}
