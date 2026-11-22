package com.dlsbot

import android.app.Activity
import android.content.Intent
import android.os.Bundle
import android.provider.Settings
import android.text.Editable
import android.text.TextWatcher
import android.widget.*

class MainActivity : Activity() {
    override fun onCreate(s: Bundle?) {
        super.onCreate(s)
        val prefs = getSharedPreferences("cfg", MODE_PRIVATE)
        val l = LinearLayout(this).apply { orientation = LinearLayout.VERTICAL; setPadding(48, 96, 48, 48) }
        l.addView(TextView(this).apply {
            text = "1) Dán API key Anthropic bên dưới.\n2) Bật Trợ năng > DLS Bot.\n" +
                "3) Mở game, bấm ⚙ trên thanh nổi, kéo JOY/A/B/C đè đúng nút trong game rồi bấm LƯU.\n" +
                "4) Bấm ▶ để AI bắt đầu đá, ⏹ để dừng."
        })
        l.addView(EditText(this).apply {
            hint = "sk-ant-..."; setText(prefs.getString("key", ""))
            addTextChangedListener(object : TextWatcher {
                override fun afterTextChanged(e: Editable?) { prefs.edit().putString("key", e.toString().trim()).apply() }
                override fun beforeTextChanged(s: CharSequence?, a: Int, b: Int, c: Int) {}
                override fun onTextChanged(s: CharSequence?, a: Int, b: Int, c: Int) {}
            })
        })
        l.addView(Button(this).apply {
            text = "Mở cài đặt Trợ năng"
            setOnClickListener { startActivity(Intent(Settings.ACTION_ACCESSIBILITY_SETTINGS)) }
        })
        setContentView(l)
    }
}
