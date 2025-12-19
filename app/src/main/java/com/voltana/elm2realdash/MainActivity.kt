package com.voltana.elm2realdash

import android.Manifest
import android.annotation.SuppressLint
import android.bluetooth.BluetoothAdapter
import android.bluetooth.BluetoothSocket
import android.content.Context
import android.content.Intent
import android.content.pm.PackageManager
import android.net.Uri
import android.os.Build
import android.os.Bundle
import android.provider.Settings
import android.view.View
import android.widget.*
import androidx.activity.result.contract.ActivityResultContracts
import androidx.appcompat.app.AppCompatActivity
import androidx.core.app.ActivityCompat
import java.io.*
import java.net.ServerSocket
import java.net.Socket
import java.text.SimpleDateFormat
import java.util.*
import java.util.concurrent.LinkedBlockingQueue
import java.util.concurrent.TimeUnit
import java.util.concurrent.atomic.AtomicBoolean
import kotlin.concurrent.thread
import java.net.Inet4Address
import java.net.NetworkInterface

class MainActivity : AppCompatActivity() {

    // UI
    private lateinit var edtDeviceName: EditText
    private lateinit var btnStart: Button
    private lateinit var btnSendFile: Button
    private lateinit var txtLog: TextView
    private var txtStatus: TextView? = null
    private lateinit var chkEnableLog: CheckBox
    private lateinit var edtFilterId: AutoCompleteTextView
    private lateinit var btnClearFilter: Button
    private lateinit var txtFreq: TextView
    private lateinit var scrollView: ScrollView

    // BT / TCP
    private var btSocket: BluetoothSocket? = null
    private var tcpServer: ServerSocket? = null
    private var tcpClient: Socket? = null
    private var tcpOut: OutputStream? = null
    @Volatile
    private var isClientConnected = false

    private val BT_UUID = java.util.UUID.fromString("00001101-0000-1000-8000-00805F9B34FB")

    // Files & dirs
    private lateinit var logsDir: File
    private lateinit var fInput: File   // frames received (raw lines)
    private lateinit var fOutput: File  // diagnostic log (ATs and replies)
    private lateinit var fAT: File      // at commands file

    // --- UI log ring buffer & freeze control ---
    private val uiLines = ArrayDeque<String>(200)  // فقط ۱۰۰ خط آخر نگه می‌داریم؛ ظرفیت اضافی برای حذف
    private var isLogFrozen = false                // با لمس، True/False می‌شود
    private var isUiLogEnabled = true              // می‌توان UI log را برای پرفورمنس خاموش کرد
    private val MAX_UI_LINES = 30

    // Reader queue (lines produced by background reader)
    private val incomingLines = LinkedBlockingQueue<String>(10000)

    // Reader control
    private val readerRunning = AtomicBoolean(false)
    private var readerThreadRef: Thread? = null

    @Volatile private var lastUiUpdate = 0L

    private var wakeLock: android.os.PowerManager.WakeLock? = null

    private lateinit var txtCan: TextView
    private lateinit var scrollCan: ScrollView

    // هر ID → آخرین نمایش؛ ترتیب درج حفظ می‌شود
    private val canRows = LinkedHashMap<String, String>()
    private val MAX_CAN_ROWS = 512
    private val knownIds = LinkedHashSet<String>()
    private var filterSelectedId: String? = null
    private val selectedTimestampsMs = ArrayDeque<Long>()
    private val freqWindowMs = 5_000L
    private lateinit var idSuggestionsAdapter: ArrayAdapter<String>

    // Permissions launcher
    private val requestPermissionsLauncher =
        registerForActivityResult(ActivityResultContracts.RequestMultiplePermissions()) { perms ->
            appendLog("Permissions result: $perms")
        }

    @SuppressLint("ClickableViewAccessibility")
    override fun onCreate(savedInstanceState: Bundle?) {
        super.onCreate(savedInstanceState)
        setContentView(R.layout.activity_main)

        val pm = getSystemService(Context.POWER_SERVICE) as android.os.PowerManager
        wakeLock = pm.newWakeLock(android.os.PowerManager.PARTIAL_WAKE_LOCK, "elm2realdash:btReader")
        wakeLock?.setReferenceCounted(false)
        wakeLock?.acquire()  // CPU بیدار می‌ماند

        // find views
        edtDeviceName = findViewById(R.id.edtDeviceName)
        btnStart = findViewById(R.id.btnStart)
        btnSendFile = findViewById(R.id.btnSendFile)
        txtLog = findViewById(R.id.txtLog)
        chkEnableLog = findViewById(R.id.chkEnableLog)
        edtFilterId = findViewById(R.id.edtFilterId)
        btnClearFilter = findViewById(R.id.btnClearFilter)
        txtFreq = findViewById(R.id.txtFreq)
        scrollView = findViewById(R.id.scrollView)
        txtCan = findViewById(R.id.txtCan)
        scrollCan = findViewById(R.id.scrollCan)
        txtStatus = null

        idSuggestionsAdapter = ArrayAdapter(this, android.R.layout.simple_dropdown_item_1line, mutableListOf())
        edtFilterId.setAdapter(idSuggestionsAdapter)
        edtFilterId.threshold = 1
        edtFilterId.setOnItemClickListener { _, _, position, _ ->
            val id = idSuggestionsAdapter.getItem(position)
            applyCanFilter(id)
        }
        edtFilterId.setOnDismissListener {
            // When user types and presses enter without selecting from dropdown
            val text = edtFilterId.text?.toString()?.trim()?.uppercase(Locale.US)
            if (!text.isNullOrEmpty()) applyCanFilter(text)
        }
        btnClearFilter.setOnClickListener { applyCanFilter(null) }

        isUiLogEnabled = loadUiLogPreference()
        chkEnableLog.isChecked = isUiLogEnabled
        applyUiLogMode(initial = true)
        chkEnableLog.setOnCheckedChangeListener { _, isChecked ->
            isUiLogEnabled = isChecked
            saveUiLogPreference(isChecked)
            applyUiLogMode(initial = false)
        }

        // لمس روی txtLog با    عث Freeze/Resume می‌شود
        txtLog.setOnTouchListener { _, event ->
            if (!isUiLogEnabled) return@setOnTouchListener false
            if (event.action == android.view.MotionEvent.ACTION_DOWN) {
                isLogFrozen = !isLogFrozen
                Toast.makeText(
                    this,
                    if (isLogFrozen) "Log frozen — برای ادامه دوباره لمس کن" else "Log resumed",
                    Toast.LENGTH_SHORT
                ).show()
                if (!isLogFrozen) {
                    // وقتی Resume شد، آخرین ۱۰۰ خط را فوراً بازنویسی و اسکرول می‌کنیم
                    refreshLogViewFromBuffer()
                }
            }
            false // اجازه بده اسکرول عادی هم کار کند
        }
        setupPaths()
        ensureFiles()
        loadSavedBTDeviceName()
        checkAndRequestPermissions()

        startTCPServer()

        btnStart.setOnClickListener {
            startBluetoothWork()
        }

        btnSendFile.setOnClickListener {
            sendLastLogFile()
        }

        appendLog("Ready.")
    }

    private fun checkAndRequestPermissions() {
        val perms = mutableListOf<String>()
        if (Build.VERSION.SDK_INT >= Build.VERSION_CODES.S) {
            perms += Manifest.permission.BLUETOOTH_CONNECT
            perms += Manifest.permission.BLUETOOTH_SCAN
        } else {
            perms += Manifest.permission.ACCESS_FINE_LOCATION
        }
        val need = perms.filter {
            ActivityCompat.checkSelfPermission(this, it) != PackageManager.PERMISSION_GRANTED
        }
        if (need.isNotEmpty()) {
            requestPermissionsLauncher.launch(need.toTypedArray())
        }
    }

    private fun setupPaths() {
        // target: Android/media/com.voltana.elm2realdash/files/Documents/car_logs/
        val mediaDir = externalMediaDirs.firstOrNull()
        val base = if (mediaDir != null && mediaDir.exists()) {
            File(mediaDir, "files/Documents/car_logs")
        } else {
            File(getExternalFilesDir(null), "Documents/car_logs")
        }
        if (!base.exists()) base.mkdirs()
        logsDir = base
        fInput = File(logsDir, "elm_input_log.txt")
        fOutput = File(logsDir, "elm_output_log.txt")
        fAT = File(logsDir, "at_commands.txt")
    }

    private fun ensureFiles() {
        if (!fAT.exists()) {
            fAT.writeText(
                """
                ATZ
                ATE0
                ATL0
                ATS0
                ATH1
                ATCAF0
                ATSP6
                ATMA
                """.trimIndent()
            )
        }
        if (!fInput.exists()) fInput.createNewFile()
        if (!fOutput.exists()) fOutput.createNewFile()
    }

    private fun appendLog(msg: String) {
        val now = SimpleDateFormat("HH:mm:ss", Locale.US).format(Date())
        val line = "$now  $msg"

        if (isUiLogEnabled) {
            // به‌جای اضافه‌کردن مستقیم به TextView، اول در بافر نگه می‌داریم
            synchronized(uiLines) {
                uiLines.addLast(line)
                // محدود به ۱۰۰ خط
                while (uiLines.size > MAX_UI_LINES) uiLines.removeFirst()
            }

            // اگر Freeze نیست، UI را از بافر بازنویسی کن و اسکرول را پایین نگه‌دار
            if (!isLogFrozen) {
                val now = System.currentTimeMillis()
                if (now - lastUiUpdate > 30) {
                    lastUiUpdate = now
                    runOnUiThread { refreshLogViewFromBuffer() }
                }
            }
        }

        // قبلی: علاوه بر UI، در فایل دیباگ هم بنویس
        try {
            synchronized(fOutput) {
                fOutput.appendText(line + "\n")
            }
        } catch (_: Exception) {}
    }

    // محتوی TextView را دقیقاً از بافر می‌سازد و به انتها اسکرول می‌کند
    private fun refreshLogViewFromBuffer() {
        if (!isUiLogEnabled) return
        val snapshot: List<String> = synchronized(uiLines) { uiLines.toList() }
        txtLog.text = snapshot.joinToString("\n") + "\n"
        scrollView.post { scrollView.fullScroll(View.FOCUS_DOWN) }
//        txtStatus?.text = snapshot.lastOrNull()?.substringAfter("  ") ?: ""
    }


    private fun loadSavedBTDeviceName() {
        val sp = getSharedPreferences("config", Context.MODE_PRIVATE)
        val saved = sp.getString("bt_name", "")
        edtDeviceName.setText(saved)
    }

    private fun loadUiLogPreference(): Boolean {
        val sp = getSharedPreferences("config", Context.MODE_PRIVATE)
        return sp.getBoolean("ui_log_enabled", true)
    }

    private fun saveBTDeviceName(name: String) {
        val sp = getSharedPreferences("config", Context.MODE_PRIVATE)
        sp.edit().putString("bt_name", name).apply()
    }

    private fun saveUiLogPreference(enabled: Boolean) {
        val sp = getSharedPreferences("config", Context.MODE_PRIVATE)
        sp.edit().putBoolean("ui_log_enabled", enabled).apply()
    }

    private fun applyUiLogMode(initial: Boolean) {
        if (!isUiLogEnabled) {
            isLogFrozen = false
            synchronized(uiLines) { uiLines.clear() }
            txtLog.text = "UI Log خاموش است (برای فعال‌سازی، تیک را بزنید)."
            txtLog.visibility = View.GONE
            if (!initial) {
                Toast.makeText(this, "UI Log خاموش شد تا هنگ و لگ کمتر شود.", Toast.LENGTH_SHORT)
                    .show()
            }
        } else {
            txtLog.visibility = View.VISIBLE
            refreshLogViewFromBuffer()
            if (!initial) {
                Toast.makeText(this, "UI Log فعال شد.", Toast.LENGTH_SHORT).show()
            }
        }
    }

    private fun getLocalIPv4s(): List<String> {
        val ips = mutableListOf<String>()
        try {
            val interfaces = NetworkInterface.getNetworkInterfaces()
            for (intf in interfaces) {
                if (!intf.isUp || intf.isLoopback) continue
                for (addr in intf.inetAddresses) {
                    if (!addr.isLoopbackAddress && addr is Inet4Address) {
                        ips += addr.hostAddress
                    }
                }
            }
        } catch (_: Exception) { }
        return ips.distinct()
    }


    private fun startTCPServer() {
        thread(name = "tcp-accept") {
            try {
                tcpServer = ServerSocket(35000) // 0.0.0.0:35000 روی همه‌ی اینترفیس‌ها
                // 🔽 اینجا IPهای دستگاه رو لاگ می‌کنیم
                val ips = getLocalIPv4s()
                if (ips.isEmpty()) {
                    appendLog("TCP Server listening on :35000 (no IPv4 found / likely offline)")
                } else {
                    ips.forEach { ip ->
                        appendLog("TCP Server listening on $ip:35000")
                    }
                }
                appendLog("Waiting for RealDash to connect...")

                tcpClient = tcpServer!!.accept()
                tcpOut = tcpClient!!.getOutputStream()
                isClientConnected = true
                appendLog(
                    "RealDash connected from ${tcpClient!!.inetAddress.hostAddress}:${tcpClient!!.port}"
                )
                // ...
            } catch (e: Exception) {
                appendLog("TCP Server error: ${e.message}")
            }
        }
    }

    private fun sendTCP(bytes: ByteArray): Boolean {
        if (!isTcpUp()) return false
        return try {
            tcpOut!!.write(bytes)
            tcpOut!!.flush()
            true
        } catch (e: Exception) {
            appendLog("TCP send error: ${e.javaClass.simpleName}: ${e.message}")
            safelyCloseTcp()
            false
        }
    }

    private fun startBluetoothWork() {
        val deviceName = edtDeviceName.text.toString().trim()
        if (deviceName.isEmpty()) {
            appendLog("Bluetooth device name is empty!")
            return
        }
        saveBTDeviceName(deviceName)

        val adapter = BluetoothAdapter.getDefaultAdapter()
        if (adapter == null) {
            appendLog("Bluetooth not supported.")
            return
        }
        if (!adapter.isEnabled) {
            appendLog("Bluetooth is OFF.")
            return
        }

        val device = adapter.bondedDevices.find { it.name.equals(deviceName, ignoreCase = true) || it.address.equals(deviceName, ignoreCase = true) }
        if (device == null) {
            appendLog("Device not found in paired devices: $deviceName")
            val names = adapter.bondedDevices.joinToString(", ") { it.name ?: it.address }
            appendLog("Paired devices: $names")
            return
        }

        appendLog("Connecting to ${device.name} (${device.address}) ...")

        if (Build.VERSION.SDK_INT >= Build.VERSION_CODES.S) {
            if (ActivityCompat.checkSelfPermission(this, Manifest.permission.BLUETOOTH_CONNECT)
                != PackageManager.PERMISSION_GRANTED
            ) {
                appendLog("Missing BLUETOOTH_CONNECT permission.")
                requestPermissionsLauncher.launch(arrayOf(Manifest.permission.BLUETOOTH_CONNECT))
                return
            }
        }

        thread {
            try {
                // try insecure then secure
                try {
                    btSocket = device.createInsecureRfcommSocketToServiceRecord(BT_UUID)
                } catch (e: Exception) {
                    btSocket = device.createRfcommSocketToServiceRecord(BT_UUID)
                }

                if (adapter.isDiscovering) adapter.cancelDiscovery()

                btSocket!!.connect()
                appendLog("Bluetooth socket connected.")

                // start reader thread BEFORE sending commands so we don't miss any early banner
                startReader(btSocket!!.inputStream)

                val inputStreamForWait = IncomingStreamQueueWrapper() // wrapper to poll queue
                // we don't use its internal stream; sendCommandAndWait will read from queue

                val output = btSocket!!.outputStream

                // read commands
                val commandsRaw = fAT.readLines().map { it.trim() }.filter { it.isNotEmpty() }
                appendLog("Read ${commandsRaw.size} AT commands from file.")

                // find monitor command (last that starts with ATMA or ATMR)
                var monitorCmd: String? = null
                for (line in commandsRaw.reversed()) {
                    val u = line.uppercase(Locale.US)
                    if (u.startsWith("ATMA") || u.startsWith("ATMR")) {
                        monitorCmd = line
                        break
                    }
                }

                // send non-monitor commands with 5s timeout; exit if any fails to respond
                val nonMonitor = if (monitorCmd != null) commandsRaw.takeWhile { it != monitorCmd } else commandsRaw
                for (cmd in nonMonitor) {
                    val ok = sendCommandAndWait(cmd, 5000L)
                    if (!ok) {
                        appendLog("Command [$cmd] did not respond within 5s -> aborting sequence.")
                        try { btSocket?.close() } catch (_: Exception) {}
                        btSocket = null
                        stopReader()
                        return@thread
                    }
                    // small breathing room
                    Thread.sleep(80)
                }

                // if there's a monitor command, handle it (ATMA continuous or ATMR batches)
                if (monitorCmd != null) {
                    val mu = monitorCmd.uppercase(Locale.US)
                    if (mu.startsWith("ATMA")) {
                        appendLog("Entering ATMA continuous monitor (last command).")
                        // ensure we actually send the ATMA command now
                        safeWrite(output, monitorCmd)
                        monitorLoopATMA()

                    } else {
                        appendLog("Monitor command not recognized: $monitorCmd")
                    }
                } else {
                    appendLog("No monitor command in AT file; finished sequence.")
                    stopReader()
                }

            } catch (e: Exception) {
                appendLog("BT Error: ${e.message}")
                try { btSocket?.close() } catch (_: Exception) {}
                btSocket = null
                stopReader()
            }
        }
    }

    // safe write to BT output (append CR)
    private fun safeWrite(output: OutputStream, cmd: String) {
        try {
            output.write((cmd + "\r").toByteArray(Charsets.UTF_8))
            output.flush()
            appendLog(">> $cmd")
            synchronized(fOutput) { fOutput.appendText(">> $cmd\n") }
            // ⬇️ این خط جدید: TX را در فایل ورودی هم ثبت کن
            synchronized(fInput) { fInput.appendText(">> $cmd\n") }
        } catch (e: Exception) {
            appendLog("Write error: ${e.message}")
        }
    }

    // -------------------------
    // Background reader:
    // reads bytes from BT input, splits into lines, pushes into incomingLines queue
    // detects '>' prompt even without newline
    // -------------------------
    private fun startReader(input: InputStream) {
        stopReader() // ensure no double
        readerRunning.set(true)
        val inStream = BufferedInputStream(input)
        readerThreadRef = thread(start = true, name = "bt-reader") {
            val buffer = ByteArray(2048)
            val sb = StringBuilder()
            try {
                while (readerRunning.get()) {
                    val available = try { inStream.available() } catch (_: Exception) { 0 }
                    if (available > 0) {
                        val len = inStream.read(buffer)
                        if (len <= 0) {
                            Thread.sleep(10)
                            continue
                        }
//                        val chunk = String(buffer, 0, len, Charsets.UTF_8)
                        val chunkRaw = String(buffer, 0, len, Charsets.UTF_8)

                        // فقط برای دیباگ موقت
                        appendLog("RAW: ${chunkRaw.replace("\n","\\n").replace("\r","\\r")}")

                        // نرمال‌سازی پایان خط: CRLF و CR → LF
                        val chunk = chunkRaw.replace("\r\n", "\n").replace('\r', '\n')
                        // append and scan for lines and '>' prompt
                        sb.append(chunk)
                        var processedUpTo = 0
                        for (i in 0 until sb.length) {
                            val c = sb[i]
                            // detect '>' prompt standalone or preceded by newline
                            if (c == '>') {
                                // push anything before '>' as a line if it contains non-space
                                val before = sb.substring(processedUpTo, i)
                                pushPartsToQueue(before)
                                incomingLines.offer(">")
                                synchronized(fOutput) { fOutput.appendText("<< >\n") }
                                processedUpTo = i + 1
                            } else if (c == '\n') {
                                // push content up to this newline as a line
                                val part = sb.substring(processedUpTo, i)
                                pushPartsToQueue(part)
                                processedUpTo = i + 1
                            }
                        }
                        // keep remainder
                        if (processedUpTo > 0) {
                            val remain = sb.substring(processedUpTo)
                            sb.setLength(0)
                            sb.append(remain)
                        }
                        // small sleep to avoid busy loop
                    } else {
                        Thread.sleep(10)
                    }
                }
            } catch (e: Exception) {
                appendLog("Reader thread read error: ${e.message}")
            } finally {
                appendLog("Reader thread stopped.")
            }
        }
    }

    private fun stopReader() {
        readerRunning.set(false)
        try {
            readerThreadRef?.interrupt()
        } catch (_: Exception) {}
        readerThreadRef = null
        incomingLines.clear()
    }

    // helper: split a raw string by CR/WS and push meaningful parts into queue and files
    private fun pushPartsToQueue(rawPart: String) {
        val cleaned = rawPart.replace("\r", "").trim()
        if (cleaned.isEmpty()) return
        incomingLines.offer(cleaned)
        try { synchronized(fOutput) { fOutput.appendText("<< $cleaned\n") } } catch (_: Exception) {}
    }


    // -------------------------
    // sendCommandAndWait: poll incomingLines queue for responses up to timeout
    // Returns true if we consider command responded (OK/ERROR/banner/> or partial data)
    // -------------------------
    private fun sendCommandAndWait(cmd: String, timeoutMs: Long): Boolean {
        try {
            // send
            val socketOut = try { btSocket?.outputStream } catch (_: Exception) { null }
            if (socketOut == null) {
                appendLog("BT output unavailable while sending $cmd")
                return false
            }
            safeWrite(socketOut, cmd)

            val deadline = System.currentTimeMillis() + timeoutMs
            var sawAnything = false
            while (System.currentTimeMillis() < deadline) {
                val remain = deadline - System.currentTimeMillis()
                val line = incomingLines.poll(remain, TimeUnit.MILLISECONDS) ?: continue
                sawAnything = true
                appendLog("<< $line")
                try { synchronized(fOutput) { fOutput.appendText("<< $line\n") } } catch (_: Exception) {}
                // if banner or definitive marker -> success
                if (line.equals("OK", true) ||
                    line.equals("ERROR", true) ||
                    line.equals("NO DATA", true) ||
                    line.contains("ELM327", true) ||
                    line == ">"
                ) {
                    return true
                } else {
                    // otherwise we treat it as "meaningful data" but continue waiting for definitive markers
                    // keep looping until timeout or definitive marker
                }
            }
            if (sawAnything) {
                appendLog("Got some data but no definitive OK/ERROR/banner within timeout for $cmd.")
                return true // treat partial as success (device may stream afterwards)
            } else {
                appendLog("!! Timeout waiting for response to $cmd")
                try { synchronized(fOutput) { fOutput.appendText("!! Timeout for $cmd\n") } } catch (_: Exception) {}
                return false
            }
        } catch (e: Exception) {
            appendLog("sendCommandAndWait error: ${e.message}")
            try { synchronized(fOutput) { fOutput.appendText("sendCommandAndWait error: ${e.message}\n") } } catch (_: Exception) {}
            return false
        }
    }

    // -------------------------
    // Monitor loops read from incomingLines queue (not directly InputStream)
    // -------------------------
    private fun monitorLoopATMA() {
        appendLog("Reading ATMA stream (using incoming queue)...")
        try {
            while (btSocket != null && btSocket!!.isConnected) {
                val line = incomingLines.poll(2, TimeUnit.SECONDS) ?: continue
                if (line.isBlank()) continue
                appendLog("RX: $line")
                updateCanLiveRow(line)
                try { synchronized(fInput) { fInput.appendText(line + "\n") } } catch (_: Exception) {}
                val frame = convertToRealDashFrame(line)
                if (frame != null && (frame[3].toInt() and 0xFF) > 0) {
                    appendLog(line)
                    try { synchronized(fOutput) { fOutput.appendText("FRAME: $line\n") } } catch (_: Exception) {}
                    val ok = sendTCP(frame)
//                    if (!ok) {
//                        appendLog("TCP disconnected — stopping monitor loop.")
//                        break
//                    }
                } else {
                    try { synchronized(fOutput) { fOutput.appendText("DROP: $line\n") } } catch (_: Exception) {}
                }
            }
        } catch (e: Exception) {
            appendLog("ATMA monitor error: ${e.message}")
        } finally {
            appendLog("ATMA monitor stopped.")
            stopReader()
        }
    }

    // Convert raw to RealDash frame (unchanged logic with some robustness)
    private fun convertToRealDashFrame(raw: String): ByteArray? {
        var hex = raw.trim().replace("\\s+".toRegex(), "").uppercase(Locale.US)
        if (hex.isEmpty()) return null
        val onlyHex = hex.replace("[^0-9A-F]".toRegex(), "")
        if (onlyHex.length < 3) return null
        val junk = hex.length - onlyHex.length
        if (junk.toDouble() / hex.length > 0.4) return null
        hex = onlyHex
        if (hex.length < 3) return null
        val id = hex.substring(0, 3)
        var data = if (hex.length > 3) hex.substring(3) else ""
        if (data.length % 2 == 1) data = data.dropLast(1)
        if (data.length > 16) data = data.substring(0, 16)
        val idNum = try { id.toInt(16) } catch (_: Exception) { return null }
        val dataBytes = if (data.isNotEmpty()) hexStringToByteArray(data) else ByteArray(0)
        if (dataBytes.size > 8) return null
        val buffer = ByteArray(5 + dataBytes.size)
        buffer[0] = 0xAA.toByte()
        buffer[1] = ((idNum shr 8) and 0xFF).toByte()
        buffer[2] = (idNum and 0xFF).toByte()
        buffer[3] = dataBytes.size.toByte()
        if (dataBytes.isNotEmpty()) dataBytes.copyInto(buffer, 4)
        buffer[buffer.size - 1] = 0x55.toByte()
        return buffer
    }

    private fun hexStringToByteArray(str: String): ByteArray {
        val len = str.length
        val out = ByteArray(len / 2)
        var j = 0
        var i = 0
        while (i < len - 1) {
            val hi = Character.digit(str[i], 16)
            val lo = Character.digit(str[i + 1], 16)
            if (hi < 0 || lo < 0) break
            out[j] = ((hi shl 4) + lo).toByte()
            i += 2
            j++
        }
        return if (j == out.size) out else out.copyOf(j)
    }

    private fun sendLastLogFile() {
//        if (!isTcpUp()) {
//            appendLog("RealDash not connected — cannot send.")
//            return
//        }
        thread(name = "rd-replay") {
            appendLog("Sending full log file to RealDash...")
            try {
                fInput.bufferedReader().useLines { lines ->
                    for (line in lines) {
//                        if (!isTcpUp()) {
//                            appendLog("Stop replay: TCP not connected.")
//                            break
//                        }
                        val frame = convertToRealDashFrame(line)
                        // فقط فریم‌های معتبر با طول > 0
                        if (frame != null && frame.size >= 5 && (frame[3].toInt() and 0xFF) > 0) {
                            appendLog(line) // اختیاری برای ردیابی
                            val ok = sendTCP(frame)
//                            if (!ok) {
//                                appendLog("Stop replay: TCP send failed/disconnected.")
//                                break
//                            }
                            updateCanLiveRow(line)
                            try { Thread.sleep(50) } catch (_: InterruptedException) {}
                        } else {
                            // اختیاری: برای عیب‌یابی
                            // appendLog("RD DROP (replay): $line")
                        }
                    }
                }
                appendLog("Log file sent.")
            } catch (e: Exception) {
                appendLog("Send last log file error: ${e.javaClass.simpleName}: ${e.message}")
            }
        }
    }

    override fun onDestroy() {
        super.onDestroy()
        try { btSocket?.close() } catch (_: Exception) {}
        try { tcpServer?.close() } catch (_: Exception) {}
        try { tcpClient?.close() } catch (_: Exception) {}
        stopReader()

        try { wakeLock?.release() } catch (_: Exception) {}
        wakeLock = null
    }

    // helper to open "manage all files" setting if needed (Android R+)
    private fun openAppManageAllFilesPermission() {
        if (Build.VERSION.SDK_INT >= Build.VERSION_CODES.R) {
            try {
                val intent = Intent(Settings.ACTION_MANAGE_APP_ALL_FILES_ACCESS_PERMISSION)
                intent.data = Uri.parse("package:$packageName")
                startActivity(intent)
            } catch (e: Exception) {
                val intent = Intent()
                intent.action = Settings.ACTION_MANAGE_ALL_FILES_ACCESS_PERMISSION
                startActivity(intent)
            }
        }
    }

    // lightweight wrapper placeholder (not used directly) kept for earlier design compatibility
    private class IncomingStreamQueueWrapper

    private data class CanMsg(val id: String, val dataBytes: List<String>)

    /**
     * پارس خط خام CAN:
     * - هرچیزی غیر از هگز حذف می‌شود
     * - ۳ کاراکتر اول = ID (سازگار با منطق فعلی)
     * - بقیه به صورت ۲-تا-۲-تا به بایت تبدیل می‌شوند
     * - اگر طول فرد بود، کاراکتر آخر داده حذف می‌شود
     * - برای نمایش، همه‌ی بایت‌ها را نگه می‌داریم (نه فقط ۸ تا)
     */
    private fun parseCanRaw(raw: String): CanMsg? {
        var hex = raw.uppercase(Locale.US)
            .replace(Regex("[^0-9A-F]"), "")  // فقط هگز
        if (hex.length < 3) return null

        val id = hex.substring(0, 3)
        var data = if (hex.length > 3) hex.substring(3) else ""
        if (data.length % 2 == 1) data = data.dropLast(1)

        val dataBytes = if (data.isNotEmpty()) data.chunked(2) else emptyList()
        return CanMsg(id, dataBytes)
    }

    private fun updateCanLiveRow(raw: String, source: String = "") {
        val msg = parseCanRaw(raw) ?: return
        val len = msg.dataBytes.size
        val dataStr = if (len > 0) msg.dataBytes.joinToString(" ") else "-"
        val line = buildString {
            append("ID ").append(msg.id)
            append(" ")
            append(dataStr)
            if (source.isNotEmpty()) append("  (").append(source).append(')')
        }

        synchronized(canRows) {
            canRows[msg.id] = line
            if (canRows.size > MAX_CAN_ROWS) {
                val it = canRows.entries.iterator()
                var toRemove = canRows.size - MAX_CAN_ROWS
                while (toRemove > 0 && it.hasNext()) { it.next(); it.remove(); toRemove-- }
            }
            knownIds.add(msg.id)
        }
        maybeUpdateIdSuggestions(msg.id)
        if (filterSelectedId != null && filterSelectedId.equals(msg.id, ignoreCase = true)) {
            trackSelectedFrequency()
        }
        runOnUiThread { refreshCanView() }
    }

    private fun refreshCanView() {
        val snapshot: List<String> = synchronized(canRows) { canRows.values.toList() }
        // خط عنوان + خطوط به‌ترتیبِ اولین مشاهده
        val text = buildString {
            append("--- CAN Live (by ID) ---\n")
            val filtered = filterSelectedId?.let { id ->
                snapshot.filter { it.contains("ID $id", ignoreCase = true) }
            } ?: snapshot
            if (filtered.isEmpty()) {
                append("No data yet.\n")
            } else {
                filtered.forEach { append(it).append('\n') }
            }
        }
        txtCan.text = text
        scrollCan.post { scrollCan.fullScroll(View.FOCUS_DOWN) } // اگر خواستی اسکرول نکند، این خط را بردار
        updateFrequencyLabel()
    }

    private fun maybeUpdateIdSuggestions(newId: String) {
        if (idSuggestionsAdapter.getPosition(newId) >= 0) return
        idSuggestionsAdapter.add(newId)
        idSuggestionsAdapter.sort { a, b -> a.compareTo(b) }
        idSuggestionsAdapter.notifyDataSetChanged()
    }

    private fun applyCanFilter(id: String?) {
        filterSelectedId = id?.uppercase(Locale.US)
        edtFilterId.setText(filterSelectedId ?: "")
        synchronized(selectedTimestampsMs) { selectedTimestampsMs.clear() }
        updateFrequencyLabel()
        refreshCanView()
    }

    private fun trackSelectedFrequency() {
        val now = System.currentTimeMillis()
        synchronized(selectedTimestampsMs) {
            selectedTimestampsMs.addLast(now)
            while (selectedTimestampsMs.isNotEmpty() && now - selectedTimestampsMs.first > freqWindowMs) {
                selectedTimestampsMs.removeFirst()
            }
        }
    }

    private fun updateFrequencyLabel() {
        val currentFilter = filterSelectedId
        if (currentFilter.isNullOrEmpty()) {
            txtFreq.text = "Freq: -"
            return
        }
        val now = System.currentTimeMillis()
        val count = synchronized(selectedTimestampsMs) {
            while (selectedTimestampsMs.isNotEmpty() && now - selectedTimestampsMs.first > freqWindowMs) {
                selectedTimestampsMs.removeFirst()
            }
            selectedTimestampsMs.size
        }
        val freqPerSec = count.toDouble() / (freqWindowMs / 1000.0)
        txtFreq.text = "Freq ($currentFilter): ${"%.2f".format(freqPerSec)} /s"
    }
    private fun isTcpUp(): Boolean {
        val c = tcpClient
        return isClientConnected &&
                tcpOut != null &&
                c != null &&
                c.isConnected &&
                !c.isClosed &&
                !c.isOutputShutdown
    }

    private fun safelyCloseTcp() {
        try { tcpOut?.flush() } catch (_: Exception) {}
        try { tcpClient?.close() } catch (_: Exception) {}
        isClientConnected = false
        tcpOut = null
        tcpClient = null
        appendLog("TCP disconnected (closed locally).")
    }

}
