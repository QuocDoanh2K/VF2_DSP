#include "Define.h"
#include "DSP.h"
#include <Preferences.h>
#include <math.h>
#include <string.h>

#define SAMPLE_RATE 44100.0f
#define GAIN_MIN   (-24)     // don vi 0.5 dB
#define GAIN_MAX   (24)

// ===== 15 bang EQ (graphic EQ 2/3 octave) =====
// loai: 0 = low-shelf, 1 = peaking, 2 = high-shelf
// Bang dau (25Hz) la low-shelf, bang cuoi (16kHz) la high-shelf, 13 bang giua la peaking.
// Muon doi tan so: sua mang BAND_FREQ (nhớ sua cung mang FREQ trong file web index.html).
static const float   BAND_FREQ[DSP_BANDS] = { 25.f, 40.f, 63.f, 100.f, 160.f, 250.f, 400.f, 630.f,
                                              1000.f, 1600.f, 2500.f, 4000.f, 6300.f, 10000.f, 16000.f };
static const uint8_t BAND_TYPE[DSP_BANDS] = { 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2 };
static const float   PEAK_Q = 2.14f;       // ~ do rong 2/3 octave

struct Preset { const char* name; int8_t g[DSP_BANDS]; };   // don vi 0.5 dB
static const Preset PRESETS[] = {
    //                         25  40  63 100 160 250 400 630  1k 1.6k 2.5k 4k 6.3k 10k 16k
    { "Mặc định", {   0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0 } },
    { "Bass mạnh", {  10, 12, 14, 12, 10,  6,  2,  0,  0,  0,  0,  0,  0,  0,  0 } },
    { "Giọng hát", {  -4, -4, -4, -2,  0,  0,  0,  2,  4,  5,  6,  8,  6,  2,  0 } },
    { "Treble sáng", {   0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  2,  4,  6,  8, 12 } },
    { "Remix", {   6, 10, 14, 14,  6, -2, -4, -2,  0,  2,  4,  6,  8, 10,  8 } },
    { "Bolero", {  -2,  0,  2,  4,  6,  4,  2,  0,  2,  4,  6,  4,  2, -2, -4 } },
    { "Nhạc trẻ", {   2,  4,  6,  6,  4,  2,  0,  0,  2,  4,  4,  4,  4,  4,  2 } },
    { "Rock", {   4,  6,  6,  4,  0, -2, -2,  0,  2,  4,  6,  6,  6,  4,  2 } },
    { "Hip-hop", {   8, 12, 14, 10,  6,  2,  0,  0,  2,  2,  2,  2,  4,  4,  2 } },
    { "Acoustic", {   0,  0,  2,  4,  4,  2,  0,  0,  2,  2,  4,  4,  4,  6,  6 } },
    { "Jazz", {   2,  4,  4,  2,  2,  0,  0,  0,  0,  2,  2,  4,  4,  4,  2 } },
    { "Nghe nhỏ", {   6,  8,  8,  6,  2,  0,  0,  0,  0,  0,  0,  2,  4,  6,  6 } },
};
#define PRESET_COUNT ((int)(sizeof(PRESETS) / sizeof(PRESETS[0])))

struct Biquad { float b0, b1, b2, a1, a2; bool on; };

// ---- Trang thai cai dat (chi dung trong loop task) ----
static int8_t gains[DSP_BANDS] = {0};
static bool   eq_on = true;
static bool     save_pending = false;
static uint32_t save_t = 0;
static volatile uint32_t eq_version = 0;

// ---- Truyen he so sang luong audio (2 task khac nhau) ----
static portMUX_TYPE mux = portMUX_INITIALIZER_UNLOCKED;
static Biquad pending[DSP_BANDS];
static float  pending_pre = 1.0f;
static bool   pending_active = false;
static volatile bool coef_dirty = true;

// ---- Trang thai luong audio ----
static Biquad cur[DSP_BANDS];
static float  cur_pre = 1.0f;
static bool   cur_active = false;
static float  z1[2][DSP_BANDS], z2[2][DSP_BANDS];

// He so bo loc theo RBJ Audio EQ Cookbook (da chuan hoa a0 = 1)
static Biquad make_biquad(uint8_t type, float f, float gain_db) {
    Biquad q = { 1.f, 0.f, 0.f, 0.f, 0.f, false };
    if (gain_db == 0.0f) return q;                  // 0 dB: bo qua bang nay

    float A  = powf(10.0f, gain_db / 40.0f);
    float w0 = 2.0f * (float)M_PI * f / SAMPLE_RATE;
    float cs = cosf(w0), sn = sinf(w0);
    float b0, b1, b2, a0, a1, a2;

    if (type == 1) {                                // peaking
        float alpha = sn / (2.0f * PEAK_Q);
        b0 = 1.0f + alpha * A;  b1 = -2.0f * cs;  b2 = 1.0f - alpha * A;
        a0 = 1.0f + alpha / A;  a1 = -2.0f * cs;  a2 = 1.0f - alpha / A;
    } else {                                        // shelf, do doc S = 1
        float alpha = sn * 0.70710678f;
        float beta  = 2.0f * sqrtf(A) * alpha;
        if (type == 0) {                            // low-shelf
            b0 =        A * ((A + 1) - (A - 1) * cs + beta);
            b1 =  2.0f * A * ((A - 1) - (A + 1) * cs);
            b2 =        A * ((A + 1) - (A - 1) * cs - beta);
            a0 =             (A + 1) + (A - 1) * cs + beta;
            a1 = -2.0f *    ((A - 1) + (A + 1) * cs);
            a2 =             (A + 1) + (A - 1) * cs - beta;
        } else {                                    // high-shelf
            b0 =        A * ((A + 1) + (A - 1) * cs + beta);
            b1 = -2.0f * A * ((A - 1) + (A + 1) * cs);
            b2 =        A * ((A + 1) + (A - 1) * cs - beta);
            a0 =             (A + 1) - (A - 1) * cs + beta;
            a1 =  2.0f *    ((A - 1) - (A + 1) * cs);
            a2 =             (A + 1) - (A - 1) * cs - beta;
        }
    }
    q.b0 = b0 / a0;  q.b1 = b1 / a0;  q.b2 = b2 / a0;
    q.a1 = a1 / a0;  q.a2 = a2 / a0;
    q.on = true;
    return q;
}

// Dinh dap ung tan so (dB) cua ca chuoi bo loc, quet 20Hz..20kHz (cac bang chong lan nen khong chi la bang lon nhat)
static float peak_response_db(const Biquad* c) {
    float peak = -100.0f;
    for (int k = 0; k < 128; k++) {
        float f  = 20.0f * powf(1000.0f, k / 127.0f);
        float w  = 2.0f * (float)M_PI * f / SAMPLE_RATE;
        float c1 = cosf(w), s1 = sinf(w), c2 = cosf(2 * w), s2 = sinf(2 * w);
        float db = 0.0f;
        for (int b = 0; b < DSP_BANDS; b++) {
            if (!c[b].on) continue;
            float nr = c[b].b0 + c[b].b1 * c1 + c[b].b2 * c2, ni = -(c[b].b1 * s1 + c[b].b2 * s2);
            float dr = 1.0f + c[b].a1 * c1 + c[b].a2 * c2,    di = -(c[b].a1 * s1 + c[b].a2 * s2);
            db += 10.0f * log10f((nr * nr + ni * ni) / (dr * dr + di * di));
        }
        if (db > peak) peak = db;
    }
    return peak;
}

static void recalc() {
    Biquad c[DSP_BANDS];
    bool  any = false;
    for (int i = 0; i < DSP_BANDS; i++) {
        float db = gains[i] * 0.5f;
        c[i] = make_biquad(BAND_TYPE[i], BAND_FREQ[i], db);
        if (db != 0.0f) any = true;
    }
    bool active = eq_on && any;

    float pre = 1.0f;
#if DSP_AUTO_HEADROOM
    // Ha tien khuech dai bang dung dinh dap ung (neu > 0 dB) de nhac to khong bi vo tieng
    if (active) {
        float pk = peak_response_db(c);
        if (pk > 0.0f) pre = powf(10.0f, -pk / 20.0f);
    }
#endif

    portENTER_CRITICAL(&mux);
    memcpy(pending, c, sizeof(c));
    pending_pre = pre;
    pending_active = active;
    coef_dirty = true;
    portEXIT_CRITICAL(&mux);
}

static void save_now() {
    Preferences p;
    p.begin("vf2", false);
    p.putBool("eqOn", eq_on);
    p.putBytes("eq15", gains, DSP_BANDS);
    p.end();
    Serial.println(">> Da luu EQ");
}

static void mark_changed() {
    eq_version++;
    recalc();
    save_pending = true;
    save_t = millis();
}

void DSP_Init() {
    Preferences p;
    p.begin("vf2", false);
    eq_on = p.getBool("eqOn", true);
    if (p.getBytes("eq15", gains, DSP_BANDS) != DSP_BANDS) memset(gains, 0, sizeof(gains));
    p.end();
    for (int i = 0; i < DSP_BANDS; i++) gains[i] = constrain(gains[i], GAIN_MIN, GAIN_MAX);
    recalc();
    Serial.printf("EQ 15 bang: %s  [", eq_on ? "BAT" : "TAT");
    for (int i = 0; i < DSP_BANDS; i++) Serial.printf(i ? " %d" : "%d", gains[i]);
    Serial.println("] (x0.5 dB)");
}

void DSP_Update() {
    if (save_pending && (int32_t)(millis() - save_t) >= DSP_SAVE_DELAY_MS) {
        save_pending = false;
        save_now();
    }
}

void DSP_Process(int16_t* pcm, uint16_t frames) {
    if (coef_dirty) {
        portENTER_CRITICAL(&mux);
        // Chi xoa trang thai bo loc khi EQ moi bat lai, hoac 1 bang vua tu 0 dB chuyen sang co gain.
        // Khi chi doi gain cua bang dang chay thi giu trang thai => keo thanh truot khong bi bup.
        bool was_active = cur_active;
        for (int b = 0; b < DSP_BANDS; b++) {
            if (!was_active || (!cur[b].on && pending[b].on)) {
                z1[0][b] = z1[1][b] = 0.0f;
                z2[0][b] = z2[1][b] = 0.0f;
            }
        }
        memcpy(cur, pending, sizeof(cur));
        cur_pre = pending_pre;
        cur_active = pending_active;
        coef_dirty = false;
        portEXIT_CRITICAL(&mux);
    }
    if (!cur_active || pcm == nullptr) return;

    for (uint16_t n = 0; n < frames; n++) {
        for (int ch = 0; ch < 2; ch++) {
            float x = pcm[n * 2 + ch] * cur_pre;
            for (int b = 0; b < DSP_BANDS; b++) {
                if (!cur[b].on) continue;
                float y = cur[b].b0 * x + z1[ch][b];            // transposed direct form II
                z1[ch][b] = cur[b].b1 * x - cur[b].a1 * y + z2[ch][b];
                z2[ch][b] = cur[b].b2 * x - cur[b].a2 * y;
                x = y;
            }
            int32_t v = (int32_t)lrintf(x);
            if (v >  32767) v =  32767;
            if (v < -32768) v = -32768;
            pcm[n * 2 + ch] = (int16_t)v;
        }
    }
}

bool   DSP_IsOn() { return eq_on; }
float  DSP_BandFreq(int band) { return (band >= 0 && band < DSP_BANDS) ? BAND_FREQ[band] : 0.0f; }
uint32_t DSP_Version() { return eq_version; }
int8_t DSP_GetGain(int band) { return (band >= 0 && band < DSP_BANDS) ? gains[band] : 0; }

void DSP_SetAll(const int8_t* g, bool on) {
    for (int i = 0; i < DSP_BANDS; i++) gains[i] = constrain((int)g[i], GAIN_MIN, GAIN_MAX);
    eq_on = on;
    mark_changed();
}

int         DSP_PresetCount() { return PRESET_COUNT; }
const char* DSP_PresetName(int i) { return (i >= 0 && i < PRESET_COUNT) ? PRESETS[i].name : ""; }

void DSP_ApplyPreset(int i) {
    if (i < 0 || i >= PRESET_COUNT) return;
    for (int b = 0; b < DSP_BANDS; b++) gains[b] = PRESETS[i].g[b];
    eq_on = true;
    mark_changed();
}
