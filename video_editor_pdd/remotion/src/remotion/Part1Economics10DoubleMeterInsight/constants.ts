// ── Colors ──────────────────────────────────────────────────────────
export const BG_COLOR = "#0D1117";
export const TRACK_BG = "#1A2332";
export const TRACK_BORDER = "#334155";
export const SCALE_COLOR = "#94A3B8";
export const TEXT_PRIMARY = "#E2E8F0";

export const LEFT_COLOR = "#4A90D9"; // Effective Context Window
export const RIGHT_COLOR = "#5AAA6E"; // Model Performance

// ── Dimensions ─────────────────────────────────────────────────────
export const WIDTH = 1920;
export const HEIGHT = 1080;

export const METER_WIDTH = 60;
export const METER_HEIGHT = 400;
export const METER_BORDER_RADIUS = 8;

export const LEFT_X = 480;
export const RIGHT_X = 1440;
export const METER_CENTER_Y = 320; // top of meter track area

// ── Frame Timing ───────────────────────────────────────────────────
export const FPS = 30;
export const TOTAL_FRAMES = 750;

// Phase boundaries (frame numbers)
export const STILLNESS_END = 45; // 0-45: dark stillness
export const TRACKS_APPEAR = 45; // 45-75: meter tracks fade in
export const TRACKS_VISIBLE = 75;
export const SCALES_APPEAR = 75; // 75-105: scale markers fade in
export const SCALES_VISIBLE = 105;
export const FILL_START = 105; // 105-225: meters fill
export const FILL_END = 225;
export const FILL_DURATION = 120;
export const PULSE_START = 225; // 225-270: peak pulse
export const PULSE_END = 270;
export const CENTER_TEXT_START = 270; // 270-330: center text
export const SUMMARY_START = 330; // 330-390: summary line
export const HOLD_START = 390; // 390-480: hold with gentle pulse
export const CHALLENGE_START = 480; // 480-540: challenge text
export const FINAL_HOLD = 540; // 540-750: hold for narration

// ── Meter Data ─────────────────────────────────────────────────────
export const LEFT_METER = {
  label: "Effective Context Window",
  color: LEFT_COLOR,
  scaleMarkers: ["1×", "5×", "10×"] as const,
  maxValue: 10,
  unit: "×",
};

export const RIGHT_METER = {
  label: "Model Performance",
  color: RIGHT_COLOR,
  scaleMarkers: ["baseline", "+50%", "+89%"] as const,
  maxValue: 89,
  unit: "%",
  prefix: "+",
};
