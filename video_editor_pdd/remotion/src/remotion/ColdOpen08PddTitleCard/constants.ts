// ─── Color Palette ───────────────────────────────────────────────
export const BG_DEEP_NAVY = "#0A1228";
export const BG_CARD_SURFACE = "#111D35";
export const ACCENT_BLUE = "#3B82F6";
export const ACCENT_CYAN = "#06B6D4";
export const ACCENT_GREEN = "#22C55E";
export const TEXT_PRIMARY = "#F8FAFC";
export const TEXT_SECONDARY = "#94A3B8";
export const GLOW_BLUE = "rgba(59, 130, 246, 0.35)";
export const GLOW_CYAN = "rgba(6, 182, 212, 0.25)";
export const BRACKET_COLOR = "#3B82F6";
export const DIVIDER_COLOR = "rgba(148, 163, 184, 0.75)";

// ─── Typography ──────────────────────────────────────────────────
export const FONT_MONO = "'SF Mono', 'Fira Code', 'Cascadia Code', monospace";
export const FONT_SANS = "'Inter', 'SF Pro Display', system-ui, sans-serif";

// ─── Layout ──────────────────────────────────────────────────────
export const CANVAS_WIDTH = 1920;
export const CANVAS_HEIGHT = 1080;
export const CENTER_X = CANVAS_WIDTH / 2;
export const CENTER_Y = CANVAS_HEIGHT / 2;

// ─── Timing (frames @ 30fps) ────────────────────────────────────
export const FPS = 30;
export const TOTAL_DURATION_FRAMES = 150; // 5 seconds

// Phase timings
export const PHASE_BRACKET_DRAW = { start: 0, end: 18 };
export const PHASE_PDD_REVEAL = { start: 6, end: 30 };
export const PHASE_SUBTITLE_IN = { start: 28, end: 48 };
export const PHASE_DIVIDER_IN = { start: 42, end: 54 };
export const PHASE_TAGLINE_IN = { start: 50, end: 70 };
export const PHASE_GLOW_PULSE = { start: 60, end: 150 };
export const PHASE_CURSOR_BLINK = { start: 30, end: 150 };
