// ── Color tokens ──
export const BG_COLOR = "#0A1628";
export const LAYER_BG_INNER = "#0F1D32";
export const LAYER_BG_MID = "#132744";
export const LAYER_BG_OUTER = "#162F54";

export const TEXT_PRIMARY = "#FFFFFF";
export const TEXT_SECONDARY = "#94A3B8";
export const ACCENT_BLUE = "#3B82F6";
export const ACCENT_GREEN = "#22C55E";
export const ACCENT_AMBER = "#F59E0B";
export const ACCENT_PURPLE = "#A855F7";
export const BORDER_GLOW = "rgba(59, 130, 246, 0.5)";
export const DIVIDER_COLOR = "rgba(148, 163, 184, 0.75)";

// ── Layout ──
export const CANVAS_WIDTH = 1920;
export const CANVAS_HEIGHT = 1080;
export const LAYER_CARD_WIDTH = 520;
export const LAYER_CARD_HEIGHT = 300;
export const LAYER_CARD_RADIUS = 16;
export const LAYER_GAP = 40;

// ── Timing (frames at 30 fps) ──
export const FPS = 30;
export const TOTAL_DURATION_FRAMES = 210; // 7 seconds

// Phase 1: Inner layer fully visible (frames 0-40)
export const PHASE_INNER_START = 0;
export const PHASE_INNER_END = 40;

// Phase 2: Zoom-out reveal to show middle layer (frames 40-90)
export const PHASE_MID_ZOOM_START = 40;
export const PHASE_MID_ZOOM_END = 90;

// Phase 3: Continue zoom-out to outer layer (frames 90-140)
export const PHASE_OUTER_ZOOM_START = 90;
export const PHASE_OUTER_ZOOM_END = 140;

// Phase 4: Final pullback to show full picture (frames 140-180)
export const PHASE_FULL_ZOOM_START = 140;
export const PHASE_FULL_ZOOM_END = 180;

// Phase 5: Hold / subtle pulse (frames 180-210)
export const PHASE_HOLD_START = 180;
export const PHASE_HOLD_END = 210;

// ── Layer content labels ──
export const LAYER_LABELS = [
  { title: "The Code", subtitle: "A single developer prompt", icon: ">" },
  { title: "The Context", subtitle: "History of every edit", icon: "\u25CB" },
  { title: "The System", subtitle: "Feedback loops at scale", icon: "\u25C7" },
] as const;
