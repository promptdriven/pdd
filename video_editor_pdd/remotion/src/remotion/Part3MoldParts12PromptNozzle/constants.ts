// ── Colors ──────────────────────────────────────────────
export const BG_COLOR = "#0A0F1A";
export const GRID_COLOR = "#1E293B";
export const GRID_OPACITY = 0.05;
export const GRID_SPACING = 60;

export const WALL_COLOR = "#4A90D9";
export const WALL_DIM_OPACITY = 0.1;
export const WALL_GLOW_OPACITY = 0.35;

export const NOZZLE_COLOR = "#D9944A";
export const NOZZLE_GLOW_BLUR = 15;
export const NOZZLE_GLOW_OPACITY = 0.5;

export const LIQUID_START_COLOR = "#D9944A";
export const LIQUID_END_COLOR = "#0D9488";

export const TERMINAL_GREEN = "#A6E3A1";
export const TERMINAL_BG = "#0D1117";
export const TERMINAL_BORDER = "#1E293B";

// ── Layout ─────────────────────────────────────────────
export const CANVAS_W = 1920;
export const CANVAS_H = 1080;

// Mold cross-section geometry (centered)
export const MOLD_CENTER_X = 960;
export const MOLD_TOP = 180;
export const MOLD_OUTER_W = 700;
export const MOLD_OUTER_H = 540;
export const MOLD_WALL_THICKNESS = 40;
export const MOLD_INNER_W = MOLD_OUTER_W - MOLD_WALL_THICKNESS * 2;
export const MOLD_INNER_H = MOLD_OUTER_H - MOLD_WALL_THICKNESS * 2;
export const MOLD_LEFT = MOLD_CENTER_X - MOLD_OUTER_W / 2;
export const MOLD_INNER_LEFT = MOLD_LEFT + MOLD_WALL_THICKNESS;
export const MOLD_INNER_TOP = MOLD_TOP + MOLD_WALL_THICKNESS;

// Nozzle dimensions
export const NOZZLE_WIDTH = 80;
export const NOZZLE_HEIGHT = 70;
export const NOZZLE_X = MOLD_CENTER_X - NOZZLE_WIDTH / 2;
export const NOZZLE_Y = MOLD_TOP - NOZZLE_HEIGHT + 10;
export const NOZZLE_OPENING_Y = MOLD_TOP + 10;

// Terminal
export const TERMINAL_X = 1450;
export const TERMINAL_Y = 920;
export const TERMINAL_W = 420;
export const TERMINAL_H = 100;

// ── Data ───────────────────────────────────────────────
export const PROMPT_TEXT =
  "Parse user IDs from untrusted input. Return None on failure, never throw. Handle unicode.";
export const PROMPT_FILE = "user_parser.prompt";

export const NOZZLE_LABELS = [
  { text: "intent", direction: "left" as const, dx: -120, dy: -30 },
  { text: "requirements", direction: "right" as const, dx: 120, dy: -30 },
  { text: "constraints", direction: "top" as const, dx: 0, dy: -70 },
];

export const CODE_VERSION_A = `def parse_user_ids(raw: str):
    result = []
    for token in raw.split(","):
        token = token.strip()
        if not token:
            continue
        try:
            uid = int(token)
            result.append(uid)
        except (ValueError, UnicodeError):
            return None
    return result`;

export const CODE_VERSION_B = `def parse_user_ids(text: str):
    ids = []
    for part in text.split(","):
        cleaned = part.strip()
        if cleaned == "":
            continue
        try:
            parsed = int(cleaned)
            ids.append(parsed)
        except (ValueError, UnicodeError):
            return None
    return ids`;

// ── Timing (frames) ────────────────────────────────────
export const FPS = 30;
export const TOTAL_FRAMES = 720;

export const PHASE_NOZZLE_GLOW_START = 0;
export const PHASE_NOZZLE_GLOW_END = 30;
export const PHASE_LABELS_START = 30;
export const PHASE_FILE_LABEL_START = 90;
export const PHASE_FILE_LABEL_END = 150;
export const PHASE_TEXT_STREAM_START = 120;
export const PHASE_LIQUID_FILL_START = 240;
export const PHASE_DRAIN_START = 300;
export const PHASE_DRAIN_END = 360;
export const PHASE_SECOND_FILL_START = 360;
export const PHASE_SECOND_FILL_END = 480;
export const PHASE_BOTH_VISIBLE_START = 480;
export const PHASE_HOLD_START = 600;
