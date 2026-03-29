// ─── Canvas ───────────────────────────────────────────────────────────
export const CANVAS_WIDTH = 1920;
export const CANVAS_HEIGHT = 1080;
export const FPS = 30;
export const TOTAL_FRAMES = 270; // 9 seconds

// ─── Layout ───────────────────────────────────────────────────────────
export const DIVIDER_GAP = 40; // px gap between panels
export const PANEL_WIDTH = (CANVAS_WIDTH - DIVIDER_GAP) / 2; // 940px each
export const DIVIDER_LINE_WIDTH = 2;
export const DIVIDER_MAX_OPACITY = 0.7;

// ─── Colors ───────────────────────────────────────────────────────────
export const BG_COLOR = '#0A1628';
export const DIVIDER_COLOR = '#FFFFFF';

// ─── Timing (frame numbers) ──────────────────────────────────────────
/** Frames 0-15: fade in from black, divider appears */
export const FADE_IN_END = 15;

/** Frame at which clip-1 ends and crossfade to clip-2 begins */
export const CLIP1_DURATION = 160; // frames 0-159 (clip 1 plays)
export const CROSSFADE_START = 150; // clip 2 fades in starting here
export const CROSSFADE_FRAMES = 10; // 10-frame crossfade
export const CLIP2_DURATION = 120; // clip 2 plays frames 150-269

/** Frame 260-270: final hold */
export const HOLD_START = 260;
