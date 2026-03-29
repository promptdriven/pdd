// constants.ts — Part3MoldParts01SectionTitleCard

// ── Canvas ──
export const WIDTH = 1920;
export const HEIGHT = 1080;
export const FPS = 30;
export const TOTAL_FRAMES = 1320;

// ── Colors ──
export const BG_COLOR = '#0A0F1A';
export const GRID_COLOR = '#1E293B';
export const GRID_OPACITY = 0.05;
export const GRID_SPACING = 60;

export const TITLE_COLOR = '#E2E8F0';
export const SECTION_LABEL_COLOR = '#64748B';
export const SECTION_LABEL_OPACITY = 0.5;
export const RULE_COLOR = '#334155';
export const RULE_OPACITY = 0.5;

// Ghost mold cross-section
export const GHOST_WALLS_COLOR = '#4A90D9';
export const GHOST_WALLS_OPACITY = 0.04;
export const GHOST_NOZZLE_COLOR = '#D9944A';
export const GHOST_NOZZLE_OPACITY = 0.03;
export const GHOST_CAVITY_COLOR = '#4AD9A0';
export const GHOST_CAVITY_OPACITY = 0.03;
export const GHOST_STROKE_WIDTH = 1.5;

// ── Typography ──
export const TITLE_FONT_SIZE = 72;
export const TITLE_FONT_WEIGHT = 700;
export const SECTION_LABEL_FONT_SIZE = 14;
export const SECTION_LABEL_FONT_WEIGHT = 600;
export const SECTION_LABEL_LETTER_SPACING = 4;

// ── Layout positions ──
export const SECTION_LABEL_Y = 400;
export const TITLE_LINE1_Y = 460;
export const RULE_Y = 505;
export const TITLE_LINE2_Y = 545;
export const TITLE_LINE2_OFFSET_X = 15;
export const RULE_WIDTH = 280;

// ── Animation keyframes ──
export const FRAME_BG_FADE_START = 0;
export const FRAME_BG_FADE_END = 15;

export const FRAME_LABEL_FADE_START = 15;
export const FRAME_LABEL_FADE_DURATION = 20;

export const FRAME_GHOST_DRAW_START = 15;
export const FRAME_GHOST_DRAW_DURATION = 30;

export const FRAME_TYPEWRITER_START = 40;
export const CHARS_PER_FRAME = 2; // frames per character

export const FRAME_RULE_DRAW_START = 60;
export const FRAME_RULE_DRAW_DURATION = 10;

export const FRAME_LINE2_FADE_START = 70;
export const FRAME_LINE2_FADE_DURATION = 20;
export const FRAME_LINE2_SLIDE_DISTANCE = 10;

export const FRAME_HOLD_START = 90;
export const FRAME_HOLD_END = 1260;

export const FRAME_FADEOUT_START = 1260;
export const FRAME_FADEOUT_DURATION = 60;

// Ghost pulse cycle
export const GHOST_PULSE_CYCLE = 60;

// ── Text content ──
export const SECTION_LABEL_TEXT = 'PART 3';
export const TITLE_LINE1_TEXT = 'THE MOLD HAS';
export const TITLE_LINE2_TEXT = 'THREE PARTS';
