// === Layout ===
export const WIDTH = 1920;
export const HEIGHT = 1080;
export const SPLIT_X = 960;
export const LEFT_PANEL_WIDTH = 958;
export const RIGHT_PANEL_WIDTH = 958;
export const FPS = 30;
export const TOTAL_FRAMES = 480;

// === Colors ===
export const BG_COLOR = '#000000';
export const LEFT_BG = '#0F172A';
export const RIGHT_BG = '#0A0F1A';
export const SPLIT_LINE_COLOR = '#334155';

// Left panel (Crafting)
export const CRAFT_ACCENT = '#C4956A';
export const WOOD_BODY = '#8B6D45';
export const WOOD_GRAIN = '#6B5233';

// Right panel (Molding)
export const MOLD_ACCENT = '#D9944A';
export const MOLD_CAVITY = '#1E293B';
export const PLASTIC_COLOR = '#94A3B8';
export const DISPOSABLE_LABEL_COLOR = '#64748B';

// === Positions (relative to panel, not global) ===
export const CHAIR_CENTER = { x: 479, y: 450 };
export const CHAIR_SIZE = { w: 300, h: 400 };

export const MOLD_CENTER = { x: 479, y: 350 };
export const MOLD_SIZE = { w: 300, h: 250 };

export const PLASTIC_CENTER = { x: 479, y: 650 };

// === Aura ===
export const AURA_BLUR = 40;
export const AURA_BASE_OPACITY = 0.12;
export const AURA_PULSE_MIN = 0.08;
export const AURA_PULSE_MAX = 0.15;
export const AURA_PULSE_PERIOD = 40; // frames

// === Animation Timing (frames) ===
export const PHASE_1_END = 20;      // Split line + headers
export const PHASE_2_START = 20;
export const PHASE_2_END = 80;      // Chair/mold draw, first marks
export const PHASE_3_START = 80;
export const PHASE_3_END = 160;     // More marks, plastic flows
export const PHASE_4_START = 160;
export const PHASE_4_END = 240;     // Auras begin
export const PHASE_5_START = 240;
export const PHASE_5_END = 320;     // Part dissolve/regen
export const PHASE_6_START = 320;
export const PHASE_6_END = 400;     // Both hold, auras pulse
export const PHASE_7_START = 400;
export const PHASE_7_END = 440;     // Summary labels appear
export const PHASE_8_START = 440;
export const PHASE_8_END = 480;     // Final hold

// === Easing durations ===
export const SPLIT_LINE_DRAW_DURATION = 15;
export const OUTLINE_DRAW_DURATION = 40;
export const CHISEL_STAGGER = 5;
export const DISSOLVE_DURATION = 20;
export const REGEN_DURATION = 15;
export const SUMMARY_FADE_DURATION = 20;
