// ─── Canvas ───
export const CANVAS_WIDTH = 1920;
export const CANVAS_HEIGHT = 1080;
export const BACKGROUND_COLOR = '#0A0F1A';
export const TOTAL_FRAMES = 480;

// ─── Spectrum Bar ───
export const BAR_X = 160;
export const BAR_Y = 460;
export const BAR_WIDTH = 1600;
export const BAR_HEIGHT = 40;
export const BAR_BORDER_RADIUS = 20;
export const BAR_BORDER_COLOR = '#334155';

// ─── Colors ───
export const LEFT_COLOR = '#4A90D9';
export const MID_COLOR = '#2A3A5A';
export const RIGHT_COLOR = '#64748B';
export const SLIDER_COLOR = '#E2E8F0';
export const SLIDER_GLOW_COLOR = '#FFFFFF';
export const NOTCH_COLOR = '#94A3B8';
export const PRIMARY_TEXT_COLOR = '#E2E8F0';
export const SECONDARY_TEXT_COLOR = '#94A3B8';
export const NOTCH_LABEL_COLOR = '#64748B';

// ─── Slider ───
export const SLIDER_SIZE = 20;
export const SLIDER_REST_FRACTION = 0.20; // 20% from left
export const SLIDER_START_X = BAR_X;
export const SLIDER_END_X = BAR_X + BAR_WIDTH * SLIDER_REST_FRACTION; // ~480
export const SLIDER_Y = BAR_Y + BAR_HEIGHT / 2; // center of bar

// ─── Notches ───
export interface NotchData {
  fraction: number;
  label: string;
}

export const NOTCH_DATA: NotchData[] = [
  { fraction: 0.46, label: 'algorithm' },
  { fraction: 0.59, label: 'hash fn' },
  { fraction: 0.71, label: 'bit ops' },
  { fraction: 0.84, label: 'perf loop' },
];

export const NOTCH_WIDTH = 4;
export const NOTCH_HEIGHT = 16;
export const NOTCH_OPACITY = 0.4;
export const NOTCH_LABEL_OPACITY = 0.3;

// ─── Zone Overlay ───
export const ZONE_FILL_OPACITY = 0.08;

// ─── Typography ───
export const FONT_FAMILY = 'Inter, system-ui, sans-serif';

// ─── Animation Timing (frames) ───
export const PHASE_BAR_START = 0;
export const PHASE_BAR_DRAW_DURATION = 40;
export const PHASE_LABELS_START = 30;
export const PHASE_LABELS_FADE_DURATION = 20;

export const PHASE_SLIDER_START = 60;
export const PHASE_SLIDER_SLIDE_DURATION = 60;

export const PHASE_NOTCH_START = 150;
export const PHASE_NOTCH_STAGGER = 20;
export const PHASE_NOTCH_POP_DURATION = 10;

export const PHASE_BOTTOM_LINE1_START = 270;
export const PHASE_BOTTOM_LINE2_START = 300;
export const PHASE_BOTTOM_FADE_DURATION = 25;

export const PHASE_FADEOUT_START = 450;
export const PHASE_FADEOUT_DURATION = 30;
