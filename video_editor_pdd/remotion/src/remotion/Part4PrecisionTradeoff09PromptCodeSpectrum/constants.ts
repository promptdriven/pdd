// ── Canvas ──
export const CANVAS_WIDTH = 1920;
export const CANVAS_HEIGHT = 1080;
export const BACKGROUND_COLOR = '#0A0F1A';

// ── Spectrum Bar ──
export const BAR_X = 160;
export const BAR_Y = 460;
export const BAR_WIDTH = 1600;
export const BAR_HEIGHT = 40;
export const BAR_BORDER_RADIUS = 20;
export const BAR_BORDER_COLOR = '#334155';

// ── Spectrum Colors ──
export const LEFT_COLOR = '#4A90D9';
export const MID_COLOR = '#2A3A5A';
export const RIGHT_COLOR = '#64748B';

// ── Slider ──
export const SLIDER_REST_FRACTION = 0.20; // 20% from left
export const SLIDER_START_X = BAR_X;
export const SLIDER_END_X = BAR_X + BAR_WIDTH * SLIDER_REST_FRACTION; // ~480
export const SLIDER_Y = BAR_Y + BAR_HEIGHT / 2; // center of bar
export const SLIDER_SIZE = 20;
export const SLIDER_COLOR = '#E2E8F0';
export const SLIDER_GLOW_COLOR = '#FFFFFF';
export const SLIDER_GLOW_OPACITY = 0.15;
export const SLIDER_GLOW_BLUR = 16;
export const SLIDER_SHADOW_COLOR = '#000000';
export const SLIDER_SHADOW_OPACITY = 0.3;
export const SLIDER_SHADOW_BLUR = 4;
export const SLIDER_SHADOW_OFFSET = 2;

// ── Zone ──
export const ZONE_FILL_COLOR = LEFT_COLOR;
export const ZONE_FILL_OPACITY = 0.08;

// ── Notch Marks ──
export const NOTCH_WIDTH = 4;
export const NOTCH_HEIGHT = 16;
export const NOTCH_COLOR = '#94A3B8';
export const NOTCH_OPACITY = 0.4;
export const NOTCH_LABEL_COLOR = '#64748B';
export const NOTCH_LABEL_OPACITY = 0.3;

export interface NotchData {
  fraction: number; // 0..1 along the spectrum
  label: string;
}

export const NOTCHES: NotchData[] = [
  { fraction: 0.46, label: 'algorithm' },
  { fraction: 0.59, label: 'hash fn' },
  { fraction: 0.71, label: 'bit ops' },
  { fraction: 0.84, label: 'perf loop' },
];

// ── Typography ──
export const LABEL_FONT_FAMILY = 'Inter, system-ui, sans-serif';
export const ENDPOINT_FONT_SIZE = 16;
export const ENDPOINT_FONT_WEIGHT = 600;
export const NOTCH_FONT_SIZE = 9;
export const BOTTOM_FONT_SIZE = 22;
export const PRIMARY_TEXT_COLOR = '#E2E8F0';
export const SECONDARY_TEXT_COLOR = '#94A3B8';

// ── Timing (frames @ 30fps) ──
export const TOTAL_FRAMES = 480;

// Phase 1: Bar draws in from center (0–60)
export const BAR_DRAW_START = 0;
export const BAR_DRAW_DURATION = 40;
export const ENDPOINT_LABEL_START = 30;
export const ENDPOINT_LABEL_DURATION = 20;

// Phase 2: Slider appears and slides (60–150)
export const SLIDER_START = 60;
export const SLIDER_SLIDE_DURATION = 60;

// Phase 3: Notch marks pop in (150–270)
export const NOTCH_START = 150;
export const NOTCH_POP_DURATION = 10;
export const NOTCH_STAGGER = 20;

// Phase 4: Bottom text fades in (270–360)
export const BOTTOM_PRIMARY_START = 270;
export const BOTTOM_SECONDARY_START = 300;
export const BOTTOM_FADE_DURATION = 25;

// Phase 5: Hold (360–450)
// Phase 6: Fade out (450–480)
export const FADE_OUT_START = 450;
export const FADE_OUT_DURATION = 30;
