// ── Canvas ──
export const CANVAS_WIDTH = 1920;
export const CANVAS_HEIGHT = 1080;
export const TOTAL_FRAMES = 240;
export const FPS = 30;

// ── Background ──
export const BG_COLOR = '#0A0F1A';

// ── Divider ──
export const DIVIDER_COLOR = '#FFFFFF';
export const DIVIDER_WIDTH = 2;
export const DIVIDER_OPACITY = 0.7; // minimum 0.7 per overlay contract

// ── Panel Layout ──
export const PANEL_WIDTH = 920;
export const CENTER_GAP = 80;
export const LEFT_PANEL_CENTER_X = PANEL_WIDTH / 2; // 460
export const RIGHT_PANEL_CENTER_X = PANEL_WIDTH / 2; // 460

// ── Headers ──
export const HEADER_FONT_SIZE = 20;
export const HEADER_FONT_WEIGHT = 700;
export const HEADER_Y = 120;

// ── Left Panel (Traditional) ──
export const TRAD_HEADER_COLOR = '#F87171';
export const TRAD_BORDER_COLOR = 'rgba(248, 113, 113, 0.2)';
export const TRAD_ARROW_COLOR = 'rgba(248, 113, 113, 0.3)';
export const TRAD_BANDAID_COLOR = 'rgba(248, 113, 113, 0.4)';
export const TRAD_ELLIPSIS_COLOR = 'rgba(248, 113, 113, 0.3)';

// ── Right Panel (PDD) ──
export const PDD_HEADER_COLOR = '#4ADE80';
export const PDD_BORDER_COLOR = 'rgba(74, 144, 217, 0.2)';
export const PDD_ARROW_COLOR = 'rgba(74, 144, 217, 0.3)';
export const PDD_FINAL_BORDER_COLOR = 'rgba(74, 222, 128, 0.5)';
export const PDD_GLOW_COLOR = 'rgba(74, 222, 128, 0.15)';
export const PDD_CODE_COLOR = '#A6E3A1';
export const PDD_CHECKMARK_COLOR = '#4ADE80';

// ── Step Boxes ──
export const TRAD_STEP_WIDTH = 260;
export const PDD_STEP_WIDTH = 280;
export const STEP_HEIGHT = 40;
export const STEP_BORDER_RADIUS = 6;
export const STEP_FILL = '#1E1E2E';
export const STEP_TEXT_COLOR = '#CDD6F4';
export const STEP_TEXT_SIZE = 14;
export const STEP_FONT_WEIGHT = 400;
export const CODE_FONT_SIZE = 13;

// ── Arrows ──
export const ARROW_THICKNESS = 1.5;
export const ARROW_LENGTH = 28;

// ── Flowchart Layout ──
export const FLOWCHART_START_Y = 200;
export const STEP_VERTICAL_SPACING = 72; // step height + arrow + gap

// ── Animation Timing ──
export const FADE_IN_DURATION = 15;
export const ARROW_DRAW_DURATION = 10;

// Sequence frames (when each step appears)
export const HEADER_APPEAR = 0;
export const STEP1_APPEAR = 20;
export const STEP2_APPEAR = 50;
export const STEP3_APPEAR = 80;
export const STEP4_APPEAR = 110;
export const STEP5_APPEAR = 140;
export const STEP6_APPEAR = 155; // LEFT only — second part of frame 140-170
export const ELLIPSIS_APPEAR = 170;

// ── Step Data ──
export interface StepData {
  text: string;
  hasBandaid: boolean;
  hasCode: boolean;
  codeText?: string;
  isFinal: boolean;
  appearFrame: number;
}

export const TRADITIONAL_STEPS: StepData[] = [
  { text: 'Bug found', hasBandaid: false, hasCode: false, isFinal: false, appearFrame: STEP1_APPEAR },
  { text: 'Patch code', hasBandaid: true, hasCode: false, isFinal: false, appearFrame: STEP2_APPEAR },
  { text: 'Similar bug elsewhere', hasBandaid: false, hasCode: false, isFinal: false, appearFrame: STEP3_APPEAR },
  { text: 'Patch again', hasBandaid: true, hasCode: false, isFinal: false, appearFrame: STEP4_APPEAR },
  { text: 'Different bug', hasBandaid: false, hasCode: false, isFinal: false, appearFrame: STEP5_APPEAR },
  { text: 'Patch again...', hasBandaid: true, hasCode: false, isFinal: false, appearFrame: STEP6_APPEAR },
];

export const PDD_STEPS: StepData[] = [
  { text: 'Bug found', hasBandaid: false, hasCode: false, isFinal: false, appearFrame: STEP1_APPEAR },
  { text: 'Add test ', hasBandaid: false, hasCode: true, codeText: 'pdd bug', isFinal: false, appearFrame: STEP2_APPEAR },
  { text: 'Regenerate ', hasBandaid: false, hasCode: true, codeText: 'pdd fix', isFinal: false, appearFrame: STEP3_APPEAR },
  { text: 'Bug impossible forever ✓', hasBandaid: false, hasCode: false, isFinal: true, appearFrame: STEP4_APPEAR },
];

// ── Glow / Pulse ──
export const GLOW_BLUR = 8;
export const GLOW_CYCLE_FRAMES = 30;
export const ELLIPSIS_CYCLE_FRAMES = 20;
