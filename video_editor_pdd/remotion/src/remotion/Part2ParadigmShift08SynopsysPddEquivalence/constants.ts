// === Colors ===
export const BG_COLOR = '#0A0F1A';
export const SYNOPSYS_COLOR = '#4A90D9';
export const PDD_COLOR = '#D9944A';
export const NEUTRAL_COLOR = '#94A3B8';
export const VERIFIED_COLOR = '#5AAA6E';
export const ARROW_COLOR = '#475569';
export const TEXT_COLOR = '#E2E8F0';
export const CONNECTION_COLOR = '#475569';

// === Layout ===
export const WIDTH = 1920;
export const HEIGHT = 1080;

export const SYNOPSYS_Y = 280;
export const PDD_Y = 680;
export const EQUIVALENCE_Y = 480;

export const STAGE_X_POSITIONS = [260, 560, 860, 1160] as const;

// === Stage Data ===
export interface StageData {
  name: string;
  icon: 'document_code' | 'gear' | 'gate_cluster' | 'shield_check' | 'document_text' | 'neural_network' | 'code_brackets';
  x: number;
  color: string;
}

export const SYNOPSYS_STAGES: StageData[] = [
  { name: 'Verilog spec', icon: 'document_code', x: 260, color: SYNOPSYS_COLOR },
  { name: 'Synthesis', icon: 'gear', x: 560, color: SYNOPSYS_COLOR },
  { name: 'Hardware', icon: 'gate_cluster', x: 860, color: NEUTRAL_COLOR },
  { name: 'FEC verified', icon: 'shield_check', x: 1160, color: VERIFIED_COLOR },
];

export const PDD_STAGES: StageData[] = [
  { name: 'Prompt spec', icon: 'document_text', x: 260, color: PDD_COLOR },
  { name: 'Generation', icon: 'neural_network', x: 560, color: PDD_COLOR },
  { name: 'Software', icon: 'code_brackets', x: 860, color: NEUTRAL_COLOR },
  { name: 'Tests pass', icon: 'shield_check', x: 1160, color: VERIFIED_COLOR },
];

// === Animation Timing (frames) ===
export const TIMING = {
  // Phase 1: Labels fade in
  LABELS_START: 0,
  LABELS_FADE: 20,

  // Phase 2: Top row builds
  TOP_ROW_START: 30,
  STAGE_FADE: 15,
  STAGE_STAGGER: 15,
  ARROW_DRAW: 10,

  // Phase 3: Bottom row builds
  BOTTOM_ROW_START: 100,

  // Phase 4: Vertical connections
  CONNECTIONS_START: 170,
  CONNECTION_DRAW: 20,
  CONNECTION_STAGGER: 10,

  // Phase 5: Equivalence symbol
  EQUIV_START: 220,
  EQUIV_FADE: 20,
  EQUIV_PULSE_PERIOD: 40,

  // Phase 6: Summary
  SUMMARY_START: 260,
  SUMMARY_FADE: 20,

  // Total
  TOTAL: 360,
} as const;
