// Component-level constants for AnimationSection05AnimationShowcase

export const CANVAS = {
  width: 1920,
  height: 1080,
};

export const COLORS = {
  background: '#0F172A',
};

export const GRID = {
  rows: 3,
  cols: 4,
  cellSize: 160,
  gap: 40,
};

export type ShapeType = 'circle' | 'square' | 'triangle';

export interface ShapeData {
  type: ShapeType;
  color: string;
  size: number;
}

export const SHAPES: ShapeData[] = [
  // Row 1
  { type: 'circle', color: '#38BDF8', size: 64 },
  { type: 'square', color: '#22C55E', size: 56 },
  { type: 'triangle', color: '#A78BFA', size: 64 },
  { type: 'circle', color: '#F472B6', size: 64 },
  // Row 2
  { type: 'square', color: '#FACC15', size: 56 },
  { type: 'triangle', color: '#38BDF8', size: 64 },
  { type: 'circle', color: '#22C55E', size: 64 },
  { type: 'square', color: '#A78BFA', size: 56 },
  // Row 3
  { type: 'triangle', color: '#F472B6', size: 64 },
  { type: 'circle', color: '#FACC15', size: 64 },
  { type: 'square', color: '#38BDF8', size: 56 },
  { type: 'triangle', color: '#22C55E', size: 64 },
];

export const ANIMATION = {
  // Frame 0-45: shapes drop in with staggered 3-frame delay
  dropPhaseEnd: 45,
  staggerDelay: 3,
  dropDistance: 100,

  // Frame 45-55: hold
  holdStart: 45,
  holdEnd: 55,

  // Frame 55-65: synchronized pulse
  pulseStart: 55,
  pulseEnd: 65,
  pulseScale: 1.15,
  hueShift: 30,

  // Frame 65-75: idle breathing
  breatheStart: 65,
  breatheEnd: 75,
  breatheScale: 1.02,

  totalDuration: 75,
};

export const SHADOW = '0 8px 24px rgba(0, 0, 0, 0.3)';
