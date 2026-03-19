// constants.ts — Abstraction Staircase configuration

export const CANVAS_WIDTH = 1920;
export const CANVAS_HEIGHT = 1080;
export const TOTAL_FRAMES = 480;
export const FPS = 30;

export const COLORS = {
  background: '#0A0F1A',
  gridLine: '#1E293B',
  stepSurface: '#1E293B',
  stepStroke: '#334155',
  stepRiser: '#0F172A',
  arrowRed: '#EF4444',
  amber: '#D9944A',
  axisLabel: '#475569',
  decadeLabel: '#475569',
} as const;

export const OPACITIES = {
  grid: 0.03,
  stepSurface: 0.3,
  stepStroke: 0.4,
  riserStroke: 0.3,
  arrowBody: 0.3,
  arrowLabel: 0.4,
  tensionLines: 0.15,
  axisLabel: 0.2,
  decadeLabel: 0.3,
  iconDefault: 0.5,
  amberGlowBase: 0.08,
  amberGlowPeak: 0.15,
  amberLabel: 0.7,
  amberDecade: 0.4,
  amberIcon: 0.6,
} as const;

export interface StepData {
  level: number;
  label: string;
  decade: string;
  x: number;
  y: number;
  color: string;
  active?: boolean;
  iconType: 'transistor' | 'schematic' | 'rtl' | 'hls' | 'nlp';
}

export const STEP_WIDTH = 280;
export const STEP_HEIGHT = 120;
export const ACTIVE_COLOR = COLORS.amber;
export const PULSE_PERIOD = 40;

export const STEPS: StepData[] = [
  {
    level: 1,
    label: 'Transistors',
    decade: '1970s',
    x: 120,
    y: 800,
    color: '#64748B',
    iconType: 'transistor',
  },
  {
    level: 2,
    label: 'Schematics',
    decade: '1980s',
    x: 400,
    y: 680,
    color: '#7A8FA3',
    iconType: 'schematic',
  },
  {
    level: 3,
    label: 'RTL / Verilog',
    decade: '1990s',
    x: 680,
    y: 560,
    color: '#94A3B8',
    iconType: 'rtl',
  },
  {
    level: 4,
    label: 'Behavioral / HLS',
    decade: '2010s',
    x: 960,
    y: 440,
    color: '#B0BEC5',
    iconType: 'hls',
  },
  {
    level: 5,
    label: 'Natural Language → Code',
    decade: '2020s',
    x: 1240,
    y: 320,
    color: '#D9944A',
    active: true,
    iconType: 'nlp',
  },
];

// Animation frame ranges
export const ANIM = {
  gridFadeIn: { start: 0, duration: 30 },
  step1: { start: 30, duration: 60 },
  step2: { start: 90, duration: 50 },
  step3: { start: 140, duration: 50 },
  step4: { start: 190, duration: 50 },
  step5: { start: 240, duration: 80 },
  hold1: { start: 320, duration: 80 },
  hold2: { start: 400, duration: 80 },
} as const;

// Step timing: when each step starts drawing
export const STEP_START_FRAMES = [30, 90, 140, 190, 240];
// Arrow timing: each arrow starts a few frames before the step it leads to
export const ARROW_START_FRAMES = [80, 130, 180, 230];
