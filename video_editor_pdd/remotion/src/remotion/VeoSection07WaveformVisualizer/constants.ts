// Component-level constants for VeoSection07WaveformVisualizer

export const CANVAS = {
  width: 1920,
  height: 1080,
};

export const COLORS = {
  background: '#0A1628',
  backdropBg: 'rgba(15, 20, 25, 0.75)',
  backdropBorder: 'rgba(212, 165, 116, 0.2)',
  barBase: '#D4A574',
  barPeak: '#F59E0B',
  playhead: 'rgba(248, 250, 252, 0.8)',
  labelText: '#D4A574',
  timestampText: '#94A3B8',
};

export const POSITIONS = {
  containerCenterX: 960,
  containerCenterY: 280,
  labelX: 600,
  labelY: 230,
  timestampX: 1320,
  timestampY: 230,
};

export const DIMENSIONS = {
  containerWidth: 800,
  containerHeight: 120,
  backdropWidth: 860,
  backdropHeight: 150,
  backdropBorderRadius: 12,
  barCount: 64,
  barWidth: 6,
  barSpacing: 6.5,
  barMinHeight: 8,
  barMaxHeight: 100,
  barBorderRadius: 3,
  playheadWidth: 2,
};

export const TYPOGRAPHY = {
  label: {
    fontFamily: 'Inter, sans-serif',
    fontWeight: 600 as const,
    fontSize: 13,
    letterSpacing: '2.5px',
  },
  timestamp: {
    fontFamily: 'JetBrains Mono, monospace',
    fontWeight: 400 as const,
    fontSize: 13,
  },
};

export const ANIMATION = {
  // Phase 1: Backdrop fade in (frames 0-12)
  backdropFadeStart: 0,
  backdropFadeEnd: 12,
  // Phase 2: Bars grow (frames 8-20)
  barsGrowStart: 8,
  barsGrowEnd: 20,
  barsStaggerDelay: 2,
  barsGroupSize: 8,
  // Phase 3: Oscillation + playhead (frames 20-75)
  oscillationStart: 20,
  oscillationEnd: 75,
  playheadStart: 20,
  playheadEnd: 75,
  // Phase 4: Fade out (frames 75-90)
  fadeOutStart: 75,
  fadeOutEnd: 90,
  totalDuration: 90,
};

// 16 amplitude keyframes that get cycled/interpolated across 64 bars
export const AMPLITUDE_KEYFRAMES = [
  0.2, 0.4, 0.7, 0.9, 0.6, 0.3, 0.5, 0.8,
  0.95, 0.7, 0.4, 0.2, 0.6, 0.85, 0.5, 0.3,
];
