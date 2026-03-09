// Component-level constants for VeoSection09WaveformVisualizer
// Audio waveform visualizer with gradient bars and timeline scrubber

export const CANVAS = {
  width: 1920,
  height: 1080,
};

export const COLORS = {
  background: '#121212',
  gradientStart: '#F59E0B', // amber (left)
  gradientEnd: '#34D399', // emerald (right)
  scrubber: 'rgba(255, 255, 255, 0.6)',
  labelText: 'rgba(255, 255, 255, 0.5)',
  timestampText: 'rgba(255, 255, 255, 0.7)',
  noiseOverlay: 'rgba(255, 255, 255, 0.02)',
};

export const TYPOGRAPHY = {
  sectionLabel: {
    fontFamily: 'Inter, sans-serif',
    fontWeight: 500 as const,
    fontSize: 14,
    letterSpacing: '3px',
  },
  timestamp: {
    fontFamily: 'JetBrains Mono, monospace',
    fontWeight: 400 as const,
    fontSize: 18,
  },
};

export const WAVEFORM = {
  barCount: 64,
  barWidth: 8,
  barGap: 4,
  baselineY: 900,
  maxHeight: 200,
  minHeight: 20,
  borderRadius: 4,
  // Total waveform width: 64 * (8 + 4) - 4 = 764px
  totalWidth: 64 * (8 + 4) - 4, // 764
};

export const POSITIONS = {
  // Center waveform horizontally: (1920 - 764) / 2 = 578
  waveformStartX: Math.round((1920 - (64 * (8 + 4) - 4)) / 2),
  labelY: 680,
  timestampX: 1800,
  timestampY: 40,
};

export const ANIMATION = {
  // Phase 1: bars grow in (0-15)
  growStart: 0,
  growEnd: 15,
  staggerPerBar: 1, // 1-frame stagger per bar

  // Phase 2: oscillation (15-75)
  oscillateStart: 15,
  oscillateEnd: 75,
  oscillationMinFactor: 0.4, // 40% of max height
  oscillationMaxFactor: 1.0, // 100% of max height

  // Phase 3: bars shrink out (75-90)
  shrinkStart: 75,
  shrinkEnd: 90,

  // Label/timestamp
  labelFadeInEnd: 15,
  labelFadeOutStart: 75,

  totalDuration: 90, // 3s at 30fps
};
