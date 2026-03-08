// Component-level constants for VeoSection08VeoTechnologyCallout

export const CANVAS = {
  width: 1920,
  height: 1080,
};

export const COLORS = {
  background: '#0A1628',
  panelBg: 'rgba(8, 18, 35, 0.94)',
  panelBorder: 'rgba(59, 130, 246, 0.3)',
  panelGlow: 'rgba(59, 130, 246, 0.12)',
  accentBlue: '#3B82F6',
  accentCyan: '#06B6D4',
  accentGreen: '#22C55E',
  accentAmber: '#F59E0B',
  headingText: '#FFFFFF',
  labelText: '#94A3B8',
  valueText: '#F1F5F9',
  metricLabel: '#64748B',
  metricValue: '#E2E8F0',
  barTrack: 'rgba(59, 130, 246, 0.12)',
  barFill: '#3B82F6',
  barFillGreen: '#22C55E',
  barFillCyan: '#06B6D4',
  divider: 'rgba(148, 163, 184, 0.15)',
  dotActive: '#22C55E',
  dotPulse: 'rgba(34, 197, 94, 0.4)',
  gridLine: 'rgba(59, 130, 246, 0.06)',
};

export const TYPOGRAPHY = {
  heading: {
    fontSize: 20,
    fontFamily: 'Inter, sans-serif',
    fontWeight: 700 as const,
    letterSpacing: '2px',
  },
  metricLabel: {
    fontSize: 11,
    fontFamily: 'Inter, sans-serif',
    fontWeight: 500 as const,
    letterSpacing: '1.2px',
    textTransform: 'uppercase' as const,
  },
  metricValue: {
    fontSize: 28,
    fontFamily: 'Inter, sans-serif',
    fontWeight: 700 as const,
    letterSpacing: '-0.5px',
  },
  metricUnit: {
    fontSize: 14,
    fontFamily: 'Inter, sans-serif',
    fontWeight: 500 as const,
  },
  pipelineLabel: {
    fontSize: 12,
    fontFamily: 'Inter, sans-serif',
    fontWeight: 600 as const,
    letterSpacing: '0.8px',
  },
};

export const PANEL = {
  x: 80,
  y: 680,
  width: 1760,
  height: 340,
  borderRadius: 16,
  padding: 36,
};

export const ANIMATION = {
  // Panel reveal: slide up + fade in, frames 0-12
  panelRevealEnd: 12,
  panelSlideDistance: 50,

  // Heading: frames 0-10
  headingEnd: 10,

  // Metrics counter: frames 5-35, stagger 4 frames each
  metricsStart: 5,
  metricsStagger: 4,
  metricCountDuration: 20,

  // Pipeline bars: frames 15-50
  pipelineStart: 15,
  pipelineStagger: 5,
  pipelineGrowDuration: 18,

  // Waveform: continuous
  waveformSpeed: 0.12,

  // Fade out: frames 80-90
  fadeOutStart: 80,
  fadeOutEnd: 90,

  totalDuration: 90,
};

export const METRICS = [
  { label: 'RESOLUTION', value: 1080, unit: 'p', suffix: ' HD' },
  { label: 'FRAME RATE', value: 30, unit: 'fps', suffix: '' },
  { label: 'CLIP LENGTH', value: 8, unit: 's', suffix: ' avg' },
  { label: 'COHERENCE', value: 97, unit: '%', suffix: '' },
];

export const PIPELINE_STAGES = [
  { label: 'Scene Understanding', progress: 100, color: '#22C55E' },
  { label: 'Motion Synthesis', progress: 100, color: '#3B82F6' },
  { label: 'Temporal Coherence', progress: 97, color: '#06B6D4' },
  { label: 'Output Encoding', progress: 100, color: '#F59E0B' },
];

export const HEADING_TEXT = 'VEO RENDERING PIPELINE';
