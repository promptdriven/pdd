// Component-level constants for VeoSection06VeoTechnologyCallout

export const CANVAS = {
  width: 1920,
  height: 1080,
};

export const COLORS = {
  background: '#0A1628',
  cardBg: 'rgba(10, 22, 40, 0.92)',
  cardBorder: 'rgba(59, 130, 246, 0.35)',
  cardGlow: 'rgba(59, 130, 246, 0.15)',
  accentBlue: '#3B82F6',
  accentCyan: '#06B6D4',
  accentGreen: '#22C55E',
  headingText: '#FFFFFF',
  labelText: '#94A3B8',
  valueText: '#F1F5F9',
  tagBg: 'rgba(59, 130, 246, 0.15)',
  tagBorder: 'rgba(59, 130, 246, 0.4)',
  tagText: '#60A5FA',
  divider: 'rgba(148, 163, 184, 0.2)',
  dotActive: '#22C55E',
  dotPulse: 'rgba(34, 197, 94, 0.4)',
  scanline: 'rgba(59, 130, 246, 0.08)',
};

export const TYPOGRAPHY = {
  heading: {
    fontSize: 28,
    fontFamily: 'Inter, sans-serif',
    fontWeight: 700 as const,
    letterSpacing: '1.5px',
  },
  label: {
    fontSize: 14,
    fontFamily: 'Inter, sans-serif',
    fontWeight: 500 as const,
    letterSpacing: '1px',
    textTransform: 'uppercase' as const,
  },
  value: {
    fontSize: 22,
    fontFamily: 'Inter, sans-serif',
    fontWeight: 600 as const,
    letterSpacing: '0.3px',
  },
  tag: {
    fontSize: 13,
    fontFamily: 'Inter, sans-serif',
    fontWeight: 600 as const,
    letterSpacing: '0.5px',
  },
};

export const CARD = {
  x: 100,
  y: 160,
  width: 520,
  height: 760,
  borderRadius: 16,
  padding: 40,
};

export const ANIMATION = {
  // Card reveal: frames 0-15
  cardRevealEnd: 15,
  cardSlideDistance: 60,

  // Heading appear: frames 5-18
  headingStart: 5,
  headingEnd: 18,

  // Specs stagger: frames 12-45, each row delayed by 6 frames
  specsStart: 12,
  specsStagger: 6,
  specSlideDist: 30,

  // Tags appear: frames 35-55
  tagsStart: 35,
  tagsStagger: 4,

  // Scanline sweep: continuous loop every 90 frames
  scanlinePeriod: 90,

  // Status dot pulse: continuous
  dotPulsePeriod: 40,

  // Fade out: frames 80-90
  fadeOutStart: 80,
  fadeOutEnd: 90,

  totalDuration: 90,
};

export const TECH_SPECS = [
  { label: 'MODEL', value: 'Veo 2' },
  { label: 'RESOLUTION', value: '1080p · 30 fps' },
  { label: 'DURATION', value: '5–8 sec clips' },
  { label: 'STYLE', value: 'Cinematic realism' },
];

export const TECH_TAGS = [
  'AI-Generated',
  'Temporal Coherence',
  'Scene Understanding',
  'Motion Synthesis',
];

export const HEADING_TEXT = 'VEO TECHNOLOGY';
