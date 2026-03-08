export const COLORS = {
  background: '#ffffff',
  headline: '#0f172a', // slate-900
  subtitle: '#64748b', // slate-500
  emphasis: '#3b82f6', // blue-500
  cursor: '#3b82f6', // blue-500
  separator: '#cbd5e1', // slate-300
} as const;

export const TYPOGRAPHY = {
  headline: {
    fontSize: 72,
    fontWeight: 900, // Black
    letterSpacing: '-0.02em',
  },
  subtitle: {
    fontSize: 32,
    fontWeight: 400, // Regular
    letterSpacing: '0.02em',
  },
  emphasis: {
    fontSize: 24,
    fontWeight: 700, // Bold
    letterSpacing: '0.15em',
    textTransform: 'uppercase' as const,
  },
} as const;

export const LAYOUT = {
  canvas: {
    width: 1920,
    height: 1080,
  },
  headline: {
    x: 960,
    y: 380,
  },
  subtitle: {
    x: 960,
    y: 500,
  },
  emphasis: {
    x: 960,
    y: 620,
  },
  cursor: {
    width: 3,
    height: 72,
  },
} as const;

export const ANIMATION = {
  typewriter: {
    startFrame: 0,
    endFrame: 45,
    framesPerChar: 2,
    blinkInterval: 15, // frames
    postTypeBlinkDuration: 5, // frames
  },
  subtitle: {
    startFrame: 50,
    endFrame: 65,
    fadeDuration: 5,
    wordStagger: 6,
  },
  wave: {
    startFrame: 70,
    endFrame: 90,
    durationPerChar: 10,
    stagger: 2,
    verticalShift: 8, // pixels
    scaleMin: 0.8,
    scaleMax: 1.2,
  },
} as const;

export const TEXT_CONTENT = {
  headline: 'Remotion Animations',
  subtitle: ['Powerful', 'Flexible', 'Programmatic'],
  separator: '·',
  emphasis: 'INTEGRATION TEST',
} as const;
