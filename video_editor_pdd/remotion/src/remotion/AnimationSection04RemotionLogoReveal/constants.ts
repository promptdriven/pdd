// Component-level constants for AnimationSection04RemotionLogoReveal

export const CANVAS = {
  width: 1920,
  height: 1080,
};

export const COLORS = {
  background: '#0A1628',
  logoBlue: '#3B82F6',
  logoGreen: '#22C55E',
  accentCyan: '#06B6D4',
  white: '#FFFFFF',
  subtitleGray: '#94A3B8',
  glowBlue: 'rgba(59, 130, 246, 0.4)',
  glowGreen: 'rgba(34, 197, 94, 0.3)',
};

export const LOGO = {
  // Triangle dimensions (Remotion-inspired play-button triangle)
  triangleSize: 260,
  cx: 960,
  cy: 480,
  // Inner border ring
  ringRadius: 200,
  ringStroke: 4,
};

export const TIMING = {
  // Ring draws in: frames 0–25
  ringStart: 0,
  ringEnd: 25,
  // Triangle scales up: frames 10–30
  triangleStart: 10,
  triangleEnd: 30,
  // Glow pulse: frames 25–50
  glowStart: 25,
  glowPeak: 37,
  glowEnd: 50,
  // Title text fades in: frames 30–45
  titleStart: 30,
  titleEnd: 45,
  // Subtitle slides up: frames 40–55
  subtitleStart: 40,
  subtitleEnd: 55,
  // Hold: frames 55–75
  totalDuration: 75,
};

export const TEXT = {
  title: 'Remotion',
  subtitle: 'Programmatic Video',
  titleSize: 72,
  subtitleSize: 28,
  titleY: 660,
  subtitleY: 740,
};
