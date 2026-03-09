// Component-level constants for VeoSection11VeoBadgeReprise
// Full branded Veo lockup with particle ring — dimmed forest canopy background

export const CANVAS = {
  width: 1920,
  height: 1080,
};

export const COLORS = {
  background: '#0A1628',
  dimmingOverlay: 'rgba(0, 0, 0, 0.7)',
  wordmark: '#FFFFFF',
  accent: '#F59E0B',
  particleColor: '#F59E0B',
  particleOpacity: 0.4,
};

export const TYPOGRAPHY = {
  wordmark: {
    fontSize: 96,
    fontFamily: 'Inter',
    fontWeight: 900 as const,
    letterSpacing: '4px',
  },
  tagline: {
    fontSize: 24,
    fontFamily: 'Inter',
    fontWeight: 300 as const,
    letterSpacing: '2px',
  },
};

export const POSITIONS = {
  wordmarkY: 480,
  taglineStartY: 580,
  taglineEndY: 560,
  accentLineY: 600,
  center: 960,
};

export const DIMENSIONS = {
  accentLineWidth: 120,
  accentLineHeight: 2,
  particleCount: 24,
  particleRadius: 200,
  particleMinSize: 3,
  particleMaxSize: 5,
};

export const ANIMATION = {
  // Dimming overlay: frames 0-10
  dimFadeStart: 0,
  dimFadeEnd: 10,

  // Wordmark scale in: frames 10-30
  wordmarkStart: 10,
  wordmarkEnd: 30,
  wordmarkScaleFrom: 0.5,
  wordmarkScaleTo: 1.0,

  // Tagline fade/slide: frames 25-40
  taglineStart: 25,
  taglineEnd: 40,

  // Accent line expand: frames 35-45
  accentLineStart: 35,
  accentLineEnd: 45,

  // Particle ring: frames 30-75
  particleStart: 30,
  particleFadeEnd: 45,
  particleHoldEnd: 75,
  particleOrbitFrames: 90,
  particleOscillationAmplitude: 8,

  // Fade out: frames 75-90
  fadeOutStart: 75,
  fadeOutEnd: 90,

  totalDuration: 90,
};

export const WORDMARK_TEXT = 'Veo';
export const TAGLINE_TEXT = 'AI-Generated Video';
