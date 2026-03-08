// Component-level constants for AnimationSection06SplitSummary

export const CANVAS = {
  width: 1920,
  height: 1080,
};

export const COLORS = {
  background: '#0F172A',
  leftPanel: '#1E293B',
  rightPanel: '#0F4C81',
  divider: '#3B82F6',
  text: '#E2E8F0',
  dividerGlow: 'rgba(59, 130, 246, 0.4)',
};

export const TYPOGRAPHY = {
  heading: {
    fontSize: 54,
    fontFamily: 'Inter, sans-serif',
    fontWeight: 700 as const,
  },
  panelLabel: {
    fontSize: 46,
    fontFamily: 'Inter, sans-serif',
    fontWeight: 700 as const,
  },
};

export const DIVIDER = {
  startX: 640,
  endX: 720,
  width: 6,
  glowBlur: 20,
};

export const TIMING = {
  // Panel fade-in
  panelFadeStart: 0,
  panelFadeEnd: 15,
  // "Before" text fade-in
  beforeTextStart: 15,
  beforeTextEnd: 30,
  // "After" text fade-in
  afterTextStart: 20,
  afterTextEnd: 35,
  // Divider slide (full duration)
  dividerSlideStart: 0,
  dividerSlideEnd: 90,
  // Glow pulse
  glowPulseStart: 60,
  glowPulseMid: 75,
  glowPulseEnd: 90,
  // Total
  totalDuration: 90,
};
