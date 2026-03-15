// Component-level constants for VeoSection01TitleCard
// Duration: ~1.7s (51 frames @ 30fps)

export const COLORS = {
  background: '#0B1120',
  titleText: '#FFFFFF',
  titleShadow: 'rgba(201, 168, 76, 0.3)',
  rule: '#C9A84C',
  subtitleText: '#FFFFFFCC',
};

export const TYPOGRAPHY = {
  title: {
    fontSize: 72,
    fontFamily: "'Inter', sans-serif",
    fontWeight: 700 as const,
  },
  subtitle: {
    fontSize: 28,
    fontFamily: "'Inter', sans-serif",
    fontWeight: 400 as const,
  },
};

export const ANIMATION = {
  // Frame 0–10: Title fades in with slide-up
  titleFadeStart: 0,
  titleFadeEnd: 10,
  titleShiftPx: 20,
  // Frame 10–18: Rule expands from center
  ruleExpandStart: 10,
  ruleExpandEnd: 18,
  // Frame 18–26: Subtitle fades in with slide-up
  subtitleFadeStart: 18,
  subtitleFadeEnd: 26,
  subtitleShiftPx: 12,
  // Frame 26–51: Hold + glow pulse on rule
  glowPulseStart: 26,
  totalDuration: 51,
};

export const DIMENSIONS = {
  ruleMaxWidth: 320,
  ruleHeight: 2,
  // Title at 40% from top
  titleTopPercent: 0.4,
  // Rule 20px below title
  ruleGap: 20,
  // Subtitle 30px below rule
  subtitleGap: 30,
};
