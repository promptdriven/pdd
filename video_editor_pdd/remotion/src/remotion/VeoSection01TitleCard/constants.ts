// Component-level constants for VeoSection01TitleCard

export const CANVAS = {
  width: 1920,
  height: 1080,
};

export const COLORS = {
  gradientTop: '#0B1D3A',
  gradientBottom: '#162D50',
  titleText: '#FFFFFF',
  rule: '#5B9BD5',
  particle: '#FFFFFF',
};

export const TYPOGRAPHY = {
  title: {
    fontSize: 64,
    fontFamily: 'Inter',
    fontWeight: 'bold' as const,
  },
};

export const ANIMATION = {
  // Background gradient fades in from black
  backgroundFadeStart: 0,
  backgroundFadeEnd: 15,
  // Title text fades in and shifts up 10px
  titleFadeStart: 15,
  titleFadeEnd: 45,
  // Horizontal rule draws outward from center
  ruleFadeStart: 30,
  ruleFadeEnd: 60,
  // Particle drift runs full duration
  particleDurationFrames: 90,
  totalDuration: 90,
};

export const DIMENSIONS = {
  ruleWidth: 200,
  ruleHeight: 2,
  particleCount: 18,
  particleMinRadius: 2,
  particleMaxRadius: 4,
  particleOpacity: 0.15,
  titleRuleGap: 24,
};
