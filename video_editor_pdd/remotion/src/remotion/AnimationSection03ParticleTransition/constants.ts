// Component-level constants for AnimationSection03ParticleTransition

export const CANVAS = {
  width: 1920,
  height: 1080,
  centerX: 960,
  centerY: 540,
};

export const COLORS = {
  gradientTop: '#0A1628',
  gradientBottom: '#1E3A8A',
  targetBackground: '#FF0000',
  particleColor: '#3B82F6',
  flashColor: '#FFFFFF',
  vignetteColor: 'rgba(0,0,0,0.4)',
};

export const PARTICLES = {
  count: 60,
  minSize: 2,
  maxSize: 6,
  burstMinSpeed: 8,
  burstMaxSpeed: 15,
  trailCopies: 3,
  trailOpacities: [0.6, 0.3, 0.1],
};

export const TIMING = {
  // Phase 1: Gather toward center
  gatherStart: 0,
  gatherEnd: 10,
  // Phase 2: Hold + flash
  holdStart: 10,
  holdEnd: 15,
  // Phase 3: Radial explosion + background crossfade
  burstStart: 15,
  burstEnd: 35,
  // Phase 4: Trails fade, red settles
  fadeStart: 35,
  fadeEnd: 45,
  totalDuration: 45,
};

export const FLASH = {
  maxRadius: 20,
  startFrame: 10,
  peakFrame: 12,
  endFrame: 15,
};
