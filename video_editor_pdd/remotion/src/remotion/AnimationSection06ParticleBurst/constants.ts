// Component-level constants for AnimationSection06ParticleBurst
// Duration: 22 frames @ 30fps (~0.75s)

export const CANVAS = {
  width: 1280,
  height: 720,
  centerX: 640,
  centerY: 360,
} as const;

export const COLORS = {
  bgFrom: '#141921',
  bgTo: '#0B1120',
  flash: '#FFFFFF',
  blueParticle: '#3B82F6',
  greenParticle: '#22C55E',
} as const;

// RGB values for background interpolation
// #141921 = rgb(20, 25, 33)
// #0B1120 = rgb(11, 17, 32)
export const BG_RGB = {
  from: { r: 20, g: 25, b: 33 },
  to: { r: 11, g: 17, b: 32 },
} as const;

export const FLASH = {
  diameter: 30,
  peakOpacity: 0.8,
} as const;

export const PARTICLES = {
  blueCount: 20,
  greenCount: 20,
  blueSizeRange: [6, 12] as readonly [number, number],
  greenSizeRange: [6, 10] as readonly [number, number],
  greenBorderRadius: 1,
  speedRange: [200, 600] as readonly [number, number],
  rotationSpeedRange: [-8, 8] as readonly [number, number],
} as const;

export const TIMING = {
  fps: 30,
  totalFrames: 22,
  // Flash scale: frames 0-2
  flashScaleStart: 0,
  flashScaleEnd: 2,
  // Flash fade: frames 2-3
  flashFadeStart: 2,
  flashFadeEnd: 3,
  // Particles begin outward travel at frame 2
  particleStartFrame: 2,
  // Particle fade: frames 5-16
  particleFadeStart: 5,
  particleFadeEnd: 16,
  // Background transition: frames 10-18
  bgTransitionStart: 10,
  bgTransitionEnd: 18,
} as const;

export type ParticleData = {
  id: number;
  shape: 'circle' | 'square';
  color: string;
  size: number;
  angle: number;
  speed: number;
  rotationSpeed: number;
};
