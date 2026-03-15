// Component-level constants for AnimationSection06ParticleBurst
// Duration: 30 frames @ 30fps (~1.0s)

export const CANVAS = {
  width: 1920,
  height: 1080,
  centerX: 960,
  centerY: 540,
} as const;

export const COLORS = {
  background: '#020617',
  flash: '#FFFFFF',
  particles: ['#3B82F6', '#6366F1', '#8B5CF6', '#E2E8F0'] as readonly string[],
} as const;

export const FLASH = {
  maxRadius: 120,
  contractedRadius: 60,
  peakOpacity: 0.8,
} as const;

export const PARTICLES = {
  count: 40,
  minRadius: 3,
  maxRadius: 8,
  minSpeed: 200, // px/s
  maxSpeed: 600, // px/s
  maxDistance: 300,
  seed: 42,
  fadeStartRatio: 0.6, // begin fading at 60% of travel distance
} as const;

export const TIMING = {
  fps: 30,
  totalFrames: 30,
  // Flash expand: frames 0-3
  flashExpandEnd: 3,
  // Flash contract+fade: frames 3-6
  flashFadeEnd: 6,
  // Particles begin at frame 3
  particleStart: 3,
  // Particles travel: frames 3-22
  particleMoveEnd: 22,
  // Remaining particles fade: frames 22-30
  totalEnd: 30,
} as const;

export type ParticleData = {
  id: number;
  color: string;
  radius: number;
  angle: number; // radians
  speed: number; // px/s — larger particles move slightly slower
  maxDistance: number; // max travel distance from origin
};
