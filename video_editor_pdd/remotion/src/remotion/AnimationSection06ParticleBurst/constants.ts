// Component-level constants for AnimationSection06ParticleBurst
// Duration: 30 frames @ 30fps (~1.0s)

export const CANVAS = {
  width: 1920,
  height: 1080,
  centerX: 960,
  centerY: 540,
} as const;

export const COLORS = {
  background: '#1E293B',
  flash: '#FFFFFF',
  particles: ['#3B82F6', '#6366F1', '#8B5CF6', '#FFFFFF'] as readonly string[],
} as const;

export const FLASH = {
  peakOpacity: 0.15,
} as const;

export const PARTICLES = {
  count: 40,
  minRadius: 4,
  maxRadius: 8,
  minDistance: 150,
  maxDistance: 500,
  angleJitter: 5, // degrees of random jitter
  seed: 42,
} as const;

export const TIMING = {
  fps: 30,
  totalFrames: 30,
  // Flash: frames 0-2
  flashStart: 0,
  flashEnd: 2,
  // Particles spawn at frame 2
  particleStart: 2,
  // Particles travel and decelerate: frames 2-24
  particleMoveEnd: 24,
  // Particles fully faded by frame 24
  particleFadeEnd: 24,
  // Final fade-out: frames 24-30
  totalEnd: 30,
} as const;

export type ParticleData = {
  id: number;
  color: string;
  radius: number;
  angle: number; // radians
  distance: number; // max travel distance from origin
};
