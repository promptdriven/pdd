// Component-level constants for AnimationSection06ParticleBurst

export const CANVAS = {
  width: 1280,
  height: 720,
};

export const COLORS = {
  backgroundStart: '#141921',
  backgroundEnd: '#0B1120',
  blue: '#3B82F6',
  green: '#22C55E',
  flash: '#FFFFFF',
};

export const PARTICLE_CONFIG = {
  totalCount: 40,
  blueCount: 20,
  greenCount: 20,
  blueSizeRange: [6, 12] as [number, number],
  greenSizeRange: [6, 10] as [number, number],
  speedRange: [200, 600] as [number, number],
  origin: { x: 640, y: 360 },
};

export const FLASH_CONFIG = {
  size: 30,
  opacity: 0.8,
  durationFrames: 3,
};

export const TIMING = {
  fps: 30,
  totalFrames: 60,
  // Flash: frames 0-3
  flashEnd: 3,
  // Particles travel: frames 3-50
  particleSpawnFrame: 0,
  particleFadeStart: 15,
  particleFadeEnd: 50,
  // Background transition: frames 30-50
  bgTransitionStart: 30,
  bgTransitionEnd: 50,
};

export type ParticleData = {
  id: number;
  shape: 'circle' | 'square';
  color: string;
  size: number;
  angle: number;
  speed: number;
  rotationSpeed: number;
};
