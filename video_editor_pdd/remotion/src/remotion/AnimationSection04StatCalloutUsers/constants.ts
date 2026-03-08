/**
 * Constants for AnimationSection04StatCalloutUsers
 * User growth statistic callout with animated counter and progress ring
 */

export const CANVAS = {
  WIDTH: 1920,
  HEIGHT: 1080,
} as const;

export const COLORS = {
  BACKGROUND_CENTER: '#1E293B',
  BACKGROUND_EDGE: '#0F172A',
  GLOW: '#3B82F6',
  ICON: '#60A5FA',
  PREFIX: '#94A3B8',
  COUNTER: '#F1F5F9',
  SUFFIX: '#CBD5E1',
  PROGRESS_RING: '#3B82F6',
  PARTICLE: '#60A5FA',
} as const;

export const TYPOGRAPHY = {
  PREFIX: {
    FAMILY: 'Inter',
    SIZE: 36,
    WEIGHT: 400,
  },
  COUNTER: {
    FAMILY: 'Inter',
    SIZE: 128,
    WEIGHT: 900,
  },
  SUFFIX: {
    FAMILY: 'Inter',
    SIZE: 40,
    WEIGHT: 500,
  },
} as const;

export const POSITIONS = {
  ICON: { X: 960, Y: 300 },
  PREFIX: { X: 960, Y: 380 },
  COUNTER: { X: 960, Y: 480 },
  SUFFIX: { X: 960, Y: 600 },
  GLOW: { X: 960, Y: 480 },
} as const;

export const DIMENSIONS = {
  ICON_SIZE: 120,
  PROGRESS_RING_DIAMETER: 320,
  PROGRESS_RING_STROKE: 12,
  GLOW_WIDTH: 600,
  GLOW_HEIGHT: 400,
} as const;

export const ANIMATION = {
  TARGET_VALUE: 1250000,
  TOTAL_FRAMES: 90,
  FPS: 30,
  ICON_START: 10,
  ICON_DURATION: 15,
  PREFIX_START: 25,
  PREFIX_DURATION: 15,
  COUNTER_START: 30,
  COUNTER_DURATION: 45,
  SUFFIX_START: 50,
  SUFFIX_DURATION: 20,
  PULSE_START: 75,
  PULSE_DURATION: 15,
  PARTICLE_COUNT: 30,
} as const;
