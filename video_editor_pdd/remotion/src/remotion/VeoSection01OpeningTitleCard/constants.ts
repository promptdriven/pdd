/**
 * VeoSection01OpeningTitleCard Component Constants
 *
 * Colors, dimensions, and timing values for the opening title card animation
 */

export const COLORS = {
  background: {
    top: '#0A0E27',
    bottom: '#1A1F3A',
  },
  accent: '#00D9FF',
  title: '#FFFFFF',
  particle: '#FFFFFF',
} as const;

export const DIMENSIONS = {
  canvas: {
    width: 1920,
    height: 1080,
  },
  title: {
    fontSize: 120,
    letterSpacing: '0.05em',
  },
  underline: {
    width: 400,
    height: 4,
  },
  particle: {
    minSize: 2,
    maxSize: 4,
    count: 50,
  },
} as const;

export const TIMING = {
  titleFadeIn: 20,
  underlineDraw: 20,
  hold: 50,
  totalDuration: 90,
} as const;

export const ANIMATION = {
  titleSpring: {
    damping: 20,
    stiffness: 100,
  },
} as const;
