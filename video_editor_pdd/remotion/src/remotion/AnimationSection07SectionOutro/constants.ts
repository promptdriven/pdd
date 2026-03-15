// Component-level constants for AnimationSection07SectionOutro
// Duration: 45 frames @ 30fps (~1.5s)

export const CANVAS = {
  width: 1920,
  height: 1080,
} as const;

export const COLORS = {
  background: '#020617',
  fadeTarget: '#000000',
  checkmark: '#22C55E',
  glow: '#22C55E',
  text: '#FFFFFF',
} as const;

export const CHECKMARK = {
  cx: 960,
  cy: 500,
  strokeWidth: 6,
  /** Total path length for dashoffset animation */
  totalPathLength: 180,
  /** Short downstroke leg (45deg, ~40px) */
  shortLegLength: 60, // approximate SVG units for the short leg path segment
  /** Long upstroke leg (315deg, ~80px) */
  longLegLength: 120, // approximate SVG units for the long leg path segment
  /** SVG viewBox size */
  viewBoxSize: 100,
  /** Glow blur radius */
  glowBlur: 20,
  /** Glow opacity */
  glowOpacity: 0.2,
} as const;

/**
 * Checkmark SVG path: short downstroke then long upstroke.
 * Coordinates within a 100x100 viewBox, centered roughly at (50,50).
 * Short leg: from (25,45) to (42,62) — 45deg downstroke, ~24 SVG units
 * Long leg: from (42,62) to (75,28) — 315deg upstroke, ~46 SVG units
 * Total stroke ~ 70 SVG units, but we use pathLength attribute = 180 for animation.
 */
export const CHECKMARK_PATH = 'M 25 45 L 42 62 L 75 28';

export const TEXT = {
  content: 'Section Complete',
  y: 600,
  fontSize: 32,
  fontWeight: 500 as const,
  fontFamily: "'Inter', sans-serif",
  maxOpacity: 0.9,
  scaleFrom: 0.95,
  scaleTo: 1.0,
} as const;

export const TIMING = {
  fps: 30,
  totalFrames: 45,
  // Checkmark stroke draw: frames 0-18
  checkmarkStart: 0,
  checkmarkEnd: 18,
  // Short leg draws: frames 0-7
  shortLegEnd: 7,
  // Long leg draws: frames 7-18
  longLegStart: 7,
  // Text fade-in: frames 18-28
  textStart: 18,
  textEnd: 28,
  // Fade to black: frames 28-45
  fadeStart: 28,
  fadeEnd: 45,
} as const;
