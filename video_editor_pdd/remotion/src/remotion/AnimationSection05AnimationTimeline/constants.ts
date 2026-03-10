// Component-level constants for AnimationSection05AnimationTimeline

export const CANVAS = {
  width: 1920,
  height: 1080,
};

export const COLORS = {
  background: '#090E1A',
  trackStroke: '#334155',
  tickStroke: '#475569',
  labelText: '#CBD5E1',
  playhead: '#FFFFFF',
  milestoneViolet: '#A78BFA',
  milestoneBlue: '#3B82F6',
  milestoneAmber: '#F59E0B',
  milestoneGreen: '#22C55E',
  milestonePink: '#EC4899',
};

export const TRACK = {
  startX: 160,
  endX: 1760,
  y: 540,
  strokeWidth: 2,
};

export const MILESTONES = [
  { x: 260, color: COLORS.milestoneViolet, label: 'Title Card' },
  { x: 560, color: COLORS.milestoneBlue, label: 'Circle Pulse' },
  { x: 860, color: COLORS.milestoneAmber, label: 'Bunny' },
  { x: 1160, color: COLORS.milestoneGreen, label: 'Slide Right' },
  { x: 1460, color: COLORS.milestonePink, label: 'Showcase' },
] as const;

export const DIMENSIONS = {
  dotRadius: 6,
  dotDiameter: 12,
  tickHeight: 24,
  tickWidth: 1,
  playheadRadius: 8,
  playheadGlowSize: 20,
};

export const TYPOGRAPHY = {
  label: {
    fontSize: 18,
    fontFamily: 'Inter, sans-serif',
    fontWeight: 400 as const,
  },
};

export const ANIMATION_TIMING = {
  // Frame 0-20: Track draws in from left to right
  trackDrawStart: 0,
  trackDrawEnd: 20,
  // Frame 20-40: Milestone dots pop in sequentially (staggered by 4 frames)
  milestonePopStart: 20,
  milestoneStagger: 4,
  // Frame 40-120: Playhead sweeps left to right
  playheadStart: 40,
  playheadEnd: 120,
  // Milestone highlight: 6-frame pulse when playhead passes
  milestoneHighlightDuration: 6,
  // Frame 120-150: Playhead fades, shimmer on track
  fadeoutStart: 120,
  fadeoutEnd: 150,
  // Total duration
  totalDuration: 150,
};
