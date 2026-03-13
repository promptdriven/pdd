// Component-level constants for AnimationSection07SectionOutro
// Duration: 22 frames @ 30fps (~0.73s)

export const CANVAS = {
  width: 1280,
  height: 720,
} as const;

export const COLORS = {
  background: '#0B1120',
  divider: 'rgba(255,255,255,0.4)',
  checkmark: '#22C55E',
  labelText: '#FFFFFF',
  fadeToBlack: '#000000',
} as const;

export const TYPOGRAPHY = {
  label: {
    fontSize: 20,
    fontFamily: "'Inter', sans-serif",
    fontWeight: 400 as const,
    letterSpacing: '1px',
  },
} as const;

export const DIMENSIONS = {
  dividerStartWidth: 300,
  dividerEndWidth: 80,
  dividerHeight: 2,
  dividerY: 330,
  checkmarkSize: 40,
  checkmarkStrokeWidth: 3,
  checkmarkCenterY: 340,
  labelY: 400,
} as const;

export const ANIMATION_TIMING = {
  // Frame 0-5: Divider contracts from 300px to 80px centered
  dividerContractStart: 0,
  dividerContractEnd: 5,
  // Frame 5-12: Checkmark stroke draws in
  checkmarkDrawStart: 5,
  checkmarkDrawEnd: 12,
  // Frame 12-16: "Complete" text fades in with subtle translateY
  textFadeStart: 12,
  textFadeEnd: 16,
  // Frame 16-19: Hold
  // Frame 19-22: Fade to black
  fadeToBlackStart: 19,
  fadeToBlackEnd: 22,
  totalDuration: 22,
} as const;

export const LABEL_TEXT = 'Complete';
