// Component-level constants for AnimationSection07SectionOutro

export const CANVAS = {
  width: 1280,
  height: 720,
};

export const COLORS = {
  background: '#0B1120',
  divider: '#FFFFFF',
  checkmark: '#22C55E',
  labelText: '#FFFFFF',
  fadeToBlack: '#000000',
};

export const TYPOGRAPHY = {
  label: {
    fontSize: 20,
    fontFamily: 'Inter',
    fontWeight: 400 as const,
  },
};

export const DIMENSIONS = {
  dividerWidth: 200,
  dividerHeight: 2,
  dividerOpacity: 0.4,
  checkmarkSize: 40,
  checkmarkStrokeWidth: 3,
};

export const ANIMATION_TIMING = {
  // Frame 0-15: Line visible then contracts to center
  lineContractStart: 0,
  lineContractEnd: 15,
  // Frame 15-35: Checkmark draws in
  checkmarkDrawStart: 15,
  checkmarkDrawEnd: 35,
  // Frame 35-45: "Complete" text fades in
  textFadeStart: 35,
  textFadeEnd: 45,
  // Frame 55-60: Fade to black
  fadeToBlackStart: 55,
  fadeToBlackEnd: 60,
  // Total duration
  totalDuration: 60,
};

export const LABEL_TEXT = 'Complete';
