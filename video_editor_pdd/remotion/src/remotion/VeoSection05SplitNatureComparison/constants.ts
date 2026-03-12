// Component-level constants for VeoSection05SplitNatureComparison

export const CANVAS = {
  width: 1920,
  height: 1080,
};

export const COLORS = {
  background: '#0D1117',
  divider: '#5B9BD5',
  labelText: '#FFFFFF',
  vignette: 'rgba(0, 0, 0, 0.6)',
};

export const TYPOGRAPHY = {
  label: {
    fontSize: 24,
    fontFamily: 'Inter',
    fontWeight: 600 as const,
  },
};

export const ANIMATION = {
  // Divider draws top to bottom
  dividerDrawStart: 0,
  dividerDrawEnd: 20,
  // Left panel wipes in from center outward
  leftPanelWipeStart: 15,
  leftPanelWipeEnd: 45,
  // Right panel wipes in from center outward
  rightPanelWipeStart: 20,
  rightPanelWipeEnd: 50,
  // Labels fade in
  labelFadeStart: 50,
  labelFadeEnd: 70,
  // Total duration
  totalDuration: 120,
};

export const DIMENSIONS = {
  dividerWidth: 3,
  dividerX: 960,
  leftPanelEnd: 957,    // x=0 to 957
  rightPanelStart: 963, // x=963 to 1920
  labelY: 980,
  leftLabelX: 480,
  rightLabelX: 1440,
  vignetteWidth: 20,
  kenBurnsStart: 1.0,
  kenBurnsEnd: 1.05,
};
