// Component-level constants for VeoSection14SectionOutro

export const CANVAS = {
  width: 1920,
  height: 1080,
};

export const COLORS = {
  background: '#0F0F0F',
  accent: '#F59E0B',
  borderFrame: 'rgba(245, 158, 11, 0.5)',
  horizontalRule: 'rgba(245, 158, 11, 0.6)',
  titleText: 'rgba(255, 255, 255, 0.9)',
  diamond: '#F59E0B',
  black: '#000000',
};

export const TYPOGRAPHY = {
  title: {
    fontSize: 48,
    fontFamily: 'Inter',
    fontWeight: 700 as const,
    letterSpacing: '6px',
    textTransform: 'uppercase' as const,
  },
};

export const POSITIONS = {
  borderMargin: 40,
  ruleY: 480,
  titleCenterY: 540,
  diamondY: 590,
};

export const DIMENSIONS = {
  ruleWidth: 300,
  ruleHeight: 2,
  borderStroke: 2,
  diamondSize: 8,
  // Border frame inner coordinates
  borderLeft: 40,
  borderTop: 40,
  borderRight: 1880,
  borderBottom: 1040,
};

export const ANIMATION_TIMING = {
  // Background fade-in: frames 0-15
  bgFadeStart: 0,
  bgFadeEnd: 15,
  // Border trace: frames 10-40 (clockwise, 4 segments of ~7 frames each)
  borderStart: 10,
  borderTopEnd: 17,
  borderRightEnd: 24,
  borderBottomEnd: 31,
  borderLeftEnd: 40,
  // Horizontal rule expansion: frames 25-45
  ruleStart: 25,
  ruleEnd: 45,
  // Title text fade-in: frames 35-55
  titleStart: 35,
  titleEnd: 55,
  // Diamond ornament: frames 50-60
  diamondStart: 50,
  diamondEnd: 60,
  // Final fade to black: frames 80-90
  fadeOutStart: 80,
  fadeOutEnd: 90,
  totalDuration: 90,
};
