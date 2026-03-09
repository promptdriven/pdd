// Component-level constants for VeoSection13VeoTechnologyReprise

export const CANVAS = {
  width: 1920,
  height: 1080,
};

export const COLORS = {
  backgroundOuter: '#121212',
  backgroundInner: '#1A1A2E',
  cardBg: 'rgba(255, 255, 255, 0.04)',
  headerText: 'rgba(255, 255, 255, 0.7)',
  metricNumber: '#FFFFFF',
  metricLabel: 'rgba(255, 255, 255, 0.6)',
  rule: 'rgba(255, 255, 255, 0.15)',
  accentIndigo: '#818CF8',
  accentAmber: '#F59E0B',
  accentEmerald: '#34D399',
};

export const TYPOGRAPHY = {
  header: {
    fontSize: 20,
    fontFamily: 'Inter, sans-serif',
    fontWeight: 700 as const,
    letterSpacing: '4px',
  },
  metricNumber: {
    fontSize: 48,
    fontFamily: 'Inter, sans-serif',
    fontWeight: 900 as const,
  },
  metricLabel: {
    fontSize: 16,
    fontFamily: 'Inter, sans-serif',
    fontWeight: 400 as const,
  },
};

export const LAYOUT = {
  headerY: 320,
  ruleY: 370,
  ruleWidth: 200,
  cardsY: 540,
  cardWidth: 320,
  cardHeight: 200,
  cardGap: 40,
  cardBorderRadius: 12,
  cardBorderLeft: 3,
  iconSize: 28,
};

export const METRICS = [
  { icon: 'film' as const, value: '2', label: 'Clips Generated', color: COLORS.accentIndigo },
  { icon: 'clock' as const, value: '~6s', label: 'of Footage', color: COLORS.accentAmber },
  { icon: 'sparkle' as const, value: '100%', label: 'AI-Rendered', color: COLORS.accentEmerald },
];

export const ANIMATION = {
  // Header fade in: frames 0-15
  headerFadeStart: 0,
  headerFadeEnd: 15,

  // Rule expansion: frames 10-20
  ruleExpandStart: 10,
  ruleExpandEnd: 20,

  // Card 1 slide in: frames 15-30
  card1Start: 15,
  card1End: 30,

  // Card 2 slide in: frames 25-40
  card2Start: 25,
  card2End: 40,

  // Card 3 slide in: frames 35-50
  card3Start: 35,
  card3End: 50,

  // Hold: frames 50-75
  holdStart: 50,
  holdEnd: 75,

  // Fade out: frames 75-90
  fadeOutStart: 75,
  fadeOutEnd: 90,

  totalDuration: 90,

  // Card offscreen start Y offset
  cardSlideDistance: 60,
};
