// Component-level constants for VeoSection08VeoTechnologyCallout

export const CANVAS = {
  width: 1920,
  height: 1080,
};

export const COLORS = {
  background: '#0A1628',
  cardBg: 'rgba(15, 15, 15, 0.85)',
  cardBorder: 'rgba(255, 255, 255, 0.08)',
  headerText: '#FFFFFF',
  nodeLabel: '#FFFFFF',
  nodeIndigo: '#818CF8',
  nodeAmber: '#F59E0B',
  nodeAmberFill: 'rgba(245, 158, 11, 0.15)',
  nodeEmerald: '#34D399',
  arrowColor: 'rgba(255, 255, 255, 0.4)',
  iconStroke: '#FFFFFF',
};

export const TYPOGRAPHY = {
  header: {
    fontSize: 22,
    fontFamily: 'Inter, sans-serif',
    fontWeight: 700 as const,
    letterSpacing: '1px',
  },
  nodeLabel: {
    fontSize: 16,
    fontFamily: 'Inter, sans-serif',
    fontWeight: 600 as const,
  },
};

export const CARD = {
  width: 800,
  height: 280,
  borderRadius: 20,
  centerX: CANVAS.width / 2,
  restY: 680,
  offscreenY: 1100,
  exitY: 720,
};

export const NODE = {
  width: 160,
  height: 80,
  borderRadius: 12,
  borderWidth: 2,
  gap: 60, // arrow length between nodes
};

export const FLOW_NODES = [
  { label: 'Text Prompt', borderColor: COLORS.nodeIndigo, filled: false },
  { label: 'Veo AI', borderColor: COLORS.nodeAmber, filled: true },
  { label: 'Video Clip', borderColor: COLORS.nodeEmerald, filled: false },
];

export const HEADER_TEXT = 'How Veo Works';

export const ANIMATION = {
  // Card slide in: frames 0-20
  cardSlideInStart: 0,
  cardSlideInEnd: 20,

  // Node 1 fade in: frames 20-35
  node1Start: 20,
  node1End: 35,

  // Arrow 1 draw + Node 2: frames 30-40
  arrow1Start: 30,
  arrow1End: 40,
  node2Start: 30,
  node2End: 40,

  // Arrow 2 draw + Node 3: frames 40-50
  arrow2Start: 40,
  arrow2End: 50,
  node3Start: 40,
  node3End: 50,

  // Hold: frames 50-75 (amber pulse on Veo AI)
  holdStart: 50,
  holdEnd: 75,

  // Fade out: frames 75-90
  fadeOutStart: 75,
  fadeOutEnd: 90,

  totalDuration: 90,
};
