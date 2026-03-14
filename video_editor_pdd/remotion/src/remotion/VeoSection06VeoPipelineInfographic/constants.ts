// Component-level constants for VeoSection06VeoPipelineInfographic
// Duration: ~1.0s (30 frames at 30fps)

export const BASE_CANVAS = {
  width: 1920,
  height: 1080,
};

export const COLORS = {
  background: '#111827',
  dotGrid: 'rgba(255,255,255,0.03)',
  titleText: '#FFFFFF',
  nodeLabel: '#FFFFFF',
  nodeFill: '#1E293B',
  indigo: '#6366F1',
  violet: '#8B5CF6',
  emerald: '#10B981',
} as const;

export const TYPOGRAPHY = {
  title: {
    fontSize: 36,
    fontFamily: "'Inter', sans-serif",
    fontWeight: 700 as const,
  },
  nodeLabel: {
    fontSize: 18,
    fontFamily: "'Inter', sans-serif",
    fontWeight: 600 as const,
  },
} as const;

export const DIMENSIONS = {
  nodeWidth: 280,
  nodeHeight: 200,
  nodeBorderRadius: 16,
  nodeBorderWidth: 2,
  iconSize: 48,
  dotGridSpacing: 40,
  arrowStrokeWidth: 3,
  arrowHeadSize: 12,
} as const;

export const POSITIONS = {
  titleY: 80,
  nodeY: 440,
  node1X: 200,
  node2X: 820,
  node3X: 1440,
  arrowY: 540,
  arrow1FromX: 480,
  arrow1ToX: 820,
  arrow2FromX: 1100,
  arrow2ToX: 1440,
} as const;

// Animation frame ranges (30fps)
export const ANIMATION = {
  // Title fade-in
  titleStart: 0,
  titleEnd: 4,
  // Node 1 scale-in
  node1Start: 4,
  node1End: 10,
  // Arrow 1 draw
  arrow1Start: 10,
  arrow1End: 14,
  // Node 2 scale-in
  node2Start: 14,
  node2End: 20,
  // Arrow 2 draw
  arrow2Start: 20,
  arrow2End: 24,
  // Node 3 scale-in + pulse
  node3Start: 24,
  node3End: 28,
  // Hold
  holdStart: 28,
  holdEnd: 30,
  totalDuration: 30,
} as const;

export const PIPELINE_NODES = [
  {
    id: 'prompt',
    label: 'Text Prompt',
    icon: 'text-cursor' as const,
    borderColor: COLORS.indigo,
    x: POSITIONS.node1X,
    animStart: ANIMATION.node1Start,
    animEnd: ANIMATION.node1End,
    pulse: false,
  },
  {
    id: 'model',
    label: 'Veo Model',
    icon: 'brain' as const,
    borderColor: COLORS.violet,
    x: POSITIONS.node2X,
    animStart: ANIMATION.node2Start,
    animEnd: ANIMATION.node2End,
    pulse: false,
  },
  {
    id: 'output',
    label: 'Video Output',
    icon: 'play' as const,
    borderColor: COLORS.emerald,
    x: POSITIONS.node3X,
    animStart: ANIMATION.node3Start,
    animEnd: ANIMATION.node3End,
    pulse: true,
  },
] as const;

export const PIPELINE_ARROWS = [
  {
    fromX: POSITIONS.arrow1FromX,
    toX: POSITIONS.arrow1ToX,
    gradientFrom: COLORS.indigo,
    gradientTo: COLORS.violet,
    animStart: ANIMATION.arrow1Start,
    animEnd: ANIMATION.arrow1End,
  },
  {
    fromX: POSITIONS.arrow2FromX,
    toX: POSITIONS.arrow2ToX,
    gradientFrom: COLORS.violet,
    gradientTo: COLORS.emerald,
    animStart: ANIMATION.arrow2Start,
    animEnd: ANIMATION.arrow2End,
  },
] as const;
