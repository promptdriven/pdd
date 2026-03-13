// Component-level constants for VeoSection06VeoPipelineInfographic
// Duration: ~0.03s (1 frame transitional beat)

export const BASE_CANVAS = {
  width: 1920,
  height: 1080,
};

export const COLORS = {
  background: '#0A1628',
  dotGrid: 'rgba(77,168,218,0.1)',
  titleText: '#FFFFFF',
  nodeLabel: '#FFFFFF',
  nodeFill: '#1B3A5C',
  scriptBorder: '#4DA8DA',
  promptBorder: '#4DA8DA',
  videoBorder: '#6FCF97',
  compositeBorder: '#F2C94C',
  arrow1: '#4DA8DA',
  arrow2: '#4DA8DA',
  arrow3: '#6FCF97',
} as const;

export const TYPOGRAPHY = {
  title: {
    fontSize: 36,
    fontFamily: "'Inter', sans-serif",
    fontWeight: 700 as const,
    letterSpacing: 8,
  },
  nodeLabel: {
    fontSize: 16,
    fontFamily: "'Inter', sans-serif",
    fontWeight: 600 as const,
  },
} as const;

export const DIMENSIONS = {
  nodeSize: 200,
  nodeBorderRadius: 16,
  nodeBorderWidth: 2,
  iconSize: 40,
  glowBlur: 16,
  glowOpacity: 0.3,
  dotGridSpacing: 40,
  arrowStrokeWidth: 2,
  arrowDashArray: '8 6',
} as const;

export const POSITIONS = {
  titleY: 100,
  nodeY: 440,
  node1X: 200,
  node2X: 560,
  node3X: 920,
  node4X: 1280,
  arrowY: 540,
  arrow1FromX: 400,
  arrow1ToX: 560,
  arrow2FromX: 760,
  arrow2ToX: 920,
  arrow3FromX: 1120,
  arrow3ToX: 1280,
} as const;

export const PIPELINE_NODES = [
  {
    label: 'Script',
    icon: 'document' as const,
    borderColor: COLORS.scriptBorder,
    x: POSITIONS.node1X,
  },
  {
    label: 'Veo Prompt',
    icon: 'sparkle' as const,
    borderColor: COLORS.promptBorder,
    x: POSITIONS.node2X,
  },
  {
    label: 'AI Video',
    icon: 'film' as const,
    borderColor: COLORS.videoBorder,
    x: POSITIONS.node3X,
  },
  {
    label: 'Remotion Composite',
    icon: 'layers' as const,
    borderColor: COLORS.compositeBorder,
    x: POSITIONS.node4X,
  },
] as const;

export const PIPELINE_ARROWS = [
  {
    fromX: POSITIONS.arrow1FromX,
    toX: POSITIONS.arrow1ToX,
    color: COLORS.arrow1,
  },
  {
    fromX: POSITIONS.arrow2FromX,
    toX: POSITIONS.arrow2ToX,
    color: COLORS.arrow2,
  },
  {
    fromX: POSITIONS.arrow3FromX,
    toX: POSITIONS.arrow3ToX,
    color: COLORS.arrow3,
  },
] as const;
