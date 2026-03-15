// Component-level constants for VeoSection05VeoPipelineInfographic
// Duration: ~1.0s (30 frames at 30fps)

export const BASE_CANVAS = {
  width: 1920,
  height: 1080,
};

export const COLORS = {
  gradientTop: '#0B1120',
  gradientBottom: '#0F1A2E',
  gold: '#C9A84C',
  nodeFill: 'rgba(201, 168, 76, 0.1)',
  nodeBorder: 'rgba(201, 168, 76, 0.5)',
  nodeLabel: '#FFFFFF',
  iconColor: '#C9A84C',
  arrowStroke: '#C9A84C',
  pulseGlow: '#C9A84C',
} as const;

export const TYPOGRAPHY = {
  nodeLabel: {
    fontSize: 20,
    fontFamily: "'Inter', sans-serif",
    fontWeight: 600 as const,
  },
} as const;

export const DIMENSIONS = {
  nodeWidth: 160,
  nodeHeight: 160,
  nodeBorderRadius: 12,
  nodeBorderWidth: 1,
  iconSize: 48,
  arrowStrokeWidth: 2,
  arrowHeadSize: 10,
  pulseRadius: 3,
} as const;

export const POSITIONS = {
  nodeCenterY: 480,
  node1X: 330,
  node2X: 870,
  node3X: 1410,
} as const;

// Animation frame ranges (30fps, 1.0s total)
export const ANIMATION = {
  // Node 1 "Prompt" scale-in
  node1Start: 0,
  node1End: 6,
  // Arrow 1 draw
  arrow1Start: 6,
  arrow1End: 10,
  // Node 2 "Veo AI" scale-in + pulse 1 begins
  node2Start: 10,
  node2End: 16,
  // Arrow 2 draw
  arrow2Start: 16,
  arrow2End: 20,
  // Node 3 "Clip" scale-in + pulse 2
  node3Start: 20,
  node3End: 26,
  // Hold with ambient glow
  holdStart: 26,
  holdEnd: 30,
  // Pulse travel windows
  pulse1Start: 10,
  pulse1End: 16,
  pulse2Start: 20,
  pulse2End: 26,
  totalDuration: 30,
} as const;

export const PIPELINE_NODES = [
  {
    id: 'prompt',
    label: 'Prompt',
    icon: 'text' as const,
    x: POSITIONS.node1X,
    y: POSITIONS.nodeCenterY,
    animStart: ANIMATION.node1Start,
    animEnd: ANIMATION.node1End,
  },
  {
    id: 'veo_ai',
    label: 'Veo AI',
    icon: 'sparkle' as const,
    x: POSITIONS.node2X,
    y: POSITIONS.nodeCenterY,
    animStart: ANIMATION.node2Start,
    animEnd: ANIMATION.node2End,
  },
  {
    id: 'clip',
    label: 'Clip',
    icon: 'film' as const,
    x: POSITIONS.node3X,
    y: POSITIONS.nodeCenterY,
    animStart: ANIMATION.node3Start,
    animEnd: ANIMATION.node3End,
  },
] as const;

export type PipelineNodeConfig = {
  id: string;
  label: string;
  icon: 'text' | 'sparkle' | 'film';
  x: number;
  y: number;
  width: number;
  height: number;
  animStart: number;
  animEnd: number;
  ambientGlow?: boolean;
};

type PipelineContractData = Record<string, unknown> | null;

const isRecord = (value: unknown): value is Record<string, unknown> =>
  Boolean(value) && typeof value === 'object' && !Array.isArray(value);

export const resolvePipelineNodes = (
  contractData: PipelineContractData,
): PipelineNodeConfig[] => {
  const contractSteps = Array.isArray(contractData?.pipeline_steps)
    ? contractData.pipeline_steps
    : [];

  return PIPELINE_NODES.map((fallbackNode, index) => {
    const contractStep = contractSteps[index];
    const step = isRecord(contractStep) ? contractStep : null;

    return {
      id: fallbackNode.id,
      label:
        typeof step?.label === 'string' ? step.label : fallbackNode.label,
      icon:
        step?.icon === 'text' || step?.icon === 'sparkle' || step?.icon === 'film'
          ? step.icon
          : fallbackNode.icon,
      x: typeof step?.x === 'number' ? step.x : fallbackNode.x,
      y: typeof step?.y === 'number' ? step.y : fallbackNode.y,
      width:
        typeof step?.width === 'number' ? step.width : DIMENSIONS.nodeWidth,
      height:
        typeof step?.height === 'number' ? step.height : DIMENSIONS.nodeHeight,
      animStart: fallbackNode.animStart,
      animEnd: fallbackNode.animEnd,
      ambientGlow: fallbackNode.id === 'veo_ai',
    };
  });
};

export const resolvePipelineArrows = (
  nodes: PipelineNodeConfig[],
) => {
  return [
    {
      fromX: nodes[0].x + nodes[0].width / 2,
      toX: nodes[1].x - nodes[1].width / 2,
      y: nodes[0].y,
      animStart: ANIMATION.arrow1Start,
      animEnd: ANIMATION.arrow1End,
      pulseStart: ANIMATION.pulse1Start,
      pulseEnd: ANIMATION.pulse1End,
    },
    {
      fromX: nodes[1].x + nodes[1].width / 2,
      toX: nodes[2].x - nodes[2].width / 2,
      y: nodes[1].y,
      animStart: ANIMATION.arrow2Start,
      animEnd: ANIMATION.arrow2End,
      pulseStart: ANIMATION.pulse2Start,
      pulseEnd: ANIMATION.pulse2End,
    },
  ] as const;
};
