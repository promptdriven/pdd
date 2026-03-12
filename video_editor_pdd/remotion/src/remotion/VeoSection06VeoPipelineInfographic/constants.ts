// Component-level constants for VeoSection06VeoPipelineInfographic

export const BASE_CANVAS = {
  width: 1920,
  height: 1080,
};

export const COLORS = {
  background: '#0D1117',
  nodeFill: '#1B2838',
  titleText: '#FFFFFF',
  nodeLabel: '#FFFFFF',
  descriptor: '#8B949E',
  prompt: '#5B9BD5',
  veo: '#D4A843',
  clip: '#40916C',
};

export const TYPOGRAPHY = {
  sectionTitle: {
    fontSize: 36,
    fontFamily: 'Inter',
    fontWeight: 700 as const,
  },
  nodeLabel: {
    fontSize: 26,
    fontFamily: 'Inter',
    fontWeight: 600 as const,
  },
  descriptor: {
    fontSize: 18,
    fontFamily: 'Inter',
    fontWeight: 400 as const,
  },
};

export const DIMENSIONS = {
  nodeWidth: 240,
  nodeHeight: 80,
  nodeBorderRadius: 12,
  nodeBorderWidth: 2,
  iconSize: 20,
};

export const POSITIONS = {
  titleY: 120,
  nodeY: 440,
  descriptorY: 540,
  node1X: 380,
  node2X: 960,
  node3X: 1540,
  arrow1Start: 500,
  arrow1End: 840,
  arrow2Start: 1080,
  arrow2End: 1420,
  arrowY: 440,
};

export const ANIMATION = {
  // Section title fade in
  titleFadeStart: 0,
  titleFadeEnd: 20,
  // Node 1 scale in
  node1Start: 15,
  node1End: 40,
  // Arrow 1 draw
  arrow1Start: 35,
  arrow1End: 55,
  // Node 2 scale in
  node2Start: 50,
  node2End: 75,
  // Arrow 2 draw
  arrow2Start: 70,
  arrow2End: 90,
  // Node 3 scale in
  node3Start: 85,
  node3End: 110,
  // Descriptor fade ins
  desc1FadeStart: 40,
  desc1FadeEnd: 60,
  desc2FadeStart: 75,
  desc2FadeEnd: 95,
  desc3FadeStart: 110,
  desc3FadeEnd: 130,
  // Total duration
  totalDuration: 150,
};

export const PIPELINE_NODES = [
  {
    label: 'Prompt',
    icon: 'text-cursor' as const,
    color: COLORS.prompt,
    descriptor: 'Text description',
    x: POSITIONS.node1X,
  },
  {
    label: 'Veo 3.1',
    icon: 'sparkle' as const,
    color: COLORS.veo,
    descriptor: 'AI video model',
    x: POSITIONS.node2X,
  },
  {
    label: 'Clip',
    icon: 'play-circle' as const,
    color: COLORS.clip,
    descriptor: '5s footage',
    x: POSITIONS.node3X,
  },
] as const;

export interface PipelineInfographicLayout {
  width: number;
  height: number;
  typography: typeof TYPOGRAPHY;
  dimensions: typeof DIMENSIONS;
  positions: typeof POSITIONS;
}

export const resolvePipelineInfographicLayout = (
  width: number,
  height: number
): PipelineInfographicLayout => {
  const scaleX = width / BASE_CANVAS.width;
  const scaleY = height / BASE_CANVAS.height;
  const uniformScale = Math.min(scaleX, scaleY);

  return {
    width,
    height,
    typography: {
      sectionTitle: {
        ...TYPOGRAPHY.sectionTitle,
        fontSize: Math.max(24, TYPOGRAPHY.sectionTitle.fontSize * uniformScale),
      },
      nodeLabel: {
        ...TYPOGRAPHY.nodeLabel,
        fontSize: Math.max(18, TYPOGRAPHY.nodeLabel.fontSize * uniformScale),
      },
      descriptor: {
        ...TYPOGRAPHY.descriptor,
        fontSize: Math.max(14, TYPOGRAPHY.descriptor.fontSize * uniformScale),
      },
    },
    dimensions: {
      nodeWidth: DIMENSIONS.nodeWidth * scaleX,
      nodeHeight: DIMENSIONS.nodeHeight * scaleY,
      nodeBorderRadius: Math.max(8, DIMENSIONS.nodeBorderRadius * uniformScale),
      nodeBorderWidth: Math.max(1.5, DIMENSIONS.nodeBorderWidth * uniformScale),
      iconSize: Math.max(14, DIMENSIONS.iconSize * uniformScale),
    },
    positions: {
      titleY: POSITIONS.titleY * scaleY,
      nodeY: POSITIONS.nodeY * scaleY,
      descriptorY: POSITIONS.descriptorY * scaleY,
      node1X: POSITIONS.node1X * scaleX,
      node2X: POSITIONS.node2X * scaleX,
      node3X: POSITIONS.node3X * scaleX,
      arrow1Start: POSITIONS.arrow1Start * scaleX,
      arrow1End: POSITIONS.arrow1End * scaleX,
      arrow2Start: POSITIONS.arrow2Start * scaleX,
      arrow2End: POSITIONS.arrow2End * scaleX,
      arrowY: POSITIONS.arrowY * scaleY,
    },
  };
};
