// Component-level constants for AnimationSection05AnimationEngineDiagram

export const CANVAS = {
  width: 1920,
  height: 1080,
};

export const COLORS = {
  background: '#1E1E2E',
  gridLine: '#2A2A3E',
  specNode: '#3B82F6',
  remotionNode: '#8B5CF6',
  videoNode: '#22C55E',
  arrowStroke: '#64748B',
  text: '#FFFFFF',
  heading: '#E2E8F0',
  pulseGlow: '#FFFFFF',
};

export const GRID = {
  spacing: 40,
  opacity: 0.2,
};

export const NODES = [
  { id: 'spec', label: 'Spec', x: 280, y: 480, color: '#3B82F6', icon: 'document' as const },
  { id: 'remotion', label: 'Remotion', x: 860, y: 480, color: '#8B5CF6', icon: 'gear' as const },
  { id: 'video', label: 'Video', x: 1440, y: 480, color: '#22C55E', icon: 'play' as const },
];

export const NODE_DIMENSIONS = {
  width: 200,
  height: 120,
  borderRadius: 16,
  iconSize: 40,
};

export const ARROWS = [
  { fromX: 480, fromY: 540, toX: 860, toY: 540 },
  { fromX: 1060, fromY: 540, toX: 1440, toY: 540 },
];

export const ARROW_STYLE = {
  strokeWidth: 4,
  arrowheadSize: 14,
};

export const PULSE = {
  radius: 12,
  blur: 8,
};

export const TYPOGRAPHY = {
  nodeLabel: {
    fontSize: 24,
    fontFamily: 'Inter',
    fontWeight: 600 as const,
  },
  heading: {
    fontSize: 36,
    fontFamily: 'Inter',
    fontWeight: 'bold' as const,
  },
};

export const ANIMATION_TIMING = {
  node1FadeStart: 0,
  node1FadeEnd: 15,
  arrow1DrawStart: 10,
  arrow1DrawEnd: 30,
  node2FadeStart: 20,
  node2FadeEnd: 35,
  arrow2DrawStart: 30,
  arrow2DrawEnd: 50,
  node3FadeStart: 40,
  node3FadeEnd: 55,
  pulseStart: 50,
  pulseEnd: 75,
  totalDuration: 75,
};
