import React from 'react';
import { AbsoluteFill, useCurrentFrame } from 'remotion';
import {
  COLORS,
  NODES,
  ARROWS,
  ANIMATION_TIMING,
  TYPOGRAPHY,
} from './constants';
import { GridOverlay } from './GridOverlay';
import { FlowNode } from './FlowNode';
import { AnimatedArrow } from './AnimatedArrow';
import { DataPulse } from './DataPulse';

export const AnimationSection05AnimationEngineDiagram: React.FC = () => {
  const frame = useCurrentFrame();

  // Heading fades in with first node
  const headingOpacity = Math.min(1, frame / 10);

  return (
    <AbsoluteFill style={{ backgroundColor: COLORS.background }}>
      {/* Grid pattern */}
      <GridOverlay />

      {/* Section heading */}
      <div
        style={{
          position: 'absolute',
          left: 72,
          top: 72,
          color: COLORS.heading,
          fontSize: TYPOGRAPHY.heading.fontSize,
          fontFamily: TYPOGRAPHY.heading.fontFamily,
          fontWeight: TYPOGRAPHY.heading.fontWeight,
          opacity: headingOpacity,
        }}
      >
        Rendering Pipeline
      </div>

      {/* Node 1 — Spec */}
      <FlowNode
        x={NODES[0].x}
        y={NODES[0].y}
        label={NODES[0].label}
        icon={NODES[0].icon}
        color={NODES[0].color}
        fadeStart={ANIMATION_TIMING.node1FadeStart}
        fadeEnd={ANIMATION_TIMING.node1FadeEnd}
      />

      {/* Arrow 1: Spec -> Remotion */}
      <AnimatedArrow
        fromX={ARROWS[0].fromX}
        fromY={ARROWS[0].fromY}
        toX={ARROWS[0].toX}
        toY={ARROWS[0].toY}
        drawStart={ANIMATION_TIMING.arrow1DrawStart}
        drawEnd={ANIMATION_TIMING.arrow1DrawEnd}
      />

      {/* Node 2 — Remotion */}
      <FlowNode
        x={NODES[1].x}
        y={NODES[1].y}
        label={NODES[1].label}
        icon={NODES[1].icon}
        color={NODES[1].color}
        fadeStart={ANIMATION_TIMING.node2FadeStart}
        fadeEnd={ANIMATION_TIMING.node2FadeEnd}
      />

      {/* Arrow 2: Remotion -> Video */}
      <AnimatedArrow
        fromX={ARROWS[1].fromX}
        fromY={ARROWS[1].fromY}
        toX={ARROWS[1].toX}
        toY={ARROWS[1].toY}
        drawStart={ANIMATION_TIMING.arrow2DrawStart}
        drawEnd={ANIMATION_TIMING.arrow2DrawEnd}
      />

      {/* Node 3 — Video */}
      <FlowNode
        x={NODES[2].x}
        y={NODES[2].y}
        label={NODES[2].label}
        icon={NODES[2].icon}
        color={NODES[2].color}
        fadeStart={ANIMATION_TIMING.node3FadeStart}
        fadeEnd={ANIMATION_TIMING.node3FadeEnd}
      />

      {/* Data pulse traveling along arrows */}
      {frame >= ANIMATION_TIMING.pulseStart && (
        <DataPulse
          startFrame={ANIMATION_TIMING.pulseStart}
          endFrame={ANIMATION_TIMING.pulseEnd}
        />
      )}
    </AbsoluteFill>
  );
};

export const defaultAnimationSection05AnimationEngineDiagramProps = {};

export default AnimationSection05AnimationEngineDiagram;
