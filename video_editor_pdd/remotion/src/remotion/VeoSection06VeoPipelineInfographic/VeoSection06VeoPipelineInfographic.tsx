import React from 'react';
import {
  AbsoluteFill,
  useCurrentFrame,
  useVideoConfig,
  interpolate,
  Easing,
} from 'remotion';
import {
  BASE_CANVAS,
  COLORS,
  TYPOGRAPHY,
  POSITIONS,
  ANIMATION,
  PIPELINE_NODES,
  PIPELINE_ARROWS,
} from './constants';
import { PipelineNode } from './PipelineNode';
import { PipelineArrow } from './PipelineArrow';
import { DotGridPattern } from './DotGridPattern';

export const VeoSection06VeoPipelineInfographic: React.FC = () => {
  const frame = useCurrentFrame();
  const { width, height } = useVideoConfig();
  const scaleX = width / BASE_CANVAS.width;
  const scaleY = height / BASE_CANVAS.height;
  const uniformScale = Math.min(scaleX, scaleY);

  // Title fade-in with easeOutCubic
  const titleOpacity = interpolate(
    frame,
    [ANIMATION.titleStart, ANIMATION.titleEnd],
    [0, 1],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.out(Easing.cubic),
    },
  );

  return (
    <AbsoluteFill
      style={{
        backgroundColor: COLORS.background,
      }}
    >
      {/* Subtle dot-grid pattern */}
      <DotGridPattern />

      {/* Section title: "How Veo Works" */}
      <div
        style={{
          position: 'absolute',
          top: POSITIONS.titleY * scaleY,
          left: 0,
          width: '100%',
          textAlign: 'center',
          fontFamily: TYPOGRAPHY.title.fontFamily,
          fontSize: TYPOGRAPHY.title.fontSize * uniformScale,
          fontWeight: TYPOGRAPHY.title.fontWeight,
          color: COLORS.titleText,
          opacity: titleOpacity,
        }}
      >
        How Veo Works
      </div>

      {/* Pipeline nodes */}
      {PIPELINE_NODES.map((node) => (
        <PipelineNode
          key={node.id}
          label={node.label}
          icon={node.icon}
          borderColor={node.borderColor}
          x={node.x * scaleX}
          y={POSITIONS.nodeY * scaleY}
          scale={uniformScale}
          animStart={node.animStart}
          animEnd={node.animEnd}
          pulse={node.pulse}
        />
      ))}

      {/* Connecting arrows with gradient */}
      {PIPELINE_ARROWS.map((arrow, i) => (
        <PipelineArrow
          key={i}
          fromX={arrow.fromX * scaleX}
          toX={arrow.toX * scaleX}
          gradientFrom={arrow.gradientFrom}
          gradientTo={arrow.gradientTo}
          animStart={arrow.animStart}
          animEnd={arrow.animEnd}
          scale={uniformScale}
          gradientId={`pipelineGrad${i}`}
        />
      ))}
    </AbsoluteFill>
  );
};

export const defaultVeoSection06VeoPipelineInfographicProps = {};

export default VeoSection06VeoPipelineInfographic;
