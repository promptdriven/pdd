import React from 'react';
import { AbsoluteFill, useVideoConfig } from 'remotion';
import {
  BASE_CANVAS,
  COLORS,
  TYPOGRAPHY,
  POSITIONS,
  PIPELINE_NODES,
  PIPELINE_ARROWS,
} from './constants';
import { PipelineNode } from './PipelineNode';
import { PipelineArrow } from './PipelineArrow';
import { DotGridPattern } from './DotGridPattern';

export const VeoSection06VeoPipelineInfographic: React.FC = () => {
  const { width, height } = useVideoConfig();
  const scaleX = width / BASE_CANVAS.width;
  const scaleY = height / BASE_CANVAS.height;
  const uniformScale = Math.min(scaleX, scaleY);

  return (
    <AbsoluteFill
      style={{
        backgroundColor: COLORS.background,
        width,
        height,
      }}
    >
      {/* Subtle dot-grid pattern */}
      <DotGridPattern />

      {/* Title: VIDEO GENERATION PIPELINE */}
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
          letterSpacing: TYPOGRAPHY.title.letterSpacing * uniformScale,
          color: COLORS.titleText,
        }}
      >
        VIDEO GENERATION PIPELINE
      </div>

      {/* Pipeline nodes */}
      {PIPELINE_NODES.map((node) => (
        <PipelineNode
          key={node.label}
          label={node.label}
          icon={node.icon}
          borderColor={node.borderColor}
          x={node.x * scaleX}
          y={POSITIONS.nodeY * scaleY}
          scale={uniformScale}
        />
      ))}

      {/* Connecting arrows */}
      {PIPELINE_ARROWS.map((arrow, i) => (
        <PipelineArrow
          key={i}
          fromX={arrow.fromX * scaleX}
          toX={arrow.toX * scaleX}
          color={arrow.color}
          scale={uniformScale}
        />
      ))}
    </AbsoluteFill>
  );
};

export const defaultVeoSection06VeoPipelineInfographicProps = {};

export default VeoSection06VeoPipelineInfographic;
