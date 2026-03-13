import React from 'react';
import { AbsoluteFill } from 'remotion';
import { COLORS, TYPOGRAPHY, POSITIONS, PIPELINE_NODES, PIPELINE_ARROWS } from './constants';
import { PipelineNode } from './PipelineNode';
import { PipelineArrow } from './PipelineArrow';
import { DotGridPattern } from './DotGridPattern';

export const VeoSection06VeoPipelineInfographic: React.FC = () => {
  return (
    <AbsoluteFill
      style={{
        backgroundColor: COLORS.background,
      }}
    >
      {/* Subtle dot-grid pattern */}
      <DotGridPattern />

      {/* Title: VIDEO GENERATION PIPELINE */}
      <div
        style={{
          position: 'absolute',
          top: POSITIONS.titleY,
          left: 0,
          width: '100%',
          textAlign: 'center',
          fontFamily: TYPOGRAPHY.title.fontFamily,
          fontSize: TYPOGRAPHY.title.fontSize,
          fontWeight: TYPOGRAPHY.title.fontWeight,
          letterSpacing: TYPOGRAPHY.title.letterSpacing,
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
          x={node.x}
          y={POSITIONS.nodeY}
        />
      ))}

      {/* Connecting arrows */}
      {PIPELINE_ARROWS.map((arrow, i) => (
        <PipelineArrow
          key={i}
          fromX={arrow.fromX}
          toX={arrow.toX}
          color={arrow.color}
        />
      ))}
    </AbsoluteFill>
  );
};

export const defaultVeoSection06VeoPipelineInfographicProps = {};

export default VeoSection06VeoPipelineInfographic;
