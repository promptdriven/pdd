import React from 'react';
import {
  AbsoluteFill,
  useVideoConfig,
} from 'remotion';
import {
  BASE_CANVAS,
  COLORS,
  POSITIONS,
  PIPELINE_NODES,
  PIPELINE_ARROWS,
} from './constants';
import { PipelineNode } from './PipelineNode';
import { PipelineArrow } from './PipelineArrow';

export const VeoSection05VeoPipelineInfographic: React.FC = () => {
  const { width, height } = useVideoConfig();
  const scaleX = width / BASE_CANVAS.width;
  const scaleY = height / BASE_CANVAS.height;
  const uniformScale = Math.min(scaleX, scaleY);

  // Arrow y is at the vertical center of each node (nodeY + nodeHeight/2)
  const arrowY = (POSITIONS.nodeY + 60) * scaleY;

  return (
    <AbsoluteFill
      style={{
        background: `linear-gradient(180deg, ${COLORS.gradientTop}, ${COLORS.gradientBottom})`,
      }}
    >
      {/* Pipeline nodes */}
      {PIPELINE_NODES.map((node) => (
        <PipelineNode
          key={node.id}
          label={node.label}
          icon={node.icon}
          x={node.x * scaleX}
          y={POSITIONS.nodeY * scaleY}
          scale={uniformScale}
          animStart={node.animStart}
          animEnd={node.animEnd}
          ambientGlow={node.id === 'veo_ai'}
        />
      ))}

      {/* Connecting arrows with progress pulses */}
      {PIPELINE_ARROWS.map((arrow, i) => (
        <PipelineArrow
          key={i}
          fromX={arrow.fromX * scaleX}
          toX={arrow.toX * scaleX}
          y={arrowY}
          animStart={arrow.animStart}
          animEnd={arrow.animEnd}
          pulseStart={arrow.pulseStart}
          pulseEnd={arrow.pulseEnd}
          scale={uniformScale}
        />
      ))}
    </AbsoluteFill>
  );
};

export const defaultVeoSection05VeoPipelineInfographicProps = {};

export default VeoSection05VeoPipelineInfographic;
