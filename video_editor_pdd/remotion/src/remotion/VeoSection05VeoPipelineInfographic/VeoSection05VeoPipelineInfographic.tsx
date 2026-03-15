import React from 'react';
import {
  AbsoluteFill,
  useVideoConfig,
} from 'remotion';
import { useVisualContractData } from '../_shared/visual-runtime';
import {
  BASE_CANVAS,
  COLORS,
  resolvePipelineArrows,
  resolvePipelineNodes,
} from './constants';
import { PipelineNode } from './PipelineNode';
import { PipelineArrow } from './PipelineArrow';

export const VeoSection05VeoPipelineInfographic: React.FC = () => {
  const { width, height } = useVideoConfig();
  const contractData = useVisualContractData<Record<string, unknown>>();
  const scaleX = width / BASE_CANVAS.width;
  const scaleY = height / BASE_CANVAS.height;
  const uniformScale = Math.min(scaleX, scaleY);
  const nodes = resolvePipelineNodes(contractData);
  const arrows = resolvePipelineArrows(nodes);

  return (
    <AbsoluteFill
      style={{
        background: `linear-gradient(180deg, ${COLORS.gradientTop}, ${COLORS.gradientBottom})`,
      }}
    >
      {/* Pipeline nodes */}
      {nodes.map((node) => (
        <PipelineNode
          key={node.id}
          label={node.label}
          icon={node.icon}
          x={node.x * scaleX}
          y={node.y * scaleY}
          width={node.width * scaleX}
          height={node.height * scaleY}
          scale={uniformScale}
          animStart={node.animStart}
          animEnd={node.animEnd}
          ambientGlow={node.ambientGlow}
        />
      ))}

      {/* Connecting arrows with progress pulses */}
      {arrows.map((arrow, i) => (
        <PipelineArrow
          key={i}
          fromX={arrow.fromX * scaleX}
          toX={arrow.toX * scaleX}
          y={arrow.y * scaleY}
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
