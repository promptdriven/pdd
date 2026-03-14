import React from 'react';
import { COLORS, DIMENSIONS, TYPOGRAPHY } from './constants';
import { PipelineIcon } from './PipelineIcon';

interface PipelineNodeProps {
  label: string;
  icon: 'document' | 'sparkle' | 'film' | 'layers';
  borderColor: string;
  x: number;
  y: number;
  scale?: number;
}

export const PipelineNode: React.FC<PipelineNodeProps> = ({
  label,
  icon,
  borderColor,
  x,
  y,
  scale = 1,
}) => {
  const { nodeSize, nodeBorderRadius, nodeBorderWidth, iconSize, glowBlur, glowOpacity } = DIMENSIONS;
  const scaledNodeSize = nodeSize * scale;
  const scaledRadius = nodeBorderRadius * scale;
  const scaledBorderWidth = Math.max(1, nodeBorderWidth * scale);
  const scaledIconSize = iconSize * scale;
  const scaledGlowBlur = glowBlur * scale;
  const scaledGap = 16 * scale;

  return (
    <div
      style={{
        position: 'absolute',
        left: x,
        top: y,
        width: scaledNodeSize,
        height: scaledNodeSize,
        borderRadius: scaledRadius,
        backgroundColor: COLORS.nodeFill,
        border: `${scaledBorderWidth}px solid ${borderColor}`,
        display: 'flex',
        flexDirection: 'column',
        alignItems: 'center',
        justifyContent: 'center',
        gap: scaledGap,
        boxShadow: `0 0 ${scaledGlowBlur}px ${borderColor}${Math.round(glowOpacity * 255).toString(16).padStart(2, '0')}`,
      }}
    >
      <PipelineIcon type={icon} color={borderColor} size={scaledIconSize} />
      <span
        style={{
          fontFamily: TYPOGRAPHY.nodeLabel.fontFamily,
          fontSize: TYPOGRAPHY.nodeLabel.fontSize * scale,
          fontWeight: TYPOGRAPHY.nodeLabel.fontWeight,
          color: COLORS.nodeLabel,
          lineHeight: 1,
          textAlign: 'center',
        }}
      >
        {label}
      </span>
    </div>
  );
};
