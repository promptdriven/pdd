import React from 'react';
import { COLORS, DIMENSIONS, TYPOGRAPHY } from './constants';
import { PipelineIcon } from './PipelineIcon';

interface PipelineNodeProps {
  label: string;
  icon: 'document' | 'sparkle' | 'film' | 'layers';
  borderColor: string;
  x: number;
  y: number;
}

export const PipelineNode: React.FC<PipelineNodeProps> = ({
  label,
  icon,
  borderColor,
  x,
  y,
}) => {
  const { nodeSize, nodeBorderRadius, nodeBorderWidth, iconSize, glowBlur, glowOpacity } = DIMENSIONS;

  return (
    <div
      style={{
        position: 'absolute',
        left: x,
        top: y,
        width: nodeSize,
        height: nodeSize,
        borderRadius: nodeBorderRadius,
        backgroundColor: COLORS.nodeFill,
        border: `${nodeBorderWidth}px solid ${borderColor}`,
        display: 'flex',
        flexDirection: 'column',
        alignItems: 'center',
        justifyContent: 'center',
        gap: 16,
        boxShadow: `0 0 ${glowBlur}px ${borderColor}${Math.round(glowOpacity * 255).toString(16).padStart(2, '0')}`,
      }}
    >
      <PipelineIcon type={icon} color={borderColor} size={iconSize} />
      <span
        style={{
          fontFamily: TYPOGRAPHY.nodeLabel.fontFamily,
          fontSize: TYPOGRAPHY.nodeLabel.fontSize,
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
