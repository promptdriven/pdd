import React from 'react';
import { useCurrentFrame, interpolate, Easing } from 'remotion';
import { COLORS, type PipelineInfographicLayout } from './constants';
import { PipelineIcon } from './PipelineIcon';

interface PipelineNodeProps {
  label: string;
  icon: 'text-cursor' | 'sparkle' | 'play-circle';
  borderColor: string;
  x: number;
  nodeY: number;
  descriptorY: number;
  scaleStart: number;
  scaleEnd: number;
  descFadeStart: number;
  descFadeEnd: number;
  descriptor: string;
  layout: PipelineInfographicLayout;
}

export const PipelineNode: React.FC<PipelineNodeProps> = ({
  label,
  icon,
  borderColor,
  x,
  nodeY,
  descriptorY,
  scaleStart,
  scaleEnd,
  descFadeStart,
  descFadeEnd,
  descriptor,
  layout,
}) => {
  const frame = useCurrentFrame();
  const { dimensions, typography } = layout;

  // Scale animation with easeOutBack (overshoot for bounce)
  const rawScale = interpolate(
    frame,
    [scaleStart, scaleEnd],
    [0, 1],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.out(Easing.back(1.7)),
    },
  );

  // Node opacity tied to scale animation start
  const nodeOpacity = interpolate(
    frame,
    [scaleStart, scaleStart + 5],
    [0, 1],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
    },
  );

  // Descriptor fade in
  const descOpacity = interpolate(
    frame,
    [descFadeStart, descFadeEnd],
    [0, 1],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.out(Easing.cubic),
    },
  );

  return (
    <>
      {/* Node container */}
      <div
        style={{
          position: 'absolute',
          left: x - dimensions.nodeWidth / 2,
          top: nodeY - dimensions.nodeHeight / 2,
          width: dimensions.nodeWidth,
          height: dimensions.nodeHeight,
          borderRadius: dimensions.nodeBorderRadius,
          backgroundColor: COLORS.nodeFill,
          border: `${dimensions.nodeBorderWidth}px solid ${borderColor}`,
          display: 'flex',
          alignItems: 'center',
          justifyContent: 'center',
          gap: 10,
          transform: `scale(${rawScale})`,
          opacity: nodeOpacity,
        }}
      >
        <PipelineIcon type={icon} color={borderColor} size={dimensions.iconSize} />
        <span
          style={{
            fontFamily: typography.nodeLabel.fontFamily,
            fontSize: typography.nodeLabel.fontSize,
            fontWeight: typography.nodeLabel.fontWeight,
            color: COLORS.nodeLabel,
            lineHeight: 1,
          }}
        >
          {label}
        </span>
      </div>

      {/* Descriptor label below node */}
      <div
        style={{
          position: 'absolute',
          left: x - dimensions.nodeWidth / 2,
          top: descriptorY,
          width: dimensions.nodeWidth,
          textAlign: 'center',
          fontFamily: typography.descriptor.fontFamily,
          fontSize: typography.descriptor.fontSize,
          fontWeight: typography.descriptor.fontWeight,
          color: COLORS.descriptor,
          opacity: descOpacity,
        }}
      >
        {descriptor}
      </div>
    </>
  );
};
