import React from 'react';
import { useCurrentFrame, interpolate, Easing } from 'remotion';
import { COLORS, DIMENSIONS, TYPOGRAPHY } from './constants';
import { PipelineIcon } from './PipelineIcon';

interface PipelineNodeProps {
  label: string;
  icon: 'text-cursor' | 'brain' | 'play';
  borderColor: string;
  x: number;
  y: number;
  scale?: number;
  animStart: number;
  animEnd: number;
  pulse?: boolean;
}

export const PipelineNode: React.FC<PipelineNodeProps> = ({
  label,
  icon,
  borderColor,
  x,
  y,
  scale = 1,
  animStart,
  animEnd,
  pulse = false,
}) => {
  const frame = useCurrentFrame();

  const { nodeWidth, nodeHeight, nodeBorderRadius, nodeBorderWidth, iconSize } =
    DIMENSIONS;
  const scaledWidth = nodeWidth * scale;
  const scaledHeight = nodeHeight * scale;
  const scaledRadius = nodeBorderRadius * scale;
  const scaledBorderWidth = Math.max(1, nodeBorderWidth * scale);
  const scaledIconSize = iconSize * scale;
  const scaledGap = 16 * scale;

  // Scale-in animation with easeOutBack (slight overshoot)
  const animProgress = interpolate(frame, [animStart, animEnd], [0, 1], {
    extrapolateLeft: 'clamp',
    extrapolateRight: 'clamp',
    easing: Easing.out(Easing.back(1.7)),
  });

  const opacity = interpolate(frame, [animStart, animStart + 2], [0, 1], {
    extrapolateLeft: 'clamp',
    extrapolateRight: 'clamp',
  });

  const nodeScale = interpolate(animProgress, [0, 1], [0.8, 1]);

  // Border pulse for output node (frame 24-28)
  let borderOpacity = 1;
  if (pulse && frame >= animEnd) {
    borderOpacity = interpolate(
      frame,
      [animEnd, animEnd + 1, animEnd + 2],
      [1, 0.6, 1],
      {
        extrapolateLeft: 'clamp',
        extrapolateRight: 'clamp',
      },
    );
  }

  return (
    <div
      style={{
        position: 'absolute',
        left: x,
        top: y,
        width: scaledWidth,
        height: scaledHeight,
        borderRadius: scaledRadius,
        backgroundColor: COLORS.nodeFill,
        border: `${scaledBorderWidth}px solid ${borderColor}`,
        borderColor: borderColor,
        opacity: opacity * borderOpacity,
        transform: `scale(${nodeScale})`,
        transformOrigin: 'center center',
        display: 'flex',
        flexDirection: 'column',
        alignItems: 'center',
        justifyContent: 'center',
        gap: scaledGap,
        boxShadow: `0 0 ${20 * scale}px ${borderColor}4D`,
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
