import React from 'react';
import { useCurrentFrame, interpolate, Easing } from 'remotion';
import { COLORS, DIMENSIONS, TYPOGRAPHY } from './constants';
import { PipelineIcon } from './PipelineIcon';

interface PipelineNodeProps {
  label: string;
  icon: 'text' | 'sparkle' | 'film';
  x: number;
  y: number;
  scale?: number;
  animStart: number;
  animEnd: number;
  ambientGlow?: boolean;
}

export const PipelineNode: React.FC<PipelineNodeProps> = ({
  label,
  icon,
  x,
  y,
  scale = 1,
  animStart,
  animEnd,
  ambientGlow = false,
}) => {
  const frame = useCurrentFrame();

  const { nodeWidth, nodeHeight, nodeBorderRadius, nodeBorderWidth, iconSize } =
    DIMENSIONS;
  const scaledWidth = nodeWidth * scale;
  const scaledHeight = nodeHeight * scale;
  const scaledRadius = nodeBorderRadius * scale;
  const scaledBorderWidth = Math.max(1, nodeBorderWidth * scale);
  const scaledIconSize = iconSize * scale;
  const scaledGap = 12 * scale;

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

  // Ambient glow pulse for "Veo AI" node during hold phase (frames 26-30)
  let glowIntensity = 0;
  if (ambientGlow && frame >= 26) {
    glowIntensity = interpolate(
      frame,
      [26, 28, 30],
      [0, 1, 0],
      {
        extrapolateLeft: 'clamp',
        extrapolateRight: 'clamp',
        easing: Easing.inOut(Easing.sin),
      },
    );
  }

  const glowSpread = 8 + glowIntensity * 16;

  return (
    <div
      style={{
        position: 'absolute',
        left: x - (scaledWidth / 2),
        top: y,
        width: scaledWidth,
        height: scaledHeight,
        borderRadius: scaledRadius,
        backgroundColor: COLORS.nodeFill,
        border: `${scaledBorderWidth}px solid ${COLORS.nodeBorder}`,
        opacity,
        transform: `scale(${nodeScale})`,
        transformOrigin: 'center center',
        display: 'flex',
        flexDirection: 'column',
        alignItems: 'center',
        justifyContent: 'center',
        gap: scaledGap,
        boxShadow: `0 0 ${glowSpread * scale}px ${COLORS.pulseGlow}4D`,
      }}
    >
      <PipelineIcon type={icon} color={COLORS.iconColor} size={scaledIconSize} />
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
