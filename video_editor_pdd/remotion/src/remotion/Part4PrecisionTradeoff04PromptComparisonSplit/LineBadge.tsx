import React from 'react';
import { useCurrentFrame, spring } from 'remotion';

interface LineBadgeProps {
  text: string;
  color: string;
  x: number;
  y: number;
  startFrame: number;
  fps?: number;
}

export const LineBadge: React.FC<LineBadgeProps> = ({
  text,
  color,
  x,
  y,
  startFrame,
  fps = 30,
}) => {
  const frame = useCurrentFrame();

  const scale = spring({
    frame: frame - startFrame,
    fps,
    config: { stiffness: 200, damping: 12 },
  });

  const clampedScale = frame < startFrame ? 0 : scale;

  return (
    <div
      style={{
        position: 'absolute',
        left: x,
        top: y,
        transform: `scale(${clampedScale})`,
        transformOrigin: 'center center',
        fontFamily: 'Inter, sans-serif',
        fontSize: 12,
        fontWeight: 700,
        color,
        opacity: 0.6,
        whiteSpace: 'nowrap',
      }}
    >
      {text}
    </div>
  );
};
