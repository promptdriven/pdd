import React from 'react';
import { useCurrentFrame, spring } from 'remotion';
import { SANS_FONT } from './constants';

const Badge: React.FC<{
  text: string;
  color: string;
  x: number;
  y: number;
  startFrame: number;
  fps?: number;
}> = ({ text, color, x, y, startFrame, fps = 30 }) => {
  const frame = useCurrentFrame();

  const elapsed = Math.max(0, frame - startFrame);
  const scale = spring({
    frame: elapsed,
    fps,
    config: {
      stiffness: 200,
      damping: 12,
    },
  });

  return (
    <div
      style={{
        position: 'absolute',
        left: x,
        top: y,
        transform: `scale(${scale})`,
        transformOrigin: 'center center',
        backgroundColor: 'rgba(0, 0, 0, 0.4)',
        borderRadius: 4,
        padding: '4px 10px',
        border: `1px solid ${color}33`,
      }}
    >
      <span
        style={{
          fontFamily: SANS_FONT,
          fontSize: 12,
          fontWeight: 700,
          color,
          opacity: 0.6,
        }}
      >
        {text}
      </span>
    </div>
  );
};

export default Badge;
