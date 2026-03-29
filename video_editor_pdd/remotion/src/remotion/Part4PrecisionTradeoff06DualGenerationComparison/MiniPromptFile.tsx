import React from 'react';
import { interpolate, useCurrentFrame, Easing } from 'remotion';

interface MiniPromptFileProps {
  x: number;
  y: number;
  width: number;
  height: number;
  borderColor: string;
  badge: string;
  lineCount: number;
  appearStart: number;
  appearDuration: number;
}

const MiniPromptFile: React.FC<MiniPromptFileProps> = ({
  x,
  y,
  width,
  height,
  borderColor,
  badge,
  lineCount,
  appearStart,
  appearDuration,
}) => {
  const frame = useCurrentFrame();

  const opacity = interpolate(
    frame,
    [appearStart, appearStart + appearDuration],
    [0, 1],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.out(Easing.quad),
    }
  );

  const scale = interpolate(
    frame,
    [appearStart, appearStart + appearDuration],
    [0.85, 1],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.out(Easing.quad),
    }
  );

  // Generate faint text lines to simulate prompt content
  const lines: React.ReactNode[] = [];
  const lineHeight = Math.min(14, (height - 40) / lineCount);
  const visibleLines = Math.min(lineCount, Math.floor((height - 40) / lineHeight));

  for (let i = 0; i < visibleLines; i++) {
    const lineWidth = 30 + Math.random() * (width - 80);
    lines.push(
      <div
        key={i}
        style={{
          width: Math.min(lineWidth, width - 40),
          height: 2,
          backgroundColor: borderColor,
          opacity: 0.2,
          marginBottom: lineHeight - 2,
          borderRadius: 1,
        }}
      />
    );
  }

  return (
    <div
      style={{
        position: 'absolute',
        left: x,
        top: y,
        width,
        height,
        opacity,
        transform: `scale(${scale})`,
        transformOrigin: 'center center',
      }}
    >
      {/* File container */}
      <div
        style={{
          width: '100%',
          height: '100%',
          border: `2px solid ${borderColor}`,
          borderRadius: 6,
          backgroundColor: 'rgba(255,255,255,0.03)',
          padding: '20px 16px 16px',
          boxSizing: 'border-box',
          overflow: 'hidden',
          position: 'relative',
        }}
      >
        {lines}
      </div>

      {/* Badge */}
      <div
        style={{
          position: 'absolute',
          top: -10,
          left: width / 2 - 32,
          backgroundColor: borderColor,
          color: '#0A0F1A',
          fontFamily: 'Inter, sans-serif',
          fontSize: 11,
          fontWeight: 600,
          padding: '2px 10px',
          borderRadius: 10,
          whiteSpace: 'nowrap',
        }}
      >
        {badge}
      </div>
    </div>
  );
};

export default MiniPromptFile;
