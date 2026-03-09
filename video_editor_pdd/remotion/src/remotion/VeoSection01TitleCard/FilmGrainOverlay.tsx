import React from 'react';
import { AbsoluteFill, useCurrentFrame, random } from 'remotion';

export const FilmGrainOverlay: React.FC = () => {
  const frame = useCurrentFrame();

  const grainElements = React.useMemo(() => {
    const elements: React.CSSProperties[] = [];
    const cols = 48;
    const rows = 27;
    for (let i = 0; i < cols * rows; i++) {
      const col = i % cols;
      const row = Math.floor(i / cols);
      elements.push({
        position: 'absolute' as const,
        left: `${(col / cols) * 100}%`,
        top: `${(row / rows) * 100}%`,
        width: 1920 / cols,
        height: 1080 / rows,
      });
    }
    return elements;
  }, []);

  return (
    <AbsoluteFill style={{ opacity: 0.03, mixBlendMode: 'overlay' }}>
      {grainElements.map((style, i) => {
        const brightness = random(`grain-${i}-${frame % 3}`) > 0.5 ? 1 : 0;
        return (
          <div
            key={i}
            style={{
              ...style,
              backgroundColor: `rgba(255,255,255,${brightness * 0.3})`,
            }}
          />
        );
      })}
    </AbsoluteFill>
  );
};
