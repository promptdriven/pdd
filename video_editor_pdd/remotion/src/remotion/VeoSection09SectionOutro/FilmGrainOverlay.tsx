import React, { useMemo } from 'react';
import { useCurrentFrame } from 'remotion';
import { CANVAS } from './constants';

export const FilmGrainOverlay: React.FC = () => {
  const frame = useCurrentFrame();

  // Generate pseudo-random grain pattern that changes each frame
  const grainStyle = useMemo(() => {
    const size = 200;
    const offsetX = ((frame * 73) % size) - size;
    const offsetY = ((frame * 47) % size) - size;
    return {
      backgroundPosition: `${offsetX}px ${offsetY}px`,
    };
  }, [frame]);

  return (
    <div
      style={{
        position: 'absolute',
        left: 0,
        top: 0,
        width: CANVAS.width,
        height: CANVAS.height,
        opacity: 0.03,
        backgroundImage:
          'url("data:image/svg+xml,%3Csvg viewBox=\'0 0 256 256\' xmlns=\'http://www.w3.org/2000/svg\'%3E%3Cfilter id=\'noise\'%3E%3CfeTurbulence type=\'fractalNoise\' baseFrequency=\'0.9\' numOctaves=\'4\' stitchTiles=\'stitch\'/%3E%3C/filter%3E%3Crect width=\'100%25\' height=\'100%25\' filter=\'url(%23noise)\'/%3E%3C/svg%3E")',
        backgroundSize: '200px 200px',
        ...grainStyle,
        pointerEvents: 'none',
        mixBlendMode: 'overlay',
      }}
    />
  );
};
