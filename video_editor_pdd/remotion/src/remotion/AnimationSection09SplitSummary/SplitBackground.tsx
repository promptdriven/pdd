import React from 'react';
import { CANVAS, COLORS } from './constants';

interface SplitBackgroundProps {
  dividerX: number;
}

export const SplitBackground: React.FC<SplitBackgroundProps> = ({ dividerX }) => {
  return (
    <>
      {/* Left region: from x=0 to divider position */}
      <div
        style={{
          position: 'absolute',
          top: 0,
          left: 0,
          width: dividerX,
          height: CANVAS.height,
          backgroundColor: COLORS.leftBackground,
          opacity: COLORS.leftOpacity,
        }}
      />
      {/* Right region: from divider position to edge */}
      <div
        style={{
          position: 'absolute',
          top: 0,
          left: dividerX,
          width: CANVAS.width - dividerX,
          height: CANVAS.height,
          backgroundColor: COLORS.rightBackground,
          opacity: COLORS.rightOpacity,
        }}
      />
    </>
  );
};
