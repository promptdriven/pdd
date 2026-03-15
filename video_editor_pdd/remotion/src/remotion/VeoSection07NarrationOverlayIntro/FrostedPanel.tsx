import React from 'react';
import { useCurrentFrame, interpolate, Easing } from 'remotion';
import { COLORS, PANEL, ANIMATION, BASE_CANVAS } from './constants';

export const FrostedPanel: React.FC<{ children: React.ReactNode }> = ({
  children,
}) => {
  const frame = useCurrentFrame();

  // Frame 0–8: Slide up from bottom (y=1080 → y=880)
  const panelY = interpolate(
    frame,
    [ANIMATION.panelSlideStart, ANIMATION.panelSlideEnd],
    [BASE_CANVAS.height, BASE_CANVAS.height - PANEL.height],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.out(Easing.cubic),
    },
  );

  return (
    <div
      style={{
        position: 'absolute',
        left: 0,
        top: panelY,
        width: BASE_CANVAS.width,
        height: PANEL.height,
        backgroundColor: COLORS.panelBg,
        backdropFilter: 'blur(20px)',
        WebkitBackdropFilter: 'blur(20px)',
        borderTop: `${PANEL.borderTopWidth}px solid ${COLORS.gold}`,
      }}
    >
      {children}
    </div>
  );
};
