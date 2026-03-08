import React from 'react';
import { useCurrentFrame, interpolate, Easing } from 'remotion';
import { CANVAS, COLORS, LOGO, TIMING } from './constants';

export const LogoTriangle: React.FC = () => {
  const frame = useCurrentFrame();

  const scale = interpolate(
    frame,
    [TIMING.triangleStart, TIMING.triangleEnd],
    [0, 1],
    { extrapolateLeft: 'clamp', extrapolateRight: 'clamp', easing: Easing.out(Easing.back(1.4)) },
  );

  const opacity = interpolate(
    frame,
    [TIMING.triangleStart, TIMING.triangleStart + 8],
    [0, 1],
    { extrapolateLeft: 'clamp', extrapolateRight: 'clamp' },
  );

  // Play-button triangle points (pointing right), centered at LOGO.cx, LOGO.cy
  const halfH = LOGO.triangleSize / 2;
  const halfW = (LOGO.triangleSize * 0.866) / 2; // equilateral-ish
  const offsetX = 15; // slight right shift so it looks centered visually

  const x1 = LOGO.cx - halfW + offsetX;
  const y1 = LOGO.cy - halfH;
  const x2 = LOGO.cx + halfW + offsetX;
  const y2 = LOGO.cy;
  const x3 = LOGO.cx - halfW + offsetX;
  const y3 = LOGO.cy + halfH;

  const points = `${x1},${y1} ${x2},${y2} ${x3},${y3}`;

  return (
    <svg
      width={CANVAS.width}
      height={CANVAS.height}
      style={{ position: 'absolute', top: 0, left: 0 }}
    >
      <defs>
        <linearGradient id="triangleGrad" x1="0%" y1="0%" x2="100%" y2="100%">
          <stop offset="0%" stopColor={COLORS.logoBlue} />
          <stop offset="100%" stopColor={COLORS.accentCyan} />
        </linearGradient>
      </defs>
      <polygon
        points={points}
        fill="url(#triangleGrad)"
        opacity={opacity}
        transform={`translate(${LOGO.cx * (1 - scale)}, ${LOGO.cy * (1 - scale)}) scale(${scale})`}
      />
    </svg>
  );
};
