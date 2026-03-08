import React from 'react';
import { useCurrentFrame, interpolate, Easing } from 'remotion';
import { CANVAS, ORBIT_LABELS } from './constants';

export const OrbitLabels: React.FC = () => {
  const frame = useCurrentFrame();

  // Fade in labels
  const opacity = interpolate(
    frame,
    [ORBIT_LABELS.fadeInStart, ORBIT_LABELS.fadeInEnd],
    [0, 1],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.out(Easing.poly(3)),
    }
  );

  if (frame < ORBIT_LABELS.fadeInStart) return null;

  // Rotation: 0.5 degrees per frame starting from fadeInStart
  const rotationDeg = (frame - ORBIT_LABELS.fadeInStart) * ORBIT_LABELS.rotationSpeed;

  return (
    <svg
      width={CANVAS.width}
      height={CANVAS.height}
      style={{ position: 'absolute', top: 0, left: 0 }}
    >
      {ORBIT_LABELS.labels.map((label, i) => {
        // Evenly space labels around the circle (120 degrees apart)
        const baseAngleDeg = (360 / ORBIT_LABELS.labels.length) * i - 90; // start from top
        const angleDeg = baseAngleDeg + rotationDeg;
        const angleRad = (angleDeg * Math.PI) / 180;

        const x = CANVAS.centerX + Math.cos(angleRad) * (ORBIT_LABELS.radius + 30);
        const y = CANVAS.centerY + Math.sin(angleRad) * (ORBIT_LABELS.radius + 30);

        return (
          <text
            key={i}
            x={x}
            y={y}
            textAnchor="middle"
            dominantBaseline="middle"
            fill={ORBIT_LABELS.color}
            fontSize={ORBIT_LABELS.fontSize}
            fontFamily={ORBIT_LABELS.fontFamily}
            opacity={opacity}
          >
            {label}
          </text>
        );
      })}
    </svg>
  );
};
