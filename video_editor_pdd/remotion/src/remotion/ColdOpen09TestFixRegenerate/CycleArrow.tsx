import React from 'react';
import { interpolate, useCurrentFrame, Easing } from 'remotion';

interface CycleArrowProps {
  fromAngleDeg: number;
  toAngleDeg: number;
  centerX: number;
  centerY: number;
  radius: number;
  color: string;
  appearFrame: number;
  travelFrame: number;
  travelDuration: number;
}

const CycleArrow: React.FC<CycleArrowProps> = ({
  fromAngleDeg,
  toAngleDeg,
  centerX,
  centerY,
  radius,
  color,
  appearFrame,
  travelFrame,
  travelDuration,
}) => {
  const frame = useCurrentFrame();

  const opacity = interpolate(frame, [appearFrame, appearFrame + 10], [0, 0.85], {
    extrapolateLeft: 'clamp',
    extrapolateRight: 'clamp',
  });

  // Animated dot traveling along arc
  const dotProgress = interpolate(
    frame,
    [travelFrame, travelFrame + travelDuration],
    [0, 1],
    { extrapolateLeft: 'clamp', extrapolateRight: 'clamp', easing: Easing.inOut(Easing.poly(3)) },
  );

  // Calculate arc path
  const arcRadius = radius + 40;
  const fromRad = (fromAngleDeg * Math.PI) / 180;
  const toRad = (toAngleDeg * Math.PI) / 180;

  // Mid-point along arc for the curved path
  const midAngle = fromRad + (toRad - fromRad > 0 ? 1 : -1) *
    Math.abs(toRad - fromRad) * 0.5;

  // SVG arc
  const startX = centerX + arcRadius * Math.cos(fromRad);
  const startY = centerY + arcRadius * Math.sin(fromRad);
  const endX = centerX + arcRadius * Math.cos(toRad);
  const endY = centerY + arcRadius * Math.sin(toRad);

  // Determine if we need a large arc
  let angleDiff = toAngleDeg - fromAngleDeg;
  if (angleDiff < 0) angleDiff += 360;
  const largeArc = angleDiff > 180 ? 1 : 0;

  // Arrow head angle
  const arrowAngle = toRad + Math.PI / 2;
  const arrowSize = 10;

  // Traveling dot position
  const dotAngle = fromRad + ((toRad - fromRad + 2 * Math.PI) % (2 * Math.PI)) * dotProgress;
  const dotX = centerX + arcRadius * Math.cos(dotAngle);
  const dotY = centerY + arcRadius * Math.sin(dotAngle);

  const pathD = `M ${startX} ${startY} A ${arcRadius} ${arcRadius} 0 ${largeArc} 1 ${endX} ${endY}`;

  return (
    <svg
      style={{
        position: 'absolute',
        left: 0,
        top: 0,
        width: '100%',
        height: '100%',
        pointerEvents: 'none',
      }}
    >
      {/* Arc path */}
      <path
        d={pathD}
        fill="none"
        stroke={color}
        strokeWidth="2.5"
        strokeDasharray="8 6"
        opacity={opacity}
      />
      {/* Arrow head */}
      <polygon
        points={`
          ${endX},${endY}
          ${endX - arrowSize * Math.cos(arrowAngle - 0.4)},${endY - arrowSize * Math.sin(arrowAngle - 0.4)}
          ${endX - arrowSize * Math.cos(arrowAngle + 0.4)},${endY - arrowSize * Math.sin(arrowAngle + 0.4)}
        `}
        fill={color}
        opacity={opacity}
      />
      {/* Traveling dot */}
      {dotProgress > 0 && dotProgress < 1 && (
        <circle
          cx={dotX}
          cy={dotY}
          r={5}
          fill={color}
          opacity={0.95}
        >
          <animate
            attributeName="r"
            values="4;7;4"
            dur="0.6s"
            repeatCount="indefinite"
          />
        </circle>
      )}
    </svg>
  );
};

export default CycleArrow;
