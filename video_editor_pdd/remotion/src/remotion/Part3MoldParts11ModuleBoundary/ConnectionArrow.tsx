import React from "react";
import { useCurrentFrame, interpolate, Easing } from "remotion";

interface ConnectionArrowProps {
  fromX: number;
  fromY: number;
  toX: number;
  toY: number;
  color: string;
  opacity: number;
  strokeWidth: number;
  dashed: boolean;
  /** Frame at which this arrow starts drawing (relative to component mount) */
  drawStart: number;
  drawDuration?: number;
  /** Extra opacity multiplier for dimming */
  opacityMultiplier?: number;
}

/**
 * Shortens a line segment by `margin` px from each end
 * so arrows don't overlap the module boxes.
 */
function shortenLine(
  x1: number,
  y1: number,
  x2: number,
  y2: number,
  margin: number
): [number, number, number, number] {
  const dx = x2 - x1;
  const dy = y2 - y1;
  const len = Math.sqrt(dx * dx + dy * dy);
  if (len === 0) return [x1, y1, x2, y2];
  const ux = dx / len;
  const uy = dy / len;
  return [
    x1 + ux * margin,
    y1 + uy * margin,
    x2 - ux * margin,
    y2 - uy * margin,
  ];
}

export const ConnectionArrow: React.FC<ConnectionArrowProps> = ({
  fromX,
  fromY,
  toX,
  toY,
  color,
  opacity,
  strokeWidth,
  dashed,
  drawStart,
  drawDuration = 20,
  opacityMultiplier = 1,
}) => {
  const frame = useCurrentFrame();

  const [sx, sy, ex, ey] = shortenLine(fromX, fromY, toX, toY, 60);

  const dx = ex - sx;
  const dy = ey - sy;
  const lineLen = Math.sqrt(dx * dx + dy * dy);

  // Draw progress: 0 → 1
  const drawProgress = interpolate(
    frame,
    [drawStart, drawStart + drawDuration],
    [0, 1],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.out(Easing.quad),
    }
  );

  // Arrowhead points
  const angle = Math.atan2(dy, dx);
  const headLen = 8;
  const headAngle = Math.PI / 6;

  const ah1x = ex - headLen * Math.cos(angle - headAngle);
  const ah1y = ey - headLen * Math.sin(angle - headAngle);
  const ah2x = ex - headLen * Math.cos(angle + headAngle);
  const ah2y = ey - headLen * Math.sin(angle + headAngle);

  // Stroke-dasharray / dashoffset for draw animation
  const dashArray = dashed ? "6 4" : `${lineLen}`;
  const dashOffset = dashed ? 0 : lineLen * (1 - drawProgress);

  const arrowOpacity = drawProgress * opacity * opacityMultiplier;

  return (
    <g opacity={arrowOpacity}>
      <line
        x1={sx}
        y1={sy}
        x2={ex}
        y2={ey}
        stroke={color}
        strokeWidth={strokeWidth}
        strokeDasharray={dashArray}
        strokeDashoffset={dashed ? undefined : dashOffset}
      />
      {/* Arrowhead towards "to" */}
      {drawProgress > 0.5 && (
        <polygon
          points={`${ex},${ey} ${ah1x},${ah1y} ${ah2x},${ah2y}`}
          fill={color}
          opacity={interpolate(drawProgress, [0.5, 1], [0, 1], {
            extrapolateLeft: "clamp",
            extrapolateRight: "clamp",
          })}
        />
      )}
    </g>
  );
};
