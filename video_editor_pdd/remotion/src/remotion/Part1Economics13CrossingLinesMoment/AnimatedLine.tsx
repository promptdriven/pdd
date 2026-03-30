// AnimatedLine.tsx — Draws a polyline that progressively reveals along its path
import React from 'react';
import { useCurrentFrame, interpolate, Easing } from 'remotion';
import { yearToX, costToY } from './constants';

interface DataPoint {
  year: number;
  cost: number;
}

interface AnimatedLineProps {
  /** Array of { year, cost } data points */
  data: DataPoint[];
  /** Stroke color */
  color: string;
  /** Stroke width in px */
  strokeWidth: number;
  /** Frame at which the draw animation starts */
  drawStart: number;
  /** Number of frames to animate the full draw */
  drawDuration: number;
  /** Whether to use dashed stroke */
  dashed?: boolean;
  /** Whether to clip reveal to a specific data index range driven by progress */
  revealFromIndex?: number;
  /** Static render (no animation): draw full line from frame 0 */
  isStatic?: boolean;
}

export const AnimatedLine: React.FC<AnimatedLineProps> = ({
  data,
  color,
  strokeWidth,
  drawStart,
  drawDuration,
  dashed = false,
  revealFromIndex,
  isStatic = false,
}) => {
  const frame = useCurrentFrame();

  // Convert data to pixel coords
  const pixelPoints = data.map((d) => ({
    x: yearToX(d.year),
    y: costToY(d.cost),
  }));

  // Compute cumulative segment lengths
  const segLengths: number[] = [0];
  for (let i = 1; i < pixelPoints.length; i++) {
    const dx = pixelPoints[i].x - pixelPoints[i - 1].x;
    const dy = pixelPoints[i].y - pixelPoints[i - 1].y;
    segLengths.push(segLengths[i - 1] + Math.sqrt(dx * dx + dy * dy));
  }
  const totalLength = segLengths[segLengths.length - 1];

  // Calculate how much of the line to reveal
  let revealFraction: number;
  if (isStatic) {
    revealFraction = 1;
  } else {
    const startIdx = revealFromIndex ?? 0;
    const startLength = segLengths[startIdx] ?? 0;
    const animatableLength = totalLength - startLength;

    const progress = interpolate(
      frame,
      [drawStart, drawStart + drawDuration],
      [0, 1],
      {
        extrapolateLeft: 'clamp',
        extrapolateRight: 'clamp',
        easing: Easing.in(Easing.quad),
      }
    );

    revealFraction = (startLength + progress * animatableLength) / totalLength;
  }

  // Build SVG path
  const pathD = pixelPoints
    .map((p, i) => `${i === 0 ? 'M' : 'L'} ${p.x} ${p.y}`)
    .join(' ');

  const dashOffset = totalLength * (1 - revealFraction);

  return (
    <svg
      width={1920}
      height={1080}
      viewBox="0 0 1920 1080"
      style={{ position: 'absolute', top: 0, left: 0 }}
    >
      <path
        d={pathD}
        fill="none"
        stroke={color}
        strokeWidth={strokeWidth}
        strokeLinecap="round"
        strokeLinejoin="round"
        strokeDasharray={dashed ? `${totalLength}` : `${totalLength}`}
        strokeDashoffset={dashOffset}
        style={
          dashed
            ? {
                strokeDasharray: `8 4`,
                // We use clip to reveal instead for dashed lines
              }
            : undefined
        }
      />
      {/* For dashed lines, overlay with proper dash pattern using a clip */}
      {dashed && (
        <>
          <defs>
            <clipPath id={`clip-reveal-${color.replace('#', '')}`}>
              <rect
                x={0}
                y={0}
                width={
                  pixelPoints.length > 0
                    ? pixelPoints[0].x +
                      revealFraction *
                        (pixelPoints[pixelPoints.length - 1].x - pixelPoints[0].x)
                    : 0
                }
                height={1080}
              />
            </clipPath>
          </defs>
          <path
            d={pathD}
            fill="none"
            stroke={color}
            strokeWidth={strokeWidth}
            strokeLinecap="round"
            strokeLinejoin="round"
            strokeDasharray="8 4"
            clipPath={`url(#clip-reveal-${color.replace('#', '')})`}
          />
        </>
      )}
    </svg>
  );
};

export default AnimatedLine;
