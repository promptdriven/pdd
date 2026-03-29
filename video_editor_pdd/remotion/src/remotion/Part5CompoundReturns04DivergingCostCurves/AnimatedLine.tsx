import React, { useMemo } from 'react';
import { interpolate, useCurrentFrame, Easing } from 'remotion';
import {
  CHART_LEFT,
  CHART_BOTTOM,
  CHART_WIDTH,
  CHART_HEIGHT,
  X_MIN,
  X_MAX,
  Y_MIN,
  Y_MAX,
} from './constants';

interface DataPoint {
  x: number;
  y: number;
}

interface AnimatedLineProps {
  data: DataPoint[];
  color: string;
  strokeWidth: number;
  startFrame: number;
  drawDuration: number;
  easingType: 'easeIn' | 'easeOut';
}

/** Map data x-coordinate to pixel x-position */
const xToPixel = (x: number) =>
  CHART_LEFT + ((x - X_MIN) / (X_MAX - X_MIN)) * CHART_WIDTH;

/** Map data y-coordinate to pixel y-position (y=0 at bottom, y=1 at top) */
const yToPixelCorrected = (y: number) =>
  CHART_BOTTOM - ((y - Y_MIN) / (Y_MAX - Y_MIN)) * CHART_HEIGHT;

export const AnimatedLine: React.FC<AnimatedLineProps> = ({
  data,
  color,
  strokeWidth,
  startFrame,
  drawDuration,
  easingType,
}) => {
  const frame = useCurrentFrame();

  // Build the SVG path from data points
  const fullPath = useMemo(() => {
    if (data.length === 0) return '';
    const parts = data.map((pt, i) => {
      const px = xToPixel(pt.x);
      const py = yToPixelCorrected(pt.y);
      return i === 0 ? `M ${px} ${py}` : `L ${px} ${py}`;
    });
    return parts.join(' ');
  }, [data]);

  // Calculate total path length for stroke-dasharray animation
  // Approximate length by summing segment distances
  const totalLength = useMemo(() => {
    let len = 0;
    for (let i = 1; i < data.length; i++) {
      const dx = xToPixel(data[i].x) - xToPixel(data[i - 1].x);
      const dy =
        yToPixelCorrected(data[i].y) - yToPixelCorrected(data[i - 1].y);
      len += Math.sqrt(dx * dx + dy * dy);
    }
    return len;
  }, [data]);

  // Progress: 0 -> 1 over drawDuration frames starting at startFrame
  const easingFn =
    easingType === 'easeIn' ? Easing.in(Easing.quad) : Easing.out(Easing.quad);

  const progress = interpolate(
    frame,
    [startFrame, startFrame + drawDuration],
    [0, 1],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: easingFn,
    }
  );

  const dashOffset = totalLength * (1 - progress);

  return (
    <svg
      width={1920}
      height={1080}
      style={{ position: 'absolute', top: 0, left: 0 }}
    >
      <path
        d={fullPath}
        fill="none"
        stroke={color}
        strokeWidth={strokeWidth}
        strokeLinecap="round"
        strokeLinejoin="round"
        strokeDasharray={totalLength}
        strokeDashoffset={dashOffset}
      />
    </svg>
  );
};

// Also export the coordinate helpers for use in GapRegion
export { xToPixel, yToPixelCorrected };

export default AnimatedLine;
