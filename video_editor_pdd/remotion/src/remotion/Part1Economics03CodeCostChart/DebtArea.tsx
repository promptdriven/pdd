import React, { useMemo } from 'react';
import { useCurrentFrame, interpolate, Easing } from 'remotion';
import {
  AMBER_LINE_COLOR,
  DEBT_FILL_OPACITY,
  IMMEDIATE_PATCH_DATA,
  TOTAL_COST_DEBT_DATA,
  dataToPixelX,
  dataToPixelY,
  type DataPoint,
} from './constants';

interface DebtAreaProps {
  fillStart: number;
  fillDuration: number;
}

/**
 * Build a closed polygon path: forward along the upper series,
 * then backward along the lower series.
 */
function buildAreaPath(upper: DataPoint[], lower: DataPoint[]): string {
  const parts: string[] = [];

  // Forward along upper
  upper.forEach((pt, i) => {
    const px = dataToPixelX(pt.x);
    const py = dataToPixelY(pt.y);
    parts.push(`${i === 0 ? 'M' : 'L'} ${px} ${py}`);
  });

  // Backward along lower
  for (let i = lower.length - 1; i >= 0; i--) {
    const px = dataToPixelX(lower[i].x);
    const py = dataToPixelY(lower[i].y);
    parts.push(`L ${px} ${py}`);
  }

  parts.push('Z');
  return parts.join(' ');
}

export const DebtArea: React.FC<DebtAreaProps> = ({
  fillStart,
  fillDuration,
}) => {
  const frame = useCurrentFrame();

  const areaPath = useMemo(
    () => buildAreaPath(TOTAL_COST_DEBT_DATA, IMMEDIATE_PATCH_DATA),
    [],
  );

  const fillProgress = interpolate(
    frame,
    [fillStart, fillStart + fillDuration],
    [0, 1],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.out(Easing.quad),
    },
  );

  const opacity = DEBT_FILL_OPACITY * fillProgress;

  // "Technical debt" label appears after fill completes
  const labelOpacity = interpolate(
    frame,
    [fillStart + fillDuration, fillStart + fillDuration + 30],
    [0, 0.85],
    { extrapolateLeft: 'clamp', extrapolateRight: 'clamp' },
  );

  // Midpoint for label placement
  const midIdx = Math.floor(TOTAL_COST_DEBT_DATA.length / 2);
  const labelX = dataToPixelX(TOTAL_COST_DEBT_DATA[midIdx].x);
  const labelY =
    (dataToPixelY(TOTAL_COST_DEBT_DATA[midIdx].y) +
      dataToPixelY(IMMEDIATE_PATCH_DATA[midIdx].y)) /
    2;

  return (
    <svg
      width={1920}
      height={1080}
      style={{ position: 'absolute', top: 0, left: 0 }}
    >
      <path d={areaPath} fill={AMBER_LINE_COLOR} opacity={opacity} />

      {labelOpacity > 0 && (
        <text
          x={labelX}
          y={labelY + 4}
          fill={AMBER_LINE_COLOR}
          fontSize={13}
          fontFamily="Inter, sans-serif"
          fontWeight={600}
          opacity={labelOpacity}
          textAnchor="middle"
        >
          Technical Debt
        </text>
      )}
    </svg>
  );
};

export default DebtArea;
