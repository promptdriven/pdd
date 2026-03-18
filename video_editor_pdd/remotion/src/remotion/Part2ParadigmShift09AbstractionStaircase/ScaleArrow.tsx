// ScaleArrow.tsx — "Couldn't scale" arrow with tension lines between steps
import React from 'react';
import { useCurrentFrame, Easing, interpolate } from 'remotion';
import { COLORS, OPACITIES, STEP_WIDTH } from './constants';

interface ScaleArrowProps {
  fromX: number;
  fromY: number;
  toX: number;
  toY: number;
  startFrame: number;
  dramatic?: boolean;
}

const ScaleArrow: React.FC<ScaleArrowProps> = ({
  fromX,
  fromY,
  toX,
  toY,
  startFrame,
  dramatic = false,
}) => {
  const frame = useCurrentFrame();

  // Arrow draw progress
  const arrowProgress = interpolate(
    frame,
    [startFrame, startFrame + 15],
    [0, 1],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.inOut(Easing.cubic),
    },
  );

  // Tension lines radiate outward from origin step
  const tensionProgress = interpolate(
    frame,
    [startFrame, startFrame + 8],
    [0, 1],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.out(Easing.exp),
    },
  );

  // Label fade-in
  const labelOpacity = interpolate(
    frame,
    [startFrame + 8, startFrame + 18],
    [0, OPACITIES.arrowLabel],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
    },
  );

  if (arrowProgress <= 0) return null;

  // Arrow starts from right side of "from" step, curves up to left side of "to" step
  const ax = fromX + STEP_WIDTH - 20;
  const ay = fromY + 20;
  const bx = toX + 20;
  const by = toY + 60;

  // Control point for the curve (arches upward)
  const cx = (ax + bx) / 2;
  const cy = Math.min(ay, by) - 40;

  // Create path for animated drawing
  const pathD = `M ${ax} ${ay} Q ${cx} ${cy} ${bx} ${by}`;

  // Tension line angles (radiating from origin)
  const tensionLineCount = dramatic ? 5 : 3;
  const tensionLength = (dramatic ? 25 : 18) * tensionProgress;
  const tensionBaseAngle = -45; // degrees, pointing upper-right
  const tensionSpread = dramatic ? 60 : 40;

  return (
    <svg
      style={{
        position: 'absolute',
        left: 0,
        top: 0,
        width: 1920,
        height: 1080,
        pointerEvents: 'none',
      }}
    >
      {/* Tension lines radiating from the origin step */}
      {Array.from({ length: tensionLineCount }).map((_, i) => {
        const angle =
          ((tensionBaseAngle - tensionSpread / 2 +
            (tensionSpread / (tensionLineCount - 1)) * i) *
            Math.PI) /
          180;
        const lx1 = ax;
        const ly1 = ay;
        const lx2 = ax + Math.cos(angle) * tensionLength;
        const ly2 = ay + Math.sin(angle) * tensionLength;
        return (
          <line
            key={i}
            x1={lx1}
            y1={ly1}
            x2={lx2}
            y2={ly2}
            stroke={COLORS.arrowRed}
            strokeWidth={1.5}
            opacity={OPACITIES.tensionLines * tensionProgress}
          />
        );
      })}

      {/* Arrow path */}
      <path
        d={pathD}
        fill="none"
        stroke={COLORS.arrowRed}
        strokeWidth={1.5}
        opacity={OPACITIES.arrowBody}
        strokeDasharray={500}
        strokeDashoffset={500 * (1 - arrowProgress)}
      />

      {/* Arrowhead */}
      {arrowProgress > 0.8 && (
        <polygon
          points={`${bx},${by} ${bx - 8},${by - 6} ${bx - 4},${by + 4}`}
          fill={COLORS.arrowRed}
          opacity={OPACITIES.arrowBody * interpolate(arrowProgress, [0.8, 1], [0, 1], { extrapolateLeft: 'clamp', extrapolateRight: 'clamp' })}
        />
      )}

      {/* "Couldn't scale" label */}
      <text
        x={cx}
        y={cy - 8}
        fill={COLORS.arrowRed}
        fontSize={9}
        fontFamily="Inter, sans-serif"
        textAnchor="middle"
        opacity={labelOpacity}
      >
        Couldn&apos;t scale
      </text>
    </svg>
  );
};

export default ScaleArrow;
