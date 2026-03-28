import React from 'react';
import { useCurrentFrame, interpolate, Easing } from 'remotion';
import { ANNOTATION_SIZE, ANNOTATION_DRAW_DURATION } from './constants';

interface AnnotationArrowProps {
  fromX: number;
  fromY: number;
  toX: number;
  toY: number;
  label: string;
  color: string;
  labelOpacity: number;
  startFrame: number;
}

const AnnotationArrow: React.FC<AnnotationArrowProps> = ({
  fromX,
  fromY,
  toX,
  toY,
  label,
  color,
  labelOpacity,
  startFrame,
}) => {
  const frame = useCurrentFrame();

  const drawProgress = interpolate(
    frame,
    [startFrame, startFrame + ANNOTATION_DRAW_DURATION],
    [0, 1],
    { extrapolateLeft: 'clamp', extrapolateRight: 'clamp', easing: Easing.out(Easing.quad) }
  );

  if (drawProgress <= 0) return null;

  const arrowLength = toX - fromX;
  const currentEndX = fromX + arrowLength * drawProgress;

  // Arrowhead dimensions
  const arrowHeadSize = 8;

  return (
    <div
      style={{
        position: 'absolute',
        left: 0,
        top: 0,
        width: '100%',
        height: '100%',
        pointerEvents: 'none',
      }}
    >
      {/* Arrow line using SVG */}
      <svg
        style={{ position: 'absolute', left: 0, top: 0, width: '100%', height: '100%' }}
        viewBox="0 0 1920 1080"
      >
        {/* Arrow line */}
        <line
          x1={fromX}
          y1={fromY}
          x2={currentEndX}
          y2={toY}
          stroke={color}
          strokeWidth={2}
          opacity={labelOpacity}
        />
        {/* Arrowhead */}
        {drawProgress > 0.5 && (
          <polygon
            points={`${toX},${toY} ${toX - arrowHeadSize},${toY - arrowHeadSize / 2} ${toX - arrowHeadSize},${toY + arrowHeadSize / 2}`}
            fill={color}
            opacity={labelOpacity * drawProgress}
          />
        )}
      </svg>

      {/* Label text */}
      <div
        style={{
          position: 'absolute',
          left: fromX - 160,
          top: fromY - 10,
          fontFamily: 'Inter, sans-serif',
          fontSize: ANNOTATION_SIZE,
          fontWeight: 400,
          color,
          opacity: labelOpacity * drawProgress,
          whiteSpace: 'nowrap',
          textAlign: 'right',
          width: 150,
        }}
      >
        {label}
      </div>
    </div>
  );
};

export default AnnotationArrow;
