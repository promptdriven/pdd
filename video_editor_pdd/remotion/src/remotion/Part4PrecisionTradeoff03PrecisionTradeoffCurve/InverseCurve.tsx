import React from 'react';
import { interpolate, useCurrentFrame, Easing } from 'remotion';
import { CHART, COLORS, TIMING, curvePoint } from './constants';

const NUM_POINTS = 200;

function generateCurvePath(): string {
  const points: { x: number; y: number }[] = [];
  for (let i = 0; i <= NUM_POINTS; i++) {
    const testCount = (i / NUM_POINTS) * 50;
    points.push(curvePoint(testCount));
  }
  return points.map((p, i) => (i === 0 ? `M ${p.x} ${p.y}` : `L ${p.x} ${p.y}`)).join(' ');
}

function generateFillPath(): string {
  const points: { x: number; y: number }[] = [];
  for (let i = 0; i <= NUM_POINTS; i++) {
    const testCount = (i / NUM_POINTS) * 50;
    points.push(curvePoint(testCount));
  }
  const pathUp = points.map((p, i) => (i === 0 ? `M ${p.x} ${p.y}` : `L ${p.x} ${p.y}`)).join(' ');
  const lastPt = points[points.length - 1];
  const firstPt = points[0];
  return `${pathUp} L ${lastPt.x} ${CHART.originY} L ${firstPt.x} ${CHART.originY} Z`;
}

export const InverseCurve: React.FC = () => {
  const frame = useCurrentFrame();

  // Curve draw progress (frames 60-180)
  const drawProgress = interpolate(
    frame,
    [TIMING.curveStart, TIMING.curveEnd],
    [0, 1],
    { extrapolateLeft: 'clamp', extrapolateRight: 'clamp', easing: Easing.inOut(Easing.cubic) }
  );

  // Pulse effect during hold (frames 390-450)
  const pulseOpacity = frame >= TIMING.holdStart
    ? 0.15 + 0.05 * Math.sin(((frame - TIMING.holdStart) / 60) * Math.PI * 2)
    : 0.15;

  const fullPath = generateCurvePath();
  const fillPath = generateFillPath();

  // Calculate total path length for dash animation
  // Approximate: we use a large value and clip
  const totalLength = 2000;
  const visibleLength = totalLength * drawProgress;

  return (
    <svg
      width={1920}
      height={1080}
      style={{ position: 'absolute', top: 0, left: 0 }}
    >
      <defs>
        {/* Glow filter */}
        <filter id="curveGlow" x="-20%" y="-20%" width="140%" height="140%">
          <feGaussianBlur in="SourceGraphic" stdDeviation="6" />
        </filter>

        {/* Fill gradient */}
        <linearGradient id="curveFillGrad" x1="0" y1="0" x2="0" y2="1">
          <stop offset="0%" stopColor={COLORS.curve} stopOpacity={0.05} />
          <stop offset="100%" stopColor={COLORS.curve} stopOpacity={0} />
        </linearGradient>

        {/* Clip path for progressive reveal */}
        <clipPath id="curveClip">
          <rect
            x={CHART.originX}
            y={0}
            width={CHART.width * drawProgress}
            height={1080}
          />
        </clipPath>
      </defs>

      {/* Fill below curve (clipped to draw progress) */}
      <path
        d={fillPath}
        fill="url(#curveFillGrad)"
        clipPath="url(#curveClip)"
        opacity={drawProgress > 0 ? 1 : 0}
      />

      {/* Glow layer */}
      <path
        d={fullPath}
        fill="none"
        stroke={COLORS.curve}
        strokeWidth={3}
        strokeDasharray={`${visibleLength} ${totalLength}`}
        filter="url(#curveGlow)"
        opacity={pulseOpacity}
      />

      {/* Main curve stroke */}
      <path
        d={fullPath}
        fill="none"
        stroke={COLORS.curve}
        strokeWidth={3}
        strokeDasharray={`${visibleLength} ${totalLength}`}
        strokeLinecap="round"
      />
    </svg>
  );
};
