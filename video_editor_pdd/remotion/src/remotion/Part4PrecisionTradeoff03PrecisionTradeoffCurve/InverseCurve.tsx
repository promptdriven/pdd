import React, { useMemo } from 'react';
import { useCurrentFrame, Easing, interpolate } from 'remotion';
import {
  CHART_LEFT,
  CHART_BOTTOM,
  CURVE_COLOR,
  ANIM,
  generateCurvePoints,
  buildCurvePath,
} from './constants';

export const InverseCurve: React.FC = () => {
  const frame = useCurrentFrame();

  const points = useMemo(() => generateCurvePoints(200), []);
  const fullPath = useMemo(() => buildCurvePath(points), [points]);

  // Curve draw progress (frame 60-180)
  const drawProgress = interpolate(
    frame,
    [ANIM.CURVE_START, ANIM.CURVE_END],
    [0, 1],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.inOut(Easing.cubic),
    }
  );

  // Pulse effect during hold phase (frame 390-450)
  const pulsePhase = interpolate(
    frame,
    [ANIM.HOLD_START, ANIM.HOLD_END],
    [0, Math.PI * 2],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
    }
  );
  const pulseScale =
    frame >= ANIM.HOLD_START ? 1 + 0.08 * Math.sin(pulsePhase) : 1;

  // Build the partial path based on draw progress
  const visibleCount = Math.max(1, Math.floor(drawProgress * points.length));
  const visiblePoints = points.slice(0, visibleCount);
  const partialPath = buildCurvePath(visiblePoints);

  // Fill area under curve (partial)
  const fillPath = useMemo(() => {
    if (visiblePoints.length < 2) return '';
    let d = buildCurvePath(visiblePoints);
    const lastPoint = visiblePoints[visiblePoints.length - 1];
    d += ` L ${lastPoint[0]} ${CHART_BOTTOM}`;
    d += ` L ${CHART_LEFT} ${CHART_BOTTOM}`;
    d += ' Z';
    return d;
  }, [visiblePoints]);

  // Don't render before curve starts
  if (frame < ANIM.CURVE_START) return null;

  // Unique filter ID
  const glowId = 'curve-glow';

  return (
    <svg
      width={1920}
      height={1080}
      style={{ position: 'absolute', top: 0, left: 0 }}
    >
      <defs>
        {/* Glow filter */}
        <filter id={glowId} x="-20%" y="-20%" width="140%" height="140%">
          <feGaussianBlur in="SourceGraphic" stdDeviation="6" result="blur" />
          <feMerge>
            <feMergeNode in="blur" />
            <feMergeNode in="SourceGraphic" />
          </feMerge>
        </filter>

        {/* Gradient for fill under curve */}
        <linearGradient id="curve-fill-grad" x1="0" y1="0" x2="0" y2="1">
          <stop offset="0%" stopColor={CURVE_COLOR} stopOpacity={0.05} />
          <stop offset="100%" stopColor={CURVE_COLOR} stopOpacity={0} />
        </linearGradient>
      </defs>

      {/* Fill under curve */}
      {fillPath && (
        <path d={fillPath} fill="url(#curve-fill-grad)" />
      )}

      {/* Glow layer */}
      <path
        d={partialPath}
        fill="none"
        stroke={CURVE_COLOR}
        strokeWidth={3 * pulseScale}
        strokeOpacity={0.15}
        filter={`url(#${glowId})`}
      />

      {/* Main curve stroke */}
      <path
        d={partialPath}
        fill="none"
        stroke={CURVE_COLOR}
        strokeWidth={3 * pulseScale}
        strokeOpacity={1}
        strokeLinecap="round"
        strokeLinejoin="round"
      />

      {/* Full curve path (hidden, for slider reference) — rendered with 0 opacity after complete */}
      {drawProgress >= 1 && (
        <path
          id="inverse-curve-full"
          d={fullPath}
          fill="none"
          stroke="transparent"
          strokeWidth={0}
        />
      )}
    </svg>
  );
};
