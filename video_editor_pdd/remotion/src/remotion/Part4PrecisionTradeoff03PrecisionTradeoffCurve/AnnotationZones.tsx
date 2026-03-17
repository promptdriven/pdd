import React from 'react';
import { useCurrentFrame, Easing, interpolate } from 'remotion';
import {
  CHART_TOP,
  CHART_BOTTOM,
  LEFT_ZONE_COLOR,
  RIGHT_ZONE_COLOR,
  CURVE_COLOR,
  ANIM,
} from './constants';

/**
 * Dense prompt icon — a miniature document with many lines
 */
const DensePromptIcon: React.FC<{ x: number; y: number; opacity: number }> = ({
  x,
  y,
  opacity,
}) => {
  const lines = 12;
  const docW = 40;
  const docH = 60;
  const lineSpacing = (docH - 10) / lines;
  return (
    <g opacity={opacity}>
      {/* Document outline */}
      <rect
        x={x - docW / 2}
        y={y - docH / 2}
        width={docW}
        height={docH}
        rx={3}
        fill="none"
        stroke={CURVE_COLOR}
        strokeWidth={1.5}
        strokeOpacity={0.5}
      />
      {/* Dense lines */}
      {Array.from({ length: lines }).map((_, i) => {
        const lineY = y - docH / 2 + 7 + i * lineSpacing;
        const lineW = i % 3 === 2 ? docW * 0.55 : docW * 0.75;
        return (
          <rect
            key={i}
            x={x - docW / 2 + 5}
            y={lineY}
            width={lineW}
            height={1.5}
            fill={CURVE_COLOR}
            fillOpacity={0.5}
            rx={0.5}
          />
        );
      })}
    </g>
  );
};

/**
 * Sparse prompt icon — a miniature document with few lines
 */
const SparsePromptIcon: React.FC<{ x: number; y: number; opacity: number }> = ({
  x,
  y,
  opacity,
}) => {
  const lines = 3;
  const docW = 40;
  const docH = 30;
  const lineSpacing = (docH - 10) / lines;
  return (
    <g opacity={opacity}>
      {/* Document outline */}
      <rect
        x={x - docW / 2}
        y={y - docH / 2}
        width={docW}
        height={docH}
        rx={3}
        fill="none"
        stroke={CURVE_COLOR}
        strokeWidth={1.5}
        strokeOpacity={0.5}
      />
      {/* Sparse lines */}
      {Array.from({ length: lines }).map((_, i) => {
        const lineY = y - docH / 2 + 7 + i * lineSpacing;
        const lineW = i === 2 ? docW * 0.4 : docW * 0.65;
        return (
          <rect
            key={i}
            x={x - docW / 2 + 5}
            y={lineY}
            width={lineW}
            height={1.5}
            fill={CURVE_COLOR}
            fillOpacity={0.5}
            rx={0.5}
          />
        );
      })}
    </g>
  );
};

/**
 * Wall icons — small rectangles arranged around a point
 */
const WallIcons: React.FC<{
  cx: number;
  cy: number;
  count: number;
  opacity: number;
}> = ({ cx, cy, count, opacity }) => {
  const radius = 35;
  return (
    <g opacity={opacity}>
      {Array.from({ length: count }).map((_, i) => {
        const angle = (i / count) * Math.PI * 2 - Math.PI / 2;
        const wx = cx + Math.cos(angle) * radius;
        const wy = cy + Math.sin(angle) * radius;
        return (
          <rect
            key={i}
            x={wx - 3}
            y={wy - 10}
            width={6}
            height={20}
            rx={1}
            fill={LEFT_ZONE_COLOR}
            fillOpacity={0.5}
          />
        );
      })}
    </g>
  );
};

export const AnnotationZones: React.FC = () => {
  const frame = useCurrentFrame();

  // Left zone fade-in (180-210)
  const leftOpacity = interpolate(
    frame,
    [ANIM.LEFT_ZONE_START, ANIM.LEFT_ZONE_START + 30],
    [0, 1],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.out(Easing.quad),
    }
  );

  // Right zone fade-in (240-270)
  const rightOpacity = interpolate(
    frame,
    [ANIM.RIGHT_ZONE_START, ANIM.RIGHT_ZONE_START + 30],
    [0, 1],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.out(Easing.quad),
    }
  );

  // During slider travel (300-390), left dims, right brightens
  const leftDim = interpolate(
    frame,
    [ANIM.SLIDER_START, ANIM.SLIDER_END],
    [1, 0.5],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.inOut(Easing.cubic),
    }
  );

  const rightBrighten = interpolate(
    frame,
    [ANIM.SLIDER_START + 45, ANIM.SLIDER_END],
    [1, 1.4],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.inOut(Easing.cubic),
    }
  );

  const finalLeftOpacity = leftOpacity * leftDim;
  const finalRightOpacity = Math.min(rightOpacity * rightBrighten, 1);

  return (
    <svg
      width={1920}
      height={1080}
      style={{ position: 'absolute', top: 0, left: 0 }}
    >
      {/* Left zone highlight — few tests */}
      {frame >= ANIM.LEFT_ZONE_START && (
        <g opacity={finalLeftOpacity}>
          {/* Background highlight rectangle */}
          <rect
            x={280}
            y={CHART_TOP}
            width={200}
            height={CHART_BOTTOM - CHART_TOP}
            fill={LEFT_ZONE_COLOR}
            fillOpacity={0.04}
          />
          {/* Dense prompt icon */}
          <DensePromptIcon x={380} y={400} opacity={1} />
          {/* Label */}
          <text
            x={380}
            y={490}
            textAnchor="middle"
            fill={LEFT_ZONE_COLOR}
            fillOpacity={0.6}
            fontSize={11}
            fontFamily="Inter, sans-serif"
          >
            Detailed prompt required
          </text>
        </g>
      )}

      {/* Right zone highlight — many tests */}
      {frame >= ANIM.RIGHT_ZONE_START && (
        <g opacity={finalRightOpacity}>
          {/* Background highlight rectangle */}
          <rect
            x={1300}
            y={CHART_TOP}
            width={300}
            height={CHART_BOTTOM - CHART_TOP}
            fill={RIGHT_ZONE_COLOR}
            fillOpacity={0.04}
          />
          {/* Sparse prompt icon */}
          <SparsePromptIcon x={1450} y={650} opacity={1} />
          {/* Wall icons surrounding the sparse prompt */}
          <WallIcons cx={1450} cy={650} count={8} opacity={1} />
          {/* Label */}
          <text
            x={1450}
            y={720}
            textAnchor="middle"
            fill={RIGHT_ZONE_COLOR}
            fillOpacity={0.6}
            fontSize={11}
            fontFamily="Inter, sans-serif"
          >
            Intent is enough
          </text>
        </g>
      )}
    </svg>
  );
};
