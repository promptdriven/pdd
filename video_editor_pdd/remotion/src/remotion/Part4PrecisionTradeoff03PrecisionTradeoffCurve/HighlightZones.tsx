import React from 'react';
import { interpolate, useCurrentFrame, Easing } from 'remotion';
import { CHART, COLORS, TIMING } from './constants';

/** Dense prompt document icon — many horizontal lines */
const DensePromptIcon: React.FC<{ x: number; y: number; opacity: number }> = ({ x, y, opacity }) => {
  const lines = 12;
  const docW = 40;
  const docH = 60;
  return (
    <g opacity={opacity}>
      {/* Document border */}
      <rect
        x={x - docW / 2}
        y={y - docH / 2}
        width={docW}
        height={docH}
        rx={2}
        fill="none"
        stroke={COLORS.curve}
        strokeWidth={1}
        strokeOpacity={0.3}
      />
      {/* Lines inside */}
      {Array.from({ length: lines }).map((_, i) => {
        const lineY = y - docH / 2 + 6 + i * (docH - 12) / (lines - 1);
        const lineW = docW - 10 - (i % 3 === 2 ? 8 : 0);
        return (
          <line
            key={i}
            x1={x - docW / 2 + 5}
            y1={lineY}
            x2={x - docW / 2 + 5 + lineW}
            y2={lineY}
            stroke={COLORS.curve}
            strokeOpacity={0.5}
            strokeWidth={1.5}
          />
        );
      })}
    </g>
  );
};

/** Sparse prompt document icon — just a few lines */
const SparsePromptIcon: React.FC<{ x: number; y: number; opacity: number }> = ({ x, y, opacity }) => {
  const lines = 3;
  const docW = 40;
  const docH = 30;
  return (
    <g opacity={opacity}>
      <rect
        x={x - docW / 2}
        y={y - docH / 2}
        width={docW}
        height={docH}
        rx={2}
        fill="none"
        stroke={COLORS.curve}
        strokeWidth={1}
        strokeOpacity={0.3}
      />
      {Array.from({ length: lines }).map((_, i) => {
        const lineY = y - docH / 2 + 7 + i * 8;
        const lineW = docW - 10 - (i === 2 ? 12 : 0);
        return (
          <line
            key={i}
            x1={x - docW / 2 + 5}
            y1={lineY}
            x2={x - docW / 2 + 5 + lineW}
            y2={lineY}
            stroke={COLORS.curve}
            strokeOpacity={0.5}
            strokeWidth={1.5}
          />
        );
      })}
    </g>
  );
};

/** Wall icons — small vertical rectangles surrounding a position */
const WallIcons: React.FC<{ cx: number; cy: number; count: number; opacity: number }> = ({
  cx,
  cy,
  count,
  opacity,
}) => {
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
            fill={COLORS.leftZone}
            fillOpacity={0.5}
          />
        );
      })}
    </g>
  );
};

export const HighlightZones: React.FC = () => {
  const frame = useCurrentFrame();

  // Left zone fade (frames 180-210)
  const leftOpacity = interpolate(
    frame,
    [TIMING.leftZoneStart, TIMING.leftZoneEnd],
    [0, 1],
    { extrapolateLeft: 'clamp', extrapolateRight: 'clamp', easing: Easing.out(Easing.quad) }
  );

  // Right zone fade (frames 240-270)
  const rightOpacity = interpolate(
    frame,
    [TIMING.rightZoneStart, TIMING.rightZoneEnd],
    [0, 1],
    { extrapolateLeft: 'clamp', extrapolateRight: 'clamp', easing: Easing.out(Easing.quad) }
  );

  // During slider travel (300-390), dim left and brighten right
  const sliderT = interpolate(
    frame,
    [TIMING.sliderStart, TIMING.sliderEnd],
    [0, 1],
    { extrapolateLeft: 'clamp', extrapolateRight: 'clamp', easing: Easing.inOut(Easing.cubic) }
  );

  const leftDim = frame >= TIMING.sliderStart ? 1 - sliderT * 0.4 : 1;
  const rightBright = frame >= TIMING.sliderStart ? 1 + sliderT * 0.3 : 1;

  return (
    <svg
      width={1920}
      height={1080}
      style={{ position: 'absolute', top: 0, left: 0 }}
    >
      {/* Left zone — few tests */}
      <g opacity={leftOpacity * leftDim}>
        {/* Highlight rectangle */}
        <rect
          x={280}
          y={CHART.topY}
          width={200}
          height={CHART.originY - CHART.topY}
          fill={COLORS.leftZone}
          fillOpacity={0.04}
        />
        {/* Dense prompt icon */}
        <DensePromptIcon x={380} y={420} opacity={1} />
        {/* Label */}
        <text
          x={380}
          y={490}
          fill={COLORS.leftZone}
          fillOpacity={0.6}
          fontSize={11}
          fontFamily="Inter, sans-serif"
          textAnchor="middle"
        >
          Detailed prompt required
        </text>
      </g>

      {/* Right zone — many tests */}
      <g opacity={rightOpacity * Math.min(rightBright, 1.3)}>
        <rect
          x={1300}
          y={CHART.topY}
          width={300}
          height={CHART.originY - CHART.topY}
          fill={COLORS.rightZone}
          fillOpacity={0.04}
        />
        {/* Sparse prompt icon */}
        <SparsePromptIcon x={1450} y={660} opacity={1} />
        {/* Wall icons surrounding sparse prompt */}
        <WallIcons cx={1450} cy={660} count={8} opacity={1} />
        {/* Label */}
        <text
          x={1450}
          y={720}
          fill={COLORS.rightZone}
          fillOpacity={0.6}
          fontSize={11}
          fontFamily="Inter, sans-serif"
          textAnchor="middle"
        >
          Intent is enough
        </text>
      </g>
    </svg>
  );
};
