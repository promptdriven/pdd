import React from 'react';
import { useCurrentFrame, interpolate, Easing } from 'remotion';
import {
  DEBT_AREA_COLOR,
  CYCLE_ANNOTATION_COLOR,
  DEBT_CHART_LEFT,
  DEBT_CHART_TOP,
  DEBT_CHART_WIDTH,
  DEBT_CHART_HEIGHT,
  PHASE_PULSE_START,
  PHASE_ANNOTATION_START,
  PHASE_ANNOTATION_FADE_DURATION,
  PULSE_CYCLE_FRAMES,
  PHASE_INSET_FADE_START,
  PHASE_INSET_FADE_END,
  AXIS_LABEL_COLOR,
  TITLE_COLOR,
} from './constants';

/**
 * Represents the "code cost chart" with a debt area that pulses,
 * plus the "Faster patching → faster growth → faster rot" annotation.
 * Fades in as the inset chart fades out.
 */
export const DebtAreaPulse: React.FC = () => {
  const frame = useCurrentFrame();

  // ── Fade-in (inverse of inset fade-out) ──
  const chartFadeIn = interpolate(
    frame,
    [PHASE_INSET_FADE_START, PHASE_INSET_FADE_END],
    [0, 1],
    { extrapolateLeft: 'clamp', extrapolateRight: 'clamp' },
  );

  // ── Pulse cycle (sinusoidal) ──
  const pulsePhase = frame >= PHASE_PULSE_START ? frame - PHASE_PULSE_START : 0;
  const pulseOpacity =
    frame >= PHASE_PULSE_START
      ? interpolate(
          Math.sin((pulsePhase / PULSE_CYCLE_FRAMES) * Math.PI * 2),
          [-1, 1],
          [0.15, 0.5],
        )
      : 0.15;

  // ── Annotation fade-in ──
  const annotationOpacity = interpolate(
    frame,
    [PHASE_ANNOTATION_START, PHASE_ANNOTATION_START + PHASE_ANNOTATION_FADE_DURATION],
    [0, 1],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.out(Easing.quad),
    },
  );

  if (chartFadeIn <= 0) return null;

  // Simplified "code cost" chart with debt area
  const chartLeft = DEBT_CHART_LEFT;
  const chartTop = DEBT_CHART_TOP;
  const chartW = DEBT_CHART_WIDTH;
  const chartH = DEBT_CHART_HEIGHT;

  // A simplified rising cost curve
  const costCurve = `M ${chartLeft} ${chartTop + chartH}
    C ${chartLeft + chartW * 0.25} ${chartTop + chartH * 0.85},
      ${chartLeft + chartW * 0.5} ${chartTop + chartH * 0.55},
      ${chartLeft + chartW * 0.75} ${chartTop + chartH * 0.3}
    L ${chartLeft + chartW} ${chartTop + chartH * 0.15}`;

  // Debt area (area between cost curve and a baseline)
  const debtArea = `M ${chartLeft} ${chartTop + chartH}
    C ${chartLeft + chartW * 0.25} ${chartTop + chartH * 0.85},
      ${chartLeft + chartW * 0.5} ${chartTop + chartH * 0.55},
      ${chartLeft + chartW * 0.75} ${chartTop + chartH * 0.3}
    L ${chartLeft + chartW} ${chartTop + chartH * 0.15}
    L ${chartLeft + chartW} ${chartTop + chartH}
    Z`;

  // "Context Rot" label area (upper portion of debt)
  const rotArea = `M ${chartLeft + chartW * 0.45} ${chartTop + chartH * 0.6}
    C ${chartLeft + chartW * 0.6} ${chartTop + chartH * 0.45},
      ${chartLeft + chartW * 0.75} ${chartTop + chartH * 0.3},
      ${chartLeft + chartW} ${chartTop + chartH * 0.15}
    L ${chartLeft + chartW} ${chartTop + chartH * 0.45}
    C ${chartLeft + chartW * 0.75} ${chartTop + chartH * 0.55},
      ${chartLeft + chartW * 0.6} ${chartTop + chartH * 0.62},
      ${chartLeft + chartW * 0.45} ${chartTop + chartH * 0.6}
    Z`;

  return (
    <div
      style={{
        position: 'absolute',
        top: 0,
        left: 0,
        width: '100%',
        height: '100%',
        opacity: chartFadeIn,
      }}
    >
      <svg
        width={1920}
        height={1080}
        viewBox="0 0 1920 1080"
        style={{ position: 'absolute', top: 0, left: 0 }}
      >
        {/* Chart axes */}
        <line
          x1={chartLeft}
          y1={chartTop}
          x2={chartLeft}
          y2={chartTop + chartH}
          stroke={AXIS_LABEL_COLOR}
          strokeWidth={1}
          opacity={0.5}
        />
        <line
          x1={chartLeft}
          y1={chartTop + chartH}
          x2={chartLeft + chartW}
          y2={chartTop + chartH}
          stroke={AXIS_LABEL_COLOR}
          strokeWidth={1}
          opacity={0.5}
        />

        {/* Y-axis label */}
        <text
          x={chartLeft - 40}
          y={chartTop + chartH / 2}
          fill={AXIS_LABEL_COLOR}
          fontSize={14}
          fontFamily="Inter, sans-serif"
          textAnchor="middle"
          transform={`rotate(-90, ${chartLeft - 40}, ${chartTop + chartH / 2})`}
        >
          Code Maintenance Cost
        </text>

        {/* X-axis label */}
        <text
          x={chartLeft + chartW / 2}
          y={chartTop + chartH + 40}
          fill={AXIS_LABEL_COLOR}
          fontSize={14}
          fontFamily="Inter, sans-serif"
          textAnchor="middle"
        >
          Time / Codebase Growth
        </text>

        {/* Debt area (base layer) */}
        <path d={debtArea} fill="#3B82F6" opacity={0.12} />

        {/* Context Rot area (pulsing) */}
        <path d={rotArea} fill={DEBT_AREA_COLOR} opacity={pulseOpacity} />

        {/* Cost curve line */}
        <path
          d={costCurve}
          fill="none"
          stroke="#3B82F6"
          strokeWidth={2.5}
          opacity={0.8}
        />

        {/* "Context Rot" label */}
        <text
          x={chartLeft + chartW * 0.72}
          y={chartTop + chartH * 0.42}
          fill={DEBT_AREA_COLOR}
          fontSize={16}
          fontFamily="Inter, sans-serif"
          fontWeight={600}
          textAnchor="middle"
          opacity={0.9}
        >
          Context Rot
        </text>

        {/* "Technical Debt" label */}
        <text
          x={chartLeft + chartW * 0.55}
          y={chartTop + chartH * 0.78}
          fill="#3B82F6"
          fontSize={14}
          fontFamily="Inter, sans-serif"
          fontWeight={500}
          textAnchor="middle"
          opacity={0.6}
        >
          Technical Debt
        </text>

        {/* Chart title */}
        <text
          x={chartLeft + chartW / 2}
          y={chartTop - 20}
          fill={TITLE_COLOR}
          fontSize={20}
          fontFamily="Inter, sans-serif"
          fontWeight={600}
          textAnchor="middle"
        >
          AI-Assisted Code: Two Stories
        </text>
      </svg>

      {/* "Faster patching → faster growth → faster rot" annotation */}
      <div
        style={{
          position: 'absolute',
          top: DEBT_CHART_TOP + DEBT_CHART_HEIGHT * 0.28,
          left: DEBT_CHART_LEFT + DEBT_CHART_WIDTH * 0.55,
          opacity: annotationOpacity,
        }}
      >
        {/* Divider line above the annotation */}
        <div
          style={{
            width: 320,
            height: 2,
            backgroundColor: CYCLE_ANNOTATION_COLOR,
            opacity: 0.75,
            marginBottom: 8,
          }}
        />
        <div
          style={{
            fontFamily: 'Inter, sans-serif',
            fontSize: 14,
            fontStyle: 'italic',
            fontWeight: 400,
            color: CYCLE_ANNOTATION_COLOR,
            opacity: 0.95,
            whiteSpace: 'nowrap',
          }}
        >
          Faster patching → faster growth → faster rot
        </div>
      </div>
    </div>
  );
};

export default DebtAreaPulse;
