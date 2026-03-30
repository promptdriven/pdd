import React from 'react';
import { useCurrentFrame, interpolate, Easing } from 'remotion';
import {
  INSET_X,
  INSET_Y,
  INSET_WIDTH,
  INSET_HEIGHT,
  INSET_BG_COLOR,
  INSET_BORDER_COLOR,
  INSET_BORDER_RADIUS,
  TITLE_COLOR,
  DEGRADATION_LABEL_COLOR,
  SOURCE_LABEL_COLOR,
  PHASE_GRID_DIM_START,
  PHASE_GRID_DIM_END,
  PHASE_INSET_BG_START,
  PHASE_INSET_BG_END,
  PHASE_LABELS_START,
  PHASE_LABELS_FADE_DURATION,
  PHASE_INSET_FADE_START,
  PHASE_INSET_FADE_END,
} from './constants';
import { ChartAxes } from './ChartAxes';
import { AnimatedLine } from './AnimatedLine';

/**
 * The inset chart container: border draw-in, background fill, title, axes, line, labels.
 * Visible from frame 0 to ~720, then fades out.
 */
export const InsetChart: React.FC = () => {
  const frame = useCurrentFrame();

  // ── Border draw-in (perimeter clip via dashoffset) ──
  const borderPerimeter = 2 * (INSET_WIDTH + INSET_HEIGHT);
  const borderDrawProgress = interpolate(
    frame,
    [PHASE_GRID_DIM_START, PHASE_GRID_DIM_END],
    [0, 1],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.out(Easing.quad),
    },
  );

  // ── Background fill-in ──
  const bgOpacity = interpolate(
    frame,
    [PHASE_INSET_BG_START, PHASE_INSET_BG_END],
    [0, 0.95],
    { extrapolateLeft: 'clamp', extrapolateRight: 'clamp' },
  );

  // ── Title type-in ──
  const titleText = 'Performance vs. Context Length';
  const titleChars = interpolate(
    frame,
    [PHASE_INSET_BG_START, PHASE_INSET_BG_END],
    [0, titleText.length],
    { extrapolateLeft: 'clamp', extrapolateRight: 'clamp' },
  );
  const displayTitle = titleText.slice(0, Math.round(titleChars));

  // ── Labels fade-in ──
  const labelsOpacity = interpolate(
    frame,
    [PHASE_LABELS_START, PHASE_LABELS_START + PHASE_LABELS_FADE_DURATION],
    [0, 1],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.out(Easing.quad),
    },
  );

  // ── Inset fade-out ──
  const insetFadeOut = interpolate(
    frame,
    [PHASE_INSET_FADE_START, PHASE_INSET_FADE_END],
    [1, 0],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.in(Easing.quad),
    },
  );

  // Don't render once fully faded
  if (insetFadeOut <= 0) return null;

  return (
    <div
      style={{
        position: 'absolute',
        left: INSET_X,
        top: INSET_Y,
        width: INSET_WIDTH,
        height: INSET_HEIGHT,
        opacity: insetFadeOut,
      }}
    >
      {/* Border drawn as SVG rect with dash animation */}
      <svg
        width={INSET_WIDTH}
        height={INSET_HEIGHT}
        style={{ position: 'absolute', top: 0, left: 0, zIndex: 2 }}
      >
        <rect
          x={0.5}
          y={0.5}
          width={INSET_WIDTH - 1}
          height={INSET_HEIGHT - 1}
          rx={INSET_BORDER_RADIUS}
          ry={INSET_BORDER_RADIUS}
          fill="none"
          stroke={INSET_BORDER_COLOR}
          strokeWidth={1}
          strokeDasharray={borderPerimeter}
          strokeDashoffset={borderPerimeter * (1 - borderDrawProgress)}
        />
      </svg>

      {/* Background fill */}
      <div
        style={{
          position: 'absolute',
          top: 1,
          left: 1,
          width: INSET_WIDTH - 2,
          height: INSET_HEIGHT - 2,
          backgroundColor: INSET_BG_COLOR,
          borderRadius: INSET_BORDER_RADIUS - 1,
          opacity: bgOpacity,
          zIndex: 1,
        }}
      />

      {/* Content layer */}
      <div
        style={{
          position: 'absolute',
          top: 0,
          left: 0,
          width: INSET_WIDTH,
          height: INSET_HEIGHT,
          zIndex: 3,
        }}
      >
        {/* Title */}
        <div
          style={{
            position: 'absolute',
            top: 12,
            left: 16,
            fontFamily: 'Inter, sans-serif',
            fontSize: 14,
            fontWeight: 600,
            color: TITLE_COLOR,
            whiteSpace: 'nowrap',
            opacity: bgOpacity > 0 ? 1 : 0,
          }}
        >
          {displayTitle}
          <span
            style={{
              opacity: frame % 20 < 10 && frame < PHASE_INSET_BG_END + 30 ? 1 : 0,
              color: TITLE_COLOR,
            }}
          >
            |
          </span>
        </div>

        {/* Chart axes */}
        <ChartAxes chartWidth={INSET_WIDTH} chartHeight={INSET_HEIGHT} />

        {/* Animated performance line */}
        <AnimatedLine chartWidth={INSET_WIDTH} chartHeight={INSET_HEIGHT} />

        {/* Degradation label + source */}
        <div
          style={{
            position: 'absolute',
            bottom: 48,
            right: 24,
            textAlign: 'right',
            opacity: labelsOpacity,
          }}
        >
          <div
            style={{
              fontFamily: 'Inter, sans-serif',
              fontSize: 12,
              fontWeight: 400,
              color: DEGRADATION_LABEL_COLOR,
              opacity: 0.8,
            }}
          >
            14-85% degradation
          </div>
          <div
            style={{
              fontFamily: 'Inter, sans-serif',
              fontSize: 11,
              fontWeight: 400,
              color: SOURCE_LABEL_COLOR,
              marginTop: 2,
            }}
          >
            (EMNLP, 2025)
          </div>
        </div>
      </div>
    </div>
  );
};

export default InsetChart;
