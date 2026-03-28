import React from 'react';
import {
  AbsoluteFill,
  useCurrentFrame,
  interpolate,
  Easing,
  Sequence,
} from 'remotion';
import {
  BG_COLOR,
  CROSSING_X,
  CROSSING_Y,
  PULSE_GLOW_COLOR,
  PULSE_RADIUS,
  PULSE_MIN_OPACITY,
  PULSE_MAX_OPACITY,
  PULSE_CYCLE_FRAMES,
  LABEL_COLOR,
  LABEL_DIMMED_OPACITY,
  REFRAME_UNDERLINE_COLOR,
  REFRAME_UNDERLINE_OPACITY,
  CHART_FADE_IN_START,
  CHART_FADE_IN_END,
  PULSE_START,
  REFRAME_TEXT_START,
  REFRAME_TEXT_END,
  CHART_FADE_OUT_START,
  CHART_FADE_OUT_END,
} from './constants';
import { CodeCostChart } from './CodeCostChart';
import { PulsingGlow } from './PulsingGlow';

export const defaultPart5CompoundReturns08EconomicsCrossingCallbackProps = {};

export const Part5CompoundReturns08EconomicsCrossingCallback: React.FC = () => {
  const frame = useCurrentFrame();

  // Chart fade-in: frames 0-30
  const chartFadeIn = interpolate(
    frame,
    [CHART_FADE_IN_START, CHART_FADE_IN_END],
    [0, 1],
    {
      easing: Easing.out(Easing.quad),
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
    }
  );

  // Chart fade-out: frames 270-300
  const chartFadeOut = interpolate(
    frame,
    [CHART_FADE_OUT_START, CHART_FADE_OUT_END],
    [1, 0],
    {
      easing: Easing.in(Easing.quad),
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
    }
  );

  // Combined chart opacity
  const chartOpacity = Math.min(chartFadeIn, chartFadeOut);

  // "We are here" label: visible from frame 30, re-emphasized at frame 90
  const weAreHereBaseOpacity = frame >= PULSE_START ? 0.6 : 0;
  const weAreHereReemphasis =
    frame >= 90 && frame < 150
      ? interpolate(frame, [90, 105, 120, 150], [0.6, 0.85, 0.85, 0.6], {
          extrapolateLeft: 'clamp',
          extrapolateRight: 'clamp',
        })
      : weAreHereBaseOpacity;
  const weAreHereOpacity = Math.max(weAreHereBaseOpacity, weAreHereReemphasis);

  // Reframe text fade-in: frames 150-180
  const reframeOpacity = interpolate(
    frame,
    [REFRAME_TEXT_START, REFRAME_TEXT_END],
    [0, 1],
    {
      easing: Easing.out(Easing.quad),
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
    }
  );

  return (
    <AbsoluteFill
      style={{
        backgroundColor: BG_COLOR,
        fontFamily: 'Inter, sans-serif',
      }}
    >
      {/* Chart layer with fade in/out */}
      <div
        style={{
          position: 'absolute',
          top: 0,
          left: 0,
          width: 1920,
          height: 1080,
          opacity: chartOpacity,
        }}
      >
        <CodeCostChart dimOpacity={LABEL_DIMMED_OPACITY} />
      </div>

      {/* Crossing point pulsing glow — starts at frame 30 */}
      <Sequence from={PULSE_START} durationInFrames={270 - PULSE_START}>
        <div style={{ opacity: chartOpacity }}>
          <PulsingGlow
            cx={CROSSING_X}
            cy={CROSSING_Y}
            radius={PULSE_RADIUS}
            color={PULSE_GLOW_COLOR}
            minOpacity={PULSE_MIN_OPACITY}
            maxOpacity={PULSE_MAX_OPACITY}
            cycleFrames={PULSE_CYCLE_FRAMES}
            startFrame={0}
          />
        </div>
      </Sequence>

      {/* Crossing point dot */}
      {frame >= PULSE_START && (
        <div
          style={{
            position: 'absolute',
            left: CROSSING_X - 5,
            top: CROSSING_Y - 5,
            width: 10,
            height: 10,
            borderRadius: '50%',
            backgroundColor: '#FFFFFF',
            opacity: chartOpacity * 0.8,
          }}
        />
      )}

      {/* "We are here." label — dimmed at 0.6, re-emphasized briefly */}
      {frame >= PULSE_START && (
        <div
          style={{
            position: 'absolute',
            left: CROSSING_X + 40,
            top: CROSSING_Y + 8,
            opacity: weAreHereOpacity * chartOpacity,
          }}
        >
          <span
            style={{
              fontFamily: 'Inter, sans-serif',
              fontSize: 24,
              fontWeight: 700,
              color: LABEL_COLOR,
            }}
          >
            We are here.
          </span>
        </div>
      )}

      {/* "The economics changed." reframe text */}
      {frame >= REFRAME_TEXT_START && (
        <div
          style={{
            position: 'absolute',
            top: 880,
            left: 0,
            width: 1920,
            display: 'flex',
            flexDirection: 'column',
            alignItems: 'center',
            opacity: reframeOpacity * chartFadeOut,
          }}
        >
          <span
            style={{
              fontFamily: 'Inter, sans-serif',
              fontSize: 22,
              fontWeight: 700,
              color: LABEL_COLOR,
              opacity: 0.95,
            }}
          >
            The economics changed.
          </span>
          {/* Subtle underline glow */}
          <div
            style={{
              marginTop: 4,
              width: 200,
              height: 3,
              borderRadius: 2,
              background: REFRAME_UNDERLINE_COLOR,
              opacity: REFRAME_UNDERLINE_OPACITY,
            }}
          />
        </div>
      )}
    </AbsoluteFill>
  );
};

export default Part5CompoundReturns08EconomicsCrossingCallback;
