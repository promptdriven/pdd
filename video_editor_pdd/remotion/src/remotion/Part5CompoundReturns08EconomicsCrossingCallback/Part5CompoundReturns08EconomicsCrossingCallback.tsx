import React from "react";
import {
  AbsoluteFill,
  useCurrentFrame,
  interpolate,
  Easing,
  Sequence,
} from "remotion";
import "../_shared/load-inter-font";
import {
  BG_COLOR,
  LABEL_COLOR,
  WE_ARE_HERE_OPACITY,
  ACCENT_UNDERLINE_COLOR,
  ACCENT_UNDERLINE_OPACITY,
  CROSSING_GLOW_COLOR,
  CROSSING_GLOW_RADIUS,
  CROSSING_GLOW_MIN_OPACITY,
  CROSSING_GLOW_MAX_OPACITY,
  CROSSING_PULSE_CYCLE,
  FADE_IN_END,
  PULSE_START,
  REEMPH_START,
  REFRAME_TEXT_START,
  FADE_OUT_START,
  FADE_OUT_END,
  TOTAL_FRAMES,
} from "./constants";
import { CodeCostChart, CROSSING_CX, CROSSING_CY } from "./CodeCostChart";
import { PulsingGlow } from "./PulsingGlow";

// ── Default props ───────────────────────────────────────────────────────────
export const defaultPart5CompoundReturns08EconomicsCrossingCallbackProps = {};

// ── Main component ──────────────────────────────────────────────────────────
export const Part5CompoundReturns08EconomicsCrossingCallback: React.FC = () => {
  const frame = useCurrentFrame();

  // ── Fade in (frames 0-30) ─────────────────────────────────────────────
  const fadeIn = interpolate(frame, [0, FADE_IN_END], [0.15, 1], {
    easing: Easing.out(Easing.quad),
    extrapolateLeft: "clamp",
    extrapolateRight: "clamp",
  });

  // ── "We are here" label re-emphasis (frames 90-120) ───────────────────
  const weAreHereOpacity = interpolate(
    frame,
    [PULSE_START, REEMPH_START, REEMPH_START + 20, REEMPH_START + 40],
    [
      WE_ARE_HERE_OPACITY,
      WE_ARE_HERE_OPACITY,
      0.9,
      WE_ARE_HERE_OPACITY,
    ],
    {
      easing: Easing.inOut(Easing.sin),
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
    }
  );

  // ── "The economics changed." text fade in (frames 150-180) ────────────
  const reframeOpacity = interpolate(
    frame,
    [REFRAME_TEXT_START, REFRAME_TEXT_START + 30],
    [0, 1],
    {
      easing: Easing.out(Easing.quad),
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
    }
  );

  // ── Fade out (frames 270-300) ─────────────────────────────────────────
  const fadeOut = interpolate(frame, [FADE_OUT_START, FADE_OUT_END], [1, 0], {
    easing: Easing.in(Easing.quad),
    extrapolateLeft: "clamp",
    extrapolateRight: "clamp",
  });

  // Master opacity: fade in then fade out
  const masterOpacity = frame < FADE_OUT_START ? fadeIn : fadeIn * fadeOut;

  return (
    <AbsoluteFill
      style={{
        backgroundColor: BG_COLOR,
        fontFamily: "Inter, sans-serif",
      }}
    >
      {/* Chart (all elements at final position, dimmed labels) */}
      <div
        style={{
          position: "absolute",
          top: 0,
          left: 0,
          width: 1920,
          height: 1080,
          opacity: masterOpacity,
        }}
      >
        <CodeCostChart />

        {/* Crossing point pulsing glow */}
        <Sequence from={PULSE_START} durationInFrames={TOTAL_FRAMES - PULSE_START}>
          <PulsingGlow
            cx={CROSSING_CX}
            cy={CROSSING_CY}
            color={CROSSING_GLOW_COLOR}
            radius={CROSSING_GLOW_RADIUS}
            minOpacity={CROSSING_GLOW_MIN_OPACITY}
            maxOpacity={CROSSING_GLOW_MAX_OPACITY}
            cycleFrames={CROSSING_PULSE_CYCLE}
            startFrame={0}
            brighterAfterFrame={REEMPH_START - PULSE_START}
            brighterMaxOpacity={0.35}
          />
        </Sequence>

        {/* "We are here." label — dimmed, near crossing point */}
        {frame >= PULSE_START && (
          <div
            style={{
              position: "absolute",
              left: CROSSING_CX + 40,
              top: CROSSING_CY - 10,
              color: LABEL_COLOR,
              opacity: weAreHereOpacity,
              fontSize: 24,
              fontWeight: 700,
              whiteSpace: "nowrap",
              pointerEvents: "none",
            }}
          >
            We are here.
          </div>
        )}
      </div>

      {/* "The economics changed." — reframe text below chart */}
      <div
        style={{
          position: "absolute",
          left: 0,
          top: 880,
          width: 1920,
          display: "flex",
          flexDirection: "column",
          alignItems: "center",
          opacity: reframeOpacity * masterOpacity,
          pointerEvents: "none",
        }}
      >
        <div
          style={{
            fontSize: 22,
            fontWeight: 700,
            color: LABEL_COLOR,
            textAlign: "center",
          }}
        >
          The economics changed.
        </div>
        {/* Subtle underline glow */}
        <div
          style={{
            width: 200,
            height: 3,
            marginTop: 6,
            borderRadius: 2,
            background: ACCENT_UNDERLINE_COLOR,
            opacity: ACCENT_UNDERLINE_OPACITY,
          }}
        />
      </div>
    </AbsoluteFill>
  );
};

export default Part5CompoundReturns08EconomicsCrossingCallback;
