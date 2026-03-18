import React from "react";
import {
  AbsoluteFill,
  useCurrentFrame,
  interpolate,
  Easing,
  Sequence,
} from "remotion";
import {
  BG_COLOR,
  TEXT_PRIMARY,
  LEFT_COLOR,
  RIGHT_COLOR,
  LEFT_X,
  RIGHT_X,
  TOTAL_FRAMES,
  TRACKS_APPEAR,
  CENTER_TEXT_START,
  SUMMARY_START,
  CHALLENGE_START,
} from "./constants";
import VerticalMeter from "./VerticalMeter";
import StaggeredText from "./StaggeredText";

// SVG path data for icons
// Window/magnifying-glass icon for context window
const WINDOW_ICON_PATH =
  "M3 6a3 3 0 0 1 3-3h12a3 3 0 0 1 3 3v8a3 3 0 0 1-3 3H6a3 3 0 0 1-3-3V6zm3-1h12a1 1 0 0 1 1 1v1H5V6a1 1 0 0 1 1-1zm-1 4v5a1 1 0 0 0 1 1h12a1 1 0 0 0 1-1V9H5zm5 10l2 2m0 0l2-2m-2 2v-4";

// Brain icon for model performance
const BRAIN_ICON_PATH =
  "M12 2C9.5 2 7.5 3.5 7 5.5C5.5 6 4.5 7.5 4.5 9c0 1.2.6 2.3 1.5 3-.3.8-.5 1.7-.5 2.5C5.5 17 7.5 19 10 19.5V22h4v-2.5c2.5-.5 4.5-2.5 4.5-5 0-.8-.2-1.7-.5-2.5.9-.7 1.5-1.8 1.5-3 0-1.5-1-3-2.5-3.5C16.5 3.5 14.5 2 12 2zm-2 7a1 1 0 1 0 0-2 1 1 0 0 0 0 2zm4 0a1 1 0 1 0 0-2 1 1 0 0 0 0 2zm-4 4a1 1 0 1 0 0-2 1 1 0 0 0 0 2zm4 0a1 1 0 1 0 0-2 1 1 0 0 0 0 2z";

export const defaultPart1Economics10DoubleMeterInsightProps = {};

export const Part1Economics10DoubleMeterInsight: React.FC = () => {
  const frame = useCurrentFrame();

  // ── Vignette opacity for stillness beat ──
  const vignetteOpacity = interpolate(frame, [0, 10], [0, 0.3], {
    extrapolateLeft: "clamp",
    extrapolateRight: "clamp",
  });

  // ── Summary fade-in ──
  const summaryOpacity = interpolate(
    frame,
    [SUMMARY_START, SUMMARY_START + 25],
    [0, 1],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.out(Easing.cubic),
    }
  );

  // ── Challenge text ──
  const challengeProgress = interpolate(
    frame,
    [CHALLENGE_START, CHALLENGE_START + 20],
    [0, 1],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.out(Easing.back(1.4)),
    }
  );
  const challengeOpacity = interpolate(
    frame,
    [CHALLENGE_START, CHALLENGE_START + 20],
    [0, 1],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.out(Easing.cubic),
    }
  );
  const challengeSlideY = interpolate(challengeProgress, [0, 1], [12, 0], {
    extrapolateLeft: "clamp",
    extrapolateRight: "clamp",
  });

  return (
    <AbsoluteFill
      style={{
        backgroundColor: BG_COLOR,
        fontFamily: "Inter, sans-serif",
      }}
    >
      {/* ── Vignette overlay ── */}
      <div
        style={{
          position: "absolute",
          inset: 0,
          background:
            "radial-gradient(ellipse at center, transparent 40%, #000000 100%)",
          opacity: vignetteOpacity,
          pointerEvents: "none",
        }}
      />

      {/* ── Left Meter — Effective Context Window ── */}
      <Sequence from={TRACKS_APPEAR} durationInFrames={TOTAL_FRAMES - TRACKS_APPEAR}>
        <VerticalMeter
          x={LEFT_X}
          label="Effective Context Window"
          color={LEFT_COLOR}
          scaleMarkers={["1×", "5×", "10×"]}
          maxValue={10}
          unit="×"
          iconPath={WINDOW_ICON_PATH}
        />
      </Sequence>

      {/* ── Right Meter — Model Performance ── */}
      <Sequence from={TRACKS_APPEAR} durationInFrames={TOTAL_FRAMES - TRACKS_APPEAR}>
        <VerticalMeter
          x={RIGHT_X}
          label="Model Performance"
          color={RIGHT_COLOR}
          scaleMarkers={["baseline", "+50%", "+89%"]}
          maxValue={89}
          unit="%"
          prefix="+"
          iconPath={BRAIN_ICON_PATH}
        />
      </Sequence>

      {/* ── Center Text — "Bigger window AND smarter model." ── */}
      <Sequence from={CENTER_TEXT_START} durationInFrames={TOTAL_FRAMES - CENTER_TEXT_START}>
        <StaggeredText
          groups={[
            { text: "Bigger window", color: LEFT_COLOR },
            { text: "AND", color: TEXT_PRIMARY },
            { text: "smarter model.", color: RIGHT_COLOR },
          ]}
          startFrame={0}
          staggerDelay={10}
          fadeDuration={15}
          y={520}
        />
      </Sequence>

      {/* ── Summary Line ── */}
      <div
        style={{
          position: "absolute",
          left: 0,
          top: 600,
          width: "100%",
          textAlign: "center",
          fontFamily: "Inter, sans-serif",
          fontSize: 16,
          fontWeight: 400,
          color: TEXT_PRIMARY,
          opacity: 0.6 * summaryOpacity,
          letterSpacing: 0.2,
        }}
      >
        Not one or the other. Both. That&apos;s a category shift.
      </div>

      {/* ── Challenge Text — "Try it yourself." ── */}
      <div
        style={{
          position: "absolute",
          left: 0,
          top: 720,
          width: "100%",
          textAlign: "center",
          fontFamily: "'Caveat', 'Segoe Script', 'Comic Sans MS', cursive",
          fontSize: 28,
          color: TEXT_PRIMARY,
          opacity: 0.5 * challengeOpacity,
          transform: `translateY(${challengeSlideY}px) rotate(-2deg)`,
          letterSpacing: 0.5,
        }}
      >
        Try it yourself.
      </div>
    </AbsoluteFill>
  );
};

export default Part1Economics10DoubleMeterInsight;
