import React from "react";
import {
  AbsoluteFill,
  OffthreadVideo,
  staticFile,
  useCurrentFrame,
  interpolate,
  spring,
  useVideoConfig,
  Easing,
} from "remotion";
import { SplitPanel } from "./SplitPanel";
import { DocumentIcon } from "./DocumentIcon";
import { ShieldIcon } from "./ShieldIcon";
import { VerticalDivider } from "./VerticalDivider";
import {
  LEFT_PANEL,
  RIGHT_PANEL,
  AMBER,
  AMBER_MUTED,
  AMBER_BG,
  GREEN,
  GREEN_MUTED,
  GREEN_BG,
  FOOTER_COLOR,
  PANEL_SPRING,
  LEFT_SLIDE_IN_START,
  RIGHT_SLIDE_IN_START,
  LEFT_HEADER_FADE_START,
  LEFT_HEADER_FADE_END,
  LEFT_STAT_FADE_START,
  LEFT_STAT_FADE_END,
  RIGHT_HEADER_FADE_START,
  RIGHT_HEADER_FADE_END,
  RIGHT_STAT_FADE_START,
  RIGHT_STAT_FADE_END,
  FOOTER_FADE_START,
  FOOTER_FADE_END,
  FADEOUT_START,
  FADEOUT_END,
} from "./constants";

export const defaultPart4Precision05SplitPromptDetailVsTestsProps = {};

export const Part4Precision05SplitPromptDetailVsTests: React.FC = () => {
  const frame = useCurrentFrame();
  const { fps } = useVideoConfig();

  // ── Left panel slide-in (spring) ──
  const leftSpring = spring({
    frame: frame - LEFT_SLIDE_IN_START,
    fps,
    config: PANEL_SPRING,
  });
  const leftSlideIn = interpolate(leftSpring, [0, 1], [-960, 0]);

  const leftOpacity = interpolate(
    frame,
    [0, 25, FADEOUT_START, FADEOUT_END],
    [0, 1, 1, 0],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp" },
  );

  // Left slide-out
  const leftSlideOut = interpolate(
    frame,
    [FADEOUT_START, FADEOUT_END],
    [0, -960],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.in(Easing.cubic),
    },
  );
  const leftTranslateX = frame >= FADEOUT_START ? leftSlideOut : leftSlideIn;

  // ── Right panel slide-in (spring) ──
  const rightSpring = spring({
    frame: frame - RIGHT_SLIDE_IN_START,
    fps,
    config: PANEL_SPRING,
  });
  const rightSlideIn = interpolate(rightSpring, [0, 1], [960, 0]);

  const rightOpacity = interpolate(
    frame,
    [0, 25, FADEOUT_START, FADEOUT_END],
    [0, 1, 1, 0],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp" },
  );

  // Right slide-out
  const rightSlideOut = interpolate(
    frame,
    [FADEOUT_START, FADEOUT_END],
    [0, 960],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.in(Easing.cubic),
    },
  );
  const rightTranslateX = frame >= FADEOUT_START ? rightSlideOut : rightSlideIn;

  // ── Footer ──
  const footerOpacity = interpolate(
    frame,
    [FOOTER_FADE_START, FOOTER_FADE_END, FADEOUT_START, FADEOUT_END],
    [0, 1, 1, 0],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp" },
  );

  return (
    <AbsoluteFill style={{ backgroundColor: "#0A1628" }}>
      {/* Veo background video */}
      <AbsoluteFill>
        <OffthreadVideo
          src={staticFile("veo/part4_precision.mp4")}
          style={{ width: "100%", height: "100%", objectFit: "cover" }}
          muted
        />
      </AbsoluteFill>

      <AbsoluteFill>
        {/* === Left Panel: Prompt Detail === */}
        <SplitPanel
          x={LEFT_PANEL.x}
          y={LEFT_PANEL.y}
          w={LEFT_PANEL.w}
          h={LEFT_PANEL.h}
          tintBg={AMBER_BG}
          accentColor={AMBER}
          mutedColor={AMBER_MUTED}
          header="PROMPT DETAIL"
          statValue="~2,000"
          costUnit="tokens per prompt"
          subtext="structured, precise, repeatable"
          icon={<DocumentIcon color={AMBER} size={120} opacity={0.3} />}
          translateX={leftTranslateX}
          opacity={leftOpacity}
          headerFadeStart={LEFT_HEADER_FADE_START}
          headerFadeEnd={LEFT_HEADER_FADE_END}
          statFadeStart={LEFT_STAT_FADE_START}
          statFadeEnd={LEFT_STAT_FADE_END}
        />

        {/* === Vertical Divider === */}
        <VerticalDivider />

        {/* === Right Panel: Test Coverage === */}
        <SplitPanel
          x={RIGHT_PANEL.x}
          y={RIGHT_PANEL.y}
          w={RIGHT_PANEL.w}
          h={RIGHT_PANEL.h}
          tintBg={GREEN_BG}
          accentColor={GREEN}
          mutedColor={GREEN_MUTED}
          header="TEST COVERAGE"
          statValue="~45s"
          costUnit="feedback loop"
          subtext="comprehensive, slow, reliable"
          icon={<ShieldIcon color={GREEN} size={120} opacity={0.3} />}
          translateX={rightTranslateX}
          opacity={rightOpacity}
          headerFadeStart={RIGHT_HEADER_FADE_START}
          headerFadeEnd={RIGHT_HEADER_FADE_END}
          statFadeStart={RIGHT_STAT_FADE_START}
          statFadeEnd={RIGHT_STAT_FADE_END}
        />

        {/* === Footer === */}
        <div
          style={{
            position: "absolute",
            bottom: 36,
            left: 0,
            width: 1920,
            textAlign: "center",
            fontFamily: "'Inter', sans-serif",
            fontWeight: 600,
            fontSize: 22,
            color: FOOTER_COLOR,
            opacity: footerOpacity,
            textShadow: "0 2px 12px rgba(0, 0, 0, 0.5)",
          }}
        >
          Both bring cost — both bring value
        </div>
      </AbsoluteFill>
    </AbsoluteFill>
  );
};

export default Part4Precision05SplitPromptDetailVsTests;
