import React from "react";
import {
  AbsoluteFill,
  OffthreadVideo,
  staticFile,
  useCurrentFrame,
  interpolate,
  spring,
  Easing,
} from "remotion";
import { SplitPanel } from "./SplitPanel";
import { VerticalDivider } from "./VerticalDivider";
import { DiffIcon } from "./DiffIcon";
import { RefreshCycleIcon } from "./RefreshCycleIcon";
import { MiniTimeline } from "./MiniTimeline";
import {
  BG_COLOR,
  RED,
  GREEN,
  SLATE_400,
  SLATE_300,
  HEADER_FONT_SIZE,
  HEADER_LETTER_SPACING,
  HEADER_FONT_WEIGHT,
  TIMELINE_LABEL_FONT_SIZE,
  TIMELINE_LABEL_FONT_WEIGHT,
  OUTCOME_FONT_SIZE,
  OUTCOME_FONT_WEIGHT,
  FOOTER_FONT_SIZE,
  FOOTER_FONT_WEIGHT,
  PANEL_SLIDE_IN_START,
  PANEL_SLIDE_IN_END,
  DIVIDER_FADE_START,
  DIVIDER_FADE_END,
  LEFT_HEADER_FADE_START,
  LEFT_HEADER_FADE_END,
  RIGHT_HEADER_FADE_START,
  RIGHT_HEADER_FADE_END,
  OUTCOME_FADE_START,
  OUTCOME_FADE_END,
  FOOTER_FADE_START,
  FOOTER_FADE_END,
  SLIDE_OUT_START,
  SLIDE_OUT_END,
  LEFT_HEADER,
  RIGHT_HEADER,
  LEFT_TIMELINE_LABEL,
  RIGHT_TIMELINE_LABEL,
  LEFT_OUTCOME,
  RIGHT_OUTCOME,
  FOOTER_TEXT,
} from "./constants";

export const defaultPart5Compound08SplitPatchingVsPddProps = {};

export const Part5Compound08SplitPatchingVsPdd: React.FC = () => {
  const frame = useCurrentFrame();

  // --- Panel slide-in (spring) ---
  const slideInProgress = spring({
    frame: frame - PANEL_SLIDE_IN_START,
    fps: 30,
    config: { damping: 16, stiffness: 160 },
  });

  // --- Panel slide-out (easeInCubic) ---
  const slideOutProgress = interpolate(
    frame,
    [SLIDE_OUT_START, SLIDE_OUT_END],
    [0, 1],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp", easing: Easing.in(Easing.cubic) }
  );

  // Left panel: slides from -960 → 0, then 0 → -960
  const leftTranslateX = interpolate(slideInProgress, [0, 1], [-960, 0]) + slideOutProgress * -960;
  const leftOpacity = interpolate(slideInProgress, [0, 1], [0, 1]) * (1 - slideOutProgress);

  // Right panel: slides from +960 → 0, then 0 → +960
  const rightTranslateX = interpolate(slideInProgress, [0, 1], [960, 0]) + slideOutProgress * 960;
  const rightOpacity = interpolate(slideInProgress, [0, 1], [0, 1]) * (1 - slideOutProgress);

  // --- Divider ---
  const dividerOpacity = interpolate(
    frame,
    [DIVIDER_FADE_START, DIVIDER_FADE_END, SLIDE_OUT_START, SLIDE_OUT_END],
    [0, 0.4, 0.4, 0],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
  );

  // --- Left header + icon ---
  const leftHeaderOpacity = interpolate(
    frame,
    [LEFT_HEADER_FADE_START, LEFT_HEADER_FADE_END],
    [0, 1],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp", easing: Easing.out(Easing.quad) }
  );

  // --- Right header + icon ---
  const rightHeaderOpacity = interpolate(
    frame,
    [RIGHT_HEADER_FADE_START, RIGHT_HEADER_FADE_END],
    [0, 1],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp", easing: Easing.out(Easing.quad) }
  );

  // --- Outcome labels ---
  const outcomeOpacity = interpolate(
    frame,
    [OUTCOME_FADE_START, OUTCOME_FADE_END],
    [0, 1],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp", easing: Easing.out(Easing.quad) }
  );

  // --- Footer ---
  const footerOpacity = interpolate(
    frame,
    [FOOTER_FADE_START, FOOTER_FADE_END, SLIDE_OUT_START, SLIDE_OUT_END],
    [0, 1, 1, 0],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
  );

  return (
    <AbsoluteFill style={{ backgroundColor: BG_COLOR }}>
      {/* Veo background video */}
      <AbsoluteFill>
        <OffthreadVideo
          src={staticFile("veo/part5_compound.mp4")}
          style={{ width: "100%", height: "100%", objectFit: "cover", opacity: 0.3 }}
          muted
        />
      </AbsoluteFill>

      {/* Left panel — Patching */}
      <SplitPanel side="left" translateX={leftTranslateX} opacity={leftOpacity}>
        {/* Header */}
        <div style={{ opacity: leftHeaderOpacity, textAlign: "center" }}>
          <div
            style={{
              fontFamily: "Inter, sans-serif",
              fontSize: HEADER_FONT_SIZE,
              fontWeight: HEADER_FONT_WEIGHT,
              letterSpacing: HEADER_LETTER_SPACING,
              color: RED,
              textTransform: "uppercase" as const,
              marginBottom: 16,
            }}
          >
            {LEFT_HEADER}
          </div>
        </div>

        {/* Icon */}
        <DiffIcon />

        {/* Mini timeline */}
        <MiniTimeline type="rising_bars" color={RED} />

        {/* Timeline label */}
        <div
          style={{
            fontFamily: "Inter, sans-serif",
            fontSize: TIMELINE_LABEL_FONT_SIZE,
            fontWeight: TIMELINE_LABEL_FONT_WEIGHT,
            color: SLATE_400,
            opacity: leftHeaderOpacity,
          }}
        >
          {LEFT_TIMELINE_LABEL}
        </div>

        {/* Outcome */}
        <div
          style={{
            fontFamily: "Inter, sans-serif",
            fontSize: OUTCOME_FONT_SIZE,
            fontWeight: OUTCOME_FONT_WEIGHT,
            color: RED,
            opacity: outcomeOpacity,
          }}
        >
          {LEFT_OUTCOME}
        </div>
      </SplitPanel>

      {/* Vertical divider */}
      <VerticalDivider opacity={dividerOpacity} />

      {/* Right panel — Generation */}
      <SplitPanel side="right" translateX={rightTranslateX} opacity={rightOpacity}>
        {/* Header */}
        <div style={{ opacity: rightHeaderOpacity, textAlign: "center" }}>
          <div
            style={{
              fontFamily: "Inter, sans-serif",
              fontSize: HEADER_FONT_SIZE,
              fontWeight: HEADER_FONT_WEIGHT,
              letterSpacing: HEADER_LETTER_SPACING,
              color: GREEN,
              textTransform: "uppercase" as const,
              marginBottom: 16,
            }}
          >
            {RIGHT_HEADER}
          </div>
        </div>

        {/* Icon */}
        <RefreshCycleIcon />

        {/* Mini timeline */}
        <MiniTimeline type="flat_sawtooth" color={GREEN} />

        {/* Timeline label */}
        <div
          style={{
            fontFamily: "Inter, sans-serif",
            fontSize: TIMELINE_LABEL_FONT_SIZE,
            fontWeight: TIMELINE_LABEL_FONT_WEIGHT,
            color: SLATE_400,
            opacity: rightHeaderOpacity,
          }}
        >
          {RIGHT_TIMELINE_LABEL}
        </div>

        {/* Outcome */}
        <div
          style={{
            fontFamily: "Inter, sans-serif",
            fontSize: OUTCOME_FONT_SIZE,
            fontWeight: OUTCOME_FONT_WEIGHT,
            color: GREEN,
            opacity: outcomeOpacity,
          }}
        >
          {RIGHT_OUTCOME}
        </div>
      </SplitPanel>

      {/* Footer — centered across both panels */}
      <div
        style={{
          position: "absolute",
          bottom: 30,
          left: 0,
          width: 1920,
          textAlign: "center",
          opacity: footerOpacity,
        }}
      >
        <span
          style={{
            fontFamily: "Inter, sans-serif",
            fontSize: FOOTER_FONT_SIZE,
            fontWeight: FOOTER_FONT_WEIGHT,
            color: SLATE_300,
          }}
        >
          {FOOTER_TEXT}
        </span>
      </div>
    </AbsoluteFill>
  );
};

export default Part5Compound08SplitPatchingVsPdd;
