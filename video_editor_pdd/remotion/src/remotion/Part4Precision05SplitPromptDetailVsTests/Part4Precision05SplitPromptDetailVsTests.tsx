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
import { VerticalDivider } from "./VerticalDivider";
import { DocumentIcon } from "./DocumentIcon";
import { ShieldIcon } from "./ShieldIcon";
import {
  LEFT_PANEL,
  RIGHT_PANEL,
  PANEL_RADIUS,
  PANEL_BG,
  AMBER,
  AMBER_MUTED,
  AMBER_BG,
  GREEN,
  GREEN_MUTED,
  GREEN_BG,
  SUBTEXT_COLOR,
  FOOTER_COLOR,
  PANEL_SPRING,
  PANEL_SLIDE_IN_START,
  PANEL_SLIDE_IN_END,
  LEFT_HEADER_START,
  LEFT_HEADER_END,
  LEFT_STAT_START,
  LEFT_STAT_END,
  RIGHT_HEADER_START,
  RIGHT_HEADER_END,
  RIGHT_STAT_START,
  RIGHT_STAT_END,
  FOOTER_START,
  FOOTER_END,
  FADEOUT_START,
  FADEOUT_END,
} from "./constants";

export const defaultPart4Precision05SplitPromptDetailVsTestsProps = {};

export const Part4Precision05SplitPromptDetailVsTests: React.FC = () => {
  const frame = useCurrentFrame();
  const { fps } = useVideoConfig();

  // ── Left panel slide in (spring) ──
  const leftSpring = spring({
    frame: frame - PANEL_SLIDE_IN_START,
    fps,
    config: PANEL_SPRING,
  });
  const leftX = interpolate(leftSpring, [0, 1], [-960, 0]);
  const leftOpacity = interpolate(
    frame,
    [PANEL_SLIDE_IN_START, PANEL_SLIDE_IN_END, FADEOUT_START, FADEOUT_END],
    [0, 1, 1, 0],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
  );
  const leftSlideOut = interpolate(
    frame,
    [FADEOUT_START, FADEOUT_END],
    [0, -960],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.in(Easing.cubic),
    }
  );
  const leftTranslateX = frame >= FADEOUT_START ? leftSlideOut : leftX;

  // ── Right panel slide in (spring) ──
  const rightSpring = spring({
    frame: frame - PANEL_SLIDE_IN_START,
    fps,
    config: PANEL_SPRING,
  });
  const rightX = interpolate(rightSpring, [0, 1], [960, 0]);
  const rightOpacity = interpolate(
    frame,
    [PANEL_SLIDE_IN_START, PANEL_SLIDE_IN_END, FADEOUT_START, FADEOUT_END],
    [0, 1, 1, 0],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
  );
  const rightSlideOut = interpolate(
    frame,
    [FADEOUT_START, FADEOUT_END],
    [0, 960],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.in(Easing.cubic),
    }
  );
  const rightTranslateX = frame >= FADEOUT_START ? rightSlideOut : rightX;

  // ── Content fade-in helpers ──
  const fadeIn = (start: number, end: number) =>
    interpolate(frame, [start, end, FADEOUT_START, FADEOUT_END], [0, 1, 1, 0], {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.out(Easing.quad),
    });

  const leftHeaderOpacity = fadeIn(LEFT_HEADER_START, LEFT_HEADER_END);
  const leftStatOpacity = fadeIn(LEFT_STAT_START, LEFT_STAT_END);
  const rightHeaderOpacity = fadeIn(RIGHT_HEADER_START, RIGHT_HEADER_END);
  const rightStatOpacity = fadeIn(RIGHT_STAT_START, RIGHT_STAT_END);
  const footerOpacity = fadeIn(FOOTER_START, FOOTER_END);

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
        {/* ═══ Left Panel — Prompt Detail ═══ */}
        <div
          style={{
            position: "absolute",
            left: LEFT_PANEL.x,
            top: LEFT_PANEL.y,
            width: LEFT_PANEL.w,
            height: LEFT_PANEL.h,
            borderRadius: PANEL_RADIUS,
            backgroundColor: PANEL_BG,
            backdropFilter: "blur(12px)",
            WebkitBackdropFilter: "blur(12px)",
            overflow: "hidden",
            transform: `translateX(${leftTranslateX}px)`,
            opacity: leftOpacity,
            display: "flex",
            flexDirection: "column",
            alignItems: "center",
            justifyContent: "center",
          }}
        >
          {/* Amber tint overlay */}
          <div
            style={{
              position: "absolute",
              inset: 0,
              backgroundColor: AMBER_BG,
              borderRadius: PANEL_RADIUS,
              pointerEvents: "none",
            }}
          />

          {/* Header */}
          <div
            style={{
              position: "relative",
              zIndex: 1,
              opacity: leftHeaderOpacity,
              display: "flex",
              flexDirection: "column",
              alignItems: "center",
              gap: 16,
            }}
          >
            <span
              style={{
                fontFamily: "Inter, sans-serif",
                fontWeight: 900,
                fontSize: 28,
                color: AMBER,
                letterSpacing: "0.15em",
                textTransform: "uppercase" as const,
              }}
            >
              PROMPT DETAIL
            </span>
            <DocumentIcon color={AMBER} size={120} opacity={0.3} />
          </div>

          {/* Cost stat */}
          <div
            style={{
              position: "relative",
              zIndex: 1,
              opacity: leftStatOpacity,
              display: "flex",
              flexDirection: "column",
              alignItems: "center",
              marginTop: 32,
              gap: 8,
            }}
          >
            <span
              style={{
                fontFamily: "Inter, sans-serif",
                fontWeight: 900,
                fontSize: 80,
                color: "#FFFFFF",
                lineHeight: 1,
              }}
            >
              ~2,000
            </span>
            <span
              style={{
                fontFamily: "Inter, sans-serif",
                fontWeight: 500,
                fontSize: 24,
                color: AMBER_MUTED,
              }}
            >
              tokens per prompt
            </span>
            <span
              style={{
                fontFamily: "Inter, sans-serif",
                fontWeight: 400,
                fontSize: 18,
                color: SUBTEXT_COLOR,
                marginTop: 8,
              }}
            >
              structured, precise, repeatable
            </span>
          </div>
        </div>

        {/* ═══ Vertical Divider ═══ */}
        <VerticalDivider />

        {/* ═══ Right Panel — Test Coverage ═══ */}
        <div
          style={{
            position: "absolute",
            left: RIGHT_PANEL.x,
            top: RIGHT_PANEL.y,
            width: RIGHT_PANEL.w,
            height: RIGHT_PANEL.h,
            borderRadius: PANEL_RADIUS,
            backgroundColor: PANEL_BG,
            backdropFilter: "blur(12px)",
            WebkitBackdropFilter: "blur(12px)",
            overflow: "hidden",
            transform: `translateX(${rightTranslateX}px)`,
            opacity: rightOpacity,
            display: "flex",
            flexDirection: "column",
            alignItems: "center",
            justifyContent: "center",
          }}
        >
          {/* Green tint overlay */}
          <div
            style={{
              position: "absolute",
              inset: 0,
              backgroundColor: GREEN_BG,
              borderRadius: PANEL_RADIUS,
              pointerEvents: "none",
            }}
          />

          {/* Header */}
          <div
            style={{
              position: "relative",
              zIndex: 1,
              opacity: rightHeaderOpacity,
              display: "flex",
              flexDirection: "column",
              alignItems: "center",
              gap: 16,
            }}
          >
            <span
              style={{
                fontFamily: "Inter, sans-serif",
                fontWeight: 900,
                fontSize: 28,
                color: GREEN,
                letterSpacing: "0.15em",
                textTransform: "uppercase" as const,
              }}
            >
              TEST COVERAGE
            </span>
            <ShieldIcon color={GREEN} size={120} opacity={0.3} />
          </div>

          {/* Cost stat */}
          <div
            style={{
              position: "relative",
              zIndex: 1,
              opacity: rightStatOpacity,
              display: "flex",
              flexDirection: "column",
              alignItems: "center",
              marginTop: 32,
              gap: 8,
            }}
          >
            <span
              style={{
                fontFamily: "Inter, sans-serif",
                fontWeight: 900,
                fontSize: 80,
                color: "#FFFFFF",
                lineHeight: 1,
              }}
            >
              ~45s
            </span>
            <span
              style={{
                fontFamily: "Inter, sans-serif",
                fontWeight: 500,
                fontSize: 24,
                color: GREEN_MUTED,
              }}
            >
              feedback loop
            </span>
            <span
              style={{
                fontFamily: "Inter, sans-serif",
                fontWeight: 400,
                fontSize: 18,
                color: SUBTEXT_COLOR,
                marginTop: 8,
              }}
            >
              comprehensive, slow, reliable
            </span>
          </div>
        </div>

        {/* ═══ Footer ═══ */}
        <div
          style={{
            position: "absolute",
            bottom: 30,
            left: 0,
            width: 1920,
            textAlign: "center" as const,
            opacity: footerOpacity,
          }}
        >
          <span
            style={{
              fontFamily: "Inter, sans-serif",
              fontWeight: 600,
              fontSize: 22,
              color: FOOTER_COLOR,
              textShadow: "0 2px 8px rgba(0, 0, 0, 0.5)",
            }}
          >
            Both bring cost — both bring value
          </span>
        </div>
      </AbsoluteFill>
    </AbsoluteFill>
  );
};

export default Part4Precision05SplitPromptDetailVsTests;
