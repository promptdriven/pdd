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
import { PanelBadge } from "./PanelBadge";
import { CodePanel } from "./CodePanel";
import { VerticalDivider } from "./VerticalDivider";
import { RatioCallout } from "./RatioCallout";
import {
  LEFT_PANEL,
  RIGHT_PANEL,
  PANEL_RADIUS,
  PANEL_BG,
  GOLD,
  GOLD_LIGHT,
  GOLD_BG,
  GOLD_PILL_BG,
  BLUE,
  BLUE_LIGHT,
  BLUE_BG,
  BLUE_PILL_BG,
  PANEL_SPRING,
  LEFT_SLIDE_IN_START,
  LEFT_SLIDE_IN_END,
  RIGHT_SLIDE_IN_START,
  RIGHT_SLIDE_IN_END,
  CODE_APPEAR_START,
  CODE_APPEAR_END,
  LINE_COUNTER_PULSE_START,
  LINE_COUNTER_PULSE_END,
  FADEOUT_START,
  FADEOUT_END,
  PROMPT_LINES,
  GENERATED_LINES,
} from "./constants";

export const defaultPart3Mold06SplitPromptVsCodeProps = {};

export const Part3Mold06SplitPromptVsCode: React.FC = () => {
  const frame = useCurrentFrame();
  const { fps } = useVideoConfig();

  // Left panel spring animation
  const leftSpring = spring({
    frame: frame - LEFT_SLIDE_IN_START,
    fps,
    config: PANEL_SPRING,
  });
  const leftX = interpolate(leftSpring, [0, 1], [-400, 0]);
  const leftOpacity = interpolate(
    frame,
    [LEFT_SLIDE_IN_START, LEFT_SLIDE_IN_END, FADEOUT_START, FADEOUT_END],
    [0, 1, 1, 0],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
  );
  // Slide out override
  const leftSlideOut = interpolate(
    frame,
    [FADEOUT_START, FADEOUT_END],
    [0, -400],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.in(Easing.cubic),
    }
  );
  const leftTranslateX = frame >= FADEOUT_START ? leftSlideOut : leftX;

  // Right panel spring animation
  const rightSpring = spring({
    frame: frame - RIGHT_SLIDE_IN_START,
    fps,
    config: PANEL_SPRING,
  });
  const rightX = interpolate(rightSpring, [0, 1], [400, 0]);
  const rightOpacity = interpolate(
    frame,
    [RIGHT_SLIDE_IN_START, RIGHT_SLIDE_IN_END, FADEOUT_START, FADEOUT_END],
    [0, 1, 1, 0],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
  );
  const rightSlideOut = interpolate(
    frame,
    [FADEOUT_START, FADEOUT_END],
    [0, 400],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.in(Easing.cubic),
    }
  );
  const rightTranslateX = frame >= FADEOUT_START ? rightSlideOut : rightX;

  // Line counter for code panel (animates 0 → 47)
  const codeLineCount = Math.round(
    interpolate(frame, [CODE_APPEAR_START, CODE_APPEAR_END], [0, 47], {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.out(Easing.cubic),
    })
  );

  // Prompt line counter opacity
  const promptCounterOpacity = interpolate(
    frame,
    [45, 60, FADEOUT_START, FADEOUT_END],
    [0, 1, 1, 0],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
  );

  // Prompt line counter pulse
  const promptPulseScale = interpolate(
    frame,
    [LINE_COUNTER_PULSE_START, LINE_COUNTER_PULSE_START + 5, LINE_COUNTER_PULSE_END],
    [1.0, 1.15, 1.0],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
  );

  // Code line counter opacity
  const codeCounterOpacity = interpolate(
    frame,
    [CODE_APPEAR_START, CODE_APPEAR_START + 10, FADEOUT_START, FADEOUT_END],
    [0, 1, 1, 0],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
  );

  return (
    <AbsoluteFill style={{ backgroundColor: "#0A1628" }}>
      {/* Veo background video */}
      <AbsoluteFill>
        <OffthreadVideo
          src={staticFile("veo/part3_mold.mp4")}
          style={{ width: "100%", height: "100%", objectFit: "cover" }}
          muted
        />
      </AbsoluteFill>

      <AbsoluteFill>
        {/* === Left Panel: Prompt === */}
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
          }}
        >
          {/* Gold tint overlay */}
          <div
            style={{
              position: "absolute",
              inset: 0,
              backgroundColor: GOLD_BG,
              borderRadius: PANEL_RADIUS,
              pointerEvents: "none",
            }}
          />

          {/* Badge */}
          <div style={{ padding: "16px 16px 0 16px", position: "relative", zIndex: 1 }}>
            <PanelBadge text="PROMPT" color={GOLD} pillBg={GOLD_PILL_BG} />
          </div>

          {/* Code area */}
          <div style={{ flex: 1, position: "relative", zIndex: 1 }}>
            <CodePanel
              lines={PROMPT_LINES}
              variant="prompt"
              keywordColor={GOLD_LIGHT}
              stringColor={GOLD}
            />
          </div>

          {/* Line counter */}
          <div
            style={{
              position: "absolute",
              bottom: 16,
              left: 16,
              fontFamily: "Inter, sans-serif",
              fontWeight: 500,
              fontSize: 18,
              color: GOLD,
              opacity: promptCounterOpacity,
              transform: `scale(${promptPulseScale})`,
              transformOrigin: "left bottom",
              zIndex: 1,
            }}
          >
            8 lines
          </div>
        </div>

        {/* === Vertical Divider === */}
        <VerticalDivider />

        {/* === Right Panel: Generated Code === */}
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
          }}
        >
          {/* Blue tint overlay */}
          <div
            style={{
              position: "absolute",
              inset: 0,
              backgroundColor: BLUE_BG,
              borderRadius: PANEL_RADIUS,
              pointerEvents: "none",
            }}
          />

          {/* Badge */}
          <div style={{ padding: "16px 16px 0 16px", position: "relative", zIndex: 1 }}>
            <PanelBadge text="GENERATED CODE" color={BLUE} pillBg={BLUE_PILL_BG} />
          </div>

          {/* Code area */}
          <div style={{ flex: 1, position: "relative", zIndex: 1 }}>
            <CodePanel
              lines={GENERATED_LINES}
              variant="code"
              keywordColor={BLUE_LIGHT}
              stringColor={BLUE}
            />
          </div>

          {/* Line counter */}
          <div
            style={{
              position: "absolute",
              bottom: 16,
              left: 16,
              fontFamily: "Inter, sans-serif",
              fontWeight: 500,
              fontSize: 18,
              color: BLUE,
              opacity: codeCounterOpacity,
              zIndex: 1,
            }}
          >
            {codeLineCount} lines
          </div>
        </div>

        {/* === Ratio Callout === */}
        <RatioCallout />
      </AbsoluteFill>
    </AbsoluteFill>
  );
};

export default Part3Mold06SplitPromptVsCode;
