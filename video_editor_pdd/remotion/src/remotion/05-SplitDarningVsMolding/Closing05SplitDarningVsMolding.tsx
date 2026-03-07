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
import { NeedleIcon } from "./NeedleIcon";
import { MoldIcon } from "./MoldIcon";
import { CostCurve } from "./CostCurve";
import { VerticalDivider } from "./VerticalDivider";
import {
  LEFT_PANEL,
  RIGHT_PANEL,
  RED,
  RED_BG,
  GREEN,
  GREEN_BG,
  BG_COLOR,
  FONT_FAMILY,
  PANEL_SPRING,
  PANEL_SLIDE_END,
  LEFT_HEADER_FADE_START,
  LEFT_HEADER_FADE_END,
  RIGHT_HEADER_FADE_START,
  RIGHT_HEADER_FADE_END,
  LEFT_CURVE_DRAW_START,
  LEFT_CURVE_DRAW_END,
  RIGHT_CURVE_DRAW_START,
  RIGHT_CURVE_DRAW_END,
  FOOTER_FADE_START,
  FOOTER_FADE_END,
  FADEOUT_START,
  FADEOUT_END,
} from "./constants";

export const defaultClosing05SplitDarningVsMoldingProps = {};

export const Closing05SplitDarningVsMolding: React.FC = () => {
  const frame = useCurrentFrame();
  const { fps } = useVideoConfig();

  // ── Left panel slide-in (spring) ──
  const leftSpring = spring({
    frame,
    fps,
    config: PANEL_SPRING,
  });
  const leftSlideIn = interpolate(leftSpring, [0, 1], [-960, 0]);

  const leftOpacity = interpolate(
    frame,
    [0, PANEL_SLIDE_END, FADEOUT_START, FADEOUT_END],
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
    frame,
    fps,
    config: PANEL_SPRING,
  });
  const rightSlideIn = interpolate(rightSpring, [0, 1], [960, 0]);

  const rightOpacity = interpolate(
    frame,
    [0, PANEL_SLIDE_END, FADEOUT_START, FADEOUT_END],
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
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.out(Easing.quad),
    },
  );

  return (
    <AbsoluteFill style={{ backgroundColor: BG_COLOR }}>
      {/* Veo background video */}
      <AbsoluteFill>
        <OffthreadVideo
          src={staticFile("veo/closing.mp4")}
          style={{ width: "100%", height: "100%", objectFit: "cover" }}
          muted
        />
      </AbsoluteFill>

      <AbsoluteFill>
        {/* === Left Panel: Darning === */}
        <SplitPanel
          x={LEFT_PANEL.x}
          y={LEFT_PANEL.y}
          w={LEFT_PANEL.w}
          h={LEFT_PANEL.h}
          tintBg={RED_BG}
          accentColor={RED}
          header="DARNING"
          icon={<NeedleIcon color={RED} size={90} opacity={0.3} />}
          costCurve={
            <CostCurve
              type="exponential"
              color={RED}
              drawStart={LEFT_CURVE_DRAW_START}
              drawEnd={LEFT_CURVE_DRAW_END}
              label="Cost rises over time"
            />
          }
          outcome="FRAGILE"
          translateX={leftTranslateX}
          opacity={leftOpacity}
          headerFadeStart={LEFT_HEADER_FADE_START}
          headerFadeEnd={LEFT_HEADER_FADE_END}
        />

        {/* === Vertical Divider === */}
        <VerticalDivider />

        {/* === Right Panel: Molding === */}
        <SplitPanel
          x={RIGHT_PANEL.x}
          y={RIGHT_PANEL.y}
          w={RIGHT_PANEL.w}
          h={RIGHT_PANEL.h}
          tintBg={GREEN_BG}
          accentColor={GREEN}
          header="MOLDING"
          icon={<MoldIcon color={GREEN} size={90} opacity={0.3} />}
          costCurve={
            <CostCurve
              type="flat"
              color={GREEN}
              drawStart={RIGHT_CURVE_DRAW_START}
              drawEnd={RIGHT_CURVE_DRAW_END}
              label="Cost stays flat"
            />
          }
          outcome="RESILIENT"
          translateX={rightTranslateX}
          opacity={rightOpacity}
          headerFadeStart={RIGHT_HEADER_FADE_START}
          headerFadeEnd={RIGHT_HEADER_FADE_END}
        />

        {/* === Footer === */}
        <div
          style={{
            position: "absolute",
            bottom: 36,
            left: 0,
            width: 1920,
            textAlign: "center",
            fontFamily: FONT_FAMILY,
            fontWeight: 700,
            fontSize: 28,
            color: "#FFFFFF",
            opacity: footerOpacity,
            textShadow: "0 2px 12px rgba(0, 0, 0, 0.5)",
          }}
        >
          Stop darning. Start molding.
        </div>
      </AbsoluteFill>
    </AbsoluteFill>
  );
};

export default Closing05SplitDarningVsMolding;
