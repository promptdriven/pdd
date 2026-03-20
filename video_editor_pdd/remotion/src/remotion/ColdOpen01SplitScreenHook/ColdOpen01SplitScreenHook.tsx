import React from "react";
import {
  AbsoluteFill,
  Sequence,
  OffthreadVideo,
  useCurrentFrame,
  interpolate,
  Easing,
} from "remotion";
import { useVisualMediaAssetSrc } from "../_shared/visual-runtime";
import FilmGrain from "./FilmGrain";
import DividerGlow from "./DividerGlow";
import {
  CANVAS_WIDTH,
  CANVAS_HEIGHT,
  TOTAL_FRAMES,
  BG_COLOR,
  DIVIDER_X,
  DIVIDER_WIDTH,
  DIVIDER_COLOR,
  DIVIDER_OPACITY,
  LEFT_PANEL_WIDTH,
  RIGHT_PANEL_X,
  RIGHT_PANEL_WIDTH,
  LEFT_TINT_COLOR,
  LEFT_TINT_OPACITY,
  LEFT_VIGNETTE_COLOR,
  LEFT_VIGNETTE_OPACITY,
  LEFT_LABEL,
  LEFT_LABEL_X,
  LEFT_LABEL_Y,
  RIGHT_TINT_COLOR,
  RIGHT_TINT_OPACITY,
  RIGHT_VIGNETTE_COLOR,
  RIGHT_VIGNETTE_OPACITY,
  RIGHT_LABEL,
  RIGHT_LABEL_X,
  RIGHT_LABEL_Y,
  GRAIN_OPACITY,
  GRAIN_FPS,
  FADE_IN_END,
  GLOW_START,
  GLOW_DURATION,
  GLOW_CYCLE_FRAMES,
  GLOW_COLOR_LEFT,
  GLOW_COLOR_RIGHT,
  GLOW_OPACITY,
  LABEL_FONT_FAMILY,
  LABEL_FONT_SIZE,
  LABEL_FONT_WEIGHT,
  LABEL_COLOR,
  LABEL_OPACITY,
} from "./constants";

// ─── Default props (required by export contract) ───────────────────
export const defaultColdOpen01SplitScreenHookProps = {};

// ─── Panel header label ────────────────────────────────────────────
const PanelLabel: React.FC<{ text: string; x: number; y: number }> = ({
  text,
  x,
  y,
}) => (
  <div
    style={{
      position: "absolute",
      left: x,
      top: y,
      fontFamily: LABEL_FONT_FAMILY,
      fontSize: LABEL_FONT_SIZE,
      fontWeight: LABEL_FONT_WEIGHT,
      color: LABEL_COLOR,
      opacity: LABEL_OPACITY,
      letterSpacing: "0.05em",
      zIndex: 10,
      pointerEvents: "none",
    }}
  >
    {text}
  </div>
);

// ─── Vignette overlay ──────────────────────────────────────────────
const Vignette: React.FC<{
  vignetteColor: string;
  vignetteOpacity: number;
  width: number;
  height: number;
}> = ({ vignetteColor, vignetteOpacity, width, height }) => (
  <div
    style={{
      position: "absolute",
      top: 0,
      left: 0,
      width,
      height,
      background: `radial-gradient(ellipse at center, transparent 40%, ${vignetteColor} 100%)`,
      opacity: vignetteOpacity,
      pointerEvents: "none",
    }}
  />
);

// ─── Color grading tint ────────────────────────────────────────────
const ColorGrade: React.FC<{
  tintColor: string;
  tintOpacity: number;
  width: number;
  height: number;
}> = ({ tintColor, tintOpacity, width, height }) => (
  <div
    style={{
      position: "absolute",
      top: 0,
      left: 0,
      width,
      height,
      backgroundColor: tintColor,
      opacity: tintOpacity,
      pointerEvents: "none",
    }}
  />
);

// ─── Main component ────────────────────────────────────────────────
export const ColdOpen01SplitScreenHook: React.FC = () => {
  const frame = useCurrentFrame();

  // Resolve media via visual-runtime context with Veo static fallbacks
  const leftSrc = useVisualMediaAssetSrc(
    "leftSrc",
    "veo/developer_cursor_edit.mp4"
  );
  const rightSrc = useVisualMediaAssetSrc(
    "rightSrc",
    "veo/grandmother_darning.mp4"
  );

  // ─── Fade-in: 0 → 1 over first 15 frames ──────────────────────
  const fadeOpacity = interpolate(frame, [0, FADE_IN_END], [0, 1], {
    easing: Easing.out(Easing.cubic),
    extrapolateLeft: "clamp",
    extrapolateRight: "clamp",
  });

  return (
    <AbsoluteFill
      style={{
        backgroundColor: BG_COLOR,
        width: CANVAS_WIDTH,
        height: CANVAS_HEIGHT,
        overflow: "hidden",
      }}
    >
      {/* ── Fade wrapper ── */}
      <AbsoluteFill style={{ opacity: fadeOpacity }}>
        {/* ════════════════════════════════════════════════
            LEFT PANEL — "2025" developer
            ════════════════════════════════════════════════ */}
        <div
          style={{
            position: "absolute",
            top: 0,
            left: 0,
            width: LEFT_PANEL_WIDTH,
            height: CANVAS_HEIGHT,
            overflow: "hidden",
          }}
        >
          {/* Video */}
          {leftSrc && (
            <OffthreadVideo
              src={leftSrc}
              style={{
                position: "absolute",
                top: 0,
                left: 0,
                width: LEFT_PANEL_WIDTH,
                height: CANVAS_HEIGHT,
                objectFit: "cover",
              }}
              muted
            />
          )}
          {/* Fallback if no video */}
          {!leftSrc && (
            <div
              style={{
                position: "absolute",
                top: 0,
                left: 0,
                width: LEFT_PANEL_WIDTH,
                height: CANVAS_HEIGHT,
                background:
                  "linear-gradient(135deg, #1a1a2e 0%, #16213e 50%, #0f3460 100%)",
              }}
            />
          )}
          {/* Color grade */}
          <ColorGrade
            tintColor={LEFT_TINT_COLOR}
            tintOpacity={LEFT_TINT_OPACITY}
            width={LEFT_PANEL_WIDTH}
            height={CANVAS_HEIGHT}
          />
          {/* Vignette */}
          <Vignette
            vignetteColor={LEFT_VIGNETTE_COLOR}
            vignetteOpacity={LEFT_VIGNETTE_OPACITY}
            width={LEFT_PANEL_WIDTH}
            height={CANVAS_HEIGHT}
          />
          {/* Label */}
          <PanelLabel text={LEFT_LABEL} x={LEFT_LABEL_X} y={LEFT_LABEL_Y} />
        </div>

        {/* ════════════════════════════════════════════════
            RIGHT PANEL — "1955" grandmother
            ════════════════════════════════════════════════ */}
        <div
          style={{
            position: "absolute",
            top: 0,
            left: RIGHT_PANEL_X,
            width: RIGHT_PANEL_WIDTH,
            height: CANVAS_HEIGHT,
            overflow: "hidden",
          }}
        >
          {/* Video */}
          {rightSrc && (
            <OffthreadVideo
              src={rightSrc}
              style={{
                position: "absolute",
                top: 0,
                left: 0,
                width: RIGHT_PANEL_WIDTH,
                height: CANVAS_HEIGHT,
                objectFit: "cover",
              }}
              muted
            />
          )}
          {/* Fallback if no video */}
          {!rightSrc && (
            <div
              style={{
                position: "absolute",
                top: 0,
                left: 0,
                width: RIGHT_PANEL_WIDTH,
                height: CANVAS_HEIGHT,
                background:
                  "linear-gradient(135deg, #2d1b00 0%, #3e2a12 50%, #4a3520 100%)",
              }}
            />
          )}
          {/* Color grade */}
          <ColorGrade
            tintColor={RIGHT_TINT_COLOR}
            tintOpacity={RIGHT_TINT_OPACITY}
            width={RIGHT_PANEL_WIDTH}
            height={CANVAS_HEIGHT}
          />
          {/* Vignette */}
          <Vignette
            vignetteColor={RIGHT_VIGNETTE_COLOR}
            vignetteOpacity={RIGHT_VIGNETTE_OPACITY}
            width={RIGHT_PANEL_WIDTH}
            height={CANVAS_HEIGHT}
          />
          {/* Film grain */}
          <FilmGrain
            opacity={GRAIN_OPACITY}
            grainFps={GRAIN_FPS}
            width={RIGHT_PANEL_WIDTH}
            height={CANVAS_HEIGHT}
          />
          {/* Label */}
          <PanelLabel text={RIGHT_LABEL} x={RIGHT_LABEL_X} y={RIGHT_LABEL_Y} />
        </div>

        {/* ════════════════════════════════════════════════
            DIVIDER — solid vertical line
            ════════════════════════════════════════════════ */}
        <div
          style={{
            position: "absolute",
            top: 0,
            left: DIVIDER_X,
            width: DIVIDER_WIDTH,
            height: CANVAS_HEIGHT,
            backgroundColor: DIVIDER_COLOR,
            opacity: DIVIDER_OPACITY,
            zIndex: 5,
            pointerEvents: "none",
          }}
        />

        {/* ════════════════════════════════════════════════
            DIVIDER GLOW — pulsing gradient at completion
            ════════════════════════════════════════════════ */}
        <Sequence from={GLOW_START} durationInFrames={GLOW_DURATION}>
          <DividerGlow
            x={DIVIDER_X}
            colorTop={GLOW_COLOR_LEFT}
            colorBottom={GLOW_COLOR_RIGHT}
            opacity={GLOW_OPACITY}
            cycleFrames={GLOW_CYCLE_FRAMES}
            canvasHeight={CANVAS_HEIGHT}
          />
        </Sequence>
      </AbsoluteFill>
    </AbsoluteFill>
  );
};

export default ColdOpen01SplitScreenHook;
