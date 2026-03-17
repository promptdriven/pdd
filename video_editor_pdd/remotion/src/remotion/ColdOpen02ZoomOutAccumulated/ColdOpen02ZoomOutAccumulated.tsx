import React from "react";
import {
  AbsoluteFill,
  useCurrentFrame,
  interpolate,
  Easing,
} from "remotion";
import {
  BG_COLOR,
  TOTAL_FRAMES,
  SPLIT_X,
  DIVIDER_WIDTH,
  DIVIDER_COLOR,
  DIVIDER_OPACITY,
  LEFT_PANEL_WIDTH,
  RIGHT_PANEL_X,
  RIGHT_PANEL_WIDTH,
  ZOOM_START_FRAME,
  ZOOM_DURATION,
  ZOOM_END_FRAME,
  ZOOM_START_SCALE,
  ZOOM_END_SCALE,
  PATCH_COUNTER_X,
  PATCH_COUNTER_Y,
  PATCH_COUNTER_COLOR,
  PATCH_COUNTER_OPACITY,
  PATCH_COUNTER_FINAL,
  MENDED_COUNTER_X,
  MENDED_COUNTER_Y,
  MENDED_COUNTER_COLOR,
  MENDED_COUNTER_OPACITY,
  MENDED_COUNTER_FINAL,
} from "./constants";
import { CodeTileGrid } from "./CodeTileGrid";
import { MendedDrawer } from "./MendedDrawer";
import { AnimatedCounter } from "./AnimatedCounter";
import { InitialCodeBlock } from "./InitialCodeBlock";
import { InitialSock } from "./InitialSock";

export const defaultColdOpen02ZoomOutAccumulatedProps = {};

export const ColdOpen02ZoomOutAccumulated: React.FC = () => {
  const frame = useCurrentFrame();

  // Zoom progress: 0 at frame 15, 1 at frame 120
  const zoomProgress = interpolate(
    frame,
    [ZOOM_START_FRAME, ZOOM_END_FRAME],
    [0, 1],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
  );

  // Smooth easeInOut(cubic) for the zoom
  const easedZoom = Easing.bezier(0.42, 0, 0.58, 1)(zoomProgress);

  // Scale interpolation: 1.0 → 0.15
  const scale = interpolate(easedZoom, [0, 1], [ZOOM_START_SCALE, ZOOM_END_SCALE]);

  // Initial items fade out as zoom progresses (they get replaced by grid)
  const initialFadeOut = interpolate(
    frame,
    [ZOOM_START_FRAME, ZOOM_START_FRAME + 40],
    [1, 0],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
  );

  // Reveal progress for tiles/garments (0 to 1 during zoom)
  const revealProgress = interpolate(
    frame,
    [ZOOM_START_FRAME + 10, ZOOM_END_FRAME + 30],
    [0, 1],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
  );

  return (
    <AbsoluteFill style={{ backgroundColor: BG_COLOR }}>
      {/* LEFT PANEL — Code codebase zoom out */}
      <div
        style={{
          position: "absolute",
          left: 0,
          top: 0,
          width: LEFT_PANEL_WIDTH,
          height: 1080,
          overflow: "hidden",
        }}
      >
        {/* Zooming container */}
        <div
          style={{
            position: "absolute",
            left: LEFT_PANEL_WIDTH / 2,
            top: 540,
            width: LEFT_PANEL_WIDTH,
            height: 1080,
            transform: `translate(-50%, -50%) scale(${scale})`,
            transformOrigin: "center center",
          }}
        >
          {/* Code tile grid (revealed during zoom) */}
          <CodeTileGrid revealProgress={revealProgress} />

          {/* Initial code block (visible before zoom, fades out) */}
          <div style={{ opacity: initialFadeOut }}>
            <InitialCodeBlock />
          </div>
        </div>

        {/* Patch counter (outside zoom container, fixed position) */}
        <AnimatedCounter
          startValue={1}
          endValue={PATCH_COUNTER_FINAL}
          prefix="patches: "
          fontFamily="'JetBrains Mono', monospace"
          color={PATCH_COUNTER_COLOR}
          opacity={PATCH_COUNTER_OPACITY}
          x={PATCH_COUNTER_X}
          y={PATCH_COUNTER_Y}
          align="left"
        />
      </div>

      {/* SPLIT DIVIDER */}
      <div
        style={{
          position: "absolute",
          left: SPLIT_X - DIVIDER_WIDTH / 2,
          top: 0,
          width: DIVIDER_WIDTH,
          height: 1080,
          backgroundColor: DIVIDER_COLOR,
          opacity: DIVIDER_OPACITY,
        }}
      />

      {/* RIGHT PANEL — Mended garments zoom out */}
      <div
        style={{
          position: "absolute",
          left: RIGHT_PANEL_X,
          top: 0,
          width: RIGHT_PANEL_WIDTH,
          height: 1080,
          overflow: "hidden",
        }}
      >
        {/* Zooming container */}
        <div
          style={{
            position: "absolute",
            left: RIGHT_PANEL_WIDTH / 2,
            top: 540,
            width: RIGHT_PANEL_WIDTH,
            height: 1080,
            transform: `translate(-50%, -50%) scale(${scale})`,
            transformOrigin: "center center",
          }}
        >
          {/* Mended drawer (revealed during zoom) */}
          <MendedDrawer revealProgress={revealProgress} />

          {/* Initial sock (visible before zoom, fades out) */}
          <div style={{ opacity: initialFadeOut }}>
            <InitialSock />
          </div>
        </div>

        {/* Mended counter (outside zoom container, fixed position) */}
        <AnimatedCounter
          startValue={1}
          endValue={MENDED_COUNTER_FINAL}
          prefix="mended: "
          fontFamily="'Inter', sans-serif"
          color={MENDED_COUNTER_COLOR}
          opacity={MENDED_COUNTER_OPACITY}
          x={MENDED_COUNTER_X}
          y={MENDED_COUNTER_Y}
          align="right"
        />
      </div>
    </AbsoluteFill>
  );
};

export default ColdOpen02ZoomOutAccumulated;
