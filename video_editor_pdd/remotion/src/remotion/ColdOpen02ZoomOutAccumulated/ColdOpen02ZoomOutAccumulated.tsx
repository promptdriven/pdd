import React from "react";
import {
  AbsoluteFill,
  interpolate,
  Easing,
  useCurrentFrame,
  Sequence,
} from "remotion";
import {
  BG_COLOR,
  SPLIT_X,
  LEFT_PANEL_WIDTH,
  RIGHT_PANEL_WIDTH,
  DIVIDER_WIDTH,
  DIVIDER_COLOR,
  DIVIDER_OPACITY,
  ZOOM_START_SCALE,
  ZOOM_END_SCALE,
  ZOOM_START_FRAME,
  ZOOM_DURATION,
  COUNTER_START_FRAME,
  COUNTER_DURATION,
  PATCHES_FINAL,
  MENDED_FINAL,
  COUNTER_BLUE,
  STITCH_AMBER,
  HEIGHT,
  CODE_TILE_BG,
  CODE_TEXT_SLATE,
  CODE_KEYWORD_PURPLE,
  DIFF_GREEN,
  GARMENT_SOCK,
} from "./constants";
import { CodeTileGrid } from "./CodeTileGrid";
import { MendedDrawer } from "./MendedDrawer";
import { AnimatedCounter } from "./AnimatedCounter";

// ── Initial state components (what's shown during the hold at frames 0-15) ──

/** Single code edit block visible before the zoom-out */
const InitialCodeEdit: React.FC = () => {
  return (
    <div
      style={{
        position: "absolute",
        left: "50%",
        top: "50%",
        transform: "translate(-50%, -50%)",
        width: 320,
        height: 220,
        backgroundColor: CODE_TILE_BG,
        borderRadius: 8,
        padding: 20,
        boxSizing: "border-box",
        border: "1px solid #1E293B",
      }}
    >
      {/* Code lines */}
      {[
        { text: "function validateInput(data) {", color: CODE_KEYWORD_PURPLE },
        { text: "  if (data === null) {", color: CODE_TEXT_SLATE },
        {
          text: "+   return { valid: false };",
          color: DIFF_GREEN,
        },
        { text: "  }", color: CODE_TEXT_SLATE },
        { text: "  const result = parse(data);", color: CODE_TEXT_SLATE },
        { text: "+   if (!result.ok) return err;", color: DIFF_GREEN },
        { text: "  return { valid: true };", color: CODE_TEXT_SLATE },
        { text: "}", color: CODE_TEXT_SLATE },
      ].map((line, i) => (
        <div
          key={i}
          style={{
            fontFamily: "'JetBrains Mono', monospace",
            fontSize: 11,
            lineHeight: "20px",
            color: line.color,
            whiteSpace: "nowrap",
          }}
        >
          {line.text}
        </div>
      ))}
    </div>
  );
};

/** Single darned sock visible before the zoom-out */
const InitialDarnedSock: React.FC = () => {
  return (
    <div
      style={{
        position: "absolute",
        left: "50%",
        top: "50%",
        transform: "translate(-50%, -50%)",
      }}
    >
      {/* Sock shape */}
      <div
        style={{
          width: 140,
          height: 200,
          backgroundColor: GARMENT_SOCK,
          borderRadius: "30px 30px 60px 60px",
          position: "relative",
          overflow: "hidden",
          border: "2px solid #7A6B5A",
        }}
      >
        {/* Darning patch */}
        <div
          style={{
            position: "absolute",
            bottom: 30,
            left: "50%",
            transform: "translateX(-50%)",
            width: 60,
            height: 60,
            borderRadius: "50%",
            overflow: "hidden",
          }}
        >
          {/* Crosshatch stitching */}
          <svg width={60} height={60} viewBox="0 0 60 60">
            {Array.from({ length: 10 }).map((_, i) => (
              <React.Fragment key={i}>
                <line
                  x1={i * 7}
                  y1={0}
                  x2={i * 7}
                  y2={60}
                  stroke={STITCH_AMBER}
                  strokeWidth={1.2}
                  opacity={0.6}
                />
                <line
                  x1={0}
                  y1={i * 7}
                  x2={60}
                  y2={i * 7}
                  stroke={STITCH_AMBER}
                  strokeWidth={1.2}
                  opacity={0.6}
                />
              </React.Fragment>
            ))}
          </svg>
        </div>
      </div>
    </div>
  );
};

// ── Main component ──

export const defaultColdOpen02ZoomOutAccumulatedProps = {};

export const ColdOpen02ZoomOutAccumulated: React.FC = () => {
  const frame = useCurrentFrame();

  // ── Zoom animation (frames 15-120) ──
  const zoomProgress = interpolate(
    frame,
    [ZOOM_START_FRAME, ZOOM_START_FRAME + ZOOM_DURATION],
    [0, 1],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.inOut(Easing.cubic),
    }
  );

  const currentScale = interpolate(
    zoomProgress,
    [0, 1],
    [ZOOM_START_SCALE, ZOOM_END_SCALE]
  );

  // Fade from initial single-item view to the full grid
  const initialOpacity = interpolate(frame, [15, 45], [1, 0], {
    extrapolateLeft: "clamp",
    extrapolateRight: "clamp",
  });

  const gridOpacity = interpolate(frame, [15, 45], [0, 1], {
    extrapolateLeft: "clamp",
    extrapolateRight: "clamp",
  });

  return (
    <AbsoluteFill style={{ backgroundColor: BG_COLOR }}>
      {/* ── Left Panel: Code ── */}
      <div
        style={{
          position: "absolute",
          left: 0,
          top: 0,
          width: LEFT_PANEL_WIDTH,
          height: HEIGHT,
          overflow: "hidden",
        }}
      >
        {/* Initial single edit (fades out during zoom) */}
        <div style={{ opacity: initialOpacity }}>
          <InitialCodeEdit />
        </div>

        {/* Full codebase grid (zooms out) */}
        <div
          style={{
            position: "absolute",
            inset: 0,
            opacity: gridOpacity,
            transform: `scale(${currentScale})`,
            transformOrigin: "center center",
          }}
        >
          <CodeTileGrid revealStartFrame={20} />
        </div>

        {/* Patches counter */}
        <Sequence from={COUNTER_START_FRAME}>
          <AnimatedCounter
            startValue={1}
            endValue={PATCHES_FINAL}
            prefix="patches: "
            fontFamily="JetBrains Mono"
            fontSize={14}
            color={COUNTER_BLUE}
            opacity={0.6}
            x={40}
            y={1020}
            startFrame={0}
            duration={COUNTER_DURATION}
            align="left"
          />
        </Sequence>
      </div>

      {/* ── Split Divider ── */}
      <div
        style={{
          position: "absolute",
          left: SPLIT_X - DIVIDER_WIDTH / 2,
          top: 0,
          width: DIVIDER_WIDTH,
          height: HEIGHT,
          backgroundColor: DIVIDER_COLOR,
          opacity: DIVIDER_OPACITY,
        }}
      />

      {/* ── Right Panel: Garments ── */}
      <div
        style={{
          position: "absolute",
          left: SPLIT_X + DIVIDER_WIDTH / 2,
          top: 0,
          width: RIGHT_PANEL_WIDTH,
          height: HEIGHT,
          overflow: "hidden",
        }}
      >
        {/* Initial single sock (fades out during zoom) */}
        <div style={{ opacity: initialOpacity }}>
          <InitialDarnedSock />
        </div>

        {/* Full mended drawer (zooms out) */}
        <div
          style={{
            position: "absolute",
            inset: 0,
            opacity: gridOpacity,
            transform: `scale(${currentScale})`,
            transformOrigin: "center center",
          }}
        >
          <MendedDrawer revealStartFrame={20} />
        </div>

        {/* Mended counter */}
        <Sequence from={COUNTER_START_FRAME}>
          <AnimatedCounter
            startValue={1}
            endValue={MENDED_FINAL}
            prefix="mended: "
            fontFamily="Inter"
            fontSize={14}
            color={STITCH_AMBER}
            opacity={0.6}
            x={1860}
            y={1020}
            startFrame={0}
            duration={COUNTER_DURATION}
            align="right"
          />
        </Sequence>
      </div>
    </AbsoluteFill>
  );
};

export default ColdOpen02ZoomOutAccumulated;
