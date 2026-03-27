import React from "react";
import {
  AbsoluteFill,
  useCurrentFrame,
  interpolate,
  Easing,
} from "remotion";
import { useVisualMediaAssetSrc } from "../_shared/visual-runtime";
import {
  CANVAS_WIDTH,
  CANVAS_HEIGHT,
  PANEL_WIDTH,
  DIVIDER_GAP,
  DIVIDER_THICKNESS,
  DIVIDER_COLOR,
  DIVIDER_MAX_OPACITY,
  BG_COLOR,
  FADE_IN_END,
} from "./constants";
import { VideoPanel } from "./VideoPanel";

/* ------------------------------------------------------------------ */
/*  Default props (empty — no external data needed)                   */
/* ------------------------------------------------------------------ */
export const defaultColdOpen01SplitScreenDarningProps = {};

/* ------------------------------------------------------------------ */
/*  Main component                                                    */
/* ------------------------------------------------------------------ */
export const ColdOpen01SplitScreenDarning: React.FC = () => {
  const frame = useCurrentFrame();

  /* ---------- resolve media aliases with Veo fallbacks ---------- */
  const leftClipA = useVisualMediaAssetSrc(
    "leftSrc",
    "veo/developer_cursor_edit.mp4"
  );
  const rightClipA = useVisualMediaAssetSrc(
    "rightSrc",
    "veo/grandmother_darning.mp4"
  );
  const leftClipB = useVisualMediaAssetSrc(
    "baseSrc",
    "veo/developer_codebase_zoomout.mp4"
  );
  const rightClipB = useVisualMediaAssetSrc(
    "revealSrc",
    "veo/grandmother_drawer_zoomout.mp4"
  );

  /* ---------- fade-in (frames 0-15) ---------- */
  const masterOpacity = interpolate(frame, [0, FADE_IN_END], [0, 1], {
    extrapolateLeft: "clamp",
    extrapolateRight: "clamp",
    easing: Easing.out(Easing.quad),
  });

  /* ---------- divider opacity ramps with the master fade ---------- */
  const dividerOpacity = masterOpacity * DIVIDER_MAX_OPACITY;

  /* ---------- layout positions ---------- */
  const leftPanelLeft = 0;
  const rightPanelLeft = PANEL_WIDTH + DIVIDER_GAP;
  const dividerLeft = PANEL_WIDTH + (DIVIDER_GAP - DIVIDER_THICKNESS) / 2;

  return (
    <AbsoluteFill
      style={{
        backgroundColor: BG_COLOR,
        width: CANVAS_WIDTH,
        height: CANVAS_HEIGHT,
        overflow: "hidden",
      }}
    >
      {/* ---- Overall fade-in wrapper ---- */}
      <AbsoluteFill style={{ opacity: masterOpacity }}>
        {/* Left panel */}
        <div
          style={{
            position: "absolute",
            left: leftPanelLeft,
            top: 0,
            width: PANEL_WIDTH,
            height: CANVAS_HEIGHT,
            overflow: "hidden",
          }}
        >
          <VideoPanel clipASrc={leftClipA} clipBSrc={leftClipB} />
        </div>

        {/* Right panel */}
        <div
          style={{
            position: "absolute",
            left: rightPanelLeft,
            top: 0,
            width: PANEL_WIDTH,
            height: CANVAS_HEIGHT,
            overflow: "hidden",
          }}
        >
          <VideoPanel clipASrc={rightClipA} clipBSrc={rightClipB} />
        </div>

        {/* Center divider */}
        <div
          style={{
            position: "absolute",
            left: dividerLeft,
            top: 0,
            width: DIVIDER_THICKNESS,
            height: CANVAS_HEIGHT,
            backgroundColor: DIVIDER_COLOR,
            opacity: dividerOpacity,
          }}
        />
      </AbsoluteFill>
    </AbsoluteFill>
  );
};

export default ColdOpen01SplitScreenDarning;
