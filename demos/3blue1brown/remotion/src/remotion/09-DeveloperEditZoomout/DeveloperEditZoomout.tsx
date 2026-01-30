import React from "react";
import {
  AbsoluteFill,
  interpolate,
  useCurrentFrame,
  Easing,
} from "remotion";
import { CodeView } from "./CodeView";
import { FileGrid } from "./FileGrid";
import { PatchMarkers } from "./PatchMarkers";
import { TodoComments } from "./TodoComments";
import { BugIndicator } from "./BugIndicator";
import {
  COLORS,
  BEATS,
  WORLD,
  EDITOR_REGION,
  DeveloperEditZoomoutPropsType,
} from "./constants";

/**
 * Main composition: IDE code view zooms out to reveal a massive codebase
 * with patch markers, TODO comments, and a new bug appearing.
 *
 * The zoom is implemented via an animated SVG viewBox that starts
 * focused on the editor region and pulls back to show the full world.
 */
export const DeveloperEditZoomout: React.FC<DeveloperEditZoomoutPropsType> = ({
  showNarration = true,
}) => {
  const frame = useCurrentFrame();

  // --- Zoom camera ---
  // Start: tight on the editor region
  // End: full world view
  const zoomProgress = interpolate(
    frame,
    [BEATS.TRANSITION_START, BEATS.ZOOM_END],
    [0, 1],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.inOut(Easing.cubic),
    }
  );

  // viewBox interpolation: from editor region to full world
  const vbX = interpolate(zoomProgress, [0, 1], [
    EDITOR_REGION.x - 40,
    0,
  ]);
  const vbY = interpolate(zoomProgress, [0, 1], [
    EDITOR_REGION.y - 30,
    0,
  ]);
  const vbW = interpolate(zoomProgress, [0, 1], [
    EDITOR_REGION.width + 80,
    WORLD.width,
  ]);
  const vbH = interpolate(zoomProgress, [0, 1], [
    EDITOR_REGION.height + 60,
    WORLD.height,
  ]);

  // Code view fades out as we zoom past it
  const codeOpacity = interpolate(
    frame,
    [BEATS.ZOOM_START, BEATS.ZOOM_START + 60],
    [1, 0],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
  );

  // Narration
  const narrationOpacity = showNarration
    ? interpolate(
        frame,
        [BEATS.NARRATION_START, BEATS.NARRATION_START + 25],
        [0, 1],
        {
          extrapolateLeft: "clamp",
          extrapolateRight: "clamp",
          easing: Easing.out(Easing.cubic),
        }
      )
    : 0;

  return (
    <AbsoluteFill
      style={{
        background: `linear-gradient(180deg, ${COLORS.BACKGROUND} 0%, ${COLORS.BACKGROUND_GRADIENT} 100%)`,
      }}
    >
      {/* Animated SVG world */}
      <svg
        width="1920"
        height="1080"
        viewBox={`${vbX} ${vbY} ${vbW} ${vbH}`}
        style={{ position: "absolute", top: 0, left: 0 }}
        preserveAspectRatio="xMidYMid meet"
      >
        {/* File grid (the entire codebase) */}
        <FileGrid frame={frame} />

        {/* Patch markers on files */}
        <PatchMarkers frame={frame} />

        {/* TODO comment labels */}
        <TodoComments frame={frame} />

        {/* Stylized code editor (fades as we zoom out) */}
        <CodeView opacity={codeOpacity} />

        {/* New bug indicator */}
        <BugIndicator frame={frame} />
      </svg>

      {/* Narration overlay (rendered in screen-space, not world-space) */}
      {narrationOpacity > 0 && (
        <div
          style={{
            position: "absolute",
            bottom: 80,
            left: 0,
            right: 0,
            textAlign: "center",
            opacity: narrationOpacity,
          }}
        >
          <div
            style={{
              display: "inline-block",
              fontSize: 34,
              fontFamily: "sans-serif",
              fontWeight: 400,
              color: COLORS.LABEL_WHITE,
              lineHeight: 1.5,
              letterSpacing: 0.5,
            }}
          >
            {"\u201C"}But they{"\u2019"}re still darning needles.{"\u201D"}
          </div>
        </div>
      )}
    </AbsoluteFill>
  );
};
