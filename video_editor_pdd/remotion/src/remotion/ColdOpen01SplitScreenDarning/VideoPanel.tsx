import React from "react";
import {
  AbsoluteFill,
  OffthreadVideo,
  useCurrentFrame,
  interpolate,
  Easing,
} from "remotion";
import {
  CLIP_A_END,
  CROSSFADE_START,
  CROSSFADE_DURATION,
  PANEL_WIDTH,
  CANVAS_HEIGHT,
} from "./constants";

/**
 * Renders two video clips with a crossfade transition.
 * clipA plays from frame 0 to CLIP_A_END; clipB fades in over
 * CROSSFADE_DURATION starting at CROSSFADE_START and plays to the end.
 */
interface VideoPanelProps {
  clipASrc: string | null;
  clipBSrc: string | null;
}

export const VideoPanel: React.FC<VideoPanelProps> = ({
  clipASrc,
  clipBSrc,
}) => {
  const frame = useCurrentFrame();

  // Crossfade: clipB opacity ramps from 0 → 1 over the overlap window
  const clipBOpacity = interpolate(
    frame,
    [CROSSFADE_START, CROSSFADE_START + CROSSFADE_DURATION],
    [0, 1],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.inOut(Easing.cubic),
    }
  );

  const videoStyle: React.CSSProperties = {
    width: PANEL_WIDTH,
    height: CANVAS_HEIGHT,
    objectFit: "cover",
  };

  return (
    <AbsoluteFill style={{ width: PANEL_WIDTH, height: CANVAS_HEIGHT }}>
      {/* Clip A – visible until crossfade completes */}
      {clipASrc && frame < CLIP_A_END && (
        <AbsoluteFill style={{ opacity: 1 - clipBOpacity }}>
          <OffthreadVideo src={clipASrc} style={videoStyle} />
        </AbsoluteFill>
      )}

      {/* Clip B – fades in at CROSSFADE_START */}
      {clipBSrc && frame >= CROSSFADE_START && (
        <AbsoluteFill style={{ opacity: clipBOpacity }}>
          <OffthreadVideo src={clipBSrc} style={videoStyle} />
        </AbsoluteFill>
      )}
    </AbsoluteFill>
  );
};

export default VideoPanel;
