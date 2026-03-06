import React from "react";
import { useCurrentFrame, interpolate, Easing } from "remotion";
import {
  TRACK_Y,
  TRACK_X_START,
  TRACK_X_END,
  TRACK_THICKNESS,
  TRACK_BASE_COLOR,
  GRADIENT_START,
  GRADIENT_END,
  PANEL_FADE_END,
  NODE3_ACTIVATE,
  NODE1_ACTIVATE,
} from "./constants";

interface TimelineTrackProps {
  globalOpacity: number;
}

export const TimelineTrack: React.FC<TimelineTrackProps> = ({
  globalOpacity,
}) => {
  const frame = useCurrentFrame();

  // Base track fades in with panel
  const baseOpacity = interpolate(frame, [0, PANEL_FADE_END], [0, 1], {
    extrapolateRight: "clamp",
    easing: Easing.out(Easing.cubic),
  });

  // Progress line draws left to right from node1 activate to node3 activate
  const trackLength = TRACK_X_END - TRACK_X_START;
  const progress = interpolate(
    frame,
    [NODE1_ACTIVATE, NODE3_ACTIVATE + 20],
    [0, 1],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.inOut(Easing.cubic),
    }
  );
  const progressWidth = trackLength * progress;

  return (
    <div style={{ opacity: globalOpacity }}>
      {/* Base dim track */}
      <div
        style={{
          position: "absolute",
          left: TRACK_X_START,
          top: TRACK_Y - TRACK_THICKNESS / 2,
          width: trackLength,
          height: TRACK_THICKNESS,
          backgroundColor: TRACK_BASE_COLOR,
          opacity: baseOpacity,
        }}
      />

      {/* Progress gradient overlay */}
      {progress > 0 && (
        <div
          style={{
            position: "absolute",
            left: TRACK_X_START,
            top: TRACK_Y - TRACK_THICKNESS / 2,
            width: progressWidth,
            height: TRACK_THICKNESS,
            background: `linear-gradient(to right, ${GRADIENT_START}, ${GRADIENT_END})`,
            opacity: baseOpacity,
          }}
        />
      )}
    </div>
  );
};

export default TimelineTrack;
