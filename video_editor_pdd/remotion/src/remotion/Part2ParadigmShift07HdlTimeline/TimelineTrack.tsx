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
  NODES,
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

  const trackLength = TRACK_X_END - TRACK_X_START;

  // Progress draws in three segments, matching node activations:
  // Node 1 (x=400) is at the track start (0%). Draw a small stub past it.
  // Node 2 (x=960) is at 50% of the track.
  // Node 3 (x=1520) is at 100%.
  const node2Frac = (NODES[1].x - TRACK_X_START) / trackLength; // 0.5

  // Frames 25-55: draw small stub past Node 1
  // Frames 55-90: hold
  // Frames 90-130: extend to Node 2 (50%)
  // Frames 130-180: hold
  // Frames 180-220: extend to Node 3 (100%)
  const progress = interpolate(
    frame,
    [25, 55, 90, 130, 180, 220],
    [0, 0.05, 0.05, node2Frac, node2Frac, 1],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
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
