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

  // Segmented progress: draws to each node as it activates
  // Node 1 (x=400) activates at frame 25, line arrives by frame 55
  // Node 2 (x=960) activates at frame 90, line arrives by frame 130
  // Node 3 (x=1520) activates at frame 180, line arrives by frame 220
  const trackLength = TRACK_X_END - TRACK_X_START;

  const node1Frac = (NODES[0].x - TRACK_X_START) / trackLength; // 0
  const node2Frac = (NODES[1].x - TRACK_X_START) / trackLength; // ~0.5
  const node3Frac = (NODES[2].x - TRACK_X_START) / trackLength; // 1

  // Segment 1: draw to node 1 (frames 25-55)
  const seg1 = interpolate(frame, [25, 55], [0, node1Frac], {
    extrapolateLeft: "clamp",
    extrapolateRight: "clamp",
    easing: Easing.inOut(Easing.cubic),
  });

  // Segment 2: draw from node 1 to node 2 (frames 90-130)
  const seg2 = interpolate(frame, [90, 130], [node1Frac, node2Frac], {
    extrapolateLeft: "clamp",
    extrapolateRight: "clamp",
    easing: Easing.inOut(Easing.cubic),
  });

  // Segment 3: draw from node 2 to node 3 (frames 180-220)
  const seg3 = interpolate(frame, [180, 220], [node2Frac, node3Frac], {
    extrapolateLeft: "clamp",
    extrapolateRight: "clamp",
    easing: Easing.inOut(Easing.cubic),
  });

  // Overall progress is the max of all segments
  const progress = Math.max(seg1, seg2, seg3);
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
