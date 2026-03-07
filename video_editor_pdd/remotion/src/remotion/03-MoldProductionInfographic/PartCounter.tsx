import React from "react";
import { useCurrentFrame, interpolate } from "remotion";
import {
  COUNTER_X,
  COUNTER_Y,
  STREAM_START,
  STREAM_FAST_START,
  STREAM_PAUSE,
  NORMAL_INTERVAL,
  FAST_INTERVAL,
  TEXT_WHITE,
  TEXT_MUTED,
  FADEOUT_START,
  FADEOUT_END,
} from "./constants";

export const PartCounter: React.FC = () => {
  const frame = useCurrentFrame();

  const opacity = interpolate(
    frame,
    [STREAM_START, STREAM_START + 20, FADEOUT_START, FADEOUT_END],
    [0, 1, 1, 0],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
  );

  if (opacity <= 0) return null;

  // Count parts based on current frame
  let count = 0;

  if (frame >= STREAM_START) {
    // Phase 1: normal interval
    const phase1End = Math.min(frame, STREAM_FAST_START);
    count += Math.floor((phase1End - STREAM_START) / NORMAL_INTERVAL) + 1;

    // Phase 2: fast interval — skip-count to suggest massive scale
    if (frame >= STREAM_FAST_START) {
      const phase2End = Math.min(frame, STREAM_PAUSE);
      const fastParts = Math.floor(
        (phase2End - STREAM_FAST_START) / FAST_INTERVAL
      );
      // Each fast part represents ~50 parts for dramatic effect
      count += fastParts * 50;
    }

    // After pause, show 1000+
    if (frame >= STREAM_PAUSE) {
      count = 1000;
    }
  }

  const displayText = count >= 1000 ? "1,000+" : count.toLocaleString();

  return (
    <div
      style={{
        position: "absolute",
        left: COUNTER_X,
        top: COUNTER_Y,
        opacity,
        display: "flex",
        alignItems: "baseline",
        gap: 4,
      }}
    >
      <span
        style={{
          fontFamily: "Inter, sans-serif",
          fontWeight: 500,
          fontSize: 24,
          color: TEXT_MUTED,
        }}
      >
        ×
      </span>
      <span
        style={{
          fontFamily: "'JetBrains Mono', 'Fira Code', monospace",
          fontWeight: 700,
          fontSize: 36,
          color: TEXT_WHITE,
          letterSpacing: "0.02em",
        }}
      >
        {displayText}
      </span>
    </div>
  );
};

export default PartCounter;
