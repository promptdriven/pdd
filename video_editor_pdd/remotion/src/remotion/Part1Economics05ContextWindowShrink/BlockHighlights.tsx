import React from "react";
import { useCurrentFrame, interpolate, Easing } from "remotion";
import {
  GRID_CENTER_X,
  GRID_CENTER_Y,
  GRID_MAX_SIZE,
  CONTEXT_WINDOW_W,
  CONTEXT_WINDOW_H,
  RED_HIGHLIGHT,
  GREEN_HIGHLIGHT,
  RED_HIGHLIGHTS,
  GREEN_HIGHLIGHTS,
  HIGHLIGHTS_START,
  HIGHLIGHTS_STAGGER,
  HOLD_START,
  PULSE_CYCLE,
} from "./constants";

/**
 * BlockHighlights — shows red blocks inside the context window
 * (irrelevant code grabbed by AI) and green blocks outside
 * (needed code that couldn't be seen).
 *
 * Green blocks pulse after the hold phase starts.
 */
export const BlockHighlights: React.FC = () => {
  const frame = useCurrentFrame();

  // At this point the grid is 32x32
  const gridSize = 32;
  const gap = 2;
  const totalGap = (gridSize - 1) * gap;
  const blockSize = (GRID_MAX_SIZE - totalGap) / gridSize;
  const gridLeft = GRID_CENTER_X - GRID_MAX_SIZE / 2;
  const gridTop = GRID_CENTER_Y - GRID_MAX_SIZE / 2;

  // Context window bounds
  const cwLeft = GRID_CENTER_X - CONTEXT_WINDOW_W / 2;
  const cwTop = GRID_CENTER_Y - CONTEXT_WINDOW_H / 2;

  const highlights: React.ReactNode[] = [];

  // Red highlights (inside window — irrelevant code)
  RED_HIGHLIGHTS.forEach((pos, i) => {
    const appearFrame = HIGHLIGHTS_START + i * HIGHLIGHTS_STAGGER;
    const opacity = interpolate(
      frame,
      [appearFrame, appearFrame + 15],
      [0, 1],
      {
        extrapolateLeft: "clamp",
        extrapolateRight: "clamp",
        easing: Easing.out(Easing.quad),
      }
    );

    if (opacity <= 0) return;

    // Position relative to context window, spread within window area
    const x = cwLeft + (pos.col / 8) * (CONTEXT_WINDOW_W - blockSize * 2) + blockSize * 0.5;
    const y = cwTop + (pos.row / 8) * (CONTEXT_WINDOW_H - blockSize * 2) + blockSize * 0.5;

    highlights.push(
      <div
        key={`red-${i}`}
        style={{
          position: "absolute",
          left: x,
          top: y,
          width: blockSize,
          height: blockSize,
          backgroundColor: `rgba(231, 76, 60, 0.15)`,
          border: `1px solid rgba(231, 76, 60, 0.3)`,
          borderRadius: 2,
          opacity,
        }}
      >
        <span
          style={{
            position: "absolute",
            top: 1,
            right: 3,
            fontSize: 8,
            color: RED_HIGHLIGHT,
            fontWeight: 700,
          }}
        >
          ✗
        </span>
      </div>
    );
  });

  // Green highlights (outside window — needed code)
  GREEN_HIGHLIGHTS.forEach((pos, i) => {
    const appearFrame =
      HIGHLIGHTS_START +
      RED_HIGHLIGHTS.length * HIGHLIGHTS_STAGGER +
      i * HIGHLIGHTS_STAGGER;
    const opacity = interpolate(
      frame,
      [appearFrame, appearFrame + 15],
      [0, 1],
      {
        extrapolateLeft: "clamp",
        extrapolateRight: "clamp",
        easing: Easing.out(Easing.quad),
      }
    );

    if (opacity <= 0) return;

    // Pulse effect during hold phase
    let pulseGlow = 0.15;
    if (frame >= HOLD_START) {
      const pulsePhase =
        ((frame - HOLD_START + i * 7) % PULSE_CYCLE) / PULSE_CYCLE;
      pulseGlow = interpolate(
        pulsePhase,
        [0, 0.5, 1],
        [0.15, 0.25, 0.15],
        { easing: Easing.inOut(Easing.sin) }
      );
    }

    const x = gridLeft + pos.col * (blockSize + gap);
    const y = gridTop + pos.row * (blockSize + gap);

    highlights.push(
      <div
        key={`green-${i}`}
        style={{
          position: "absolute",
          left: x,
          top: y,
          width: blockSize,
          height: blockSize,
          backgroundColor: `rgba(90, 170, 110, ${pulseGlow})`,
          border: `1px solid rgba(90, 170, 110, 0.3)`,
          borderRadius: 2,
          opacity,
          boxShadow: `0 0 6px rgba(90, 170, 110, ${pulseGlow})`,
        }}
      >
        <span
          style={{
            position: "absolute",
            top: 1,
            right: 3,
            fontSize: 8,
            color: GREEN_HIGHLIGHT,
            fontWeight: 700,
          }}
        >
          ✓
        </span>
      </div>
    );
  });

  return (
    <div
      style={{
        position: "absolute",
        top: 0,
        left: 0,
        width: "100%",
        height: "100%",
        pointerEvents: "none" as const,
      }}
    >
      {highlights}
    </div>
  );
};

export default BlockHighlights;
