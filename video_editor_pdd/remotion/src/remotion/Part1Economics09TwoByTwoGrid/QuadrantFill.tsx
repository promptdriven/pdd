import React from "react";
import { useCurrentFrame, interpolate, Easing } from "remotion";

/**
 * QuadrantFill — renders a single quadrant's fill, glow border, and typed-in label.
 *
 * Props:
 *  - position: "top-left" | "top-right" | "bottom-left" | "bottom-right"
 *  - color: hex string for the quadrant theme
 *  - fillOpacity: target opacity for the background fill
 *  - glowOpacity: target opacity for the border glow
 *  - label: text to type in (e.g. "GitHub study: +55%")
 *  - labelColor: color of the label text
 *  - labelSize: font size of the label
 *  - animStartFrame: the first frame of this quadrant's reveal (relative to the sequence)
 */

// ── Grid geometry (inlined) ──
const GRID_SIZE = 600;
const CELL_SIZE = 300;
const GRID_CENTER_X = 960;
const GRID_CENTER_Y = 480;
const GRID_LEFT = GRID_CENTER_X - GRID_SIZE / 2;
const GRID_TOP = GRID_CENTER_Y - GRID_SIZE / 2;

const FILL_ANIM_FRAMES = 30;
const CHARS_PER_FRAME = 0.5; // 2 frames per char

interface QuadrantFillProps {
  position: "top-left" | "top-right" | "bottom-left" | "bottom-right";
  color: string;
  fillOpacity: number;
  glowOpacity: number;
  label: string;
  labelColor: string;
  labelSize: number;
  animStartFrame: number;
}

const positionToOffset = (
  pos: QuadrantFillProps["position"]
): { x: number; y: number } => {
  switch (pos) {
    case "top-left":
      return { x: 0, y: 0 };
    case "top-right":
      return { x: CELL_SIZE, y: 0 };
    case "bottom-left":
      return { x: 0, y: CELL_SIZE };
    case "bottom-right":
      return { x: CELL_SIZE, y: CELL_SIZE };
  }
};

export const QuadrantFill: React.FC<QuadrantFillProps> = ({
  position,
  color,
  fillOpacity,
  glowOpacity,
  label,
  labelColor,
  labelSize,
  animStartFrame,
}) => {
  const frame = useCurrentFrame();

  const offset = positionToOffset(position);
  const cellX = GRID_LEFT + offset.x;
  const cellY = GRID_TOP + offset.y;

  // Fill fade-in progress
  const fillProgress = interpolate(
    frame,
    [animStartFrame, animStartFrame + FILL_ANIM_FRAMES],
    [0, 1],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.out(Easing.cubic),
    }
  );

  // Number of chars revealed for type-in effect
  const typeStartFrame = animStartFrame + 10; // slight delay after fill starts
  const charsRevealed = Math.floor(
    Math.max(0, (frame - typeStartFrame) * CHARS_PER_FRAME)
  );
  const displayedLabel = label.slice(0, Math.min(charsRevealed, label.length));

  const currentFillOpacity = fillOpacity * fillProgress;
  const currentGlowOpacity = glowOpacity * fillProgress;

  return (
    <>
      {/* Background fill */}
      <div
        style={{
          position: "absolute",
          left: cellX,
          top: cellY,
          width: CELL_SIZE,
          height: CELL_SIZE,
          backgroundColor: color,
          opacity: currentFillOpacity,
        }}
      />

      {/* Glow border */}
      <div
        style={{
          position: "absolute",
          left: cellX,
          top: cellY,
          width: CELL_SIZE,
          height: CELL_SIZE,
          border: `2px solid ${color}`,
          opacity: currentGlowOpacity,
          boxShadow: `inset 0 0 30px ${color}40, 0 0 20px ${color}30`,
          pointerEvents: "none",
        }}
      />

      {/* Label — centered in cell */}
      <div
        style={{
          position: "absolute",
          left: cellX,
          top: cellY,
          width: CELL_SIZE,
          height: CELL_SIZE,
          display: "flex",
          alignItems: "center",
          justifyContent: "center",
          fontFamily: "Inter, sans-serif",
          fontSize: labelSize,
          fontWeight: 700,
          color: labelColor,
          textAlign: "center",
          padding: 16,
          lineHeight: 1.4,
        }}
      >
        {displayedLabel}
        {/* Blinking cursor while typing */}
        {charsRevealed < label.length && charsRevealed > 0 && (
          <span
            style={{
              opacity: Math.sin(frame * 0.3) > 0 ? 0.8 : 0,
              marginLeft: 1,
              fontWeight: 300,
            }}
          >
            |
          </span>
        )}
      </div>
    </>
  );
};

export default QuadrantFill;
