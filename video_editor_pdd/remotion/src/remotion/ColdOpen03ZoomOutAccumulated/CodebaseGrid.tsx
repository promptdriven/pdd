import React from "react";
import { useCurrentFrame, interpolate, Easing } from "remotion";
import {
  CODE_BLOCK_W,
  CODE_BLOCK_H,
  CODE_BLOCK_COUNT,
  CODE_BLOCK_FILL,
  CODE_BLOCK_BORDER,
  CODE_BLOCK_BORDER_OPACITY,
  DIFF_RED,
  DIFF_GREEN,
  DIFF_MARKER_PERCENT,
  FLOATING_COMMENTS,
  COMMENT_TEXT_COLOR,
  COMMENT_TEXT_OPACITY,
  COMMENT_FONT_SIZE,
  FONT_FAMILY,
  PANEL_WIDTH,
  CANVAS_HEIGHT,
  ZOOM_START,
  ZOOM_END,
  ZOOM_FROM,
  ZOOM_TO,
  COMMENTS_START,
  COMMENTS_DURATION,
  RED_GLOW_COLOR,
  RED_GLOW_OPACITY,
  PULSE_START,
  PULSE_DURATION,
  seededRandom,
} from "./constants";

// Pre-generate code block positions in a grid-like dependency graph layout
const GRID_COLS = 10;
const GRID_ROWS = 8;
const GRID_MARGIN_X = 60;
const GRID_MARGIN_Y = 40;
const CELL_SPACING_X = (PANEL_WIDTH - 2 * GRID_MARGIN_X) / GRID_COLS;
const CELL_SPACING_Y = (CANVAS_HEIGHT - 2 * GRID_MARGIN_Y) / GRID_ROWS;

interface CodeBlock {
  x: number;
  y: number;
  hasDiff: boolean;
  diffIsRed: boolean;
  distFromCenter: number;
}

const CENTER_X = PANEL_WIDTH / 2;
const CENTER_Y = CANVAS_HEIGHT / 2;

const codeBlocks: CodeBlock[] = Array.from(
  { length: CODE_BLOCK_COUNT },
  (_, i) => {
    const col = i % GRID_COLS;
    const row = Math.floor(i / GRID_COLS);
    const jitterX = (seededRandom(i * 3 + 1) - 0.5) * 16;
    const jitterY = (seededRandom(i * 3 + 2) - 0.5) * 12;
    const x = GRID_MARGIN_X + col * CELL_SPACING_X + jitterX;
    const y = GRID_MARGIN_Y + row * CELL_SPACING_Y + jitterY;
    const hasDiff = seededRandom(i * 7) < DIFF_MARKER_PERCENT / 100;
    const diffIsRed = seededRandom(i * 11) < 0.5;
    const dx = x + CODE_BLOCK_W / 2 - CENTER_X;
    const dy = y + CODE_BLOCK_H / 2 - CENTER_Y;
    const distFromCenter = Math.sqrt(dx * dx + dy * dy);
    return { x, y, hasDiff, diffIsRed, distFromCenter };
  }
);

// Normalize distances for staggering
const maxDist = Math.max(...codeBlocks.map((b) => b.distFromCenter));

// Pre-generate comment positions
interface FloatingComment {
  text: string;
  x: number;
  y: number;
  delayFrames: number;
}

const floatingComments: FloatingComment[] = FLOATING_COMMENTS.map((text, i) => ({
  text,
  x: 30 + seededRandom(i * 17 + 100) * (PANEL_WIDTH - 200),
  y: 60 + seededRandom(i * 23 + 200) * (CANVAS_HEIGHT - 160),
  delayFrames: i * 1.5, // ~50ms apart at 30fps ≈ 1.5 frames
}));

export const CodebaseGrid: React.FC = () => {
  const frame = useCurrentFrame();

  // Zoom
  const scale = interpolate(frame, [ZOOM_START, ZOOM_END], [ZOOM_FROM, ZOOM_TO], {
    extrapolateLeft: "clamp",
    extrapolateRight: "clamp",
    easing: Easing.inOut(Easing.cubic),
  });

  // Brightness pulse (frames 180-210)
  const pulseProgress = interpolate(
    frame,
    [PULSE_START, PULSE_START + PULSE_DURATION],
    [0, Math.PI * 2],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
  );
  const brightnessOffset = frame >= PULSE_START ? Math.sin(pulseProgress) * 0.02 : 0;
  const brightness = 1 + brightnessOffset;

  return (
    <div
      style={{
        width: PANEL_WIDTH,
        height: CANVAS_HEIGHT,
        position: "relative",
        overflow: "hidden",
        filter: `brightness(${brightness})`,
      }}
    >
      {/* Red glow behind the mass */}
      <div
        style={{
          position: "absolute",
          left: "50%",
          top: "50%",
          width: 800,
          height: 800,
          transform: "translate(-50%, -50%)",
          borderRadius: "50%",
          background: `radial-gradient(circle, ${RED_GLOW_COLOR} 0%, transparent 70%)`,
          opacity: RED_GLOW_OPACITY,
          pointerEvents: "none",
        }}
      />

      {/* Zoomed content */}
      <div
        style={{
          position: "absolute",
          left: "50%",
          top: "50%",
          width: PANEL_WIDTH,
          height: CANVAS_HEIGHT,
          transform: `translate(-50%, -50%) scale(${scale})`,
          transformOrigin: "center center",
        }}
      >
        {/* Code blocks */}
        {codeBlocks.map((block, i) => {
          // Staggered fade-in from center outward during zoom
          const normalizedDist = block.distFromCenter / maxDist;
          const blockFadeStart = ZOOM_START + normalizedDist * 60;
          const blockOpacity = interpolate(
            frame,
            [blockFadeStart, blockFadeStart + 20],
            [0, 1],
            {
              extrapolateLeft: "clamp",
              extrapolateRight: "clamp",
              easing: Easing.out(Easing.quad),
            }
          );

          // Diff marker pulse at frame 90
          const diffPulse =
            block.hasDiff && frame >= 90 && frame <= 100
              ? interpolate(frame, [90, 95, 100], [1, 1.6, 1], {
                  extrapolateLeft: "clamp",
                  extrapolateRight: "clamp",
                })
              : 1;

          return (
            <div
              key={i}
              style={{
                position: "absolute",
                left: block.x,
                top: block.y,
                width: CODE_BLOCK_W,
                height: CODE_BLOCK_H,
                backgroundColor: CODE_BLOCK_FILL,
                border: `1px solid ${CODE_BLOCK_BORDER}`,
                borderColor: `rgba(48, 54, 61, ${CODE_BLOCK_BORDER_OPACITY})`,
                borderRadius: 2,
                opacity: blockOpacity,
              }}
            >
              {block.hasDiff && (
                <div
                  style={{
                    position: "absolute",
                    left: 2,
                    top: block.diffIsRed ? 2 : CODE_BLOCK_H - 8,
                    width: CODE_BLOCK_W - 4,
                    height: 4,
                    backgroundColor: block.diffIsRed ? DIFF_RED : DIFF_GREEN,
                    borderRadius: 1,
                    opacity: 0.8,
                    transform: `scaleY(${diffPulse})`,
                    transformOrigin: "center",
                  }}
                />
              )}
            </div>
          );
        })}
      </div>

      {/* Floating TODO comments (appear at frame 90+) */}
      {floatingComments.map((comment, i) => {
        const commentStart = COMMENTS_START + comment.delayFrames;
        const commentOpacity = interpolate(
          frame,
          [commentStart, commentStart + 15],
          [0, COMMENT_TEXT_OPACITY],
          {
            extrapolateLeft: "clamp",
            extrapolateRight: "clamp",
            easing: Easing.out(Easing.quad),
          }
        );
        // Slight drift from edge
        const driftX = interpolate(
          frame,
          [commentStart, commentStart + 30],
          [comment.x < CENTER_X ? -40 : 40, 0],
          {
            extrapolateLeft: "clamp",
            extrapolateRight: "clamp",
            easing: Easing.out(Easing.quad),
          }
        );

        return (
          <div
            key={`comment-${i}`}
            style={{
              position: "absolute",
              left: comment.x + driftX,
              top: comment.y,
              fontFamily: FONT_FAMILY,
              fontSize: COMMENT_FONT_SIZE,
              color: COMMENT_TEXT_COLOR,
              opacity: commentOpacity,
              whiteSpace: "nowrap",
              pointerEvents: "none",
            }}
          >
            {comment.text}
          </div>
        );
      })}
    </div>
  );
};

export default CodebaseGrid;
