import React from "react";
import {
  useCurrentFrame,
  interpolate,
  Easing,
} from "remotion";

// ── Inline constants (no cross-file imports) ──
const MODULES = [
  "auth", "parser", "router", "validator", "logger",
  "cache", "queue", "mailer", "search", "analytics",
  "billing", "permissions", "notifications", "export",
  "import", "scheduler", "webhook", "api_client",
  "transformer", "serializer",
];

const CODE_BLOCK_HEIGHTS = [
  240, 310, 200, 280, 190, 340, 220, 260, 300, 180,
  350, 230, 270, 320, 210, 290, 250, 330, 195, 285,
];

const WINDOW_WIDTH = 500;
const WINDOW_HEIGHT = 700;
const WINDOW_CENTER_X = 960;
const WINDOW_CENTER_Y = 480;
const WINDOW_LEFT = WINDOW_CENTER_X - WINDOW_WIDTH / 2;
const WINDOW_TOP = WINDOW_CENTER_Y - WINDOW_HEIGHT / 2;

const CODE_GAP = 4;
const PROMPT_BLOCK_HEIGHT = 30;
const PROMPT_GAP = 3;
const BLOCK_HORIZONTAL_PADDING = 16;
const BLOCK_WIDTH = WINDOW_WIDTH - BLOCK_HORIZONTAL_PADDING * 2;

// Timing
const FRAME_CODE_SLIDE_START = 60;
const FRAME_CODE_SLIDE_END = 300;
const STAGGER = 12; // frames between each block starting its slide

const FRAME_COMPRESS_START = 420;
const FRAME_COMPRESS_END = 600;

// Compute Y offsets for code blocks
function getCodeYOffsets(): number[] {
  const offsets: number[] = [];
  let y = 0;
  for (let i = 0; i < MODULES.length; i++) {
    offsets.push(y);
    y += CODE_BLOCK_HEIGHTS[i] + CODE_GAP;
  }
  return offsets;
}

// Compute Y offsets for prompt blocks
function getPromptYOffsets(): number[] {
  const offsets: number[] = [];
  let y = 0;
  for (let i = 0; i < MODULES.length; i++) {
    offsets.push(y);
    y += PROMPT_BLOCK_HEIGHT + PROMPT_GAP;
  }
  return offsets;
}

const codeYOffsets = getCodeYOffsets();
const promptYOffsets = getPromptYOffsets();

interface SingleBlockProps {
  index: number;
  name: string;
  codeHeight: number;
  codeY: number;
  promptY: number;
}

const SingleBlock: React.FC<SingleBlockProps> = ({
  index,
  name,
  codeHeight,
  codeY,
  promptY,
}) => {
  const frame = useCurrentFrame();

  // ── Phase 1: slide in from the left ──
  const slideStart = FRAME_CODE_SLIDE_START + index * STAGGER;
  const slideEnd = slideStart + 30;
  const slideProgress = interpolate(
    frame,
    [slideStart, slideEnd],
    [0, 1],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp", easing: Easing.out(Easing.cubic) }
  );

  // ── Phase 2: compression morph ──
  const morphProgress = interpolate(
    frame,
    [FRAME_COMPRESS_START, FRAME_COMPRESS_END],
    [0, 1],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp", easing: Easing.inOut(Easing.cubic) }
  );

  // Before compression starts, use code values. During compression, morph.
  const currentHeight = interpolate(morphProgress, [0, 1], [codeHeight, PROMPT_BLOCK_HEIGHT]);
  const currentY = interpolate(morphProgress, [0, 1], [codeY, promptY]);

  // Colors: morph from gray to blue
  const bgR = Math.round(interpolate(morphProgress, [0, 1], [30, 74]));
  const bgG = Math.round(interpolate(morphProgress, [0, 1], [41, 144]));
  const bgB = Math.round(interpolate(morphProgress, [0, 1], [59, 217]));
  const bgAlpha = interpolate(morphProgress, [0, 1], [1, 0.15]);
  const bgColor = `rgba(${bgR},${bgG},${bgB},${bgAlpha})`;

  const borderR = Math.round(interpolate(morphProgress, [0, 1], [51, 74]));
  const borderG = Math.round(interpolate(morphProgress, [0, 1], [65, 144]));
  const borderB = Math.round(interpolate(morphProgress, [0, 1], [85, 217]));
  const borderColor = `rgb(${borderR},${borderG},${borderB})`;

  // Label color morphs from gray to blue
  const labelR = Math.round(interpolate(morphProgress, [0, 1], [100, 74]));
  const labelG = Math.round(interpolate(morphProgress, [0, 1], [116, 144]));
  const labelB = Math.round(interpolate(morphProgress, [0, 1], [139, 217]));
  const labelColor = `rgb(${labelR},${labelG},${labelB})`;

  // Slide in: translate from left
  const translateX = interpolate(slideProgress, [0, 1], [-WINDOW_WIDTH - 100, 0]);

  // Block is invisible until its slide begins
  if (frame < slideStart) return null;

  return (
    <div
      style={{
        position: "absolute",
        top: currentY,
        left: BLOCK_HORIZONTAL_PADDING,
        width: BLOCK_WIDTH,
        height: currentHeight,
        transform: `translateX(${translateX}px)`,
        backgroundColor: bgColor,
        border: `1px solid ${borderColor}`,
        borderRadius: 4,
        display: "flex",
        alignItems: "center",
        justifyContent: "center",
        overflow: "hidden",
      }}
    >
      <span
        style={{
          fontFamily: "Inter, sans-serif",
          fontSize: interpolate(morphProgress, [0, 1], [11, 10]),
          fontWeight: 400,
          color: labelColor,
          letterSpacing: 0.5,
          userSelect: "none",
        }}
      >
        {name}
      </span>
    </div>
  );
};

/**
 * Renders all 20 module blocks inside the context window.
 * Handles slide-in (Phase 1) and compression morph (Phase 2).
 */
export const ModuleBlocks: React.FC = () => {
  return (
    <div
      style={{
        position: "absolute",
        left: WINDOW_LEFT,
        top: WINDOW_TOP,
        width: WINDOW_WIDTH,
        height: WINDOW_HEIGHT,
        overflow: "hidden",
        borderRadius: 8,
      }}
    >
      {MODULES.map((name, i) => (
        <SingleBlock
          key={name}
          index={i}
          name={name}
          codeHeight={CODE_BLOCK_HEIGHTS[i]}
          codeY={codeYOffsets[i]}
          promptY={promptYOffsets[i]}
        />
      ))}
    </div>
  );
};

export default ModuleBlocks;
