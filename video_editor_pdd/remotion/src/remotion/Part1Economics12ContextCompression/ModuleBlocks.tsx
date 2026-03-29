// ModuleBlocks.tsx — Renders the 20 module blocks in code or prompt form with morph animation
import React from "react";
import { interpolate, useCurrentFrame, Easing } from "remotion";

import {
  MODULE_NAMES,
  CODE_BLOCK_HEIGHTS,
  PROMPT_BLOCK_HEIGHT,
  CODE_BLOCK_GAP,
  PROMPT_BLOCK_GAP,
  WINDOW_LEFT,
  WINDOW_TOP,
  WINDOW_WIDTH,
  WINDOW_HEIGHT,
  WINDOW_BORDER_WIDTH,
  CODE_BLOCK_FILL,
  CODE_BLOCK_BORDER,
  CODE_LABEL_COLOR,
  PROMPT_BLOCK_FILL,
  PROMPT_BLOCK_BORDER,
  PHASE_CODE_SLIDE_START,
  CODE_SLIDE_STAGGER,
  PHASE_COMPRESS_START,
  PHASE_COMPRESS_END,
} from "./constants";

const INNER_LEFT = WINDOW_LEFT + WINDOW_BORDER_WIDTH + 8;
const INNER_TOP = WINDOW_TOP + WINDOW_BORDER_WIDTH + 8;
const INNER_WIDTH = WINDOW_WIDTH - (WINDOW_BORDER_WIDTH + 8) * 2;
const CLIP_HEIGHT = WINDOW_HEIGHT - (WINDOW_BORDER_WIDTH + 8) * 2;

/** Compute the stacked Y offsets for code blocks */
function computeCodeOffsets(): number[] {
  const offsets: number[] = [];
  let y = 0;
  for (let i = 0; i < MODULE_NAMES.length; i++) {
    offsets.push(y);
    y += CODE_BLOCK_HEIGHTS[i] + CODE_BLOCK_GAP;
  }
  return offsets;
}

/** Compute the stacked Y offsets for prompt blocks */
function computePromptOffsets(): number[] {
  const offsets: number[] = [];
  let y = 0;
  for (let i = 0; i < MODULE_NAMES.length; i++) {
    offsets.push(y);
    y += PROMPT_BLOCK_HEIGHT + PROMPT_BLOCK_GAP;
  }
  return offsets;
}

const codeOffsets = computeCodeOffsets();
const promptOffsets = computePromptOffsets();

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

  // Phase 1: slide in from left
  const slideStart = PHASE_CODE_SLIDE_START + index * CODE_SLIDE_STAGGER;
  const slideEnd = slideStart + 25;
  const slideProgress = interpolate(frame, [slideStart, slideEnd], [0, 1], {
    extrapolateLeft: "clamp",
    extrapolateRight: "clamp",
    easing: Easing.out(Easing.cubic),
  });

  // Phase 2: compression morph (frame 420-600)
  const compressDuration = PHASE_COMPRESS_END - PHASE_COMPRESS_START;
  const morphProgress = interpolate(
    frame,
    [PHASE_COMPRESS_START, PHASE_COMPRESS_START + compressDuration],
    [0, 1],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.inOut(Easing.cubic),
    }
  );

  // Interpolate block height
  const currentHeight = interpolate(morphProgress, [0, 1], [codeHeight, PROMPT_BLOCK_HEIGHT], {
    extrapolateLeft: "clamp",
    extrapolateRight: "clamp",
  });

  // Interpolate Y position
  const currentY = interpolate(morphProgress, [0, 1], [codeY, promptY], {
    extrapolateLeft: "clamp",
    extrapolateRight: "clamp",
  });

  // Interpolate colors via opacity crossfade
  const codeOpacity = 1 - morphProgress;
  const promptOpacity = morphProgress;

  // X offset for slide-in
  const xOffset = interpolate(slideProgress, [0, 1], [-INNER_WIDTH - 50, 0], {
    extrapolateLeft: "clamp",
    extrapolateRight: "clamp",
  });

  const blockOpacity = slideProgress;

  // Font size interpolation for morph
  const fontSize = interpolate(morphProgress, [0, 1], [11, 10], {
    extrapolateLeft: "clamp",
    extrapolateRight: "clamp",
  });

  return (
    <div
      style={{
        position: "absolute",
        left: xOffset,
        top: currentY,
        width: INNER_WIDTH,
        height: currentHeight,
        borderRadius: 4,
        opacity: blockOpacity,
        overflow: "hidden",
        display: "flex",
        alignItems: "center",
        paddingLeft: 12,
      }}
    >
      {/* Code block background */}
      <div
        style={{
          position: "absolute",
          inset: 0,
          backgroundColor: CODE_BLOCK_FILL,
          border: `1px solid ${CODE_BLOCK_BORDER}`,
          borderRadius: 4,
          opacity: codeOpacity,
        }}
      />
      {/* Prompt block background */}
      <div
        style={{
          position: "absolute",
          inset: 0,
          backgroundColor: PROMPT_BLOCK_FILL,
          border: `1px solid ${PROMPT_BLOCK_BORDER}`,
          borderRadius: 4,
          opacity: promptOpacity,
        }}
      />
      {/* Label */}
      <span
        style={{
          position: "relative",
          zIndex: 1,
          fontFamily: "Inter, sans-serif",
          fontSize,
          fontWeight: 400,
          color: interpolateColor(morphProgress, CODE_LABEL_COLOR, "#93C5FD"),
          whiteSpace: "nowrap",
        }}
      >
        {name}
      </span>
    </div>
  );
};

/** Simple hex color interpolation */
function interpolateColor(t: number, from: string, to: string): string {
  const f = hexToRgb(from);
  const toRgb = hexToRgb(to);
  const r = Math.round(f.r + (toRgb.r - f.r) * t);
  const g = Math.round(f.g + (toRgb.g - f.g) * t);
  const b = Math.round(f.b + (toRgb.b - f.b) * t);
  return `rgb(${r},${g},${b})`;
}

function hexToRgb(hex: string): { r: number; g: number; b: number } {
  const h = hex.replace("#", "");
  return {
    r: parseInt(h.substring(0, 2), 16),
    g: parseInt(h.substring(2, 4), 16),
    b: parseInt(h.substring(4, 6), 16),
  };
}

const ModuleBlocks: React.FC = () => {
  return (
    <div
      style={{
        position: "absolute",
        left: INNER_LEFT,
        top: INNER_TOP,
        width: INNER_WIDTH,
        height: CLIP_HEIGHT,
        overflow: "hidden",
      }}
    >
      {MODULE_NAMES.map((name, i) => (
        <SingleBlock
          key={name}
          index={i}
          name={name}
          codeHeight={CODE_BLOCK_HEIGHTS[i]}
          codeY={codeOffsets[i]}
          promptY={promptOffsets[i]}
        />
      ))}
    </div>
  );
};

export default ModuleBlocks;
