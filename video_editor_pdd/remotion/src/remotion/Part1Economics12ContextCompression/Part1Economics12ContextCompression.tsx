import React from "react";
import {
  AbsoluteFill,
  Sequence,
  interpolate,
  useCurrentFrame,
  Easing,
} from "remotion";

import {
  BACKGROUND_COLOR,
  WINDOW_LEFT,
  WINDOW_TOP,
  WINDOW_WIDTH,
  WINDOW_HEIGHT,
  WINDOW_BORDER_COLOR,
  WINDOW_BORDER_WIDTH,
  WINDOW_BORDER_RADIUS,
  WINDOW_GLOW_OPACITY,
  WINDOW_GLOW_BLUR,
  MODULE_NAMES,
  MODULE_COUNT,
  OVERFLOW_COUNT,
  CODE_BLOCK_BORDER_WIDTH,
  CODE_BLOCK_GAP,
  CODE_BLOCK_HEIGHTS,
  PROMPT_BLOCK_HEIGHT,
  PROMPT_BLOCK_GAP,
  PROMPT_BLOCK_FILL_OPACITY,
  OVERFLOW_COLOR,
  REMAINING_SPACE_COLOR,
  FONT_FAMILY,
  MODULE_LABEL_SIZE,
  MODULE_LABEL_COLOR,
  PHASE_LABEL_SIZE,
  PHASE_LABEL_COLOR,
  RATIO_LABEL_SIZE,
  PHASE_WINDOW_DRAW_START,
  PHASE_WINDOW_DRAW_END,
  PHASE_CODE_SLIDE_START,
  PHASE_OVERFLOW_HOLD_START,
  PHASE_COMPRESS_START,
  PHASE_COMPRESS_END,
  PHASE_RESULT_START,
  CODE_SLIDE_STAGGER,
  CODE_SLIDE_DURATION_PER_BLOCK,
} from "./constants";

import { ContextWindowFrame } from "./ContextWindowFrame";
import { OverflowIndicator } from "./OverflowIndicator";
import { RemainingSpace } from "./RemainingSpace";

// ─── Precompute layout positions ───────────────────────────────────

// Code blocks: stacked from top of window, with gap
const codeBlockPositions: { y: number; height: number }[] = [];
{
  let currentY = 0;
  for (let i = 0; i < MODULE_COUNT; i++) {
    codeBlockPositions.push({ y: currentY, height: CODE_BLOCK_HEIGHTS[i] });
    currentY += CODE_BLOCK_HEIGHTS[i] + CODE_BLOCK_GAP;
  }
}

// Prompt blocks: stacked from top of window, with gap
const promptBlockPositions: { y: number; height: number }[] = [];
{
  let currentY = 8; // top padding
  for (let i = 0; i < MODULE_COUNT; i++) {
    promptBlockPositions.push({ y: currentY, height: PROMPT_BLOCK_HEIGHT });
    currentY += PROMPT_BLOCK_HEIGHT + PROMPT_BLOCK_GAP;
  }
}
const totalPromptHeight =
  MODULE_COUNT * PROMPT_BLOCK_HEIGHT + (MODULE_COUNT - 1) * PROMPT_BLOCK_GAP + 16;

// ─── Individual Module Block ───────────────────────────────────────

interface ModuleBlockProps {
  index: number;
  name: string;
}

const ModuleBlock: React.FC<ModuleBlockProps> = ({ index, name }) => {
  const frame = useCurrentFrame();
  const blockPadding = 10; // inner padding from window edge
  const blockWidth = WINDOW_WIDTH - blockPadding * 2;

  // Phase 1: Slide in from left (staggered)
  const slideStart = PHASE_CODE_SLIDE_START + index * CODE_SLIDE_STAGGER;
  const slideEnd = slideStart + CODE_SLIDE_DURATION_PER_BLOCK;

  const slideProgress = interpolate(frame, [slideStart, slideEnd], [0, 1], {
    extrapolateLeft: "clamp",
    extrapolateRight: "clamp",
    easing: Easing.out(Easing.cubic),
  });

  // Phase 2: Compression morph (420-600)
  const morphProgress = interpolate(
    frame,
    [PHASE_COMPRESS_START, PHASE_COMPRESS_END],
    [0, 1],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.inOut(Easing.cubic),
    }
  );

  // Interpolate between code position and prompt position
  const codeY = codeBlockPositions[index].y;
  const codeH = codeBlockPositions[index].height;
  const promptY = promptBlockPositions[index].y;
  const promptH = promptBlockPositions[index].height;

  const currentY = interpolate(morphProgress, [0, 1], [codeY, promptY]);
  const currentH = interpolate(morphProgress, [0, 1], [codeH, promptH]);

  // Colors morph
  const bgR = interpolate(morphProgress, [0, 1], [0x1e, 0x4a]);
  const bgG = interpolate(morphProgress, [0, 1], [0x29, 0x90]);
  const bgB = interpolate(morphProgress, [0, 1], [0x3b, 0xd9]);
  const bgAlpha = interpolate(morphProgress, [0, 1], [1, PROMPT_BLOCK_FILL_OPACITY]);

  const borderR = interpolate(morphProgress, [0, 1], [0x33, 0x4a]);
  const borderG = interpolate(morphProgress, [0, 1], [0x41, 0x90]);
  const borderB = interpolate(morphProgress, [0, 1], [0x55, 0xd9]);

  // Slide in from left offset
  const xOffset = interpolate(slideProgress, [0, 1], [-600, 0]);

  // Opacity: appear when sliding in
  const blockOpacity = interpolate(slideProgress, [0, 0.1], [0, 1], {
    extrapolateLeft: "clamp",
    extrapolateRight: "clamp",
  });

  // Determine if block overflows the window in code phase
  const absoluteTop = WINDOW_TOP + currentY;
  const windowBottom = WINDOW_TOP + WINDOW_HEIGHT;

  // If fully below window in code phase and not yet morphing, hide
  const isOverflowing = absoluteTop >= windowBottom && morphProgress < 0.5;

  return (
    <div
      style={{
        position: "absolute",
        left: WINDOW_LEFT + blockPadding + xOffset,
        top: WINDOW_TOP + currentY,
        width: blockWidth,
        height: currentH,
        backgroundColor: `rgba(${Math.round(bgR)}, ${Math.round(bgG)}, ${Math.round(bgB)}, ${bgAlpha})`,
        border: `${CODE_BLOCK_BORDER_WIDTH}px solid rgba(${Math.round(borderR)}, ${Math.round(borderG)}, ${Math.round(borderB)}, ${interpolate(morphProgress, [0, 1], [0.8, 1])})`,
        borderRadius: interpolate(morphProgress, [0, 1], [4, 3]),
        opacity: isOverflowing ? 0 : blockOpacity,
        display: "flex",
        alignItems: "center",
        paddingLeft: 12,
        overflow: "hidden",
      }}
    >
      <span
        style={{
          fontFamily: FONT_FAMILY,
          fontSize: interpolate(morphProgress, [0, 1], [MODULE_LABEL_SIZE, 10]),
          fontWeight: 400,
          color: MODULE_LABEL_COLOR,
          opacity: interpolate(morphProgress, [0, 1], [0.8, 1]),
          whiteSpace: "nowrap",
        }}
      >
        {name}
      </span>
    </div>
  );
};

// ─── Phase Label ───────────────────────────────────────────────────

interface PhaseLabelProps {
  text: string;
  color: string;
  fontSize: number;
  yPosition: number;
  appearFrame: number;
  disappearFrame?: number;
  useBackEasing?: boolean;
}

const PhaseLabel: React.FC<PhaseLabelProps> = ({
  text,
  color,
  fontSize,
  yPosition,
  appearFrame,
  disappearFrame,
  useBackEasing,
}) => {
  const frame = useCurrentFrame();

  let opacity: number;
  if (disappearFrame != null) {
    if (frame < appearFrame) {
      opacity = 0;
    } else if (frame < disappearFrame - 20) {
      opacity = interpolate(frame, [appearFrame, appearFrame + 25], [0, 1], {
        extrapolateLeft: "clamp",
        extrapolateRight: "clamp",
      });
    } else {
      opacity = interpolate(frame, [disappearFrame - 20, disappearFrame], [1, 0], {
        extrapolateLeft: "clamp",
        extrapolateRight: "clamp",
      });
    }
  } else {
    opacity = interpolate(frame, [appearFrame, appearFrame + 25], [0, 1], {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
    });
  }

  const scale = useBackEasing
    ? interpolate(frame, [appearFrame, appearFrame + 30], [0.85, 1], {
        extrapolateLeft: "clamp",
        extrapolateRight: "clamp",
        easing: Easing.out(Easing.back(1.4)),
      })
    : 1;

  return (
    <div
      style={{
        position: "absolute",
        left: 0,
        top: yPosition,
        width: 1920,
        textAlign: "center",
        fontFamily: FONT_FAMILY,
        fontSize,
        fontWeight: 700,
        color,
        opacity,
        transform: `scale(${scale})`,
      }}
    >
      {text}
    </div>
  );
};

// ─── Clip mask for the window ──────────────────────────────────────

interface WindowClipProps {
  children: React.ReactNode;
  showOverflow: boolean;
}

const WindowClip: React.FC<WindowClipProps> = ({ children, showOverflow }) => {
  if (showOverflow) {
    // During compression, don't clip — let blocks be visible as they move
    return <>{children}</>;
  }
  return (
    <div
      style={{
        position: "absolute",
        left: WINDOW_LEFT,
        top: WINDOW_TOP,
        width: WINDOW_WIDTH,
        height: WINDOW_HEIGHT,
        overflow: "hidden",
        borderRadius: WINDOW_BORDER_RADIUS,
      }}
    >
      {/* Re-offset children so they're positioned within the clip */}
      <div
        style={{
          position: "relative",
          left: -WINDOW_LEFT,
          top: -WINDOW_TOP,
          width: 1920,
          height: 1080,
        }}
      >
        {children}
      </div>
    </div>
  );
};

// ─── Main Component ────────────────────────────────────────────────

export const defaultPart1Economics12ContextCompressionProps = {};

export const Part1Economics12ContextCompression: React.FC = () => {
  const frame = useCurrentFrame();

  // Determine if we're in compression phase (don't clip during morph)
  const isCompressing = frame >= PHASE_COMPRESS_START && frame < PHASE_COMPRESS_END;
  const isPostCompress = frame >= PHASE_COMPRESS_END;

  return (
    <AbsoluteFill style={{ backgroundColor: BACKGROUND_COLOR }}>
      {/* Context window frame — always visible */}
      <ContextWindowFrame
        windowLeft={WINDOW_LEFT}
        windowTop={WINDOW_TOP}
        windowWidth={WINDOW_WIDTH}
        windowHeight={WINDOW_HEIGHT}
        borderColor={WINDOW_BORDER_COLOR}
        borderWidth={WINDOW_BORDER_WIDTH}
        borderRadius={WINDOW_BORDER_RADIUS}
        glowOpacity={WINDOW_GLOW_OPACITY}
        glowBlur={WINDOW_GLOW_BLUR}
        drawStart={PHASE_WINDOW_DRAW_START}
        drawEnd={PHASE_WINDOW_DRAW_END}
      />

      {/* Module blocks inside clip region */}
      <WindowClip showOverflow={isCompressing}>
        {MODULE_NAMES.map((name, i) => (
          <ModuleBlock key={name} index={i} name={name} />
        ))}
      </WindowClip>

      {/* Overflow indicator — visible during overflow hold, fades during compression */}
      <Sequence from={PHASE_OVERFLOW_HOLD_START} durationInFrames={PHASE_COMPRESS_END - PHASE_OVERFLOW_HOLD_START}>
        <OverflowFade>
          <OverflowIndicator
            windowLeft={WINDOW_LEFT}
            windowTop={WINDOW_TOP}
            windowWidth={WINDOW_WIDTH}
            windowHeight={WINDOW_HEIGHT}
            overflowCount={OVERFLOW_COUNT}
            color={OVERFLOW_COLOR}
            appearFrame={0}
          />
        </OverflowFade>
      </Sequence>

      {/* Phase 1 label: "20 modules as code — doesn't fit" */}
      <PhaseLabel
        text="20 modules as code — doesn't fit."
        color={PHASE_LABEL_COLOR}
        fontSize={PHASE_LABEL_SIZE}
        yPosition={WINDOW_TOP + WINDOW_HEIGHT + 60}
        appearFrame={PHASE_OVERFLOW_HOLD_START + 10}
        disappearFrame={PHASE_COMPRESS_START}
      />

      {/* Remaining space indicator — after compression */}
      {isPostCompress && (
        <RemainingSpace
          windowLeft={WINDOW_LEFT}
          windowTop={WINDOW_TOP}
          windowWidth={WINDOW_WIDTH}
          windowHeight={WINDOW_HEIGHT}
          usedHeight={totalPromptHeight}
          fillColor={REMAINING_SPACE_COLOR}
          appearFrame={PHASE_RESULT_START}
        />
      )}

      {/* Phase 2 label: "Same system. 5-10× more fits." */}
      <PhaseLabel
        text="Same system. 5-10× more fits."
        color={REMAINING_SPACE_COLOR}
        fontSize={RATIO_LABEL_SIZE}
        yPosition={WINDOW_TOP + WINDOW_HEIGHT + 60}
        appearFrame={PHASE_RESULT_START + 15}
        useBackEasing
      />
    </AbsoluteFill>
  );
};

// ─── OverflowFade helper ───────────────────────────────────────────
// Fades out the overflow indicator as compression progresses

const OverflowFade: React.FC<{ children: React.ReactNode }> = ({ children }) => {
  const frame = useCurrentFrame();
  // This sequence starts at PHASE_OVERFLOW_HOLD_START, so local frame 0 = global 300
  const localCompressStart = PHASE_COMPRESS_START - PHASE_OVERFLOW_HOLD_START;
  const fadeOpacity = interpolate(
    frame,
    [localCompressStart, localCompressStart + 30],
    [1, 0],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
    }
  );
  return <div style={{ opacity: fadeOpacity }}>{children}</div>;
};

export default Part1Economics12ContextCompression;
