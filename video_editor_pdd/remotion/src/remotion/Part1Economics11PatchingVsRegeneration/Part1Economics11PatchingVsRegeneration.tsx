import React from 'react';
import {
  AbsoluteFill,
  useCurrentFrame,
  interpolate,
  Easing,
  Sequence,
} from 'remotion';
import TokenBlockGrid from './TokenBlockGrid';
import CuratedBlocks from './CuratedBlocks';
import {
  BACKGROUND_COLOR,
  PANEL_WIDTH,
  PANEL_HEIGHT,
  LEFT_PANEL_X,
  LEFT_PANEL_Y,
  RIGHT_PANEL_X,
  RIGHT_PANEL_Y,
  TOKEN_ROWS,
  TOKEN_COLS,
  TOKEN_BLOCK_WIDTH,
  TOKEN_BLOCK_HEIGHT,
  TOKEN_GAP,
  TOKEN_PADDING,
  PROMPT_BLOCK_HEIGHT,
  TESTS_BLOCK_HEIGHT,
  GROUNDING_BLOCK_HEIGHT,
  BLOCK_GAP,
  BLOCK_PADDING,
  BLOCK_LABEL_FONT_SIZE,
  COLOR_RED_IRRELEVANT,
  COLOR_GREEN_RELEVANT,
  COLOR_GRAY_NEUTRAL,
  COLOR_BLUE_PROMPT,
  COLOR_AMBER_TESTS,
  COLOR_SLATE_HEADER,
  COLOR_BORDER_DASHED,
  COLOR_EMPTY_SPACE,
  COLOR_ROOM_TEXT,
  DISTRIBUTION_IRRELEVANT,
  DISTRIBUTION_RELEVANT,
  PANEL_DRAW_START,
  PANEL_DRAW_END,
  LEFT_FILL_START,
  LEFT_FILL_END,
  RIGHT_PROMPT_START,
  RIGHT_TESTS_START,
  RIGHT_GROUNDING_START,
  RIGHT_ROOM_START,
  LABELS_APPEAR_START,
  LABELS_APPEAR_END,
  FONT_FAMILY,
  HEADER_FONT_SIZE,
  HEADER_FONT_WEIGHT,
  LABEL_FONT_SIZE,
  TOTAL_FRAMES,
} from './constants';

export const defaultPart1Economics11PatchingVsRegenerationProps = {};

// ── Title bar ───────────────────────────────────────────────────────────
const SectionTitle: React.FC = () => {
  const frame = useCurrentFrame();
  const opacity = interpolate(frame, [0, 30], [0, 0.85], {
    extrapolateLeft: 'clamp',
    extrapolateRight: 'clamp',
    easing: Easing.out(Easing.quad),
  });

  return (
    <div
      style={{
        position: 'absolute',
        top: 40,
        left: 0,
        width: 1920,
        textAlign: 'center',
        fontFamily: FONT_FAMILY,
        fontSize: 32,
        fontWeight: 700,
        color: '#E2E8F0',
        opacity,
        letterSpacing: '-0.01em',
      }}
    >
      Context Window Comparison
    </div>
  );
};

// ── Reusable panel wrapper ──────────────────────────────────────────────
interface PanelFrameProps {
  x: number;
  y: number;
  width: number;
  height: number;
  borderColor: string;
  borderStyle: 'solid' | 'dashed';
  header: string;
  headerColor: string;
  children: React.ReactNode;
}

const PanelFrame: React.FC<PanelFrameProps> = ({
  x,
  y,
  width,
  height,
  borderColor,
  borderStyle,
  header,
  headerColor,
  children,
}) => {
  const frame = useCurrentFrame();

  // Panel outline draw-in animation
  const drawProgress = interpolate(
    frame,
    [PANEL_DRAW_START, PANEL_DRAW_END],
    [0, 1],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.out(Easing.quad),
    }
  );

  // Header typewriter effect
  const headerVisibleChars = Math.floor(
    interpolate(frame, [10, PANEL_DRAW_END], [0, header.length], {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.out(Easing.quad),
    })
  );

  const panelPerimeter = 2 * (width + height);
  const dashOffset = panelPerimeter * (1 - drawProgress);

  return (
    <div
      style={{
        position: 'absolute',
        left: x,
        top: y,
        width,
        height,
      }}
    >
      {/* Panel outline via SVG for dash-offset animation */}
      <svg
        width={width}
        height={height}
        style={{ position: 'absolute', top: 0, left: 0 }}
      >
        <rect
          x={1}
          y={1}
          width={width - 2}
          height={height - 2}
          fill="none"
          stroke={borderColor}
          strokeWidth={2}
          strokeDasharray={
            borderStyle === 'dashed'
              ? `8 4`
              : `${panelPerimeter}`
          }
          strokeDashoffset={
            borderStyle === 'dashed'
              ? dashOffset * 0.5
              : dashOffset
          }
          rx={8}
          ry={8}
          style={{ opacity: drawProgress }}
        />
      </svg>

      {/* Header above the panel */}
      <div
        style={{
          position: 'absolute',
          top: -40,
          left: 0,
          width: '100%',
          fontFamily: FONT_FAMILY,
          fontSize: HEADER_FONT_SIZE,
          fontWeight: HEADER_FONT_WEIGHT,
          color: headerColor,
          letterSpacing: '0.03em',
        }}
      >
        {header.slice(0, headerVisibleChars)}
        {headerVisibleChars < header.length && (
          <span
            style={{
              opacity: frame % 10 < 5 ? 0.8 : 0,
              marginLeft: 1,
            }}
          >
            |
          </span>
        )}
      </div>

      {/* Panel contents */}
      <div
        style={{
          position: 'absolute',
          top: 0,
          left: 0,
          width,
          height,
          overflow: 'hidden',
          borderRadius: 8,
        }}
      >
        {children}
      </div>
    </div>
  );
};

// ── Comparison labels ───────────────────────────────────────────────────
const ComparisonLabels: React.FC = () => {
  const frame = useCurrentFrame();

  const opacity = interpolate(
    frame,
    [LABELS_APPEAR_START, LABELS_APPEAR_END],
    [0, 1],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.out(Easing.quad),
    }
  );

  const slideY = interpolate(
    frame,
    [LABELS_APPEAR_START, LABELS_APPEAR_END],
    [10, 0],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.out(Easing.quad),
    }
  );

  const labelStyle: React.CSSProperties = {
    position: 'absolute',
    top: LEFT_PANEL_Y + PANEL_HEIGHT + 24,
    fontFamily: FONT_FAMILY,
    fontSize: LABEL_FONT_SIZE,
    fontWeight: 400,
    opacity,
    transform: `translateY(${slideY}px)`,
    textAlign: 'center',
  };

  return (
    <>
      <div
        style={{
          ...labelStyle,
          left: LEFT_PANEL_X,
          width: PANEL_WIDTH,
          color: COLOR_RED_IRRELEVANT,
        }}
      >
        15,000 tokens — mostly wrong
      </div>
      <div
        style={{
          ...labelStyle,
          left: RIGHT_PANEL_X,
          width: PANEL_WIDTH,
          color: COLOR_GREEN_RELEVANT,
        }}
      >
        2,300 tokens — all curated
      </div>
    </>
  );
};

// ── Divider line ────────────────────────────────────────────────────────
const CenterDivider: React.FC = () => {
  const frame = useCurrentFrame();

  const dividerHeight = interpolate(frame, [30, 90], [0, PANEL_HEIGHT + 80], {
    extrapolateLeft: 'clamp',
    extrapolateRight: 'clamp',
    easing: Easing.out(Easing.quad),
  });

  return (
    <div
      style={{
        position: 'absolute',
        left: 960,
        top: LEFT_PANEL_Y - 50,
        width: 2,
        height: dividerHeight,
        backgroundColor: '#334155',
        opacity: 0.4,
        borderRadius: 1,
        transform: 'translateX(-1px)',
      }}
    />
  );
};

// ── "VS" badge ──────────────────────────────────────────────────────────
const VsBadge: React.FC = () => {
  const frame = useCurrentFrame();
  const opacity = interpolate(frame, [50, 80], [0, 0.7], {
    extrapolateLeft: 'clamp',
    extrapolateRight: 'clamp',
    easing: Easing.out(Easing.quad),
  });

  const scale = interpolate(frame, [50, 80], [0.5, 1], {
    extrapolateLeft: 'clamp',
    extrapolateRight: 'clamp',
    easing: Easing.out(Easing.quad),
  });

  return (
    <div
      style={{
        position: 'absolute',
        left: 960,
        top: LEFT_PANEL_Y + PANEL_HEIGHT / 2,
        transform: `translate(-50%, -50%) scale(${scale})`,
        fontFamily: FONT_FAMILY,
        fontSize: 18,
        fontWeight: 700,
        color: '#64748B',
        opacity,
        backgroundColor: BACKGROUND_COLOR,
        padding: '6px 14px',
        borderRadius: 20,
        border: '1px solid #334155',
        letterSpacing: '0.1em',
      }}
    >
      VS
    </div>
  );
};

// ── Subtle bottom label ─────────────────────────────────────────────────
const BottomInsight: React.FC = () => {
  const frame = useCurrentFrame();
  const opacity = interpolate(frame, [510, 550], [0, 0.62], {
    extrapolateLeft: 'clamp',
    extrapolateRight: 'clamp',
    easing: Easing.out(Easing.quad),
  });

  return (
    <div
      style={{
        position: 'absolute',
        bottom: 50,
        left: 0,
        width: 1920,
        textAlign: 'center',
        fontFamily: FONT_FAMILY,
        fontSize: 18,
        fontWeight: 400,
        color: '#94A3B8',
        opacity,
        letterSpacing: '0.02em',
      }}
    >
      Natural language is the model&apos;s deepest fluency
    </div>
  );
};

// ── Main component ──────────────────────────────────────────────────────
export const Part1Economics11PatchingVsRegeneration: React.FC = () => {
  const curatedBlockDefs = [
    {
      label: 'Prompt (300 tokens)',
      color: COLOR_BLUE_PROMPT,
      height: PROMPT_BLOCK_HEIGHT,
      startFrame: RIGHT_PROMPT_START,
    },
    {
      label: 'Tests (2,000 tokens)',
      color: COLOR_AMBER_TESTS,
      height: TESTS_BLOCK_HEIGHT,
      startFrame: RIGHT_TESTS_START,
    },
    {
      label: 'Grounding example',
      color: COLOR_GREEN_RELEVANT,
      height: GROUNDING_BLOCK_HEIGHT,
      startFrame: RIGHT_GROUNDING_START,
    },
  ];

  return (
    <AbsoluteFill style={{ backgroundColor: BACKGROUND_COLOR }}>
      {/* Section title */}
      <SectionTitle />

      {/* Center divider */}
      <CenterDivider />

      {/* VS badge */}
      <VsBadge />

      {/* Left panel: Agentic Patching */}
      <Sequence from={0} durationInFrames={TOTAL_FRAMES}>
        <PanelFrame
          x={LEFT_PANEL_X}
          y={LEFT_PANEL_Y}
          width={PANEL_WIDTH}
          height={PANEL_HEIGHT}
          borderColor={COLOR_BORDER_DASHED}
          borderStyle="dashed"
          header="Agentic Patching"
          headerColor={COLOR_SLATE_HEADER}
        >
          <TokenBlockGrid
            rows={TOKEN_ROWS}
            cols={TOKEN_COLS}
            blockWidth={TOKEN_BLOCK_WIDTH}
            blockHeight={TOKEN_BLOCK_HEIGHT}
            gap={TOKEN_GAP}
            padding={TOKEN_PADDING}
            irrelevantColor={COLOR_RED_IRRELEVANT}
            relevantColor={COLOR_GREEN_RELEVANT}
            neutralColor={COLOR_GRAY_NEUTRAL}
            irrelevantRatio={DISTRIBUTION_IRRELEVANT}
            relevantRatio={DISTRIBUTION_RELEVANT}
            fillStartFrame={LEFT_FILL_START}
            fillEndFrame={LEFT_FILL_END}
            staggerPerRow={3}
          />
        </PanelFrame>
      </Sequence>

      {/* Right panel: PDD Regeneration */}
      <Sequence from={0} durationInFrames={TOTAL_FRAMES}>
        <PanelFrame
          x={RIGHT_PANEL_X}
          y={RIGHT_PANEL_Y}
          width={PANEL_WIDTH}
          height={PANEL_HEIGHT}
          borderColor={COLOR_BLUE_PROMPT}
          borderStyle="solid"
          header="PDD Regeneration"
          headerColor={COLOR_BLUE_PROMPT}
        >
          <CuratedBlocks
            blocks={curatedBlockDefs}
            panelInnerWidth={PANEL_WIDTH}
            padding={BLOCK_PADDING}
            gap={BLOCK_GAP}
            roomToThinkStartFrame={RIGHT_ROOM_START}
            roomToThinkColor={COLOR_ROOM_TEXT}
            emptySpaceColor={COLOR_EMPTY_SPACE}
            panelHeight={PANEL_HEIGHT}
            fontFamily={FONT_FAMILY}
            labelFontSize={BLOCK_LABEL_FONT_SIZE}
          />
        </PanelFrame>
      </Sequence>

      {/* Comparison labels below panels */}
      <ComparisonLabels />

      {/* Bottom insight text */}
      <BottomInsight />
    </AbsoluteFill>
  );
};

export default Part1Economics11PatchingVsRegeneration;
