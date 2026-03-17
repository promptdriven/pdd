import React from 'react';
import {
  AbsoluteFill,
  interpolate,
  useCurrentFrame,
  Easing,
  Sequence,
} from 'remotion';
import { PromptDocument } from './PromptDocument';
import { MoldCrossSection } from './MoldCrossSection';
import { TimelineBar } from './TimelineBar';
import { CANVAS, COLORS, STAGES, ANIM, DOC_WIDTH, MOLD_WIDTH, MOLD_HEIGHT } from './constants';

export const defaultPart4PrecisionTradeoff05TestAccumulationInsightProps = {};

// ─── Stage Column ──────────────────────────────────────────────────────────────

const StageColumn: React.FC<{
  stageIndex: number;
  animationStart: number;
}> = ({ stageIndex, animationStart }) => {
  const frame = useCurrentFrame();
  const stage = STAGES[stageIndex];

  const fadeIn = interpolate(
    frame,
    [animationStart, animationStart + 30],
    [0, 1],
    { extrapolateLeft: 'clamp', extrapolateRight: 'clamp', easing: Easing.out(Easing.cubic) }
  );

  const slideUp = interpolate(
    frame,
    [animationStart, animationStart + 30],
    [20, 0],
    { extrapolateLeft: 'clamp', extrapolateRight: 'clamp', easing: Easing.out(Easing.cubic) }
  );

  // Center prompt and mold within the column
  const columnCenterX = stage.x + 250; // center of 500px column
  const docX = columnCenterX - DOC_WIDTH / 2;
  const moldX = columnCenterX - MOLD_WIDTH / 2;

  // Vertical layout: header, prompt doc, mold, label
  const headerY = 110;
  const docY = 150;
  const moldY = docY + stage.promptHeight + 30;
  const labelY = moldY + MOLD_HEIGHT + 20;

  return (
    <div
      style={{
        position: 'absolute',
        left: stage.x,
        top: 0,
        width: 500,
        height: CANVAS.HEIGHT,
        opacity: fadeIn,
        transform: `translateY(${slideUp}px)`,
      }}
    >
      {/* Stage header */}
      <div
        style={{
          position: 'absolute',
          left: 0,
          top: headerY,
          width: 500,
          textAlign: 'center',
          fontFamily: 'Inter, sans-serif',
          fontSize: 13,
          fontWeight: 600,
          color: stage.color,
          opacity: 0.5,
          letterSpacing: 2,
        }}
      >
        {stage.label}
      </div>

      {/* Prompt Document */}
      <PromptDocument
        x={docX - stage.x}
        y={docY}
        width={DOC_WIDTH}
        height={stage.promptHeight}
        lineCount={stage.promptLines}
        lineColor={COLORS.promptLine}
        lineOpacity={0.4}
        animationStart={animationStart}
      />

      {/* Prompt line count label */}
      <div
        style={{
          position: 'absolute',
          left: docX - stage.x + DOC_WIDTH + 8,
          top: docY + stage.promptHeight / 2 - 8,
          fontFamily: 'Inter, sans-serif',
          fontSize: 10,
          fontWeight: 500,
          color: COLORS.promptLine,
          opacity: 0.35,
          whiteSpace: 'nowrap',
        }}
      >
        {stage.promptLines} lines
      </div>

      {/* Mold Cross Section */}
      <MoldCrossSection
        x={moldX - stage.x}
        y={moldY}
        width={MOLD_WIDTH}
        height={MOLD_HEIGHT}
        wallCount={stage.wallCount}
        wallColor={COLORS.wall}
        wallOpacity={0.7}
        wallStroke={stage.wallStroke}
        fillColor={COLORS.fill}
        fillOpacity={stage.fillOpacity}
        animationStart={animationStart}
        glow={stageIndex === 2 ? { color: '#5AAA6E', blur: 12, opacity: 0.1 } : undefined}
      />

      {/* Wall count label */}
      <div
        style={{
          position: 'absolute',
          left: moldX - stage.x + MOLD_WIDTH + 8,
          top: moldY + MOLD_HEIGHT / 2 - 8,
          fontFamily: 'Inter, sans-serif',
          fontSize: 10,
          fontWeight: 500,
          color: COLORS.wall,
          opacity: 0.35,
          whiteSpace: 'nowrap',
        }}
      >
        {stage.wallCount} walls
      </div>

      {/* Stage description label */}
      <div
        style={{
          position: 'absolute',
          left: 0,
          top: labelY,
          width: 500,
          textAlign: 'center',
          fontFamily: 'Inter, sans-serif',
          fontSize: 10,
          color: stage.color,
          opacity: 0.5,
        }}
      >
        {stage.description}
      </div>
    </div>
  );
};

// ─── Connecting Arrow ──────────────────────────────────────────────────────────

const ConnectingArrow: React.FC<{
  fromX: number;
  toX: number;
  y: number;
  animationStart: number;
  label?: string;
}> = ({ fromX, toX, y, animationStart, label }) => {
  const frame = useCurrentFrame();

  const drawProgress = interpolate(
    frame,
    [animationStart, animationStart + 15],
    [0, 1],
    { extrapolateLeft: 'clamp', extrapolateRight: 'clamp', easing: Easing.out(Easing.quad) }
  );

  const arrowWidth = (toX - fromX) * drawProgress;

  return (
    <>
      <svg
        style={{
          position: 'absolute',
          left: fromX,
          top: y - 8,
          width: toX - fromX + 10,
          height: 16,
          overflow: 'visible',
        }}
      >
        {/* Line */}
        <line
          x1={0}
          y1={8}
          x2={arrowWidth}
          y2={8}
          stroke={COLORS.arrowLine}
          strokeWidth={2}
          strokeOpacity={0.3}
        />
        {/* Arrowhead */}
        {drawProgress > 0.8 && (
          <polygon
            points={`${arrowWidth - 8},3 ${arrowWidth},8 ${arrowWidth - 8},13`}
            fill={COLORS.arrowLine}
            opacity={0.3 * Math.min(1, (drawProgress - 0.8) / 0.2)}
          />
        )}
      </svg>
      {/* Label above arrow */}
      {label && (
        <div
          style={{
            position: 'absolute',
            left: fromX,
            top: y - 22,
            width: toX - fromX,
            textAlign: 'center',
            fontFamily: 'Inter, sans-serif',
            fontSize: 9,
            color: COLORS.arrowText,
            opacity: 0.3 * drawProgress,
          }}
        >
          {label}
        </div>
      )}
    </>
  );
};

// ─── Main Component ────────────────────────────────────────────────────────────

export const Part4PrecisionTradeoff05TestAccumulationInsight: React.FC = () => {
  const frame = useCurrentFrame();

  // Title fade in
  const titleOpacity = interpolate(
    frame,
    [ANIM.titleIn.start, ANIM.titleIn.start + ANIM.titleIn.dur],
    [0, 0.7],
    { extrapolateLeft: 'clamp', extrapolateRight: 'clamp', easing: Easing.out(Easing.quad) }
  );

  // Callout fade in
  const calloutOpacity = interpolate(
    frame,
    [ANIM.callout.start, ANIM.callout.start + ANIM.callout.dur],
    [0, 0.6],
    { extrapolateLeft: 'clamp', extrapolateRight: 'clamp', easing: Easing.out(Easing.quad) }
  );

  // Center Y for arrows between stages (roughly mid-mold area)
  const arrowY = 340;

  return (
    <AbsoluteFill style={{ backgroundColor: CANVAS.BG }}>
      {/* ── Title ── */}
      <div
        style={{
          position: 'absolute',
          left: 0,
          top: 50,
          width: CANVAS.WIDTH,
          textAlign: 'center',
          fontFamily: 'Inter, sans-serif',
          fontSize: 18,
          fontWeight: 700,
          color: COLORS.title,
          opacity: titleOpacity,
          letterSpacing: 1,
        }}
      >
        TEST ACCUMULATION OVER TIME
      </div>

      {/* ── Stage 1: Day 1 ── */}
      <Sequence from={ANIM.stage1.start} layout="none">
        <StageColumn stageIndex={0} animationStart={ANIM.stage1.start} />
      </Sequence>

      {/* ── Arrow 1→2 ── */}
      <Sequence from={ANIM.arrow1.start} layout="none">
        <ConnectingArrow
          fromX={STAGES[0].x + 400}
          toX={STAGES[1].x + 100}
          y={arrowY}
          animationStart={ANIM.arrow1.start}
          label="walls added, prompt simplified"
        />
      </Sequence>

      {/* ── Stage 2: Month 1 ── */}
      <Sequence from={ANIM.stage2.start} layout="none">
        <StageColumn stageIndex={1} animationStart={ANIM.stage2.start} />
      </Sequence>

      {/* ── Arrow 2→3 ── */}
      <Sequence from={ANIM.arrow2.start} layout="none">
        <ConnectingArrow
          fromX={STAGES[1].x + 400}
          toX={STAGES[2].x + 100}
          y={arrowY}
          animationStart={ANIM.arrow2.start}
          label="walls added, prompt simplified"
        />
      </Sequence>

      {/* ── Stage 3: Month 6 ── */}
      <Sequence from={ANIM.stage3.start} layout="none">
        <StageColumn stageIndex={2} animationStart={ANIM.stage3.start} />
      </Sequence>

      {/* ── Timeline Bar ── */}
      <Sequence from={ANIM.timeline.start} layout="none">
        <TimelineBar
          y={915}
          xStart={160}
          xEnd={1760}
          markers={[
            { label: 'Day 1', x: STAGES[0].x + 250 },
            { label: 'Month 1', x: STAGES[1].x + 250 },
            { label: 'Month 6', x: STAGES[2].x + 250 },
          ]}
          gradientFrom="#D9944A"
          gradientTo="#5AAA6E"
          animationStart={ANIM.timeline.start}
          fillDuration={ANIM.timeline.dur}
        />
      </Sequence>

      {/* ── Callout ── */}
      <div
        style={{
          position: 'absolute',
          left: 0,
          top: 980,
          width: CANVAS.WIDTH,
          textAlign: 'center',
          fontFamily: 'Inter, sans-serif',
          fontSize: 13,
          color: COLORS.callout,
          opacity: calloutOpacity,
        }}
      >
        Not just about catching bugs. It&apos;s about making prompts{' '}
        <span style={{ color: COLORS.simpler }}>simpler</span> and regeneration{' '}
        <span style={{ color: COLORS.safer }}>safer</span> over time.
      </div>
    </AbsoluteFill>
  );
};

export default Part4PrecisionTradeoff05TestAccumulationInsight;
