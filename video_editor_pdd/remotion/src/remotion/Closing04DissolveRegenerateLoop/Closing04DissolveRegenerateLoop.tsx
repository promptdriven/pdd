import React from 'react';
import { AbsoluteFill, useCurrentFrame } from 'remotion';
import {
  BG_COLOR,
  GRID_COLOR,
  GRID_OPACITY,
  GRID_SPACING,
  CANVAS_WIDTH,
  CANVAS_HEIGHT,
  CODE_V1,
  CODE_V2,
  CODE_V3,
  // Cycle 1 timing
  C1_DISSOLVE_START,
  C1_DISSOLVE_END,
  C1_REGEN_START,
  C1_TERMINAL_START,
  C1_CHECK_START,
  // Cycle 2 timing
  C2_DISSOLVE_START,
  C2_DISSOLVE_END,
  C2_REGEN_START,
  C2_TERMINAL_START,
  C2_CHECK_START,
  // Hold
  HOLD_START,
} from './constants';
import PddTriangle from './PddTriangle';
import DissolveParticles from './DissolveParticles';
import CodeBlock from './CodeBlock';
import TerminalStrip from './TerminalStrip';

// ── Grid Background ────────────────────────────────────────────────
const GridBackground: React.FC = () => {
  const lines: React.ReactNode[] = [];
  for (let x = GRID_SPACING; x < CANVAS_WIDTH; x += GRID_SPACING) {
    lines.push(
      <line
        key={`v-${x}`}
        x1={x}
        y1={0}
        x2={x}
        y2={CANVAS_HEIGHT}
        stroke={GRID_COLOR}
        strokeWidth={1}
        opacity={GRID_OPACITY}
      />
    );
  }
  for (let y = GRID_SPACING; y < CANVAS_HEIGHT; y += GRID_SPACING) {
    lines.push(
      <line
        key={`h-${y}`}
        x1={0}
        y1={y}
        x2={CANVAS_WIDTH}
        y2={y}
        stroke={GRID_COLOR}
        strokeWidth={1}
        opacity={GRID_OPACITY}
      />
    );
  }
  return (
    <svg
      width={CANVAS_WIDTH}
      height={CANVAS_HEIGHT}
      style={{ position: 'absolute', top: 0, left: 0 }}
    >
      {lines}
    </svg>
  );
};

// ── Exported Props ─────────────────────────────────────────────────
export const defaultClosing04DissolveRegenerateLoopProps = {};

// ── Main Component ─────────────────────────────────────────────────
export const Closing04DissolveRegenerateLoop: React.FC = () => {
  const frame = useCurrentFrame();

  // Determine which code block phase we're in
  // Phase 1: V1 visible from frame 0, dissolves at C1_DISSOLVE_START
  // Phase 2: V2 types in at C1_REGEN_START, dissolves at C2_DISSOLVE_START
  // Phase 3: V3 types in at C2_REGEN_START, holds through end

  const isAfterHoldStart = frame >= HOLD_START;

  return (
    <AbsoluteFill
      style={{
        backgroundColor: BG_COLOR,
        overflow: 'hidden',
      }}
    >
      {/* Grid */}
      <GridBackground />

      {/* Background PDD triangle — always present at low opacity */}
      <PddTriangle
        triangleOpacity={0.3}
        glowOpacity={0.1}
        brightenAtEnd={isAfterHoldStart}
      />

      {/* ── CYCLE 1 ─────────────────────────────────────────── */}

      {/* V1 code: visible immediately, dissolves at frame 10 */}
      <CodeBlock
        code={CODE_V1}
        typeInStartFrame={0}
        dissolveStartFrame={C1_DISSOLVE_START}
        showImmediate
      />

      {/* V1 dissolve particles */}
      <DissolveParticles
        code={CODE_V1}
        dissolveStartFrame={C1_DISSOLVE_START}
        dissolveDuration={C1_DISSOLVE_END - C1_DISSOLVE_START}
        seed={42}
      />

      {/* V2 code: types in at frame 30, dissolves at frame 65 */}
      <CodeBlock
        code={CODE_V2}
        typeInStartFrame={C1_REGEN_START}
        dissolveStartFrame={C2_DISSOLVE_START}
      />

      {/* Cycle 1 terminal */}
      <TerminalStrip
        command="pdd test"
        result="✓ All tests passed"
        typeStartFrame={C1_TERMINAL_START}
        checkStartFrame={C1_CHECK_START}
      />

      {/* ── CYCLE 2 ─────────────────────────────────────────── */}

      {/* V2 dissolve particles */}
      <DissolveParticles
        code={CODE_V2}
        dissolveStartFrame={C2_DISSOLVE_START}
        dissolveDuration={C2_DISSOLVE_END - C2_DISSOLVE_START}
        seed={137}
      />

      {/* V3 code: types in at frame 85, never dissolves (use very high frame) */}
      <CodeBlock
        code={CODE_V3}
        typeInStartFrame={C2_REGEN_START}
        dissolveStartFrame={9999}
      />

      {/* Cycle 2 terminal — overlays the cycle 1 terminal after C2_TERMINAL_START */}
      {frame >= C2_TERMINAL_START && (
        <TerminalStrip
          command="pdd test"
          result="✓ All tests passed"
          typeStartFrame={C2_TERMINAL_START}
          checkStartFrame={C2_CHECK_START}
        />
      )}
    </AbsoluteFill>
  );
};

export default Closing04DissolveRegenerateLoop;
