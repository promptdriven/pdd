import React from 'react';
import {
  AbsoluteFill,
  useCurrentFrame,
  interpolate,
  Easing,
  Sequence,
} from 'remotion';
import {
  BG_COLOR,
  COMPILER_COLOR,
  LABEL_COLOR,
  COL_1_X,
  COL_2_X,
  COL_3_X,
  PHASE2_START,
  CODE_APPEAR,
  COMPILER_APPEAR,
  NETLIST_APPEAR,
  TOTAL_FRAMES,
} from './constants';
import { CircuitGrid } from './CircuitGrid';
import { HandDrawnSchematic } from './HandDrawnSchematic';
import { VerilogCodeBlock } from './VerilogCodeBlock';
import { CompilerIcon } from './CompilerIcon';
import { GateNetlist } from './GateNetlist';
import { FlowArrow } from './FlowArrow';
import { EquivalenceOverlay } from './EquivalenceOverlay';

export const defaultPart2ParadigmShift07VerilogSynthesisTripleProps = {};

/**
 * Phase 1: Schematic dissolves → Verilog code appears → compiler → single netlist.
 * Frames 0–180.
 */
const Phase1: React.FC = () => {
  const frame = useCurrentFrame();

  // Cross-fade out Phase 1 as Phase 2 comes in (frames 180–220 of parent = 0–40 of Phase2)
  const phase1Opacity = interpolate(frame, [160, 180], [1, 0], {
    extrapolateLeft: 'clamp',
    extrapolateRight: 'clamp',
  });

  return (
    <div style={{ position: 'absolute', inset: 0, opacity: phase1Opacity }}>
      {/* Hand-drawn schematic dissolving (frames 0-40) */}
      <HandDrawnSchematic />

      {/* Verilog code block fades in with typing (frame 40+) */}
      <VerilogCodeBlock
        x={960}
        y={250}
        width={500}
        height={220}
        fontSize={11}
        startFrame={CODE_APPEAR}
        typeEffect
      />

      {/* Arrow from code → compiler (frame 90+) */}
      <FlowArrow
        x1={960}
        y1={365}
        x2={960}
        y2={455}
        startFrame={COMPILER_APPEAR}
        drawDuration={15}
      />

      {/* Compiler icon (frame 90+) */}
      <CompilerIcon
        x={960}
        y={480}
        size={60}
        startFrame={COMPILER_APPEAR}
        label="Synthesis"
        pulse
      />

      {/* Arrow from compiler → netlist (frame 90+) */}
      <FlowArrow
        x1={960}
        y1={515}
        x2={960}
        y2={555}
        startFrame={COMPILER_APPEAR + 10}
        drawDuration={15}
      />

      {/* Single gate-level netlist (frame 130+) */}
      <GateNetlist
        x={960}
        y={660}
        width={400}
        height={200}
        gateCount={6}
        layout="horizontal"
        startFrame={NETLIST_APPEAR}
        drawDuration={40}
      />
    </div>
  );
};

/**
 * Phase 2: Triple synthesis — 3 columns with different netlists.
 * Starts at frame 180 of the parent.
 */
const Phase2: React.FC = () => {
  const frame = useCurrentFrame();

  // Fade in Phase 2
  const phase2Opacity = interpolate(frame, [0, 30], [0, 1], {
    extrapolateLeft: 'clamp',
    extrapolateRight: 'clamp',
    easing: Easing.out(Easing.quad),
  });

  // "Same input" label
  const labelOpacity = interpolate(frame, [10, 30], [0, 0.4], {
    extrapolateLeft: 'clamp',
    extrapolateRight: 'clamp',
  });

  const columns = [COL_1_X, COL_2_X, COL_3_X];

  return (
    <div style={{ position: 'absolute', inset: 0, opacity: phase2Opacity }}>
      {/* "Same input" label at top */}
      <div
        style={{
          position: 'absolute',
          top: 25,
          left: 0,
          width: 1920,
          textAlign: 'center',
          fontFamily: "'Inter', sans-serif",
          fontSize: 12,
          color: LABEL_COLOR,
          opacity: labelOpacity,
          letterSpacing: 0.5,
        }}
      >
        Same input
      </div>

      {/* Shared code block at top (no typing effect, immediate) */}
      <VerilogCodeBlock
        x={960}
        y={120}
        width={800}
        height={160}
        fontSize={10}
        startFrame={0}
        typeEffect={false}
      />

      {/* Three arrows down to compilers (frame 40 of Phase 2 = frame 220 global) */}
      {columns.map((cx, i) => (
        <FlowArrow
          key={`arrow-${i}`}
          x1={cx}
          y1={205}
          x2={cx}
          y2={370}
          startFrame={40}
          drawDuration={20}
        />
      ))}

      {/* Three compiler icons at arrow midpoints */}
      {columns.map((cx, i) => (
        <CompilerIcon
          key={`compiler-${i}`}
          x={cx}
          y={310}
          size={40}
          startFrame={45 + i * 5}
          label=""
          pulse
        />
      ))}

      {/* Three different gate-level netlists (frame 100 of Phase 2 = frame 280 global) */}
      <GateNetlist
        x={COL_1_X}
        y={560}
        width={380}
        height={250}
        gateCount={6}
        layout="horizontal_compact"
        startFrame={100}
        drawDuration={60}
      />
      <GateNetlist
        x={COL_2_X}
        y={560}
        width={380}
        height={250}
        gateCount={8}
        layout="vertical_long"
        startFrame={100}
        drawDuration={60}
      />
      <GateNetlist
        x={COL_3_X}
        y={560}
        width={380}
        height={250}
        gateCount={5}
        layout="mixed_optimized"
        startFrame={100}
        drawDuration={60}
      />

      {/* Netlist labels */}
      {['Netlist A — 6 gates', 'Netlist B — 8 gates', 'Netlist C — 5 gates'].map((label, i) => {
        const labelFade = interpolate(frame, [160 + i * 5, 175 + i * 5], [0, 0.35], {
          extrapolateLeft: 'clamp',
          extrapolateRight: 'clamp',
        });
        return (
          <div
            key={`label-${i}`}
            style={{
              position: 'absolute',
              left: columns[i] - 100,
              top: 695,
              width: 200,
              textAlign: 'center',
              fontFamily: "'Inter', sans-serif",
              fontSize: 10,
              color: LABEL_COLOR,
              opacity: labelFade,
            }}
          >
            {label}
          </div>
        );
      })}

      {/* Equivalence overlay: checkmarks + label (frame 220 of Phase 2 = frame 400 global) */}
      <EquivalenceOverlay startFrame={220} />
    </div>
  );
};

export const Part2ParadigmShift07VerilogSynthesisTriple: React.FC = () => {
  return (
    <AbsoluteFill style={{ backgroundColor: BG_COLOR }}>
      {/* Circuit board grid background */}
      <CircuitGrid />

      {/* Phase 1: Schematic → Verilog → Synthesis → Single Netlist (frames 0-180) */}
      <Sequence from={0} durationInFrames={PHASE2_START + 40}>
        <Phase1 />
      </Sequence>

      {/* Phase 2: Triple synthesis (frames 180-540) */}
      <Sequence from={PHASE2_START} durationInFrames={TOTAL_FRAMES - PHASE2_START}>
        <Phase2 />
      </Sequence>
    </AbsoluteFill>
  );
};

export default Part2ParadigmShift07VerilogSynthesisTriple;
