import React from 'react';
import { AbsoluteFill, useCurrentFrame, interpolate, Easing } from 'remotion';
import { BG_COLOR } from './constants';
import { BlueprintGrid } from './BlueprintGrid';
import { SchematicDissolve } from './SchematicDissolve';
import { CodeBlock } from './CodeBlock';
import { SynthesisChip } from './SynthesisChip';
import { GateStream } from './GateStream';

export const defaultPart2ParadigmShift12VerilogSynthesisProps = {};

/**
 * Section 2.12: Verilog Synthesis — Schematic to Code
 *
 * A transformation animation showing:
 * 1. Dense schematic dissolves (0–60)
 * 2. Verilog code types in (60–150)
 * 3. Synthesis chip appears (150–210)
 * 4. Gate stream flows out (210–360)
 *
 * Duration: 360 frames (12s @ 30fps)
 */
export const Part2ParadigmShift12VerilogSynthesis: React.FC = () => {
  const frame = useCurrentFrame();

  // Subtle label for the abstraction level, fades in after code is typed
  const abstractionLabelOpacity = interpolate(
    frame,
    [120, 150],
    [0, 0.85],
    { extrapolateLeft: 'clamp', extrapolateRight: 'clamp', easing: Easing.out(Easing.cubic) }
  );

  // "Generated Gates" label appears when gate stream starts
  const gatesLabelOpacity = interpolate(
    frame,
    [220, 250],
    [0, 0.85],
    { extrapolateLeft: 'clamp', extrapolateRight: 'clamp', easing: Easing.out(Easing.cubic) }
  );

  // Stage indicators along the bottom
  const stageProgress = interpolate(
    frame,
    [0, 60, 150, 210, 300],
    [0, 1, 2, 3, 3],
    { extrapolateLeft: 'clamp', extrapolateRight: 'clamp' }
  );

  const stages = ['Schematic', 'HDL Code', 'Synthesis', 'Gate Netlist'];

  return (
    <AbsoluteFill
      style={{
        backgroundColor: BG_COLOR,
        overflow: 'hidden',
      }}
    >
      {/* Blueprint grid background */}
      <BlueprintGrid />

      {/* Phase 1: Schematic dissolves (frames 0–60) */}
      <SchematicDissolve />

      {/* Phase 2: Verilog code types in (frames 60–150) */}
      <CodeBlock />

      {/* Label: "Hardware Description Language" */}
      {frame >= 120 && (
        <div
          style={{
            position: 'absolute',
            left: 560,
            top: 62,
            fontFamily: 'Inter, system-ui, sans-serif',
            fontSize: 18,
            fontWeight: 600,
            color: '#C792EA',
            opacity: abstractionLabelOpacity,
            letterSpacing: 1,
          }}
        >
          Verilog HDL
        </div>
      )}

      {/* Phase 3: Synthesis chip (frames 150+) */}
      <SynthesisChip />

      {/* Phase 4: Gate stream (frames 210+) */}
      <GateStream />

      {/* Label: "Auto-Generated Gates" */}
      {frame >= 220 && (
        <div
          style={{
            position: 'absolute',
            right: 180,
            top: 530,
            fontFamily: 'Inter, system-ui, sans-serif',
            fontSize: 18,
            fontWeight: 600,
            color: '#5AAA6E',
            opacity: gatesLabelOpacity,
            letterSpacing: 0.5,
          }}
        >
          Gate-Level Netlist
        </div>
      )}

      {/* Abstraction flow arrow (bottom) */}
      <div
        style={{
          position: 'absolute',
          bottom: 60,
          left: 0,
          width: 1920,
          display: 'flex',
          justifyContent: 'center',
          alignItems: 'center',
          gap: 0,
        }}
      >
        {stages.map((stage, i) => {
          const isActive = stageProgress >= i;
          const isCurrent = Math.floor(stageProgress) === i;

          return (
            <React.Fragment key={stage}>
              {/* Stage dot + label */}
              <div
                style={{
                  display: 'flex',
                  flexDirection: 'column',
                  alignItems: 'center',
                  opacity: isActive ? 0.9 : 0.25,
                  transition: 'opacity 0.3s',
                }}
              >
                <div
                  style={{
                    width: isCurrent ? 14 : 10,
                    height: isCurrent ? 14 : 10,
                    borderRadius: '50%',
                    backgroundColor: isActive ? '#4A90D9' : '#334155',
                    border: isCurrent ? '2px solid #93C5FD' : 'none',
                    marginBottom: 8,
                  }}
                />
                <span
                  style={{
                    fontFamily: 'Inter, system-ui, sans-serif',
                    fontSize: 13,
                    fontWeight: isCurrent ? 600 : 400,
                    color: isActive ? '#CBD5E1' : '#475569',
                  }}
                >
                  {stage}
                </span>
              </div>

              {/* Connector line between stages */}
              {i < stages.length - 1 && (
                <div
                  style={{
                    width: 100,
                    height: 2,
                    backgroundColor: stageProgress > i ? '#4A90D9' : '#334155',
                    opacity: stageProgress > i ? 0.7 : 0.25,
                    marginBottom: 24,
                    marginLeft: 8,
                    marginRight: 8,
                    borderRadius: 1,
                  }}
                />
              )}
            </React.Fragment>
          );
        })}
      </div>

      {/* Horizontal rule / divider above stage indicators */}
      <div
        style={{
          position: 'absolute',
          bottom: 110,
          left: 200,
          right: 200,
          height: 2,
          backgroundColor: '#4A90D9',
          opacity: 0.7,
          borderRadius: 1,
        }}
      />
    </AbsoluteFill>
  );
};

export default Part2ParadigmShift12VerilogSynthesis;
