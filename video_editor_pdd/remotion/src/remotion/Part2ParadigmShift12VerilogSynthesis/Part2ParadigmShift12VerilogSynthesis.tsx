import React from "react";
import {
  AbsoluteFill,
  useCurrentFrame,
  interpolate,
} from "remotion";
import { BG_COLOR, TOTAL_FRAMES, WIDTH, HEIGHT } from "./constants";
import { BlueprintGrid } from "./BlueprintGrid";
import { SchematicDissolve } from "./SchematicDissolve";
import { CodeBlock } from "./CodeBlock";
import { SynthesisChip } from "./SynthesisChip";
import { GateStream } from "./GateStream";

export const defaultPart2ParadigmShift12VerilogSynthesisProps = {};

/**
 * Section 2.12: Verilog Synthesis — Schematic to Code
 *
 * Animation sequence (360 frames @ 30fps = 12s):
 *   0–60:   Dense schematic dissolves (particle scatter)
 *   60–150: Verilog code types in line by line
 *   150–210: Synthesis chip fades in, input arrow pulses
 *   210–300: Code flows in, gate symbols stream out
 *   300–360: Gate stream continues, hold
 */
export const Part2ParadigmShift12VerilogSynthesis: React.FC = () => {
  const frame = useCurrentFrame();

  // Section title fade (visible from frame 0 for readability, fades out as code types in)
  const titleOpacity = interpolate(frame, [0, 10, 50, 70], [0.85, 0.85, 0.85, 0], {
    extrapolateLeft: "clamp",
    extrapolateRight: "clamp",
  });

  // Progression label at bottom
  const progressLabels = [
    { text: "Hand-drawn Schematic", start: 0, end: 60 },
    { text: "Hardware Description Language", start: 60, end: 150 },
    { text: "Automatic Synthesis", start: 150, end: 361 },
  ];

  const activeLabel = progressLabels.find(
    (l) => frame >= l.start && frame < l.end
  );

  const labelOpacity = activeLabel
    ? interpolate(
        frame,
        [activeLabel.start, activeLabel.start + 15, activeLabel.end - 15, activeLabel.end],
        [0, 0.85, 0.85, 0],
        { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
      )
    : 0;

  // Bottom progression bar
  const progress = interpolate(frame, [0, TOTAL_FRAMES], [0, 1], {
    extrapolateLeft: "clamp",
    extrapolateRight: "clamp",
  });

  // Abstraction level indicator
  const abstractionLevel = interpolate(frame, [0, 60, 150, 360], [1, 2, 3, 3], {
    extrapolateLeft: "clamp",
    extrapolateRight: "clamp",
  });
  const abstractionOpacity = interpolate(frame, [0, 20], [0, 0.78], {
    extrapolateLeft: "clamp",
    extrapolateRight: "clamp",
  });

  return (
    <AbsoluteFill
      style={{
        backgroundColor: BG_COLOR,
        width: WIDTH,
        height: HEIGHT,
        overflow: "hidden",
      }}
    >
      {/* Blueprint grid background */}
      <BlueprintGrid />

      {/* Phase 1: Schematic dissolve (frames 0–60) */}
      <SchematicDissolve />

      {/* Phase 2: Verilog code typing (frames 60–150+) */}
      <CodeBlock />

      {/* Phase 3: Synthesis chip (frames 150+) */}
      <SynthesisChip />

      {/* Phase 4: Gate stream (frames 210+) */}
      <GateStream />

      {/* Section title overlay */}
      <div
        style={{
          position: "absolute",
          top: 40,
          left: 0,
          width: WIDTH,
          textAlign: "center",
          fontFamily: "'Inter', sans-serif",
          fontSize: 28,
          fontWeight: 600,
          color: "#E2E8F0",
          opacity: titleOpacity,
          letterSpacing: 1,
          textShadow: "0 2px 8px rgba(0,0,0,0.5)",
        }}
      >
        Verilog Synthesis
      </div>

      {/* Progression label */}
      {activeLabel && (
        <div
          style={{
            position: "absolute",
            bottom: 80,
            left: 0,
            width: WIDTH,
            textAlign: "center",
            fontFamily: "'Inter', sans-serif",
            fontSize: 20,
            fontWeight: 500,
            color: "#94A3B8",
            opacity: labelOpacity,
            letterSpacing: 1,
          }}
        >
          {activeLabel.text}
        </div>
      )}

      {/* Abstraction level indicator (top-right) */}
      <div
        style={{
          position: "absolute",
          top: 40,
          right: 60,
          display: "flex",
          flexDirection: "column",
          alignItems: "flex-end",
          opacity: abstractionOpacity,
        }}
      >
        <span
          style={{
            fontFamily: "'Inter', sans-serif",
            fontSize: 11,
            color: "#546E7A",
            letterSpacing: 1.5,
            marginBottom: 6,
            textTransform: "uppercase",
          }}
        >
          Abstraction
        </span>
        <div style={{ display: "flex", gap: 4 }}>
          {[1, 2, 3].map((level) => (
            <div
              key={level}
              style={{
                width: 24,
                height: 6,
                borderRadius: 3,
                backgroundColor:
                  level <= Math.round(abstractionLevel)
                    ? "#4A90D9"
                    : "rgba(74, 144, 217, 0.15)",
                transition: "background-color 0.3s",
              }}
            />
          ))}
        </div>
      </div>

      {/* Bottom progress bar */}
      <div
        style={{
          position: "absolute",
          bottom: 40,
          left: 100,
          width: WIDTH - 200,
          height: 3,
          backgroundColor: "rgba(74, 144, 217, 0.1)",
          borderRadius: 2,
        }}
      >
        <div
          style={{
            width: `${progress * 100}%`,
            height: "100%",
            backgroundColor: "#4A90D9",
            borderRadius: 2,
            opacity: 0.6,
          }}
        />
      </div>

      {/* Progress stages (schematic → code → gates) */}
      <div
        style={{
          position: "absolute",
          bottom: 50,
          left: 100,
          width: WIDTH - 200,
          display: "flex",
          justifyContent: "space-between",
        }}
      >
        {[
          { label: "Schematic", at: 0 },
          { label: "Code", at: 0.42 },
          { label: "Gates", at: 0.83 },
        ].map((stage, si) => {
          const isActive = progress >= stage.at;
          return (
            <span
              key={si}
              style={{
                fontFamily: "'Inter', sans-serif",
                fontSize: 10,
                color: isActive ? "#4A90D9" : "#546E7A",
                opacity: isActive ? 0.8 : 0.4,
                letterSpacing: 1,
                textTransform: "uppercase",
              }}
            >
              {stage.label}
            </span>
          );
        })}
      </div>
    </AbsoluteFill>
  );
};

export default Part2ParadigmShift12VerilogSynthesis;
