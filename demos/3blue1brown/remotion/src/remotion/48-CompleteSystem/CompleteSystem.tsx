import React from "react";
import { AbsoluteFill, interpolate, useCurrentFrame, Easing } from "remotion";
import {
  COLORS,
  BEATS,
  MODULES,
  CONNECTIONS,
  CompleteSystemPropsType,
} from "./constants";

// ── Module Block ────────────────────────────────────────────────
interface ModuleBlockProps {
  name: string;
  x: number;
  y: number;
  promptGlow: number;
  testGlow: number;
  codeOpacity: number;
}

const ModuleBlock: React.FC<ModuleBlockProps> = ({
  name,
  x,
  y,
  promptGlow,
  testGlow,
  codeOpacity,
}) => (
  <div
    style={{
      position: "absolute",
      left: x,
      top: y,
      width: 320,
    }}
  >
    {/* Module label */}
    <div
      style={{
        fontSize: 14,
        color: COLORS.LABEL_DIM,
        marginBottom: 8,
        fontFamily: "monospace",
      }}
    >
      {name}/
    </div>

    {/* Prompt file - GLOWS */}
    <div
      style={{
        backgroundColor: "rgba(74, 144, 217, 0.15)",
        border: "1px solid #4A90D9",
        borderRadius: 6,
        padding: "8px 12px",
        marginBottom: 6,
        boxShadow: `0 0 ${20 * promptGlow}px rgba(74, 144, 217, ${0.6 * promptGlow})`,
        fontFamily: "monospace",
        fontSize: 13,
        color: COLORS.PROMPT_BLUE,
      }}
    >
      {name}.prompt
    </div>

    {/* Test file - GLOWS */}
    <div
      style={{
        backgroundColor: "rgba(217, 148, 74, 0.15)",
        border: "1px solid #D9944A",
        borderRadius: 6,
        padding: "8px 12px",
        marginBottom: 6,
        boxShadow: `0 0 ${20 * testGlow}px rgba(217, 148, 74, ${0.6 * testGlow})`,
        fontFamily: "monospace",
        fontSize: 13,
        color: COLORS.TEST_AMBER,
      }}
    >
      test_{name}.py
    </div>

    {/* Generated code - NO GLOW, dim */}
    <div
      style={{
        backgroundColor: "rgba(160, 160, 160, 0.08)",
        border: "1px solid rgba(160, 160, 160, 0.2)",
        borderRadius: 6,
        padding: "8px 12px",
        opacity: codeOpacity,
        fontFamily: "monospace",
        fontSize: 13,
        color: "rgba(160, 160, 160, 0.6)",
      }}
    >
      {name}.py
    </div>
  </div>
);

// ── Connection Lines ────────────────────────────────────────────
interface ModuleConnectionsProps {
  opacity: number;
}

const ModuleConnections: React.FC<ModuleConnectionsProps> = ({ opacity }) => (
  <svg
    style={{
      position: "absolute",
      width: "100%",
      height: "100%",
      top: 0,
      left: 0,
      pointerEvents: "none",
    }}
  >
    {CONNECTIONS.map(([fromIdx, toIdx], i) => {
      const from = MODULES[fromIdx];
      const to = MODULES[toIdx];
      // Connect from center of module blocks (320px wide, ~120px tall)
      const fromCX = from.x + 160;
      const fromCY = from.y + 60;
      const toCX = to.x + 160;
      const toCY = to.y + 60;

      return (
        <line
          key={i}
          x1={fromCX}
          y1={fromCY}
          x2={toCX}
          y2={toCY}
          stroke="rgba(255, 255, 255, 0.08)"
          strokeWidth={1}
          strokeDasharray="6 8"
          opacity={opacity}
        />
      );
    })}
  </svg>
);

// ── Main Component ──────────────────────────────────────────────
export const CompleteSystem: React.FC<CompleteSystemPropsType> = ({
  showConnections = true,
}) => {
  const frame = useCurrentFrame();

  // Camera pull-back (zoom out)
  const scale = interpolate(
    frame,
    [BEATS.ZOOM_START, BEATS.ZOOM_END],
    [1.8, 1.0],
    { extrapolateRight: "clamp", easing: Easing.out(Easing.cubic) }
  );

  // Glow activation for prompts (staggered per module)
  const promptGlow = (moduleIndex: number) =>
    interpolate(
      frame,
      [
        BEATS.PROMPT_GLOW_START + moduleIndex * BEATS.PROMPT_GLOW_STAGGER,
        BEATS.PROMPT_GLOW_START + moduleIndex * BEATS.PROMPT_GLOW_STAGGER + 30,
      ],
      [0, 1],
      { extrapolateRight: "clamp", easing: Easing.out(Easing.quad) }
    );

  // Glow activation for tests (staggered, after prompts)
  const testGlow = (moduleIndex: number) =>
    interpolate(
      frame,
      [
        BEATS.TEST_GLOW_START + moduleIndex * BEATS.TEST_GLOW_STAGGER,
        BEATS.TEST_GLOW_START + moduleIndex * BEATS.TEST_GLOW_STAGGER + 30,
      ],
      [0, 1],
      { extrapolateRight: "clamp", easing: Easing.out(Easing.quad) }
    );

  // Code dim
  const codeDim = interpolate(
    frame,
    [BEATS.CODE_DIM_START, BEATS.CODE_DIM_END],
    [0.8, 0.4],
    { extrapolateRight: "clamp", easing: Easing.out(Easing.quad) }
  );

  return (
    <AbsoluteFill style={{ backgroundColor: COLORS.BACKGROUND }}>
      <div
        style={{
          transform: `scale(${scale})`,
          transformOrigin: "center center",
          width: "100%",
          height: "100%",
          position: "relative",
        }}
      >
        {/* Connection lines between modules */}
        {showConnections && <ModuleConnections opacity={0.15} />}

        {/* Module blocks */}
        {MODULES.map((mod, i) => (
          <ModuleBlock
            key={mod.name}
            name={mod.name}
            x={mod.x}
            y={mod.y}
            promptGlow={promptGlow(i)}
            testGlow={testGlow(i)}
            codeOpacity={codeDim}
          />
        ))}
      </div>
    </AbsoluteFill>
  );
};
