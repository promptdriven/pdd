import React from "react";
import { AbsoluteFill, interpolate, useCurrentFrame, Easing } from "remotion";
import { COLORS, BEATS, ThreeComponentsPropsType } from "./constants";

interface ComponentBlockProps {
  label: string;
  sublabel: string;
  color: string;
  glowIntensity: number;
  x: number;
  y: number;
}

const ComponentBlock: React.FC<ComponentBlockProps> = ({
  label,
  sublabel,
  color,
  glowIntensity,
  x,
  y,
}) => (
  <div
    style={{
      position: "absolute",
      left: x,
      top: y,
      transform: "translate(-50%, -50%)",
      textAlign: "center",
    }}
  >
    <div
      style={{
        width: 160,
        height: 70,
        background: `rgba(${color === "#4A90D9" ? "74, 144, 217" : color === "#5AAA6E" ? "90, 170, 110" : "217, 148, 74"}, ${0.15 + 0.2 * glowIntensity})`,
        border: `2px solid ${color}`,
        borderRadius: 12,
        display: "flex",
        alignItems: "center",
        justifyContent: "center",
        boxShadow: glowIntensity > 0 ? `0 0 ${25 * glowIntensity}px ${color}` : "none",
      }}
    >
      <span
        style={{
          fontSize: 16,
          fontWeight: "bold",
          color: color,
        }}
      >
        {label}
      </span>
    </div>
    <div
      style={{
        marginTop: 8,
        fontSize: 14,
        color: COLORS.LABEL_GRAY,
      }}
    >
      {sublabel}
    </div>
  </div>
);

export const ThreeComponents: React.FC<ThreeComponentsPropsType> = ({
  showFormula = true,
}) => {
  const frame = useCurrentFrame();

  // System visibility
  const systemOpacity = interpolate(
    frame,
    [BEATS.SYSTEM_START, BEATS.SYSTEM_END],
    [0, 1],
    { extrapolateRight: "clamp", easing: Easing.out(Easing.cubic) }
  );

  // Component glows
  const promptGlow = interpolate(
    frame,
    [BEATS.PROMPT_GLOW_START, BEATS.PROMPT_GLOW_END, BEATS.PROMPT_GLOW_END + 60],
    [0, 1, 0.3],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
  );

  const groundingGlow = interpolate(
    frame,
    [BEATS.GROUNDING_GLOW_START, BEATS.GROUNDING_GLOW_END, BEATS.GROUNDING_GLOW_END + 60],
    [0, 1, 0.3],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
  );

  const wallsGlow = interpolate(
    frame,
    [BEATS.WALLS_GLOW_START, BEATS.WALLS_GLOW_END, BEATS.WALLS_GLOW_END + 60],
    [0, 1, 0.4],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
  );

  // Code output
  const codeOpacity = interpolate(
    frame,
    [BEATS.CODE_OUTPUT_START, BEATS.CODE_OUTPUT_END],
    [0, 1],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
  );

  // Formula
  const formulaOpacity = interpolate(
    frame,
    [BEATS.FORMULA_START, BEATS.FORMULA_END],
    [0, 1],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
  );

  // Layout
  const centerX = 960;
  const promptY = 180;
  const groundingY = 340;
  const wallsY = 500;
  const outputY = 680;

  return (
    <AbsoluteFill style={{ backgroundColor: COLORS.BACKGROUND }}>
      <div style={{ opacity: systemOpacity }}>
        {/* Prompt component */}
        <ComponentBlock
          label="PROMPT"
          sublabel="Intent"
          color={COLORS.NOZZLE_BLUE}
          glowIntensity={promptGlow}
          x={centerX}
          y={promptY}
        />

        {/* Flow arrow 1 */}
        <svg
          width="40"
          height="60"
          style={{
            position: "absolute",
            left: centerX - 20,
            top: promptY + 50,
          }}
        >
          <line
            x1={20}
            y1={0}
            x2={20}
            y2={45}
            stroke={frame > BEATS.PROMPT_GLOW_START ? COLORS.NOZZLE_BLUE : COLORS.LABEL_GRAY}
            strokeWidth={2}
            opacity={0.6}
          />
          <polygon
            points="20,55 12,42 28,42"
            fill={frame > BEATS.PROMPT_GLOW_START ? COLORS.NOZZLE_BLUE : COLORS.LABEL_GRAY}
            opacity={0.6}
          />
        </svg>

        {/* Grounding component */}
        <ComponentBlock
          label="GROUNDING"
          sublabel="Style"
          color={COLORS.GROUNDING_GREEN}
          glowIntensity={groundingGlow}
          x={centerX}
          y={groundingY}
        />

        {/* Flow arrow 2 */}
        <svg
          width="40"
          height="60"
          style={{
            position: "absolute",
            left: centerX - 20,
            top: groundingY + 50,
          }}
        >
          <line
            x1={20}
            y1={0}
            x2={20}
            y2={45}
            stroke={frame > BEATS.GROUNDING_GLOW_START ? COLORS.GROUNDING_GREEN : COLORS.LABEL_GRAY}
            strokeWidth={2}
            opacity={0.6}
          />
          <polygon
            points="20,55 12,42 28,42"
            fill={frame > BEATS.GROUNDING_GLOW_START ? COLORS.GROUNDING_GREEN : COLORS.LABEL_GRAY}
            opacity={0.6}
          />
        </svg>

        {/* Walls/Tests component */}
        <ComponentBlock
          label="TESTS"
          sublabel="Constraints"
          color={COLORS.WALLS_AMBER}
          glowIntensity={wallsGlow}
          x={centerX}
          y={wallsY}
        />

        {/* Flow arrow 3 */}
        <svg
          width="40"
          height="60"
          style={{
            position: "absolute",
            left: centerX - 20,
            top: wallsY + 50,
          }}
        >
          <line
            x1={20}
            y1={0}
            x2={20}
            y2={45}
            stroke={frame > BEATS.WALLS_GLOW_START ? COLORS.WALLS_AMBER : COLORS.LABEL_GRAY}
            strokeWidth={2}
            opacity={0.6}
          />
          <polygon
            points="20,55 12,42 28,42"
            fill={frame > BEATS.WALLS_GLOW_START ? COLORS.WALLS_AMBER : COLORS.LABEL_GRAY}
            opacity={0.6}
          />
        </svg>

        {/* Code output */}
        <div
          style={{
            position: "absolute",
            left: centerX,
            top: outputY,
            transform: "translate(-50%, -50%)",
            opacity: codeOpacity,
            textAlign: "center",
          }}
        >
          <div
            style={{
              width: 200,
              height: 60,
              background: "rgba(138, 156, 175, 0.15)",
              border: `2px solid ${COLORS.CODE_GRAY}`,
              borderRadius: 12,
              display: "flex",
              alignItems: "center",
              justifyContent: "center",
              gap: 8,
            }}
          >
            <span style={{ fontSize: 14, color: COLORS.CODE_GRAY }}>Generated Code</span>
            <span style={{ fontSize: 18, color: COLORS.SUCCESS_GREEN }}>✓✓✓</span>
          </div>
        </div>
      </div>

      {/* Integration formula */}
      {showFormula && formulaOpacity > 0 && (
        <div
          style={{
            position: "absolute",
            bottom: 80,
            left: "50%",
            transform: "translateX(-50%)",
            opacity: formulaOpacity,
            textAlign: "center",
          }}
        >
          <div
            style={{
              fontSize: 24,
              fontWeight: "bold",
              marginBottom: 8,
            }}
          >
            <span style={{ color: COLORS.NOZZLE_BLUE }}>Prompt</span>
            {" + "}
            <span style={{ color: COLORS.WALLS_AMBER }}>Tests</span>
            {" + "}
            <span style={{ color: COLORS.GROUNDING_GREEN }}>Grounding</span>
          </div>
          <div style={{ fontSize: 18, color: COLORS.LABEL_GRAY }}>
            Intent + Constraints + Style
          </div>
          <div style={{ fontSize: 20, color: COLORS.LABEL_WHITE, marginTop: 8 }}>
            = Complete Specification
          </div>
        </div>
      )}
    </AbsoluteFill>
  );
};
