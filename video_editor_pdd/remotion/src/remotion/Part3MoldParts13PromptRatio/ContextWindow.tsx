import React from "react";
import { useCurrentFrame, interpolate, Easing } from "remotion";
import {
  BLOCK_BG,
  RED_TINT,
  RED_LABEL,
  GREEN_TINT,
  SUBLABEL_COLOR,
  CTX_WINDOW_WIDTH,
  CTX_WINDOW_HEIGHT,
  CTX_LEFT_X,
  CTX_RIGHT_X,
  CTX_Y,
  DENSE_CODE_FILLER,
  CLEAN_PROMPT_FILLER,
  LEFT_FILL_START,
  LEFT_FILL_DUR,
  RIGHT_FILL_START,
  RIGHT_FILL_DUR,
  EMPHASIS_START,
  EMPHASIS_DUR,
  CROSSFADE_START,
  CROSSFADE_DUR,
} from "./constants";

interface WindowPanelProps {
  x: number;
  tintColor: string;
  label: string;
  sublabel: string;
  sublabelColor: string;
  sublabelWeight: number;
  lines: string[];
  lineFontSize: number;
  lineColor: string;
  fillProgress: number;
  emphasisGlow?: number;
}

const WindowPanel: React.FC<WindowPanelProps> = ({
  x,
  tintColor,
  label,
  sublabel,
  sublabelColor,
  sublabelWeight,
  lines,
  lineFontSize,
  lineColor,
  fillProgress,
  emphasisGlow = 0,
}) => {
  const visibleLines = Math.floor(fillProgress * lines.length);

  return (
    <div
      style={{
        position: "absolute",
        left: x,
        top: CTX_Y,
        width: CTX_WINDOW_WIDTH,
      }}
    >
      {/* Label */}
      <div
        style={{
          fontFamily: "Inter, sans-serif",
          fontSize: 14,
          fontWeight: 600,
          color: tintColor,
          marginBottom: 8,
        }}
      >
        {label}
      </div>

      {/* Window rectangle */}
      <div
        style={{
          width: CTX_WINDOW_WIDTH,
          height: CTX_WINDOW_HEIGHT,
          backgroundColor: BLOCK_BG,
          border: `2px solid rgba(${tintColor === RED_TINT ? "239, 68, 68" : "74, 222, 128"}, 0.2)`,
          borderRadius: 8,
          padding: 10,
          overflow: "hidden",
          boxSizing: "border-box",
          boxShadow: emphasisGlow > 0
            ? `0 0 ${emphasisGlow * 30}px rgba(74, 222, 128, ${emphasisGlow * 0.3})`
            : "none",
        }}
      >
        {lines.slice(0, visibleLines).map((line, i) => (
          <div
            key={i}
            style={{
              fontFamily: "'JetBrains Mono', monospace",
              fontSize: lineFontSize,
              lineHeight: `${lineFontSize + 3}px`,
              color: lineColor,
              whiteSpace: "pre",
              opacity: tintColor === RED_TINT ? 0.4 : 0.8,
            }}
          >
            {line || "\u00A0"}
          </div>
        ))}
      </div>

      {/* Sublabel */}
      <div
        style={{
          fontFamily: "Inter, sans-serif",
          fontSize: tintColor === RED_TINT ? 12 : 14,
          fontWeight: sublabelWeight,
          color: sublabelColor,
          marginTop: 8,
          textShadow:
            emphasisGlow > 0
              ? `0 0 ${emphasisGlow * 15}px rgba(74, 222, 128, 0.5)`
              : "none",
        }}
      >
        {sublabel}
      </div>
    </div>
  );
};

export const ContextWindowComparison: React.FC = () => {
  const frame = useCurrentFrame();

  // Overall phase 2 opacity (crossfade in)
  const phaseOpacity = interpolate(
    frame,
    [CROSSFADE_START, CROSSFADE_START + CROSSFADE_DUR],
    [0, 1],
    {
      easing: Easing.inOut(Easing.cubic),
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
    }
  );

  // Left window fill progress
  const leftFill = interpolate(
    frame,
    [LEFT_FILL_START, LEFT_FILL_START + LEFT_FILL_DUR],
    [0, 1],
    {
      easing: Easing.out(Easing.quad),
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
    }
  );

  // Right window fill progress
  const rightFill = interpolate(
    frame,
    [RIGHT_FILL_START, RIGHT_FILL_START + RIGHT_FILL_DUR],
    [0, 1],
    {
      easing: Easing.out(Easing.quad),
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
    }
  );

  // Emphasis glow on right window
  const emphasisRaw = interpolate(
    frame,
    [
      EMPHASIS_START,
      EMPHASIS_START + EMPHASIS_DUR / 2,
      EMPHASIS_START + EMPHASIS_DUR,
    ],
    [0, 1, 0.6],
    {
      easing: Easing.inOut(Easing.sin),
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
    }
  );

  // Title
  const titleOpacity = interpolate(
    frame,
    [CROSSFADE_START + 10, CROSSFADE_START + 30],
    [0, 1],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
    }
  );

  return (
    <div
      style={{
        position: "absolute",
        left: 0,
        top: 0,
        width: "100%",
        height: "100%",
        opacity: phaseOpacity,
      }}
    >
      {/* Section title */}
      <div
        style={{
          position: "absolute",
          top: 100,
          width: "100%",
          textAlign: "center",
          fontFamily: "Inter, sans-serif",
          fontSize: 24,
          fontWeight: 600,
          color: "#E2E8F0",
          opacity: titleOpacity,
          letterSpacing: "-0.02em",
        }}
      >
        Context Window Comparison
      </div>

      {/* "vs" divider */}
      <div
        style={{
          position: "absolute",
          left: "50%",
          top: CTX_Y + CTX_WINDOW_HEIGHT / 2 + 30,
          transform: "translate(-50%, -50%)",
          fontFamily: "Inter, sans-serif",
          fontSize: 18,
          fontWeight: 600,
          color: SUBLABEL_COLOR,
          opacity: titleOpacity * 0.8,
        }}
      >
        vs
      </div>

      {/* Left: Raw code window */}
      <WindowPanel
        x={CTX_LEFT_X}
        tintColor={RED_TINT}
        label="15,000 tokens of raw code"
        sublabel="Dense. Hard to parse."
        sublabelColor={SUBLABEL_COLOR}
        sublabelWeight={400}
        lines={DENSE_CODE_FILLER}
        lineFontSize={8}
        lineColor={RED_LABEL}
        fillProgress={leftFill}
      />

      {/* Right: Prompts window */}
      <WindowPanel
        x={CTX_RIGHT_X}
        tintColor={GREEN_TINT}
        label="Prompts for 10 modules"
        sublabel="10× more system knowledge"
        sublabelColor={GREEN_TINT}
        sublabelWeight={700}
        lines={CLEAN_PROMPT_FILLER}
        lineFontSize={10}
        lineColor={GREEN_TINT}
        fillProgress={rightFill}
        emphasisGlow={emphasisRaw}
      />
    </div>
  );
};
