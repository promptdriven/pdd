import React, { useMemo } from "react";
import { AbsoluteFill, interpolate, useCurrentFrame, Easing } from "remotion";
import { COLORS, BEATS, BothGenerateFinalPropsType } from "./constants";

// Version label component
interface VersionLabelProps {
  text: string;
  side: "left" | "right";
}

const VersionLabel: React.FC<VersionLabelProps> = ({ text, side }) => (
  <div
    style={{
      position: "absolute",
      top: 30,
      left: side === "left" ? 60 : undefined,
      right: side === "right" ? 60 : undefined,
      fontSize: 24,
      fontWeight: "bold",
      color: COLORS.LABEL_WHITE,
      letterSpacing: 2,
    }}
  >
    {text}
  </div>
);

// Long prompt condensed (50 lines)
const LongPromptCondensed: React.FC = () => {
  // Use useMemo to generate stable random widths
  const lineWidths = useMemo(
    () => [...Array(10)].map(() => 60 + Math.random() * 35),
    []
  );

  return (
    <div
      style={{
        position: "absolute",
        left: 60,
        top: 100,
        width: 350,
      }}
    >
      <div
        style={{
          backgroundColor: COLORS.NOZZLE_BLUE,
          padding: "8px 12px",
          borderRadius: "8px 8px 0 0",
          fontFamily: "JetBrains Mono, monospace",
          fontSize: 14,
          color: "white",
          display: "flex",
          justifyContent: "space-between",
        }}
      >
        <span>parser_v1.prompt</span>
        <span style={{ opacity: 0.7 }}>50 lines</span>
      </div>
      <div
        style={{
          backgroundColor: COLORS.CODE_BG,
          padding: 12,
          borderRadius: "0 0 8px 8px",
          height: 180,
        }}
      >
        {/* Dense lines indicator */}
        {lineWidths.map((width, i) => (
          <div
            key={i}
            style={{
              height: 6,
              backgroundColor: COLORS.LINE_PLACEHOLDER,
              marginBottom: 4,
              borderRadius: 3,
              width: `${width}%`,
            }}
          />
        ))}
        <div
          style={{
            color: "rgba(255, 255, 255, 0.4)",
            fontSize: 12,
            marginTop: 8,
          }}
        >
          ... (40 more lines)
        </div>
      </div>
    </div>
  );
};

// Short prompt with surrounding test walls
const ShortPromptWithWallsCondensed: React.FC = () => {
  // Use useMemo to generate stable random widths
  const lineWidths = useMemo(
    () => [...Array(4)].map(() => 50 + Math.random() * 40),
    []
  );

  return (
    <div
      style={{
        position: "absolute",
        left: 60,
        top: 100,
      }}
    >
      {/* Small prompt */}
      <div style={{ width: 250 }}>
        <div
          style={{
            backgroundColor: COLORS.NOZZLE_BLUE,
            padding: "8px 12px",
            borderRadius: "8px 8px 0 0",
            fontFamily: "JetBrains Mono, monospace",
            fontSize: 14,
            color: "white",
            display: "flex",
            justifyContent: "space-between",
          }}
        >
          <span>parser_v2.prompt</span>
          <span style={{ opacity: 0.7 }}>10 lines</span>
        </div>
        <div
          style={{
            backgroundColor: COLORS.CODE_BG,
            padding: 12,
            borderRadius: "0 0 8px 8px",
            height: 80,
          }}
        >
          {lineWidths.map((width, i) => (
            <div
              key={i}
              style={{
                height: 6,
                backgroundColor: COLORS.LINE_PLACEHOLDER,
                marginBottom: 4,
                borderRadius: 3,
                width: `${width}%`,
              }}
            />
          ))}
        </div>
      </div>

      {/* Surrounding walls (tests) */}
      <div
        style={{
          position: "absolute",
          left: 280,
          top: 20,
          display: "flex",
          flexWrap: "wrap",
          width: 160,
          gap: 6,
        }}
      >
        {[...Array(16)].map((_, i) => (
          <div
            key={i}
            style={{
              width: 25,
              height: 35,
              backgroundColor: COLORS.WALLS_AMBER,
              borderRadius: 3,
              boxShadow: "0 0 10px rgba(217, 148, 74, 0.4)",
            }}
          />
        ))}
        <div
          style={{
            width: "100%",
            textAlign: "center",
            color: "rgba(255, 255, 255, 0.5)",
            fontSize: 11,
            marginTop: 4,
          }}
        >
          47 tests
        </div>
      </div>
    </div>
  );
};

// Generation arrow component
interface GenerationArrowProps {
  progress: number;
}

const GenerationArrow: React.FC<GenerationArrowProps> = ({ progress }) => {
  const arrowLength = 60;
  const dashProgress = progress * arrowLength;

  return (
    <div
      style={{
        position: "absolute",
        left: 180,
        top: 320,
        opacity: progress > 0 ? 1 : 0,
      }}
    >
      <svg width="40" height="80">
        <line
          x1={20}
          y1={0}
          x2={20}
          y2={arrowLength}
          stroke={COLORS.NOZZLE_BLUE}
          strokeWidth={3}
          strokeDasharray={arrowLength}
          strokeDashoffset={arrowLength - dashProgress}
          opacity={0.8}
        />
        {progress > 0.8 && (
          <polygon
            points="20,70 12,55 28,55"
            fill={COLORS.NOZZLE_BLUE}
            opacity={0.8}
          />
        )}
      </svg>
    </div>
  );
};

// Code output component
interface CodeOutputProps {
  progress: number;
  showSuccess: boolean;
  successOpacity: number;
}

const CodeOutput: React.FC<CodeOutputProps> = ({
  progress,
  showSuccess,
  successOpacity,
}) => {
  // Use useMemo to generate stable random widths for code lines
  const codeLineWidths = useMemo(
    () => [...Array(5)].map(() => 40 + Math.random() * 50),
    []
  );

  const visibleLines = Math.floor(progress * 5);

  return (
    <div
      style={{
        position: "absolute",
        left: 60,
        bottom: 140,
        width: 350,
      }}
    >
      <div
        style={{
          backgroundColor: COLORS.CODE_BG,
          borderRadius: 8,
          padding: 12,
          height: 120,
          border: "1px solid rgba(255, 255, 255, 0.1)",
          position: "relative",
        }}
      >
        <div
          style={{
            fontFamily: "JetBrains Mono, monospace",
            fontSize: 12,
            color: "rgba(255, 255, 255, 0.5)",
            marginBottom: 8,
          }}
        >
          output.py
        </div>

        {/* Generated code lines */}
        {codeLineWidths.slice(0, visibleLines).map((width, i) => (
          <div
            key={i}
            style={{
              height: 5,
              backgroundColor: COLORS.CODE_LINE,
              marginBottom: 3,
              borderRadius: 2,
              width: `${width}%`,
            }}
          />
        ))}

        {/* Success checkmark */}
        {showSuccess && (
          <div
            style={{
              position: "absolute",
              right: 16,
              bottom: 16,
              color: COLORS.SUCCESS_GREEN,
              fontSize: 28,
              opacity: successOpacity,
              transform: `scale(${interpolate(successOpacity, [0, 1], [0.5, 1])})`,
            }}
          >
            ✓
          </div>
        )}
      </div>
    </div>
  );
};

// Final message component
interface FinalMessageProps {
  opacity: number;
}

const FinalMessage: React.FC<FinalMessageProps> = ({ opacity }) => (
  <div
    style={{
      position: "absolute",
      bottom: 60,
      left: 0,
      right: 0,
      textAlign: "center",
      opacity,
    }}
  >
    <div
      style={{
        fontSize: 36,
        color: "white",
        fontWeight: 600,
        marginBottom: 12,
        textShadow: "0 0 40px rgba(255, 255, 255, 0.3)",
      }}
    >
      More tests, less prompt.
    </div>
    <div
      style={{
        fontSize: 28,
        color: COLORS.WALLS_AMBER,
        fontWeight: 500,
      }}
    >
      The walls do the precision work.
    </div>
  </div>
);

// Main component
export const BothGenerateFinal: React.FC<BothGenerateFinalPropsType> = ({
  showFinalMessage = true,
}) => {
  const frame = useCurrentFrame();

  // Split setup
  const setupOpacity = interpolate(
    frame,
    [BEATS.SETUP_START, BEATS.SETUP_END],
    [0, 1],
    { extrapolateRight: "clamp", easing: Easing.out(Easing.cubic) }
  );

  // Generation progress (for both sides)
  const generationProgress = interpolate(
    frame,
    [BEATS.GENERATION_START, BEATS.GENERATION_END],
    [0, 1],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
  );

  // Success checkmarks
  const successOpacity = interpolate(
    frame,
    [BEATS.SUCCESS_START, BEATS.SUCCESS_END],
    [0, 1],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.out(Easing.back(1.5)),
    }
  );

  // Dim sides for final message
  const sidesDim = interpolate(
    frame,
    [BEATS.DIM_START, BEATS.DIM_END],
    [1, 0.4],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp", easing: Easing.out(Easing.quad) }
  );

  // Final message opacity
  const messageOpacity = interpolate(
    frame,
    [BEATS.MESSAGE_START, BEATS.MESSAGE_END],
    [0, 1],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp", easing: Easing.out(Easing.cubic) }
  );

  return (
    <AbsoluteFill style={{ backgroundColor: COLORS.BACKGROUND }}>
      {/* Center divider */}
      <div
        style={{
          position: "absolute",
          left: "50%",
          top: 0,
          width: 1,
          height: "100%",
          backgroundColor: COLORS.DIVIDER,
          opacity: setupOpacity,
        }}
      />

      {/* Left side - Version 1 (Long Prompt) */}
      <div
        style={{
          position: "absolute",
          left: 0,
          top: 0,
          width: "50%",
          height: "100%",
          opacity: setupOpacity * sidesDim,
        }}
      >
        <VersionLabel text="VERSION 1" side="left" />
        <LongPromptCondensed />
        <GenerationArrow progress={generationProgress} />
        <CodeOutput
          progress={generationProgress}
          showSuccess={successOpacity > 0}
          successOpacity={successOpacity}
        />
      </div>

      {/* Right side - Version 2 (Short Prompt + Tests) */}
      <div
        style={{
          position: "absolute",
          right: 0,
          top: 0,
          width: "50%",
          height: "100%",
          opacity: setupOpacity * sidesDim,
        }}
      >
        <VersionLabel text="VERSION 2" side="right" />
        <ShortPromptWithWallsCondensed />
        <GenerationArrow progress={generationProgress} />
        <CodeOutput
          progress={generationProgress}
          showSuccess={successOpacity > 0}
          successOpacity={successOpacity}
        />
      </div>

      {/* Final message */}
      {showFinalMessage && messageOpacity > 0 && (
        <FinalMessage opacity={messageOpacity} />
      )}
    </AbsoluteFill>
  );
};
