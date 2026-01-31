import React from "react";
import { AbsoluteFill, interpolate, useCurrentFrame, Easing } from "remotion";
import {
  COLORS,
  BEATS,
  SHORT_PROMPT_CONTENT,
  WALL_COUNT,
  CENTER_X,
  CENTER_Y,
  INNER_RADIUS,
  ShortPromptTestsPropsType,
} from "./constants";

interface SmallPromptFileProps {
  filename: string;
  content: string;
  lineCount: number;
  opacity: number;
}

const SmallPromptFile: React.FC<SmallPromptFileProps> = ({
  filename,
  content,
  lineCount,
  opacity,
}) => {
  return (
    <div
      style={{
        position: "absolute",
        left: "50%",
        top: "50%",
        transform: "translate(-50%, -50%)",
        width: 500,
        opacity,
        zIndex: 10,
      }}
    >
      {/* File header */}
      <div
        style={{
          backgroundColor: COLORS.NOZZLE_BLUE,
          padding: "10px 16px",
          borderTopLeftRadius: 8,
          borderTopRightRadius: 8,
          display: "flex",
          alignItems: "center",
          justifyContent: "space-between",
        }}
      >
        <span
          style={{
            color: "white",
            fontFamily: "JetBrains Mono, monospace",
            fontSize: 16,
          }}
        >
          {filename}
        </span>
        <span
          style={{
            color: "rgba(255, 255, 255, 0.7)",
            fontSize: 12,
            fontFamily: "JetBrains Mono, monospace",
          }}
        >
          {lineCount} lines
        </span>
      </div>

      {/* File content */}
      <div
        style={{
          backgroundColor: COLORS.FILE_CONTENT_BG,
          padding: 16,
          borderBottomLeftRadius: 8,
          borderBottomRightRadius: 8,
        }}
      >
        {content.split("\n").map((line, i) => (
          <div
            key={i}
            style={{
              fontFamily: "JetBrains Mono, monospace",
              fontSize: 14,
              color: line.startsWith("#")
                ? COLORS.NOZZLE_BLUE
                : COLORS.LABEL_GRAY,
              marginBottom: 4,
              lineHeight: 1.5,
            }}
          >
            {line || "\u00A0"}
          </div>
        ))}
      </div>
    </div>
  );
};

interface SurroundingWallsProps {
  count: number;
  pulse: number;
}

const SurroundingWalls: React.FC<SurroundingWallsProps> = ({ count, pulse }) => {
  // Generate wall positions in a ring around center
  const walls = [];

  for (let i = 0; i < count; i++) {
    const angle = (i / WALL_COUNT) * Math.PI * 2;
    const radius = INNER_RADIUS + (i % 3) * 60;
    walls.push({
      x: CENTER_X + Math.cos(angle) * radius - 20,
      y: CENTER_Y + Math.sin(angle) * radius - 30,
      delay: i * 4,
    });
  }

  return (
    <>
      {walls.map((wall, i) => (
        <div
          key={i}
          style={{
            position: "absolute",
            left: wall.x,
            top: wall.y,
            width: 40,
            height: 60,
            backgroundColor: COLORS.WALLS_AMBER,
            borderRadius: 4,
            transform: `scale(${pulse})`,
            boxShadow: `0 0 20px rgba(217, 148, 74, 0.5)`,
            zIndex: 1,
          }}
        />
      ))}
    </>
  );
};

interface TerminalSnippetProps {
  command: string;
  output: string;
  opacity: number;
}

const TerminalSnippet: React.FC<TerminalSnippetProps> = ({
  command,
  output,
  opacity,
}) => {
  return (
    <div
      style={{
        position: "absolute",
        right: 80,
        bottom: 80,
        backgroundColor: COLORS.TERMINAL_BG,
        borderRadius: 8,
        padding: 16,
        opacity,
        border: "1px solid rgba(255, 255, 255, 0.1)",
        zIndex: 20,
      }}
    >
      <div
        style={{
          fontFamily: "JetBrains Mono, monospace",
          fontSize: 14,
          color: COLORS.LABEL_GRAY,
          marginBottom: 8,
        }}
      >
        $ {command}
      </div>
      <div
        style={{
          fontFamily: "JetBrains Mono, monospace",
          fontSize: 14,
          color: COLORS.SUCCESS_GREEN,
          display: "flex",
          alignItems: "center",
          gap: 8,
        }}
      >
        {output}
      </div>
    </div>
  );
};

export const ShortPromptTests: React.FC<ShortPromptTestsPropsType> = ({
  showTerminal = true,
}) => {
  const frame = useCurrentFrame();

  // Prompt opacity with easeOutCubic
  const promptOpacity = interpolate(
    frame,
    [BEATS.PROMPT_START, BEATS.PROMPT_END],
    [0, 1],
    { extrapolateRight: "clamp", easing: Easing.out(Easing.cubic) }
  );

  // Number of walls visible (staggered appearance)
  const wallProgress = interpolate(
    frame,
    [BEATS.WALLS_START, BEATS.WALLS_END],
    [0, WALL_COUNT],
    { extrapolateRight: "clamp", easing: Easing.out(Easing.back(1.5)) }
  );
  const wallCount = Math.floor(wallProgress);

  // Terminal opacity with easeOutCubic
  const terminalOpacity = showTerminal
    ? interpolate(
        frame,
        [BEATS.TERMINAL_START, BEATS.TERMINAL_END],
        [0, 1],
        { extrapolateLeft: "clamp", extrapolateRight: "clamp", easing: Easing.out(Easing.cubic) }
      )
    : 0;

  // Wall pulse effect (easeInOutSine approximation with sine wave)
  const wallPulse =
    frame > BEATS.TERMINAL_START
      ? 1 + Math.sin(frame * 0.08) * 0.05
      : 1;

  return (
    <AbsoluteFill style={{ backgroundColor: COLORS.BACKGROUND }}>
      {/* Many test walls surrounding prompt */}
      <SurroundingWalls count={wallCount} pulse={wallPulse} />

      {/* Small prompt file */}
      <SmallPromptFile
        filename="parser_v2.prompt"
        content={SHORT_PROMPT_CONTENT}
        lineCount={10}
        opacity={promptOpacity}
      />

      {/* Terminal snippet */}
      {showTerminal && (
        <TerminalSnippet
          command="pdd test parser"
          output="47 tests passed \u2713"
          opacity={terminalOpacity}
        />
      )}
    </AbsoluteFill>
  );
};
