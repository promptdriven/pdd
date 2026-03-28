import React from "react";
import {
  AbsoluteFill,
  useCurrentFrame,
  interpolate,
  Easing,
  Sequence,
} from "remotion";
import {
  BG_COLOR,
  GREEN_ACCENT,
  ARTIFACT_LABEL_COLOR,
  CANVAS_WIDTH,
  CANVAS_HEIGHT,
  CODE_FILE_X,
  CODE_FILE_Y,
  PROMPT_FILE_X,
  PROMPT_FILE_Y,
  MODULE_HEIGHT,
  TOTAL_FRAMES,
  LABELS_START,
  LABELS_FADE_DURATION,
} from "./constants";
import { CodebaseBackground } from "./CodebaseBackground";
import { HighlightedModule } from "./HighlightedModule";
import { TerminalPanel } from "./TerminalPanel";
import { PromptFile } from "./PromptFile";
import { ParticleFlow } from "./ParticleFlow";

export const defaultWhereToStart03ModuleHighlightTerminalProps = {};

/**
 * Section 6.3: Module Highlight & Terminal Command
 *
 * A module highlights with green glow, a terminal slides up and types a command,
 * a prompt file materializes with particle flow from code to prompt,
 * then the code desaturates to "artifact" and the prompt glows as "source of truth".
 *
 * Duration: 270 frames (9s @ 30fps)
 */
export const WhereToStart03ModuleHighlightTerminal: React.FC = () => {
  const frame = useCurrentFrame();

  // Labels fade in
  const labelOpacity = interpolate(
    frame,
    [LABELS_START, LABELS_START + LABELS_FADE_DURATION],
    [0, 1],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.out(Easing.quad),
    }
  );

  return (
    <AbsoluteFill
      style={{
        backgroundColor: BG_COLOR,
        overflow: "hidden",
        width: CANVAS_WIDTH,
        height: CANVAS_HEIGHT,
      }}
    >
      {/* Layer 1: Dimmed codebase background */}
      <Sequence from={0} durationInFrames={TOTAL_FRAMES}>
        <CodebaseBackground />
      </Sequence>

      {/* Layer 2: Highlighted module (code file) */}
      <Sequence from={0} durationInFrames={TOTAL_FRAMES}>
        <HighlightedModule />
      </Sequence>

      {/* Layer 3: Terminal panel sliding up and typing */}
      <Sequence from={0} durationInFrames={TOTAL_FRAMES}>
        <TerminalPanel />
      </Sequence>

      {/* Layer 4: Prompt file materializing */}
      <Sequence from={0} durationInFrames={TOTAL_FRAMES}>
        <PromptFile />
      </Sequence>

      {/* Layer 5: Particle flow from code → prompt */}
      <Sequence from={0} durationInFrames={TOTAL_FRAMES}>
        <ParticleFlow />
      </Sequence>

      {/* Layer 6: Labels — "artifact" and "source of truth" */}
      <div
        style={{
          position: "absolute",
          left: CODE_FILE_X - 60,
          top: CODE_FILE_Y + MODULE_HEIGHT / 2 + 20,
          width: 120,
          textAlign: "center",
          fontFamily: "Inter, sans-serif",
          fontSize: 16,
          fontStyle: "italic",
          color: ARTIFACT_LABEL_COLOR,
          opacity: labelOpacity * 0.6,
        }}
      >
        artifact
      </div>

      <div
        style={{
          position: "absolute",
          left: PROMPT_FILE_X - 80,
          top: PROMPT_FILE_Y + MODULE_HEIGHT / 2 + 20,
          width: 160,
          textAlign: "center",
          fontFamily: "Inter, sans-serif",
          fontSize: 16,
          fontWeight: 600,
          color: GREEN_ACCENT,
          opacity: labelOpacity,
        }}
      >
        source of truth
      </div>

      {/* Connecting line hint between files (subtle) */}
      {frame >= 150 && (
        <svg
          style={{
            position: "absolute",
            inset: 0,
            width: "100%",
            height: "100%",
            pointerEvents: "none",
          }}
        >
          {/* Arrow from code to prompt */}
          <line
            x1={CODE_FILE_X + 150}
            y1={CODE_FILE_Y}
            x2={PROMPT_FILE_X - 150}
            y2={PROMPT_FILE_Y}
            stroke={GREEN_ACCENT}
            strokeWidth={1}
            opacity={interpolate(
              frame,
              [150, 180, 240, 270],
              [0, 0.15, 0.15, 0.1],
              {
                extrapolateLeft: "clamp",
                extrapolateRight: "clamp",
              }
            )}
            strokeDasharray="6 4"
          />
        </svg>
      )}
    </AbsoluteFill>
  );
};

export default WhereToStart03ModuleHighlightTerminal;
