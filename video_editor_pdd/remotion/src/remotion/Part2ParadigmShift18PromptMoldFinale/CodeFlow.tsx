import React, { useMemo } from "react";
import { useCurrentFrame, interpolate, Easing } from "remotion";
import {
  CODE_TEXT_COLOR,
  CAVITY_X,
  CAVITY_Y,
  CAVITY_WIDTH,
  CAVITY_HEIGHT,
  WALL_THICKNESS,
  REGEN_INTERVAL,
  DISSOLVE_DURATION,
  FILL_DURATION,
  CODE_GENERATIONS,
} from "./constants";

// Padding inside the cavity walls
const INNER_PAD = 16;
const LINE_HEIGHT = 20;
const INNER_X = CAVITY_X + WALL_THICKNESS + INNER_PAD;
const INNER_Y = CAVITY_Y + WALL_THICKNESS + INNER_PAD;
const INNER_WIDTH = CAVITY_WIDTH - 2 * (WALL_THICKNESS + INNER_PAD);
const INNER_HEIGHT = CAVITY_HEIGHT - 2 * (WALL_THICKNESS + INNER_PAD);

// Connection line from prompt to cavity
const STREAM_SOURCE_Y = 180; // below prompt document

interface CodeFlowProps {
  /** Whether the flash is currently active (for parent coordination) */
  onFlashState?: (active: boolean) => void;
}

export const CodeFlow: React.FC<CodeFlowProps> = () => {
  const frame = useCurrentFrame();

  // Determine which generation we're on (0, 1, 2)
  const genIndex = Math.min(
    Math.floor(frame / REGEN_INTERVAL),
    CODE_GENERATIONS.length - 1
  );
  const localFrame = frame - genIndex * REGEN_INTERVAL;

  // Phase within each generation:
  // 0..DISSOLVE_DURATION: dissolve previous (except gen 0)
  // DISSOLVE_DURATION..DISSOLVE_DURATION+FILL_DURATION: fill new
  // after: hold
  const isFirstGen = genIndex === 0;
  const dissolveEnd = isFirstGen ? 0 : DISSOLVE_DURATION;
  const fillStart = dissolveEnd;
  const fillEnd = fillStart + FILL_DURATION;

  // Dissolve opacity (previous generation fading out)
  const dissolveOpacity = isFirstGen
    ? 0
    : interpolate(localFrame, [0, dissolveEnd], [0.6, 0], {
        extrapolateLeft: "clamp",
        extrapolateRight: "clamp",
        easing: Easing.in(Easing.quad),
      });

  // Fill progress for current generation
  const fillProgress = interpolate(localFrame, [fillStart, fillEnd], [0, 1], {
    extrapolateLeft: "clamp",
    extrapolateRight: "clamp",
    easing: Easing.out(Easing.cubic),
  });

  // Current code lines
  const codeLines = CODE_GENERATIONS[genIndex];
  const prevLines =
    genIndex > 0 ? CODE_GENERATIONS[genIndex - 1] : [];

  // Stream particles from prompt to cavity
  const streamOpacity = interpolate(
    fillProgress,
    [0, 0.3, 0.9, 1],
    [0, 0.6, 0.4, 0],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
  );

  // Number of visible lines based on fill progress
  const visibleLines = Math.floor(fillProgress * codeLines.length);

  // Per-line fade for the last appearing line
  const lastLineFade =
    visibleLines < codeLines.length && visibleLines > 0
      ? (fillProgress * codeLines.length) % 1
      : 1;

  // Generate stream particles
  const particles = useMemo(() => {
    const pts: Array<{ id: number; xOffset: number; speed: number }> = [];
    for (let i = 0; i < 8; i++) {
      pts.push({
        id: i,
        xOffset: ((i * 47 + 13) % INNER_WIDTH) - INNER_WIDTH / 2,
        speed: 0.6 + (i % 3) * 0.2,
      });
    }
    return pts;
  }, []);

  return (
    <>
      {/* Stream connection line */}
      <div
        style={{
          position: "absolute",
          left: CAVITY_X + CAVITY_WIDTH / 2 - 1,
          top: STREAM_SOURCE_Y,
          width: 2,
          height: CAVITY_Y - STREAM_SOURCE_Y,
          background: `linear-gradient(to bottom, ${CODE_TEXT_COLOR}00, ${CODE_TEXT_COLOR}66)`,
          opacity: streamOpacity,
        }}
      />

      {/* Stream particles */}
      {fillProgress > 0 && fillProgress < 1 && (
        <>
          {particles.map((p) => {
            const yProgress =
              ((frame * p.speed * 0.05 + p.id * 0.12) % 1);
            const py = STREAM_SOURCE_Y + yProgress * (CAVITY_Y - STREAM_SOURCE_Y);
            return (
              <div
                key={p.id}
                style={{
                  position: "absolute",
                  left: CAVITY_X + CAVITY_WIDTH / 2 + p.xOffset * 0.3,
                  top: py,
                  width: 3,
                  height: 3,
                  borderRadius: "50%",
                  backgroundColor: CODE_TEXT_COLOR,
                  opacity: streamOpacity * 0.5,
                }}
              />
            );
          })}
        </>
      )}

      {/* Dissolving previous code (during regeneration) */}
      {!isFirstGen && localFrame < dissolveEnd && (
        <div
          style={{
            position: "absolute",
            left: INNER_X,
            top: INNER_Y,
            width: INNER_WIDTH,
            height: INNER_HEIGHT,
            overflow: "hidden",
            opacity: dissolveOpacity,
            filter: `blur(${interpolate(localFrame, [0, dissolveEnd], [0, 4], {
              extrapolateRight: "clamp",
            })}px)`,
          }}
        >
          {prevLines.map((line, i) => (
            <div
              key={i}
              style={{
                fontFamily: "'JetBrains Mono', monospace",
                fontSize: 12,
                color: CODE_TEXT_COLOR,
                lineHeight: `${LINE_HEIGHT}px`,
                whiteSpace: "pre",
              }}
            >
              {line}
            </div>
          ))}
        </div>
      )}

      {/* Current generation code lines */}
      <div
        style={{
          position: "absolute",
          left: INNER_X,
          top: INNER_Y,
          width: INNER_WIDTH,
          height: INNER_HEIGHT,
          overflow: "hidden",
        }}
      >
        {codeLines.map((line, i) => {
          const isVisible = i < visibleLines;
          const isLastVisible = i === visibleLines - 1 && visibleLines <= codeLines.length;
          const lineOpacity = isVisible
            ? isLastVisible
              ? 0.6 * lastLineFade
              : 0.6
            : 0;
          // Slight upward settle animation
          const lineY = isVisible
            ? isLastVisible
              ? interpolate(lastLineFade, [0, 1], [8, 0])
              : 0
            : 12;

          return (
            <div
              key={`${genIndex}-${i}`}
              style={{
                fontFamily: "'JetBrains Mono', monospace",
                fontSize: 12,
                color: CODE_TEXT_COLOR,
                opacity: lineOpacity,
                lineHeight: `${LINE_HEIGHT}px`,
                whiteSpace: "pre",
                transform: `translateY(${lineY}px)`,
              }}
            >
              {line}
            </div>
          );
        })}
      </div>

      {/* Shimmer overlay during regeneration */}
      {!isFirstGen && localFrame >= 0 && localFrame < dissolveEnd + 5 && (
        <div
          style={{
            position: "absolute",
            left: CAVITY_X + WALL_THICKNESS,
            top: CAVITY_Y + WALL_THICKNESS,
            width: CAVITY_WIDTH - 2 * WALL_THICKNESS,
            height: CAVITY_HEIGHT - 2 * WALL_THICKNESS,
            background: `radial-gradient(ellipse at 50% ${interpolate(
              localFrame,
              [0, dissolveEnd + 5],
              [30, 70],
              { extrapolateRight: "clamp" }
            )}%, rgba(217, 148, 74, 0.08), transparent)`,
            pointerEvents: "none",
          }}
        />
      )}
    </>
  );
};
