import React from "react";
import {
  AbsoluteFill,
  useCurrentFrame,
  useVideoConfig,
  interpolate,
  Easing,
  Sequence,
} from "remotion";
import {
  BG_COLOR,
  TEXT_COLOR,
  AMBER_ACCENT,
  GREEN_ACCENT,
  DISSOLVE_END,
  PROMPT_FADE_START,
  TEST_FADE_START,
  LABEL_START,
  LABEL_CHAR_DELAY,
  UNDERLINE_DELAY,
  UNDERLINE_DURATION,
  BOTTOM_LABEL_SIZE,
  BOTTOM_LABEL_TEXT,
  DIFF_LINES,
  CANVAS_WIDTH,
} from "./constants";
import { BlueprintGrid } from "./BlueprintGrid";
import { PromptDocument } from "./PromptDocument";
import { TestSuitePanel } from "./TestSuitePanel";

// ── Inline sub-components (small, used only here) ───────────────────────────

/**
 * Fake code diff that scatters/dissolves in the opening frames.
 */
const CodeDiffDissolve: React.FC<{ frame: number }> = ({ frame }) => {
  const opacity = interpolate(frame, [0, DISSOLVE_END], [0.8, 0], {
    extrapolateLeft: "clamp",
    extrapolateRight: "clamp",
    easing: Easing.in(Easing.quad),
  });

  // Scatter effect: lines drift outward as they fade
  const scatter = interpolate(frame, [0, DISSOLVE_END], [0, 30], {
    extrapolateLeft: "clamp",
    extrapolateRight: "clamp",
    easing: Easing.in(Easing.quad),
  });

  if (frame >= DISSOLVE_END) return null;

  return (
    <div
      style={{
        position: "absolute",
        left: 360,
        top: 180,
        width: 1200,
        opacity,
      }}
    >
      {DIFF_LINES.map((line, i) => {
        const isAdd = line.startsWith("+");
        const isRemove = line.startsWith("-");
        // Each line scatters in a slightly different direction
        const angle = ((i * 47) % 360) * (Math.PI / 180);
        const dx = Math.cos(angle) * scatter;
        const dy = Math.sin(angle) * scatter * 0.6;

        return (
          <div
            key={i}
            style={{
              fontFamily: "'JetBrains Mono', monospace",
              fontSize: 15,
              fontWeight: 400,
              color: isAdd ? "#5AAA6E" : isRemove ? "#E05252" : "#94A3B8",
              lineHeight: "28px",
              whiteSpace: "nowrap",
              transform: `translate(${dx}px, ${dy}px)`,
            }}
          >
            {line || "\u00A0"}
          </div>
        );
      })}
    </div>
  );
};

/**
 * Typewriter label with centered underline.
 */
const BottomLabel: React.FC<{ localFrame: number }> = ({ localFrame }) => {
  const totalChars = BOTTOM_LABEL_TEXT.length;
  const charsVisible = Math.min(
    totalChars,
    Math.floor(localFrame / LABEL_CHAR_DELAY)
  );
  const displayedText = BOTTOM_LABEL_TEXT.slice(0, charsVisible);

  // Cursor blink
  const showCursor = charsVisible < totalChars && localFrame % 8 < 5;

  // Underline draws from center after label is typed
  const underlineFrame = localFrame - UNDERLINE_DELAY;
  const underlineProgress =
    underlineFrame > 0
      ? interpolate(
          underlineFrame,
          [0, UNDERLINE_DURATION],
          [0, 1],
          {
            extrapolateLeft: "clamp",
            extrapolateRight: "clamp",
            easing: Easing.inOut(Easing.cubic),
          }
        )
      : 0;

  const underlineWidth = 400;

  return (
    <div
      style={{
        position: "absolute",
        left: 0,
        top: 850,
        width: CANVAS_WIDTH,
        display: "flex",
        flexDirection: "column",
        alignItems: "center",
      }}
    >
      {/* Label text */}
      <div
        style={{
          fontFamily: "Inter, sans-serif",
          fontSize: BOTTOM_LABEL_SIZE,
          fontWeight: 700,
          color: TEXT_COLOR,
          textAlign: "center",
          minHeight: 36,
          opacity: 0.95,
        }}
      >
        {displayedText}
        {showCursor && (
          <span style={{ color: AMBER_ACCENT, fontWeight: 400 }}>|</span>
        )}
      </div>

      {/* Underline from center */}
      {underlineProgress > 0 && (
        <div
          style={{
            marginTop: 8,
            width: underlineWidth,
            height: 2,
            position: "relative",
          }}
        >
          <div
            style={{
              position: "absolute",
              left: `${50 - (underlineProgress * 50)}%`,
              width: `${underlineProgress * 100}%`,
              height: 2,
              backgroundColor: GREEN_ACCENT,
              opacity: 0.9,
              borderRadius: 1,
            }}
          />
        </div>
      )}
    </div>
  );
};

// ── Main Component ──────────────────────────────────────────────────────────

export const defaultPart2ParadigmShift17ReviewSpecVerifyOutputProps = {};

export const Part2ParadigmShift17ReviewSpecVerifyOutput: React.FC = () => {
  const frame = useCurrentFrame();
  const { fps } = useVideoConfig();

  return (
    <AbsoluteFill style={{ backgroundColor: BG_COLOR }}>
      {/* Blueprint grid background */}
      <BlueprintGrid />

      {/* Phase 1: Code diff dissolve (frames 0–45) */}
      <CodeDiffDissolve frame={frame} />

      {/* Phase 2: Prompt document (frames 45+) */}
      <Sequence from={PROMPT_FADE_START} layout="none">
        <PromptDocument
          localFrame={Math.max(0, frame - PROMPT_FADE_START)}
          globalFrame={frame}
        />
      </Sequence>

      {/* Phase 3: Test suite (frames 105+) */}
      <Sequence from={TEST_FADE_START} layout="none">
        <TestSuitePanel
          localFrame={Math.max(0, frame - TEST_FADE_START)}
          globalFrame={frame}
          fps={fps}
        />
      </Sequence>

      {/* Phase 4: Bottom label with typewriter + underline (frames 180+) */}
      <Sequence from={LABEL_START} layout="none">
        <BottomLabel localFrame={Math.max(0, frame - LABEL_START)} />
      </Sequence>

      {/* Morph shimmer overlay (frames 240–330): subtle full-screen glow pulse */}
      {frame >= 240 && frame <= 330 && (
        <AbsoluteFill
          style={{
            background: `radial-gradient(ellipse at 50% 50%, ${AMBER_ACCENT}08 0%, transparent 70%)`,
            opacity: interpolate(
              frame,
              [240, 270, 300, 330],
              [0, 0.3, 0.3, 0],
              { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
            ),
            pointerEvents: "none",
          }}
        />
      )}
    </AbsoluteFill>
  );
};

export default Part2ParadigmShift17ReviewSpecVerifyOutput;
