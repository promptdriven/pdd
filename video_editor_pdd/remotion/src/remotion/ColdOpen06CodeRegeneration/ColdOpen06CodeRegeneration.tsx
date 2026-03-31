import React from "react";
import {
  AbsoluteFill,
  useCurrentFrame,
  interpolate,
  Easing,
} from "remotion";
import CodeLine from "./CodeLine";
import SelectionHighlight from "./SelectionHighlight";
import TerminalOverlay from "./TerminalOverlay";
import {
  BG_COLOR,
  GUTTER_BG,
  GUTTER_WIDTH,
  CODE_TOP_PADDING,
  CODE_LINE_HEIGHT,
  CURSOR_COLOR,
  CANVAS_WIDTH,
  PATCHED_CODE_LINES,
  CLEAN_CODE_LINES,
  OLD_LINE_COUNT,
  PHASE_SHOW_OLD_END,
  PHASE_SELECT_START,
  PHASE_SELECT_END,
  PHASE_DELETE_START,
  PHASE_DELETE_END,
  PHASE_EMPTY_END,
  PHASE_REGEN_START,
  PHASE_REGEN_END,
  PHASE_TERMINAL_START,
  FPS,
} from "./constants";

// ── Editor chrome ──────────────────────────────────────────────

const EditorTitleBar: React.FC = () => (
  <div
    style={{
      position: "absolute",
      top: 0,
      left: 0,
      width: CANVAS_WIDTH,
      height: CODE_TOP_PADDING,
      backgroundColor: "#181825",
      display: "flex",
      alignItems: "center",
      paddingLeft: 16,
      fontFamily: "'JetBrains Mono', monospace",
      fontSize: 13,
      color: "#CDD6F4",
      borderBottom: "1px solid #313244",
      zIndex: 10,
    }}
  >
    {/* Traffic lights */}
    <div style={{ display: "flex", gap: 8, marginRight: 16 }}>
      <div
        style={{
          width: 12,
          height: 12,
          borderRadius: "50%",
          backgroundColor: "#F38BA8",
        }}
      />
      <div
        style={{
          width: 12,
          height: 12,
          borderRadius: "50%",
          backgroundColor: "#F9E2AF",
        }}
      />
      <div
        style={{
          width: 12,
          height: 12,
          borderRadius: "50%",
          backgroundColor: "#A6E3A1",
        }}
      />
    </div>
    <span>process_order.py</span>
  </div>
);

// ── Blinking cursor ────────────────────────────────────────────

const BlinkingCursor: React.FC<{ lineIndex: number }> = ({ lineIndex }) => {
  const frame = useCurrentFrame();
  const visible = Math.floor(frame / 8) % 2 === 0;

  return (
    <div
      style={{
        position: "absolute",
        top: CODE_TOP_PADDING + lineIndex * CODE_LINE_HEIGHT,
        left: GUTTER_WIDTH + 16,
        width: 2,
        height: CODE_LINE_HEIGHT - 4,
        backgroundColor: CURSOR_COLOR,
        opacity: visible ? 1 : 0,
      }}
    />
  );
};

// ── Main component ─────────────────────────────────────────────

export const defaultColdOpen06CodeRegenerationProps = {};

export const ColdOpen06CodeRegeneration: React.FC = () => {
  const frame = useCurrentFrame();

  // ── Phase calculations ─────────────────────────────────

  // Phase 1: Old code visible (frame 0-25, fades with selection)
  const showOldCode = frame < PHASE_DELETE_END;

  // Phase 2: Selection sweep (frame 5-25)
  const selectionProgress =
    frame >= PHASE_SELECT_START && frame < PHASE_SELECT_END
      ? interpolate(
          frame,
          [PHASE_SELECT_START, PHASE_SELECT_END],
          [0, 1],
          { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
        )
      : frame >= PHASE_SELECT_END && frame < PHASE_DELETE_END
        ? 1
        : 0;

  // Phase 4: Empty beat (frame 35-45) — just line numbers + cursor
  const isEmptyPhase = frame >= PHASE_DELETE_END && frame < PHASE_EMPTY_END;

  // Phase 5: Regeneration (frame 45-120)
  // ~3 lines per second = 3/30 = 0.1 lines per frame
  const regenLinesVisible =
    frame >= PHASE_REGEN_START
      ? Math.min(
          CLEAN_CODE_LINES.length,
          Math.floor(((frame - PHASE_REGEN_START) / FPS) * 3)
        )
      : 0;

  const regenDone = frame >= PHASE_REGEN_END;

  // Phase 6: Terminal overlay (frame 120-150)
  const terminalOpacity =
    frame >= PHASE_TERMINAL_START
      ? interpolate(
          frame,
          [PHASE_TERMINAL_START, PHASE_TERMINAL_START + 15],
          [0, 1],
          {
            easing: Easing.out(Easing.quad),
            extrapolateLeft: "clamp",
            extrapolateRight: "clamp",
          }
        )
      : 0;

  // ── Compute old code opacity during delete ────────────
  const oldCodeOpacity = showOldCode
    ? frame < PHASE_SHOW_OLD_END
      ? 0.85
      : frame < PHASE_DELETE_START
        ? 0.85
        : interpolate(
            frame,
            [PHASE_DELETE_START, PHASE_DELETE_END],
            [0.85, 0],
            {
              easing: Easing.in(Easing.cubic),
              extrapolateLeft: "clamp",
              extrapolateRight: "clamp",
            }
          )
    : 0;

  // Old code collapses upward during delete
  const oldCodeTranslateY =
    frame >= PHASE_DELETE_START && frame < PHASE_DELETE_END
      ? interpolate(
          frame,
          [PHASE_DELETE_START, PHASE_DELETE_END],
          [0, -OLD_LINE_COUNT * CODE_LINE_HEIGHT * 0.5],
          {
            easing: Easing.in(Easing.cubic),
            extrapolateLeft: "clamp",
            extrapolateRight: "clamp",
          }
        )
      : 0;

  // Show empty line numbers during the empty phase and regen
  const showEmptyGutter =
    isEmptyPhase || frame >= PHASE_REGEN_START;

  return (
    <AbsoluteFill
      style={{
        backgroundColor: BG_COLOR,
        overflow: "hidden",
      }}
    >
      {/* Editor title bar */}
      <EditorTitleBar />

      {/* Gutter background (always visible) */}
      <div
        style={{
          position: "absolute",
          top: CODE_TOP_PADDING,
          left: 0,
          width: GUTTER_WIDTH,
          height: "100%",
          backgroundColor: GUTTER_BG,
        }}
      />

      {/* ── Old patched code ─────────────────────────────── */}
      {showOldCode && (
        <div
          style={{
            position: "absolute",
            top: CODE_TOP_PADDING,
            left: 0,
            width: CANVAS_WIDTH,
            opacity: oldCodeOpacity,
            transform: `translateY(${oldCodeTranslateY}px)`,
          }}
        >
          {PATCHED_CODE_LINES.map((line, i) => (
            <CodeLine key={`old-${i}`} lineNumber={i + 1} text={line} />
          ))}
        </div>
      )}

      {/* ── Selection highlight ──────────────────────────── */}
      {selectionProgress > 0 && frame < PHASE_DELETE_END && (
        <SelectionHighlight
          totalLines={OLD_LINE_COUNT}
          progress={selectionProgress}
        />
      )}

      {/* ── Empty phase: line numbers + cursor ───────────── */}
      {showEmptyGutter && !showOldCode && (
        <div
          style={{
            position: "absolute",
            top: CODE_TOP_PADDING,
            left: 0,
            width: GUTTER_WIDTH,
          }}
        >
          {Array.from(
            { length: regenDone ? CLEAN_CODE_LINES.length : Math.max(1, regenLinesVisible) },
            (_, i) => (
              <div
                key={`ln-${i}`}
                style={{
                  height: CODE_LINE_HEIGHT,
                  display: "flex",
                  alignItems: "center",
                  justifyContent: "flex-end",
                  paddingRight: 12,
                  fontFamily: "'JetBrains Mono', monospace",
                  fontSize: 14,
                  color: "#6C7086",
                }}
              >
                {i + 1}
              </div>
            )
          )}
        </div>
      )}

      {/* ── Blinking cursor during empty beat ────────────── */}
      {isEmptyPhase && <BlinkingCursor lineIndex={0} />}

      {/* ── Regenerated code (typewriter) ─────────────────── */}
      {frame >= PHASE_REGEN_START && regenLinesVisible > 0 && (
        <div
          style={{
            position: "absolute",
            top: CODE_TOP_PADDING,
            left: 0,
            width: CANVAS_WIDTH,
          }}
        >
          {CLEAN_CODE_LINES.slice(0, regenLinesVisible).map((line, i) => (
            <CodeLine key={`new-${i}`} lineNumber={i + 1} text={line} />
          ))}
        </div>
      )}

      {/* Cursor at end of last regen line */}
      {frame >= PHASE_REGEN_START &&
        regenLinesVisible > 0 &&
        !regenDone && (
          <BlinkingCursor lineIndex={regenLinesVisible - 1} />
        )}

      {/* ── Terminal overlay ─────────────────────────────── */}
      {terminalOpacity > 0 && (
        <TerminalOverlay
          command="pdd generate process_order"
          opacity={terminalOpacity}
        />
      )}
    </AbsoluteFill>
  );
};

export default ColdOpen06CodeRegeneration;
