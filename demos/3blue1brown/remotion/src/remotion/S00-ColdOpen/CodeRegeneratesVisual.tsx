import React from "react";
import { AbsoluteFill, interpolate, Easing } from "remotion";
import { COLD_OPEN_FPS } from "./constants";

// ── Old patched code (~30 lines with git-blame history) ─────────────
// Reuses the same code from CodeBlinks for visual continuity.
const OLD_CODE_LINES = [
  { text: 'def parse_user_input(raw_input, context=None, legacy=False):', blame: '#3A4A5A' },
  { text: '    """Parse and validate user input string."""', blame: '#3A4A5A' },
  { text: '    # patched: handle None input (hotfix 2024-01)', blame: '#4A3A3A' },
  { text: '    if raw_input is None:', blame: '#4A3A3A' },
  { text: '        return {"error": "null_input", "value": None}', blame: '#4A3A3A' },
  { text: '', blame: '#3A4A5A' },
  { text: '    try:', blame: '#3A4A5A' },
  { text: '        # workaround for unicode edge case', blame: '#4A4A3A' },
  { text: '        if isinstance(raw_input, bytes):', blame: '#4A4A3A' },
  { text: "            raw_input = raw_input.decode('utf-8', errors='replace')", blame: '#4A4A3A' },
  { text: '', blame: '#4A4A3A' },
  { text: '        result = _inner_parse(raw_input)', blame: '#4A4A3A' },
  { text: '', blame: '#4A4A3A' },
  { text: "        # don't remove -- breaks downstream", blame: '#5A3A3A' },
  { text: '        if legacy:', blame: '#5A3A3A' },
  { text: '            try:', blame: '#5A3A3A' },
  { text: '                result = _apply_legacy_transform(result, context)', blame: '#5A3A3A' },
  { text: '            except (KeyError, AttributeError):', blame: '#5A3A3A' },
  { text: '                result["_legacy_compat"] = True', blame: '#5A3A3A' },
  { text: '', blame: '#5A3A3A' },
  { text: '        # TODO: this whole block needs refactoring', blame: '#5A3A3A' },
  { text: '        if context and context.get("strict_mode"):', blame: '#5A3A3A' },
  { text: '            for key in list(result.keys()):', blame: '#5A3A3A' },
  { text: '                if key.startswith("_"):', blame: '#5A3A3A' },
  { text: '                    if key != "_legacy_compat":', blame: '#5A3A3A' },
  { text: '                        del result[key]', blame: '#5A3A3A' },
  { text: '', blame: '#3A3A4A' },
  { text: '        return result', blame: '#3A3A4A' },
  { text: '', blame: '#3A3A4A' },
  { text: '    except UnicodeDecodeError:', blame: '#3A3A4A' },
  { text: '        return {"error": "encoding", "raw": str(raw_input)[:50]}', blame: '#3A3A4A' },
  { text: '    except Exception as e:  # pylint: disable=broad-except', blame: '#3A3A4A' },
  { text: '        return {"error": "unknown", "detail": str(e)}', blame: '#3A3A4A' },
];

// ── New clean code (~15 lines with syntax highlighting per spec) ─────
interface CodeToken {
  text: string;
  color: string;
}

const NEW_CODE_LINES: CodeToken[][] = [
  [
    { text: 'def', color: '#569CD6' },
    { text: ' ', color: '#C0C0C0' },
    { text: 'parse_user_input', color: '#DCDCAA' },
    { text: '(raw_input: ', color: '#C0C0C0' },
    { text: 'str', color: '#4EC9B0' },
    { text: ' | ', color: '#C0C0C0' },
    { text: 'None', color: '#569CD6' },
    { text: ', context: ', color: '#C0C0C0' },
    { text: 'dict', color: '#4EC9B0' },
    { text: ' | ', color: '#C0C0C0' },
    { text: 'None', color: '#569CD6' },
    { text: ' = ', color: '#C0C0C0' },
    { text: 'None', color: '#569CD6' },
    { text: ') -> ', color: '#C0C0C0' },
    { text: 'dict', color: '#4EC9B0' },
    { text: ':', color: '#C0C0C0' },
  ],
  [
    { text: '    ', color: '#C0C0C0' },
    { text: '"""Parse and validate user input string.', color: '#6A9955' },
  ],
  [{ text: '', color: '#C0C0C0' }],
  [{ text: '    Args:', color: '#6A9955' }],
  [{ text: '        raw_input: The raw input string to parse, or None.', color: '#6A9955' }],
  [{ text: '        context: Optional context dictionary for strict mode filtering.', color: '#6A9955' }],
  [{ text: '', color: '#C0C0C0' }],
  [{ text: '    Returns:', color: '#6A9955' }],
  [{ text: '        Parsed result dictionary, or error dictionary on failure.', color: '#6A9955' }],
  [{ text: '    """', color: '#6A9955' }],
  [
    { text: '    ', color: '#C0C0C0' },
    { text: 'if', color: '#C586C0' },
    { text: ' raw_input ', color: '#C0C0C0' },
    { text: 'is', color: '#C586C0' },
    { text: ' ', color: '#C0C0C0' },
    { text: 'None', color: '#569CD6' },
    { text: ':', color: '#C0C0C0' },
  ],
  [
    { text: '        ', color: '#C0C0C0' },
    { text: 'return', color: '#C586C0' },
    { text: ' {', color: '#C0C0C0' },
    { text: '"error"', color: '#CE9178' },
    { text: ': ', color: '#C0C0C0' },
    { text: '"null_input"', color: '#CE9178' },
    { text: ', ', color: '#C0C0C0' },
    { text: '"value"', color: '#CE9178' },
    { text: ': ', color: '#C0C0C0' },
    { text: 'None', color: '#569CD6' },
    { text: '}', color: '#C0C0C0' },
  ],
  [
    { text: '    text = raw_input ', color: '#C0C0C0' },
    { text: 'if', color: '#C586C0' },
    { text: ' isinstance(raw_input, ', color: '#C0C0C0' },
    { text: 'str', color: '#4EC9B0' },
    { text: ') ', color: '#C0C0C0' },
    { text: 'else', color: '#C586C0' },
    { text: ' raw_input.decode(', color: '#C0C0C0' },
    { text: '"utf-8"', color: '#CE9178' },
    { text: ', errors=', color: '#C0C0C0' },
    { text: '"replace"', color: '#CE9178' },
    { text: ')', color: '#C0C0C0' },
  ],
  [
    { text: '    result = _inner_parse(text)', color: '#C0C0C0' },
  ],
  [
    { text: '    ', color: '#C0C0C0' },
    { text: 'if', color: '#C586C0' },
    { text: ' context ', color: '#C0C0C0' },
    { text: 'and', color: '#C586C0' },
    { text: ' context.get(', color: '#C0C0C0' },
    { text: '"strict_mode"', color: '#CE9178' },
    { text: '):', color: '#C0C0C0' },
  ],
  [
    { text: '        result = {k: v ', color: '#C0C0C0' },
    { text: 'for', color: '#C586C0' },
    { text: ' k, v ', color: '#C0C0C0' },
    { text: 'in', color: '#C586C0' },
    { text: ' result.items() ', color: '#C0C0C0' },
    { text: 'if', color: '#C586C0' },
    { text: ' ', color: '#C0C0C0' },
    { text: 'not', color: '#C586C0' },
    { text: ' k.startswith(', color: '#C0C0C0' },
    { text: '"_"', color: '#CE9178' },
    { text: ')}', color: '#C0C0C0' },
  ],
  [
    { text: '    ', color: '#C0C0C0' },
    { text: 'return', color: '#C586C0' },
    { text: ' result', color: '#C0C0C0' },
  ],
];

// ── Animation phase timing (relative frame offsets within 150-frame sequence) ──
// Scaled from original 450-frame (15s) design to 150 frames (5s) — ratio 1/3.
// Seven phases compressed:
//   Phase 1: Selection flash       frames 0-2     (0-0.07s)
//   Phase 2: Delete sweep          frames 2-10    (0.07-0.33s)
//   Phase 3: Empty beat + cursor   frames 10-22   (0.33-0.73s)
//   Phase 4: Terminal activity     frames 20-22   (0.67-0.73s)
//   Phase 5: Regeneration          frames 22-30   (0.73-1.0s)
//   Phase 6: Terminal completion   frames 30-32   (1.0-1.07s)
//   Phase 7: Hold on clean code    frames 32-150  (1.07-5.0s)

const PHASE = {
  SELECTION_START: 0,
  SELECTION_END: 2,
  DELETE_START: 2,
  DELETE_END: 10,
  EMPTY_START: 10,
  EMPTY_END: 22,
  TERMINAL_APPEAR: 10,    // terminal fades in during empty beat
  TERMINAL_GENERATING: 20, // "Generating from prompt..."
  REGEN_START: 22,
  REGEN_END: 30,
  TERMINAL_DONE: 30,      // "Done. (0.8s) checkmark"
  HOLD_START: 32,
  TITLE_FADE_START: 999,  // disabled — TitleCardVisual handles title separately
};

const START_LINE_NUMBER = 47;
const LINE_HEIGHT = 24; // matches CodeBlinks for visual continuity
const CODE_FONT_SIZE = 16;
const EDITOR_TOP = 36; // top bar height
const CODE_TOP = EDITOR_TOP + 16; // padding below top bar
const GUTTER_WIDTH = 52;
const BLAME_WIDTH = 6;
const CODE_LEFT = GUTTER_WIDTH + BLAME_WIDTH + 22; // gutter + blame + padding

// ── Sub-components ──────────────────────────────────────────────────

const EditorTopBar: React.FC<{ filename: string }> = ({ filename }) => (
  <div
    style={{
      position: "absolute",
      top: 0,
      left: 0,
      right: 0,
      height: EDITOR_TOP,
      background: "#181825",
      borderBottom: "1px solid #2A2A3A",
      display: "flex",
      alignItems: "center",
      paddingLeft: 16,
      zIndex: 10,
    }}
  >
    <div style={{ display: "flex", gap: 6, marginRight: 16 }}>
      <div style={{ width: 10, height: 10, borderRadius: "50%", background: "#FF5F56" }} />
      <div style={{ width: 10, height: 10, borderRadius: "50%", background: "#FFBD2E" }} />
      <div style={{ width: 10, height: 10, borderRadius: "50%", background: "#27C93F" }} />
    </div>
    <div
      style={{
        fontFamily: "'JetBrains Mono', monospace",
        fontSize: 12,
        color: "#8A8A9A",
        background: "#1E1E2E",
        padding: "4px 14px",
        borderRadius: "6px 6px 0 0",
        borderTop: "1px solid #3A3A5A",
        borderLeft: "1px solid #2A2A3A",
        borderRight: "1px solid #2A2A3A",
        marginTop: 2,
      }}
    >
      {filename}
    </div>
  </div>
);

interface LineNumberGutterProps {
  startLine: number;
  lineCount: number;
  blameColors?: string[];
  blameOpacity?: number;
}

const LineNumberGutter: React.FC<LineNumberGutterProps> = ({
  startLine,
  lineCount,
  blameColors,
  blameOpacity = 1,
}) => (
  <div
    style={{
      position: "absolute",
      top: EDITOR_TOP,
      left: 0,
      width: GUTTER_WIDTH,
      height: `calc(100% - ${EDITOR_TOP}px)`,
      background: "#1A1A28",
      display: "flex",
      flexDirection: "column",
      paddingTop: 16,
      borderRight: "1px solid #2A2A3A",
      zIndex: 5,
    }}
  >
    {Array.from({ length: lineCount }, (_, i) => (
      <div
        key={i}
        style={{
          fontFamily: "'JetBrains Mono', monospace",
          fontSize: CODE_FONT_SIZE,
          lineHeight: `${LINE_HEIGHT}px`,
          color: "#555555",
          textAlign: "right",
          paddingRight: 8,
          userSelect: "none",
        }}
      >
        {startLine + i}
      </div>
    ))}
  </div>
);

const BlameGutter: React.FC<{
  colors: string[];
  opacity: number;
}> = ({ colors, opacity }) => (
  <div
    style={{
      position: "absolute",
      top: EDITOR_TOP,
      left: GUTTER_WIDTH,
      width: BLAME_WIDTH,
      height: `calc(100% - ${EDITOR_TOP}px)`,
      paddingTop: 16,
      zIndex: 5,
      opacity,
    }}
  >
    {colors.map((color, i) => (
      <div
        key={i}
        style={{
          height: LINE_HEIGHT,
          background: color,
          width: "100%",
          opacity: 0.7,
        }}
      />
    ))}
  </div>
);

const WarningIcon: React.FC<{
  lineIndex: number;
  opacity: number;
}> = ({ lineIndex, opacity }) => (
  <div
    style={{
      position: "absolute",
      top: CODE_TOP + lineIndex * LINE_HEIGHT,
      left: GUTTER_WIDTH + BLAME_WIDTH + 2,
      width: 16,
      height: 16,
      display: "flex",
      alignItems: "center",
      justifyContent: "center",
      zIndex: 6,
      opacity,
    }}
  >
    <svg width="14" height="14" viewBox="0 0 14 14" fill="none">
      <path
        d="M7 1L13 13H1L7 1Z"
        fill="#E8A317"
        fillOpacity={0.7}
        stroke="#E8A317"
        strokeWidth={0.5}
      />
      <text
        x="7"
        y="11"
        textAnchor="middle"
        fill="#1E1E2E"
        fontSize="8"
        fontWeight="bold"
        fontFamily="sans-serif"
      >
        !
      </text>
    </svg>
  </div>
);

const Scrollbar: React.FC = () => (
  <div
    style={{
      position: "absolute",
      top: EDITOR_TOP,
      right: 0,
      width: 10,
      height: `calc(100% - ${EDITOR_TOP}px)`,
      background: "#1A1A28",
      zIndex: 5,
    }}
  >
    <div
      style={{
        position: "absolute",
        top: 40,
        left: 2,
        width: 6,
        height: 120,
        background: "#3A3A4A",
        borderRadius: 3,
        opacity: 0.5,
      }}
    />
  </div>
);

const BlinkingCursor: React.FC<{
  lineIndex: number;
  column: number;
  visible: boolean;
}> = ({ lineIndex, column, visible }) => (
  <div
    style={{
      position: "absolute",
      top: CODE_TOP + lineIndex * LINE_HEIGHT,
      left: CODE_LEFT + column * 9.6, // approximate monospace char width at 16px
      width: 9,
      height: 20,
      background: "#FFFFFF",
      opacity: visible ? 0.9 : 0,
      zIndex: 7,
    }}
  />
);

interface TerminalSnippetProps {
  localFrame: number;
}

const TerminalSnippet: React.FC<TerminalSnippetProps> = ({ localFrame }) => {
  const containerOpacity = interpolate(
    localFrame,
    [PHASE.TERMINAL_APPEAR, PHASE.TERMINAL_APPEAR + 15],
    [0, 1],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp", easing: Easing.out(Easing.cubic) }
  );

  const showGenerating = localFrame >= PHASE.TERMINAL_GENERATING;
  const showDone = localFrame >= PHASE.TERMINAL_DONE;

  return (
    <div
      style={{
        position: "absolute",
        bottom: 40,
        right: 40,
        opacity: containerOpacity,
        width: 310,
        padding: "10px 14px",
        backgroundColor: "#252535",
        borderRadius: 6,
        border: "1px solid #3a3a4a",
        fontFamily: "'JetBrains Mono', monospace",
        fontSize: 12,
        lineHeight: 1.8,
        zIndex: 30,
      }}
    >
      <div style={{ color: "#E0E0E0" }}>$ pdd generate user_parser</div>
      {showGenerating && (
        <div style={{ color: "#888" }}>Generating from prompt...</div>
      )}
      {showDone && (
        <div style={{ color: "#5AAA6E" }}>
          Done. (0.8s) {"\u2713"}
        </div>
      )}
    </div>
  );
};

// ── Main component ──────────────────────────────────────────────────

interface CodeRegeneratesVisualProps {
  localFrame: number;
  totalFrames: number;
}

export const CodeRegeneratesVisual: React.FC<CodeRegeneratesVisualProps> = ({
  localFrame,
  totalFrames,
}) => {
  const fps = COLD_OPEN_FPS;

  // ── Phase 1: Selection flash (blue highlight over all old code lines) ──
  // Opacity 0 -> 0.4 -> 0. Midpoint at halfway between start and end.
  const selectionMid = (PHASE.SELECTION_START + PHASE.SELECTION_END) / 2;
  const selectionOpacity = interpolate(
    localFrame,
    [PHASE.SELECTION_START, selectionMid, PHASE.SELECTION_END],
    [0, 0.4, 0],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
  );

  // ── Phase 2: Delete sweep (staggered per line, top-first) ──
  // Stagger scaled to fit within delete phase (max stagger < phase length / line count)
  const deletePhaseLength = PHASE.DELETE_END - PHASE.DELETE_START;
  const lineStagger = deletePhaseLength / (OLD_CODE_LINES.length + 1);

  // Blame gutter + warning icon fade with deletion
  const blameOpacity = interpolate(
    localFrame,
    [PHASE.DELETE_START, PHASE.DELETE_END],
    [1, 0],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
  );
  const warningOpacity = blameOpacity;

  // ── Phase 3: Cursor blink (~0.53s cycle) ──
  const blinkCycleFrames = Math.round(0.53 * fps); // ~16 frames
  const halfCycle = Math.round(blinkCycleFrames / 2);
  const inEmptyBeat = localFrame >= PHASE.EMPTY_START && localFrame < PHASE.REGEN_START;
  const postRegen = localFrame >= PHASE.REGEN_END;
  const showCursor = inEmptyBeat || postRegen;
  const cursorVisible =
    showCursor &&
    Math.floor((localFrame - PHASE.EMPTY_START) / halfCycle) % 2 === 0;

  // ── Phase 5: Regeneration (line-by-line reveal) ──
  const regenLength = PHASE.REGEN_END - PHASE.REGEN_START; // 24 frames
  const framesPerLine = regenLength / NEW_CODE_LINES.length; // ~1.33 frames/line

  // ── Phase 7: Title crossfade in final portion ──
  const titleOpacity = interpolate(
    localFrame,
    [PHASE.TITLE_FADE_START, PHASE.TITLE_FADE_START + 60],
    [0, 1],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp", easing: Easing.out(Easing.cubic) }
  );

  const titleY = interpolate(
    localFrame,
    [PHASE.TITLE_FADE_START, PHASE.TITLE_FADE_START + 60],
    [20, 0],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp", easing: Easing.out(Easing.cubic) }
  );

  // Code dims as title appears
  const codeDim = interpolate(
    localFrame,
    [PHASE.TITLE_FADE_START, PHASE.TITLE_FADE_START + 60],
    [1, 0.25],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
  );

  const deletionComplete = localFrame >= PHASE.DELETE_END;
  const regenStarted = localFrame >= PHASE.REGEN_START;

  // Line count for gutter: show old count during deletion, empty during hold,
  // then incrementally show new lines during regeneration
  const visibleNewLines = regenStarted
    ? Math.min(
        NEW_CODE_LINES.length,
        Math.ceil(
          ((localFrame - PHASE.REGEN_START) / regenLength) * NEW_CODE_LINES.length
        )
      )
    : 0;
  const gutterLineCount = deletionComplete
    ? visibleNewLines > 0
      ? visibleNewLines
      : 0
    : OLD_CODE_LINES.length;

  // Old code blame colors
  const oldBlameColors = OLD_CODE_LINES.map((l) => l.blame);

  // TODO comment line index (for warning icon)
  const warningLineIndex = OLD_CODE_LINES.findIndex((l) =>
    l.text.includes("TODO")
  );

  return (
    <AbsoluteFill style={{ backgroundColor: "#1E1E2E" }}>
      {/* ── Editor chrome: filename bar ── */}
      <EditorTopBar filename="user_parser.py" />

      {/* ── Scrollbar ── */}
      <Scrollbar />

      {/* ── Line number gutter ── */}
      {gutterLineCount > 0 && (
        <LineNumberGutter
          startLine={START_LINE_NUMBER}
          lineCount={gutterLineCount}
        />
      )}

      {/* ── Empty gutter during empty beat (line numbers gone, just background) ── */}
      {deletionComplete && !regenStarted && (
        <div
          style={{
            position: "absolute",
            top: EDITOR_TOP,
            left: 0,
            width: GUTTER_WIDTH,
            height: `calc(100% - ${EDITOR_TOP}px)`,
            background: "#1A1A28",
            borderRight: "1px solid #2A2A3A",
            zIndex: 5,
          }}
        />
      )}

      {/* ── Git blame gutter (old code only, fades with deletion) ── */}
      {!deletionComplete && (
        <BlameGutter colors={oldBlameColors} opacity={blameOpacity} />
      )}

      {/* ── Warning icon on TODO line ── */}
      {!deletionComplete && warningLineIndex >= 0 && (
        <WarningIcon lineIndex={warningLineIndex} opacity={warningOpacity} />
      )}

      {/* ── Old patched code (with selection flash + staggered upward deletion) ── */}
      {!deletionComplete && (
        <div
          style={{
            position: "absolute",
            top: CODE_TOP,
            left: CODE_LEFT,
            right: 14,
            overflow: "hidden",
          }}
        >
          {OLD_CODE_LINES.map((line, i) => {
            // Per-line deletion: top lines go first, 0.5-frame stagger
            const lineDeleteStart = PHASE.DELETE_START + i * lineStagger;
            const lineDeleteEnd = Math.min(
              lineDeleteStart + deletePhaseLength * 0.5,
              PHASE.DELETE_END
            );
            const lineOpacity = interpolate(
              localFrame,
              [lineDeleteStart, lineDeleteEnd],
              [1, 0],
              {
                extrapolateLeft: "clamp",
                extrapolateRight: "clamp",
                easing: Easing.in(Easing.quad),
              }
            );
            const lineTranslateY = interpolate(
              localFrame,
              [lineDeleteStart, lineDeleteEnd],
              [0, -20],
              {
                extrapolateLeft: "clamp",
                extrapolateRight: "clamp",
                easing: Easing.in(Easing.quad),
              }
            );

            // Determine code color based on line type (syntax highlighting)
            const isComment = line.text.trimStart().startsWith("#");
            const isDocstring = line.text.trimStart().startsWith('"""');
            const isEmpty = line.text.trim() === "";
            let textColor = "#C0C0C0";
            if (isComment) textColor = "#6A7A5A";
            else if (isDocstring) textColor = "#CE9178";

            return (
              <div
                key={i}
                style={{
                  height: LINE_HEIGHT,
                  fontFamily: "'JetBrains Mono', monospace",
                  fontSize: CODE_FONT_SIZE,
                  color: textColor,
                  lineHeight: `${LINE_HEIGHT}px`,
                  whiteSpace: "pre",
                  opacity: lineOpacity,
                  transform: `translateY(${lineTranslateY}px)`,
                  position: "relative",
                }}
              >
                {isEmpty ? " " : line.text}
                {/* Selection flash overlay (Phase 1) */}
                {localFrame < PHASE.SELECTION_END + 2 && (
                  <div
                    style={{
                      position: "absolute",
                      top: 0,
                      left: -CODE_LEFT,
                      right: -14,
                      bottom: 0,
                      background: "#264F78",
                      opacity: selectionOpacity,
                      pointerEvents: "none",
                    }}
                  />
                )}
              </div>
            );
          })}
        </div>
      )}

      {/* ── Empty editor cursor (during empty beat: frames 30-66) ── */}
      {inEmptyBeat && (
        <BlinkingCursor lineIndex={0} column={0} visible={cursorVisible} />
      )}

      {/* ── New clean code (line-by-line regeneration with char reveal) ── */}
      {regenStarted && (
        <div
          style={{
            position: "absolute",
            top: CODE_TOP,
            left: CODE_LEFT,
            right: 14,
            overflow: "hidden",
            opacity: codeDim,
          }}
        >
          {NEW_CODE_LINES.map((tokens, lineIndex) => {
            const lineStart = PHASE.REGEN_START + lineIndex * framesPerLine;
            const lineEnd = lineStart + framesPerLine;

            // Line visibility: appears at lineStart
            if (localFrame < lineStart) return null;

            // Character reveal progress within this line (easeOutCubic per line)
            const charReveal = interpolate(
              localFrame,
              [lineStart, lineEnd],
              [0, 1],
              {
                extrapolateLeft: "clamp",
                extrapolateRight: "clamp",
                easing: Easing.out(Easing.cubic),
              }
            );

            // Total character count for this line
            const totalChars = tokens.reduce((sum, t) => sum + t.text.length, 0);
            const visibleChars = Math.ceil(charReveal * totalChars);

            let charsRendered = 0;

            return (
              <div
                key={lineIndex}
                style={{
                  height: LINE_HEIGHT,
                  fontFamily: "'JetBrains Mono', monospace",
                  fontSize: CODE_FONT_SIZE,
                  lineHeight: `${LINE_HEIGHT}px`,
                  whiteSpace: "pre",
                  position: "relative",
                }}
              >
                {tokens.map((token, tIdx) => {
                  const tokenStart = charsRendered;
                  charsRendered += token.text.length;

                  if (tokenStart >= visibleChars) return null;

                  const visibleLen = Math.min(
                    token.text.length,
                    visibleChars - tokenStart
                  );
                  const visibleText = token.text.substring(0, visibleLen);

                  return (
                    <span key={tIdx} style={{ color: token.color }}>
                      {visibleText}
                    </span>
                  );
                })}
                {/* Leading edge blur effect (subtle, per spec) */}
                {charReveal < 1 && totalChars > 0 && (
                  <span
                    style={{
                      display: "inline-block",
                      width: 8,
                      height: 18,
                      background:
                        "linear-gradient(90deg, rgba(192,192,192,0.4), transparent)",
                      filter: "blur(2px)",
                      verticalAlign: "middle",
                    }}
                  />
                )}
              </div>
            );
          })}
        </div>
      )}

      {/* ── Post-regeneration cursor (blinks at end of new function) ── */}
      {postRegen && (
        <BlinkingCursor
          lineIndex={NEW_CODE_LINES.length}
          column={0}
          visible={cursorVisible}
        />
      )}

      {/* ── Terminal snippet (bottom-right, per spec's PDD Command Placement) ── */}
      <TerminalSnippet localFrame={localFrame} />

      {/* ── Title overlay crossfade ("Prompt-Driven Development") ── */}
      {localFrame >= PHASE.TITLE_FADE_START && (
        <div
          style={{
            position: "absolute",
            top: 0,
            left: 0,
            right: 0,
            bottom: 0,
            display: "flex",
            alignItems: "center",
            justifyContent: "center",
            opacity: titleOpacity,
            zIndex: 50,
          }}
        >
          <h1
            style={{
              transform: `translateY(${titleY}px)`,
              fontFamily: "Inter, system-ui, sans-serif",
              fontSize: 72,
              fontWeight: 600,
              color: "#F8F4F0",
              letterSpacing: "0.02em",
              margin: 0,
              textShadow:
                "0 0 60px rgba(74, 144, 217, 0.15), 0 0 40px rgba(0,0,0,0.8)",
            }}
          >
            Prompt-Driven Development
          </h1>
        </div>
      )}
    </AbsoluteFill>
  );
};
