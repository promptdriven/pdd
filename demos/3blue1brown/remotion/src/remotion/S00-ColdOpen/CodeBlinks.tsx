import React from "react";
import {
  AbsoluteFill,
  interpolate,
  useCurrentFrame,
  useVideoConfig,
  Easing,
} from "remotion";

// ── Code lines with patch-era color coding ──────────────────────────
// Each line has text content and a color representing its "era"
const ORIGINAL = "#C0C0C0";
const PATCH_1 = "#C4A8A0"; // hotfix 2024-01
const PATCH_2 = "#C89890"; // unicode fix
const PATCH_3 = "#CC8880"; // refactor-todo era
const COMMENT_COLOR = "#6A7A5A"; // muted green for comments
const STRING_COLOR = "#CE9178"; // warm orange for strings
const KEYWORD_COLOR = "#569CD6"; // blue for keywords
const FUNCTION_COLOR = "#DCDCAA"; // yellow for function names

interface CodeLine {
  text: string;
  color: string;
  blameColor: string;
  indent: number;
}

const CODE_LINES: CodeLine[] = [
  { text: 'def parse_user_input(raw_input, context=None, legacy=False):', color: ORIGINAL, blameColor: '#3A4A5A', indent: 0 },
  { text: '    """Parse and validate user input string."""', color: ORIGINAL, blameColor: '#3A4A5A', indent: 0 },
  { text: '    # patched: handle None input (hotfix 2024-01)', color: PATCH_1, blameColor: '#4A3A3A', indent: 0 },
  { text: '    if raw_input is None:', color: PATCH_1, blameColor: '#4A3A3A', indent: 0 },
  { text: '        return {"error": "null_input", "value": None}', color: PATCH_1, blameColor: '#4A3A3A', indent: 0 },
  { text: '', color: ORIGINAL, blameColor: '#3A4A5A', indent: 0 },
  { text: '    try:', color: ORIGINAL, blameColor: '#3A4A5A', indent: 0 },
  { text: '        # workaround for unicode edge case', color: PATCH_2, blameColor: '#4A4A3A', indent: 0 },
  { text: '        if isinstance(raw_input, bytes):', color: PATCH_2, blameColor: '#4A4A3A', indent: 0 },
  { text: "            raw_input = raw_input.decode('utf-8', errors='replace')", color: PATCH_2, blameColor: '#4A4A3A', indent: 0 },
  { text: '', color: ORIGINAL, blameColor: '#4A4A3A', indent: 0 },
  { text: '        result = _inner_parse(raw_input)', color: ORIGINAL, blameColor: '#4A4A3A', indent: 0 },
  { text: '', color: ORIGINAL, blameColor: '#4A4A3A', indent: 0 },
  { text: "        # don't remove -- breaks downstream", color: PATCH_3, blameColor: '#5A3A3A', indent: 0 },
  { text: '        if legacy:', color: PATCH_3, blameColor: '#5A3A3A', indent: 0 },
  { text: '            try:', color: PATCH_3, blameColor: '#5A3A3A', indent: 0 },
  { text: '                result = _apply_legacy_transform(result, context)', color: PATCH_3, blameColor: '#5A3A3A', indent: 0 },
  { text: '            except (KeyError, AttributeError):', color: PATCH_3, blameColor: '#5A3A3A', indent: 0 },
  { text: '                result["_legacy_compat"] = True', color: PATCH_3, blameColor: '#5A3A3A', indent: 0 },
  { text: '', color: ORIGINAL, blameColor: '#5A3A3A', indent: 0 },
  { text: '        # TODO: this whole block needs refactoring', color: PATCH_3, blameColor: '#5A3A3A', indent: 0 },
  { text: "        if context and context.get(\"strict_mode\"):", color: PATCH_3, blameColor: '#5A3A3A', indent: 0 },
  { text: '            for key in list(result.keys()):', color: PATCH_3, blameColor: '#5A3A3A', indent: 0 },
  { text: '                if key.startswith("_"):', color: PATCH_3, blameColor: '#5A3A3A', indent: 0 },
  { text: '                    if key != "_legacy_compat":', color: PATCH_3, blameColor: '#5A3A3A', indent: 0 },
  { text: '                        del result[key]', color: PATCH_3, blameColor: '#5A3A3A', indent: 0 },
  { text: '', color: ORIGINAL, blameColor: '#3A3A4A', indent: 0 },
  { text: '        return result', color: ORIGINAL, blameColor: '#3A3A4A', indent: 0 },
  { text: '', color: ORIGINAL, blameColor: '#3A3A4A', indent: 0 },
  { text: '    except UnicodeDecodeError:', color: PATCH_2, blameColor: '#3A3A4A', indent: 0 },
  { text: '        return {"error": "encoding", "raw": str(raw_input)[:50]}', color: PATCH_2, blameColor: '#3A3A4A', indent: 0 },
  { text: '    except Exception as e:  # pylint: disable=broad-except', color: ORIGINAL, blameColor: '#3A3A4A', indent: 0 },
  { text: '        return {"error": "unknown", "detail": str(e)}', color: ORIGINAL, blameColor: '#3A3A4A', indent: 0 },
];

const START_LINE_NUMBER = 47;
const CURSOR_LINE = 21; // 0-indexed into CODE_LINES (the TODO comment line)
const WARNING_LINE = 20; // line with the TODO comment

// ── Sub-components ──────────────────────────────────────────────────

const EditorTopBar: React.FC<{ filename: string }> = ({ filename }) => (
  <div
    style={{
      position: "absolute",
      top: 0,
      left: 0,
      right: 0,
      height: 36,
      background: "#181825",
      borderBottom: "1px solid #2A2A3A",
      display: "flex",
      alignItems: "center",
      paddingLeft: 16,
      zIndex: 10,
    }}
  >
    {/* Window dots */}
    <div style={{ display: "flex", gap: 6, marginRight: 16 }}>
      <div style={{ width: 10, height: 10, borderRadius: "50%", background: "#FF5F56" }} />
      <div style={{ width: 10, height: 10, borderRadius: "50%", background: "#FFBD2E" }} />
      <div style={{ width: 10, height: 10, borderRadius: "50%", background: "#27C93F" }} />
    </div>
    {/* Filename tab */}
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

const LineNumberGutter: React.FC<{
  startLine: number;
  lineCount: number;
}> = ({ startLine, lineCount }) => (
  <div
    style={{
      position: "absolute",
      top: 36,
      left: 0,
      width: 52,
      height: "calc(100% - 36px)",
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
          fontSize: 16,
          lineHeight: "24px",
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
  lines: CodeLine[];
}> = ({ lines }) => (
  <div
    style={{
      position: "absolute",
      top: 36,
      left: 52,
      width: 6,
      height: "calc(100% - 36px)",
      paddingTop: 16,
      zIndex: 5,
    }}
  >
    {lines.map((line, i) => (
      <div
        key={i}
        style={{
          height: 24,
          background: line.blameColor,
          width: "100%",
          opacity: 0.7,
        }}
      />
    ))}
  </div>
);

const WarningIcon: React.FC<{
  lineIndex: number;
}> = ({ lineIndex }) => (
  <div
    style={{
      position: "absolute",
      top: 36 + 16 + lineIndex * 24,
      left: 60,
      width: 16,
      height: 16,
      display: "flex",
      alignItems: "center",
      justifyContent: "center",
      zIndex: 6,
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

const Cursor: React.FC<{
  lineIndex: number;
  visible: boolean;
}> = ({ lineIndex, visible }) => {
  if (!visible) return null;
  // Position cursor at end of the TODO comment line
  const cursorLeft = 80 + 48 * 9.2; // approximate character width * column
  return (
    <div
      style={{
        position: "absolute",
        top: 36 + 16 + lineIndex * 24,
        left: cursorLeft,
        width: 9,
        height: 20,
        background: "#FFFFFF",
        zIndex: 7,
        opacity: 0.9,
      }}
    />
  );
};

const Scrollbar: React.FC = () => (
  <div
    style={{
      position: "absolute",
      top: 36,
      right: 0,
      width: 10,
      height: "calc(100% - 36px)",
      background: "#1A1A28",
      zIndex: 5,
    }}
  >
    {/* Scrollbar thumb */}
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

const Vignette: React.FC<{ opacity: number }> = ({ opacity }) => {
  if (opacity <= 0) return null;
  return (
    <div
      style={{
        position: "absolute",
        top: 0,
        left: 0,
        right: 0,
        bottom: 0,
        background:
          "radial-gradient(ellipse at center, transparent 50%, rgba(0,0,0,0.8) 100%)",
        opacity,
        pointerEvents: "none",
        zIndex: 20,
      }}
    />
  );
};

// ── Syntax-highlighted code line renderer ────────────────────────────

const renderCodeLine = (line: CodeLine, index: number): React.ReactNode => {
  const text = line.text;
  const baseColor = line.color;

  // Empty lines
  if (text.trim() === "") {
    return (
      <div
        key={index}
        style={{
          height: 24,
          lineHeight: "24px",
          fontFamily: "'JetBrains Mono', monospace",
          fontSize: 16,
          whiteSpace: "pre",
        }}
      >
        {" "}
      </div>
    );
  }

  // Comment lines
  if (text.trimStart().startsWith("#")) {
    return (
      <div
        key={index}
        style={{
          height: 24,
          lineHeight: "24px",
          fontFamily: "'JetBrains Mono', monospace",
          fontSize: 16,
          color: COMMENT_COLOR,
          whiteSpace: "pre",
        }}
      >
        {text}
      </div>
    );
  }

  // Docstring
  if (text.trimStart().startsWith('"""')) {
    return (
      <div
        key={index}
        style={{
          height: 24,
          lineHeight: "24px",
          fontFamily: "'JetBrains Mono', monospace",
          fontSize: 16,
          color: STRING_COLOR,
          whiteSpace: "pre",
        }}
      >
        {text}
      </div>
    );
  }

  // For regular code lines, apply the patch-era base color
  // with keyword highlighting
  const keywords = ["def", "if", "else", "try", "except", "for", "in", "return", "del", "is", "and", "not", "None", "True", "False"];
  const parts: React.ReactNode[] = [];
  const tokens = text.split(/(\s+|\b)/);

  tokens.forEach((token, ti) => {
    if (keywords.includes(token)) {
      parts.push(
        <span key={`${index}-${ti}`} style={{ color: KEYWORD_COLOR }}>
          {token}
        </span>
      );
    } else if (token.startsWith("_") && /^_\w+/.test(token) && !token.includes('"')) {
      // Private function/variable names
      parts.push(
        <span key={`${index}-${ti}`} style={{ color: FUNCTION_COLOR }}>
          {token}
        </span>
      );
    } else if ((token.startsWith('"') || token.startsWith("'")) && (token.endsWith('"') || token.endsWith("'"))) {
      parts.push(
        <span key={`${index}-${ti}`} style={{ color: STRING_COLOR }}>
          {token}
        </span>
      );
    } else {
      parts.push(
        <span key={`${index}-${ti}`} style={{ color: baseColor }}>
          {token}
        </span>
      );
    }
  });

  return (
    <div
      key={index}
      style={{
        height: 24,
        lineHeight: "24px",
        fontFamily: "'JetBrains Mono', monospace",
        fontSize: 16,
        whiteSpace: "pre",
      }}
    >
      {parts}
    </div>
  );
};

// ── Main component ──────────────────────────────────────────────────

export const CODE_BLINKS_FPS = 30;
export const CODE_BLINKS_DURATION_FRAMES = 300; // 10 seconds standalone

interface CodeBlinksProps {
  /** Total frames for this instance (300 for standalone, shorter when embedded) */
  durationFrames?: number;
}

export const CodeBlinks: React.FC<CodeBlinksProps> = ({
  durationFrames = CODE_BLINKS_DURATION_FRAMES,
}) => {
  const frame = useCurrentFrame();
  const { fps } = useVideoConfig();

  // Scale animation timing proportionally to duration
  const scale = durationFrames / 300;
  const fadeInEnd = Math.round(15 * scale);
  const cursorStartFrame = fadeInEnd;
  const vignetteStart = Math.round(240 * scale);
  const vignetteEnd = durationFrames;

  // Fade in from black with easeOutCubic
  const fadeIn = interpolate(frame, [0, fadeInEnd], [0, 1], {
    extrapolateLeft: "clamp",
    extrapolateRight: "clamp",
    easing: Easing.out(Easing.cubic),
  });

  // Cursor blink: ~530ms cycle (on for ~265ms, off for ~265ms)
  const blinkCycleFrames = Math.round(0.53 * fps);
  const halfCycle = Math.round(blinkCycleFrames / 2);
  const cursorVisible =
    frame < cursorStartFrame
      ? false
      : Math.floor((frame - cursorStartFrame) / halfCycle) % 2 === 0;

  // Vignette: subtle darkening at edges in the final portion
  const vignetteOpacity = interpolate(
    frame,
    [vignetteStart, vignetteEnd],
    [0, 0.05],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
  );

  return (
    <AbsoluteFill style={{ backgroundColor: "#1E1E2E", opacity: fadeIn }}>
      {/* Editor top bar */}
      <EditorTopBar filename="user_parser.py" />

      {/* Line number gutter */}
      <LineNumberGutter
        startLine={START_LINE_NUMBER}
        lineCount={CODE_LINES.length}
      />

      {/* Git blame gutter */}
      <BlameGutter lines={CODE_LINES} />

      {/* Scrollbar */}
      <Scrollbar />

      {/* Code area */}
      <div
        style={{
          position: "absolute",
          top: 36,
          left: 80,
          right: 14,
          bottom: 0,
          paddingTop: 16,
          overflow: "hidden",
        }}
      >
        {CODE_LINES.map((line, i) => renderCodeLine(line, i))}
      </div>

      {/* Warning icon next to TODO comment */}
      <WarningIcon lineIndex={WARNING_LINE} />

      {/* Blinking cursor */}
      <Cursor lineIndex={CURSOR_LINE} visible={cursorVisible} />

      {/* Vignette overlay */}
      <Vignette opacity={vignetteOpacity} />
    </AbsoluteFill>
  );
};
