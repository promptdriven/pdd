import React from "react";
import { useCurrentFrame, interpolate, Easing } from "remotion";
import {
  CODE_LINE_HEIGHT,
  CODE_FONT_SIZE,
  GUTTER_WIDTH,
  CODE_LEFT_PADDING,
  EDITOR_TOP_PADDING,
  LINE_NUMBER_COLOR,
  EDITOR_GUTTER_BG,
  KEYWORD_COLOR,
  FUNCTION_COLOR,
  STRING_COLOR,
  COMMENT_COLOR,
  VARIABLE_COLOR,
  OPERATOR_COLOR,
  NUMBER_COLOR,
  DECORATOR_COLOR,
  BUILTIN_COLOR,
  SELF_COLOR,
  PARAMETER_COLOR,
} from "./constants";

// === Syntax highlighting helpers ===

const PYTHON_KEYWORDS = new Set([
  "def", "return", "if", "else", "elif", "for", "in", "not", "and", "or",
  "None", "True", "False", "try", "except", "raise", "break", "continue",
  "class", "import", "from", "as", "with", "pass", "while", "is",
]);

const PYTHON_BUILTINS = new Set([
  "len", "range", "print", "int", "str", "float", "list", "dict", "set",
  "tuple", "type", "isinstance", "getattr", "setattr", "hasattr",
  "ValueError", "TimeoutError", "KeyError", "TypeError",
  "OrderValidationError", "OrderResult",
]);

interface TokenSpan {
  text: string;
  color: string;
}

function tokenizePythonLine(line: string): TokenSpan[] {
  const tokens: TokenSpan[] = [];
  let i = 0;

  while (i < line.length) {
    // Whitespace
    if (line[i] === " " || line[i] === "\t") {
      let ws = "";
      while (i < line.length && (line[i] === " " || line[i] === "\t")) {
        ws += line[i];
        i++;
      }
      tokens.push({ text: ws, color: VARIABLE_COLOR });
      continue;
    }

    // Comments
    if (line[i] === "#") {
      tokens.push({ text: line.slice(i), color: COMMENT_COLOR });
      break;
    }

    // Strings (single or double quotes, including triple-quotes)
    if (line[i] === '"' || line[i] === "'") {
      const quote = line[i];
      let str = quote;
      i++;
      // Check for triple-quote
      if (line[i] === quote && line[i + 1] === quote) {
        str += quote + quote;
        i += 2;
        // Read until closing triple-quote
        while (i < line.length) {
          if (line[i] === quote && line[i + 1] === quote && line[i + 2] === quote) {
            str += quote + quote + quote;
            i += 3;
            break;
          }
          str += line[i];
          i++;
        }
      } else {
        // Single-quoted string
        while (i < line.length && line[i] !== quote) {
          if (line[i] === "\\") {
            str += line[i];
            i++;
          }
          if (i < line.length) {
            str += line[i];
            i++;
          }
        }
        if (i < line.length) {
          str += line[i];
          i++;
        }
      }
      tokens.push({ text: str, color: STRING_COLOR });
      continue;
    }

    // Numbers
    if (/[0-9]/.test(line[i])) {
      let num = "";
      while (i < line.length && /[0-9.]/.test(line[i])) {
        num += line[i];
        i++;
      }
      tokens.push({ text: num, color: NUMBER_COLOR });
      continue;
    }

    // Identifiers / keywords
    if (/[a-zA-Z_]/.test(line[i])) {
      let word = "";
      while (i < line.length && /[a-zA-Z0-9_]/.test(line[i])) {
        word += line[i];
        i++;
      }

      if (word === "self") {
        tokens.push({ text: word, color: SELF_COLOR });
      } else if (word === "def" || word === "class") {
        tokens.push({ text: word, color: KEYWORD_COLOR });
        // Next non-space word is the function/class name
        let space = "";
        while (i < line.length && line[i] === " ") {
          space += line[i];
          i++;
        }
        if (space) tokens.push({ text: space, color: VARIABLE_COLOR });
        let name = "";
        while (i < line.length && /[a-zA-Z0-9_]/.test(line[i])) {
          name += line[i];
          i++;
        }
        if (name) tokens.push({ text: name, color: FUNCTION_COLOR });
      } else if (PYTHON_KEYWORDS.has(word)) {
        tokens.push({ text: word, color: KEYWORD_COLOR });
      } else if (PYTHON_BUILTINS.has(word)) {
        tokens.push({ text: word, color: BUILTIN_COLOR });
      } else {
        // Check if it's a function call (followed by '(')
        const lookAhead = line.slice(i).trimStart();
        if (lookAhead.startsWith("(")) {
          tokens.push({ text: word, color: FUNCTION_COLOR });
        } else {
          tokens.push({ text: word, color: VARIABLE_COLOR });
        }
      }
      continue;
    }

    // Decorators
    if (line[i] === "@") {
      let dec = "@";
      i++;
      while (i < line.length && /[a-zA-Z0-9_.]/.test(line[i])) {
        dec += line[i];
        i++;
      }
      tokens.push({ text: dec, color: DECORATOR_COLOR });
      continue;
    }

    // Operators and punctuation
    tokens.push({ text: line[i], color: OPERATOR_COLOR });
    i++;
  }

  return tokens;
}

// === Rendered code line ===

interface CodeLineProps {
  lineNumber: number;
  text: string;
  opacity: number;
  yOffset: number;
}

const CodeLine: React.FC<CodeLineProps> = ({
  lineNumber,
  text,
  opacity,
  yOffset,
}) => {
  const tokens = tokenizePythonLine(text);
  const top = EDITOR_TOP_PADDING + (lineNumber - 1) * CODE_LINE_HEIGHT;

  return (
    <div
      style={{
        position: "absolute",
        top: top + yOffset,
        left: 0,
        width: "100%",
        height: CODE_LINE_HEIGHT,
        display: "flex",
        flexDirection: "row",
        alignItems: "center",
        opacity,
        fontFamily: '"JetBrains Mono", "Fira Code", monospace',
        fontSize: CODE_FONT_SIZE,
        lineHeight: `${CODE_LINE_HEIGHT}px`,
        whiteSpace: "pre",
      }}
    >
      {/* Line number gutter */}
      <div
        style={{
          width: GUTTER_WIDTH,
          textAlign: "right",
          paddingRight: 12,
          color: LINE_NUMBER_COLOR,
          backgroundColor: EDITOR_GUTTER_BG,
          height: "100%",
          display: "flex",
          alignItems: "center",
          justifyContent: "flex-end",
          flexShrink: 0,
          userSelect: "none",
        }}
      >
        {lineNumber}
      </div>

      {/* Code content */}
      <div
        style={{
          paddingLeft: CODE_LEFT_PADDING,
          display: "flex",
          flexDirection: "row",
        }}
      >
        {tokens.map((token, idx) => (
          <span key={idx} style={{ color: token.color }}>
            {token.text}
          </span>
        ))}
      </div>
    </div>
  );
};

// === Phase renderers ===

interface CodeLinesDisplayProps {
  lines: string[];
  startLineNumber: number;
  lineOpacity?: number;
  lineYOffset?: number;
}

/** Render a static block of code lines */
export const StaticCodeLines: React.FC<CodeLinesDisplayProps> = ({
  lines,
  startLineNumber,
  lineOpacity = 1,
  lineYOffset = 0,
}) => {
  return (
    <>
      {lines.map((line, idx) => (
        <CodeLine
          key={idx}
          lineNumber={startLineNumber + idx}
          text={line}
          opacity={lineOpacity}
          yOffset={lineYOffset}
        />
      ))}
    </>
  );
};

interface FlowInCodeLinesProps {
  lines: string[];
  startLineNumber: number;
  /** Frame at which flow-in animation started (relative to component mount) */
  flowStartFrame: number;
}

/**
 * Lines that flow in one per frame with easeOut(cubic) opacity + slide.
 * Each line takes ~6 frames to fully settle.
 */
export const FlowInCodeLines: React.FC<FlowInCodeLinesProps> = ({
  lines,
  startLineNumber,
  flowStartFrame,
}) => {
  const frame = useCurrentFrame();

  return (
    <>
      {lines.map((line, idx) => {
        const lineAppearFrame = flowStartFrame + idx;
        const elapsed = frame - lineAppearFrame;

        if (elapsed < 0) return null;

        const opacity = interpolate(elapsed, [0, 6], [0, 1], {
          extrapolateRight: "clamp",
          easing: Easing.out(Easing.cubic),
        });

        const yOffset = interpolate(elapsed, [0, 6], [8, 0], {
          extrapolateRight: "clamp",
          easing: Easing.out(Easing.cubic),
        });

        return (
          <CodeLine
            key={idx}
            lineNumber={startLineNumber + idx}
            text={line}
            opacity={opacity}
            yOffset={yOffset}
          />
        );
      })}
    </>
  );
};

export default StaticCodeLines;
