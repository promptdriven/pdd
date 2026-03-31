import React from "react";
import {
  SYN_KEYWORD,
  SYN_FUNCTION,
  SYN_STRING,
  SYN_COMMENT,
  SYN_OPERATOR,
  SYN_NUMBER,
  SYN_DEFAULT,
  SYN_DECORATOR,
  SYN_BUILTIN,
  SYN_PARAM,
  CODE_FONT_SIZE,
  CODE_LINE_HEIGHT,
  GUTTER_BG,
  GUTTER_WIDTH,
  LINE_NUMBER_COLOR,
  CODE_LEFT_PADDING,
} from "./constants";

// ── Token types ─────────────────────────────────────────────────

interface Token {
  text: string;
  color: string;
}

const KEYWORDS = new Set([
  "def",
  "return",
  "if",
  "else",
  "for",
  "in",
  "not",
  "None",
  "True",
  "False",
  "raise",
  "with",
  "import",
  "from",
  "class",
  "and",
  "or",
  "is",
]);

const BUILTINS = new Set(["len", "abs", "round", "print", "range", "ValueError"]);

/**
 * Naive Python tokenizer — good enough for visual syntax highlighting.
 */
function tokenize(line: string): Token[] {
  const tokens: Token[] = [];
  let i = 0;

  while (i < line.length) {
    // Whitespace
    if (line[i] === " ") {
      let ws = "";
      while (i < line.length && line[i] === " ") {
        ws += " ";
        i++;
      }
      tokens.push({ text: ws, color: SYN_DEFAULT });
      continue;
    }

    // Comment
    if (line[i] === "#") {
      tokens.push({ text: line.slice(i), color: SYN_COMMENT });
      break;
    }

    // String (single or double quote, including f-strings)
    if (line[i] === '"' || line[i] === "'") {
      const quote = line[i];
      // Check for triple quotes
      if (line.slice(i, i + 3) === quote.repeat(3)) {
        const end = line.indexOf(quote.repeat(3), i + 3);
        if (end !== -1) {
          tokens.push({ text: line.slice(i, end + 3), color: SYN_STRING });
          i = end + 3;
        } else {
          tokens.push({ text: line.slice(i), color: SYN_STRING });
          break;
        }
        continue;
      }
      let j = i + 1;
      while (j < line.length && line[j] !== quote) {
        if (line[j] === "\\") j++; // skip escaped char
        j++;
      }
      tokens.push({ text: line.slice(i, j + 1), color: SYN_STRING });
      i = j + 1;
      continue;
    }

    // f-string prefix
    if (
      (line[i] === "f" || line[i] === "F") &&
      i + 1 < line.length &&
      (line[i + 1] === '"' || line[i + 1] === "'")
    ) {
      const quote = line[i + 1];
      let j = i + 2;
      while (j < line.length && line[j] !== quote) {
        if (line[j] === "\\") j++;
        j++;
      }
      tokens.push({ text: line.slice(i, j + 1), color: SYN_STRING });
      i = j + 1;
      continue;
    }

    // Decorator
    if (line[i] === "@") {
      let j = i + 1;
      while (j < line.length && /[a-zA-Z0-9_.]/.test(line[j])) j++;
      tokens.push({ text: line.slice(i, j), color: SYN_DECORATOR });
      i = j;
      continue;
    }

    // Number
    if (/[0-9]/.test(line[i])) {
      let j = i;
      while (j < line.length && /[0-9.]/.test(line[j])) j++;
      tokens.push({ text: line.slice(i, j), color: SYN_NUMBER });
      i = j;
      continue;
    }

    // Word (identifier / keyword)
    if (/[a-zA-Z_]/.test(line[i])) {
      let j = i;
      while (j < line.length && /[a-zA-Z0-9_]/.test(line[j])) j++;
      const word = line.slice(i, j);

      if (KEYWORDS.has(word)) {
        tokens.push({ text: word, color: SYN_KEYWORD });
      } else if (BUILTINS.has(word)) {
        tokens.push({ text: word, color: SYN_BUILTIN });
      } else if (j < line.length && line[j] === "(") {
        tokens.push({ text: word, color: SYN_FUNCTION });
      } else if (i > 0 && line.slice(0, i).trimEnd().endsWith("def")) {
        tokens.push({ text: word, color: SYN_FUNCTION });
      } else if (j < line.length && (line[j] === ":" || line[j] === "=")) {
        tokens.push({ text: word, color: SYN_PARAM });
      } else {
        tokens.push({ text: word, color: SYN_DEFAULT });
      }
      i = j;
      continue;
    }

    // Operators / punctuation
    tokens.push({ text: line[i], color: SYN_OPERATOR });
    i++;
  }

  return tokens;
}

// ── Component ───────────────────────────────────────────────────

interface CodeLineProps {
  lineNumber: number;
  text: string;
  opacity?: number;
  yOffset?: number;
}

const CodeLine: React.FC<CodeLineProps> = ({
  lineNumber,
  text,
  opacity = 1,
  yOffset = 0,
}) => {
  const tokens = tokenize(text);
  const y = yOffset;

  return (
    <div
      style={{
        display: "flex",
        height: CODE_LINE_HEIGHT,
        opacity,
        transform: `translateY(${y}px)`,
        whiteSpace: "pre",
        fontFamily: "'JetBrains Mono', monospace",
        fontSize: CODE_FONT_SIZE,
        lineHeight: `${CODE_LINE_HEIGHT}px`,
      }}
    >
      {/* Gutter */}
      <div
        style={{
          width: GUTTER_WIDTH,
          minWidth: GUTTER_WIDTH,
          backgroundColor: GUTTER_BG,
          color: LINE_NUMBER_COLOR,
          textAlign: "right",
          paddingRight: 12,
          userSelect: "none",
        }}
      >
        {lineNumber}
      </div>

      {/* Code content */}
      <div style={{ paddingLeft: CODE_LEFT_PADDING }}>
        {tokens.map((token, idx) => (
          <span key={idx} style={{ color: token.color }}>
            {token.text}
          </span>
        ))}
      </div>
    </div>
  );
};

export default CodeLine;
