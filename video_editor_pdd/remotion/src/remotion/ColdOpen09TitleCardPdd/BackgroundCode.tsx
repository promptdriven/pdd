import React from "react";
import {
  CANVAS_WIDTH,
  CANVAS_HEIGHT,
  CODE_BG_OPACITY,
  CLEAN_FUNCTION_CODE,
} from "./constants";

// Syntax-highlighted code lines as styled spans
const KEYWORDS = new Set([
  "def",
  "return",
  "for",
  "in",
  "all",
  "import",
  "from",
  "True",
  "False",
  "None",
]);
const BUILTINS = new Set(["len", "sum", "all", "set", "dict", "list", "bool", "str", "float"]);

interface TokenStyle {
  color: string;
  fontStyle?: string;
}

function classifyToken(token: string): TokenStyle {
  if (KEYWORDS.has(token)) return { color: "#CBA6F7" };
  if (BUILTINS.has(token)) return { color: "#FAB387" };
  return { color: "#CDD6F4" };
}

function renderCodeLine(line: string, idx: number): React.ReactNode {
  // Simple tokenization for visual effect
  const lineNum = String(idx + 1).padStart(2, " ");

  // Detect string literals
  const parts: React.ReactNode[] = [];
  let remaining = line;
  let partKey = 0;

  // Handle comments
  if (remaining.trimStart().startsWith("#")) {
    return (
      <div key={idx} style={{ whiteSpace: "pre", height: 22 }}>
        <span style={{ color: "#585B70" }}>{lineNum} </span>
        <span style={{ color: "#6C7086", fontStyle: "italic" }}>
          {remaining}
        </span>
      </div>
    );
  }

  // Handle triple-quoted docstrings
  if (remaining.trimStart().startsWith('"""')) {
    return (
      <div key={idx} style={{ whiteSpace: "pre", height: 22 }}>
        <span style={{ color: "#585B70" }}>{lineNum} </span>
        <span style={{ color: "#A6E3A1" }}>{remaining}</span>
      </div>
    );
  }

  // Split by strings and colorize
  const stringRegex = /(f?"[^"]*"|'[^']*')/g;
  let match: RegExpExecArray | null;
  let lastIndex = 0;

  while ((match = stringRegex.exec(remaining)) !== null) {
    if (match.index > lastIndex) {
      const before = remaining.slice(lastIndex, match.index);
      parts.push(...tokenizeCode(before, partKey));
      partKey += 100;
    }
    parts.push(
      <span key={`s${partKey}`} style={{ color: "#A6E3A1" }}>
        {match[0]}
      </span>
    );
    partKey++;
    lastIndex = match.index + match[0].length;
  }

  if (lastIndex < remaining.length) {
    parts.push(...tokenizeCode(remaining.slice(lastIndex), partKey));
  }

  return (
    <div key={idx} style={{ whiteSpace: "pre", height: 22 }}>
      <span style={{ color: "#585B70" }}>{lineNum} </span>
      {parts}
    </div>
  );
}

function tokenizeCode(code: string, startKey: number): React.ReactNode[] {
  const tokens = code.split(/(\b)/);
  return tokens.map((token, i) => {
    const style = classifyToken(token);
    return (
      <span key={startKey + i} style={{ color: style.color }}>
        {token}
      </span>
    );
  });
}

export const BackgroundCode: React.FC = () => {
  const lines = CLEAN_FUNCTION_CODE.split("\n");

  return (
    <div
      style={{
        position: "absolute",
        top: 0,
        left: 0,
        width: CANVAS_WIDTH,
        height: CANVAS_HEIGHT,
        opacity: CODE_BG_OPACITY,
        fontFamily: "'JetBrains Mono', 'Fira Code', 'Courier New', monospace",
        fontSize: 14,
        lineHeight: "22px",
        padding: "40px 60px",
        boxSizing: "border-box",
        overflow: "hidden",
      }}
    >
      {lines.map((line, i) => renderCodeLine(line, i))}
    </div>
  );
};

export default BackgroundCode;
