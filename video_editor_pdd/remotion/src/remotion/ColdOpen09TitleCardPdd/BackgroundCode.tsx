import React from "react";
import {
  CLEAN_FUNCTION_CODE,
  CODE_FONT_SIZE,
  CODE_LINE_HEIGHT,
  CODE_FONT_FAMILY,
  CODE_PADDING_TOP,
  CODE_PADDING_LEFT,
  SYN_KEYWORD,
  SYN_STRING,
  SYN_FUNCTION,
  SYN_TYPE,
  SYN_COMMENT,
  SYN_NUMBER,
  SYN_OPERATOR,
  SYN_DEFAULT,
} from "./constants";

/** Represents a single colored span of code text. */
interface Token {
  text: string;
  color: string;
}

const KEYWORDS = new Set([
  "def",
  "if",
  "else",
  "return",
  "import",
  "from",
  "class",
  "for",
  "while",
  "in",
  "not",
  "and",
  "or",
  "True",
  "False",
  "None",
  "max",
]);

const TYPES = new Set([
  "Order",
  "Decimal",
  "int",
  "str",
  "float",
  "bool",
  "list",
  "dict",
]);

/**
 * Very lightweight Python tokenizer — good enough for visual background texture.
 * Does not need to be semantically correct; it's at 15% opacity.
 */
function tokenizeLine(line: string): Token[] {
  const tokens: Token[] = [];
  let i = 0;

  while (i < line.length) {
    // Leading whitespace
    if (line[i] === " " || line[i] === "\t") {
      let ws = "";
      while (i < line.length && (line[i] === " " || line[i] === "\t")) {
        ws += line[i];
        i++;
      }
      tokens.push({ text: ws, color: SYN_DEFAULT });
      continue;
    }

    // Comments
    if (line[i] === "#") {
      tokens.push({ text: line.slice(i), color: SYN_COMMENT });
      break;
    }

    // Triple-quoted strings (docstrings)
    if (line.slice(i, i + 3) === '"""') {
      const end = line.indexOf('"""', i + 3);
      if (end !== -1) {
        tokens.push({ text: line.slice(i, end + 3), color: SYN_STRING });
        i = end + 3;
      } else {
        tokens.push({ text: line.slice(i), color: SYN_STRING });
        break;
      }
      continue;
    }

    // Strings
    if (line[i] === '"' || line[i] === "'") {
      const quote = line[i];
      let s = quote;
      i++;
      while (i < line.length && line[i] !== quote) {
        if (line[i] === "\\") {
          s += line[i];
          i++;
        }
        if (i < line.length) {
          s += line[i];
          i++;
        }
      }
      if (i < line.length) {
        s += line[i];
        i++;
      }
      tokens.push({ text: s, color: SYN_STRING });
      continue;
    }

    // Numbers
    if (/[0-9]/.test(line[i])) {
      let num = "";
      while (i < line.length && /[0-9.]/.test(line[i])) {
        num += line[i];
        i++;
      }
      tokens.push({ text: num, color: SYN_NUMBER });
      continue;
    }

    // Operators & punctuation
    if (/[+\-*/><=:,().\[\]{}@]/.test(line[i])) {
      tokens.push({ text: line[i], color: SYN_OPERATOR });
      i++;
      continue;
    }

    // Words (identifiers, keywords, types)
    if (/[a-zA-Z_]/.test(line[i])) {
      let word = "";
      while (i < line.length && /[a-zA-Z_0-9]/.test(line[i])) {
        word += line[i];
        i++;
      }

      if (KEYWORDS.has(word)) {
        tokens.push({ text: word, color: SYN_KEYWORD });
      } else if (TYPES.has(word)) {
        tokens.push({ text: word, color: SYN_TYPE });
      } else if (i < line.length && line[i] === "(") {
        tokens.push({ text: word, color: SYN_FUNCTION });
      } else {
        tokens.push({ text: word, color: SYN_DEFAULT });
      }
      continue;
    }

    // Fallback
    tokens.push({ text: line[i], color: SYN_DEFAULT });
    i++;
  }

  return tokens;
}

/**
 * Renders the background regenerated code with lightweight syntax highlighting.
 * Intended to be displayed at very low opacity as visual texture behind the title.
 */
export const BackgroundCode: React.FC = () => {
  const lines = CLEAN_FUNCTION_CODE.split("\n");

  return (
    <div
      style={{
        position: "absolute",
        top: CODE_PADDING_TOP,
        left: CODE_PADDING_LEFT,
        fontFamily: CODE_FONT_FAMILY,
        fontSize: CODE_FONT_SIZE,
        lineHeight: CODE_LINE_HEIGHT,
        whiteSpace: "pre",
      }}
    >
      {lines.map((line, lineIdx) => {
        const lineTokens = tokenizeLine(line);
        return (
          <div key={lineIdx}>
            {lineTokens.map((tok, tokIdx) => (
              <span key={tokIdx} style={{ color: tok.color }}>
                {tok.text}
              </span>
            ))}
            {lineTokens.length === 0 && "\u00A0"}
          </div>
        );
      })}
    </div>
  );
};

export default BackgroundCode;
