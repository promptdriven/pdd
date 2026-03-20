import React from "react";
import {
  BASE_CODE_COLOR,
  KEYWORD_COLOR,
  STRING_COLOR,
  COMMENT_COLOR,
  FUNCTION_NAME_COLOR,
  FONT_SIZE,
  LINE_HEIGHT,
} from "./constants";

/** A single token with a color. */
interface Token {
  text: string;
  color: string;
}

/**
 * Very lightweight syntax highlighter for the specific TypeScript
 * snippet in this component. Handles keywords, strings, comments,
 * and the function name `processUserInput`.
 */
function tokenize(line: string): Token[] {
  // Full-line comment
  const trimmed = line.trimStart();
  if (trimmed.startsWith("//")) {
    const indent = line.slice(0, line.length - trimmed.length);
    return [
      { text: indent, color: BASE_CODE_COLOR },
      { text: trimmed, color: COMMENT_COLOR },
    ];
  }

  const tokens: Token[] = [];
  // Regex-based tokenizer: keywords, strings, function name, rest
  const pattern =
    /(\b(?:function|const|let|return|if|else|true|false)\b)|(processUserInput)|('(?:[^'\\]|\\.)*')|(\/[^/]*\/[gimsuy]*)|([^'"/\w]+|\w+)/g;

  let match: RegExpExecArray | null;
  while ((match = pattern.exec(line)) !== null) {
    const [full, keyword, funcName, str, regex, rest] = match;
    if (keyword) {
      tokens.push({ text: keyword, color: KEYWORD_COLOR });
    } else if (funcName) {
      tokens.push({ text: funcName, color: FUNCTION_NAME_COLOR });
    } else if (str) {
      tokens.push({ text: str, color: STRING_COLOR });
    } else if (regex) {
      tokens.push({ text: regex, color: STRING_COLOR });
    } else if (rest) {
      tokens.push({ text: rest, color: BASE_CODE_COLOR });
    } else {
      tokens.push({ text: full, color: BASE_CODE_COLOR });
    }
  }

  return tokens.length > 0 ? tokens : [{ text: line, color: BASE_CODE_COLOR }];
}

interface CodeLineProps {
  text: string;
  isComment: boolean;
}

export const CodeLine: React.FC<CodeLineProps> = ({ text, isComment }) => {
  const tokens = tokenize(text);

  return (
    <div
      style={{
        display: "flex",
        alignItems: "baseline",
        height: LINE_HEIGHT,
        fontFamily: "'JetBrains Mono', 'Fira Code', 'Courier New', monospace",
        fontSize: FONT_SIZE,
        lineHeight: `${LINE_HEIGHT}px`,
        whiteSpace: "pre",
      }}
    >
      {tokens.map((tok, i) => (
        <span
          key={i}
          style={{
            color: tok.color,
            opacity: isComment ? 0.7 : 1,
          }}
        >
          {tok.text}
        </span>
      ))}
    </div>
  );
};

export default CodeLine;
