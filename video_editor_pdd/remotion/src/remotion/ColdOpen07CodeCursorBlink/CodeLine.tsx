import React from "react";
import {
  LINE_HEIGHT,
  FONT_SIZE,
  LINE_NUMBER_FONT_SIZE,
  LINE_NUMBER_COLOR,
  GUTTER_WIDTH,
  CODE_LEFT_PADDING,
  PATCH_BORDER_WIDTH,
  COMMENT_COLOR,
  TODO_COMMENT_COLOR,
  HOTFIX_COMMENT_COLOR,
  KEYWORD_COLOR,
  FUNCTION_COLOR,
  STRING_COLOR,
  TYPE_COLOR,
  OPERATOR_COLOR,
  NUMBER_COLOR,
  PARAM_COLOR,
  VARIABLE_COLOR,
  RECENT_PATCH_COLOR,
  RECENT_PATCH_OPACITY,
  MEDIUM_PATCH_COLOR,
  MEDIUM_PATCH_OPACITY,
  OLD_PATCH_COLOR,
  OLD_PATCH_OPACITY,
} from "./constants";

// ─── Token types for syntax highlighting ───
type TokenType =
  | "keyword"
  | "function"
  | "string"
  | "type"
  | "operator"
  | "number"
  | "comment"
  | "todo"
  | "hotfix"
  | "param"
  | "variable"
  | "plain";

interface Token {
  text: string;
  type: TokenType;
}

export type PatchAge = "recent" | "medium" | "old" | null;

interface CodeLineProps {
  lineNumber: number;
  tokens: Token[];
  patchAge: PatchAge;
  yOffset: number;
}

const TOKEN_COLORS: Record<TokenType, string> = {
  keyword: KEYWORD_COLOR,
  function: FUNCTION_COLOR,
  string: STRING_COLOR,
  type: TYPE_COLOR,
  operator: OPERATOR_COLOR,
  number: NUMBER_COLOR,
  comment: COMMENT_COLOR,
  todo: TODO_COMMENT_COLOR,
  hotfix: HOTFIX_COMMENT_COLOR,
  param: PARAM_COLOR,
  variable: VARIABLE_COLOR,
  plain: VARIABLE_COLOR,
};

function getPatchBorderStyle(age: PatchAge): React.CSSProperties {
  if (!age) return {};
  const map: Record<string, { color: string; opacity: number }> = {
    recent: { color: RECENT_PATCH_COLOR, opacity: RECENT_PATCH_OPACITY },
    medium: { color: MEDIUM_PATCH_COLOR, opacity: MEDIUM_PATCH_OPACITY },
    old: { color: OLD_PATCH_COLOR, opacity: OLD_PATCH_OPACITY },
  };
  const { color, opacity } = map[age];
  return {
    borderLeft: `${PATCH_BORDER_WIDTH}px solid ${color}`,
    backgroundColor: `${color}${Math.round(opacity * 255)
      .toString(16)
      .padStart(2, "0")}`,
  };
}

export const CodeLine: React.FC<CodeLineProps> = ({
  lineNumber,
  tokens,
  patchAge,
  yOffset,
}) => {
  const isComment = tokens.some(
    (t) => t.type === "comment" || t.type === "todo" || t.type === "hotfix"
  );

  return (
    <div
      style={{
        position: "absolute",
        top: yOffset,
        left: 0,
        right: 0,
        height: LINE_HEIGHT,
        display: "flex",
        alignItems: "center",
        ...getPatchBorderStyle(patchAge),
      }}
    >
      {/* Line number */}
      <span
        style={{
          width: GUTTER_WIDTH,
          textAlign: "right",
          paddingRight: 12,
          fontFamily: "'JetBrains Mono', 'Fira Code', 'Courier New', monospace",
          fontSize: LINE_NUMBER_FONT_SIZE,
          color: LINE_NUMBER_COLOR,
          opacity: 0.5,
          flexShrink: 0,
          userSelect: "none",
        }}
      >
        {lineNumber}
      </span>

      {/* Code tokens */}
      <span
        style={{
          paddingLeft: CODE_LEFT_PADDING,
          fontFamily: "'JetBrains Mono', 'Fira Code', 'Courier New', monospace",
          fontSize: FONT_SIZE,
          fontStyle: isComment ? "italic" : "normal",
          whiteSpace: "pre",
          lineHeight: `${LINE_HEIGHT}px`,
        }}
      >
        {tokens.map((token, i) => (
          <span
            key={i}
            style={{
              color: TOKEN_COLORS[token.type],
              fontStyle:
                token.type === "comment" ||
                token.type === "todo" ||
                token.type === "hotfix"
                  ? "italic"
                  : "inherit",
            }}
          >
            {token.text}
          </span>
        ))}
      </span>
    </div>
  );
};

export default CodeLine;

// ─── Helper to build token arrays quickly ───
export function kw(text: string): Token { return { text, type: "keyword" }; }
export function fn(text: string): Token { return { text, type: "function" }; }
export function str(text: string): Token { return { text, type: "string" }; }
export function typ(text: string): Token { return { text, type: "type" }; }
export function op(text: string): Token { return { text, type: "operator" }; }
export function num(text: string): Token { return { text, type: "number" }; }
export function cmt(text: string): Token { return { text, type: "comment" }; }
export function todo(text: string): Token { return { text, type: "todo" }; }
export function hotfix(text: string): Token { return { text, type: "hotfix" }; }
export function param(text: string): Token { return { text, type: "param" }; }
export function v(text: string): Token { return { text, type: "variable" }; }
export function plain(text: string): Token { return { text, type: "plain" }; }
