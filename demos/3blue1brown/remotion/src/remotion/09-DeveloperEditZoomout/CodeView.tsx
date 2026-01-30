import React from "react";
import { COLORS, CODE_LINES, EDITOR_REGION } from "./constants";

/**
 * Stylized IDE code view rendered in world-space SVG coordinates.
 * Shows the code the developer just edited before the zoom-out.
 */
export const CodeView: React.FC<{ opacity: number }> = ({ opacity }) => {
  if (opacity <= 0) return null;

  const { x, y, width, height } = EDITOR_REGION;
  const lineHeight = 17;
  const startY = y + 28;
  const lineNumX = x + 8;
  const codeX = x + 40;

  // Build displayable lines from CODE_LINES tokens
  // Group consecutive tokens into lines (split on closing braces / returns)
  const lines: { lineNum: number; tokens: { type: string; text: string }[] }[] =
    [];
  let currentTokens: { type: string; text: string }[] = [];
  let lineNum = 1;

  CODE_LINES.forEach((token) => {
    currentTokens.push(token);
    // End line after complete statements
    if (
      token.text.endsWith("{") ||
      token.text.endsWith("}") ||
      token.text.endsWith(";") ||
      token.type === "comment" ||
      token.text.includes("// patched")
    ) {
      lines.push({ lineNum, tokens: [...currentTokens] });
      currentTokens = [];
      lineNum++;
    }
  });
  if (currentTokens.length > 0) {
    lines.push({ lineNum, tokens: currentTokens });
  }

  const colorMap: Record<string, string> = {
    keyword: COLORS.CODE_KEYWORD,
    string: COLORS.CODE_STRING,
    function: COLORS.CODE_FUNCTION,
    variable: COLORS.CODE_VARIABLE,
    comment: COLORS.CODE_COMMENT,
    plain: COLORS.CODE_PLAIN,
  };

  return (
    <g opacity={opacity}>
      {/* Editor background */}
      <rect
        x={x}
        y={y}
        width={width}
        height={height}
        rx={6}
        fill={COLORS.CODE_BG}
        stroke={COLORS.FILE_BORDER}
        strokeWidth={2}
      />
      {/* Title bar */}
      <rect
        x={x}
        y={y}
        width={width}
        height={22}
        rx={6}
        fill="#2d2d2d"
      />
      <text
        x={x + width / 2}
        y={y + 15}
        textAnchor="middle"
        fontSize={10}
        fill={COLORS.CODE_LINE_NUMBER}
        fontFamily="monospace"
      >
        pricing.ts
      </text>

      {/* Code lines */}
      {lines.slice(0, Math.floor((height - 30) / lineHeight)).map((line, li) => {
        let xOffset = 0;
        return (
          <g key={li}>
            {/* Line number */}
            <text
              x={lineNumX}
              y={startY + li * lineHeight}
              fontSize={11}
              fill={COLORS.CODE_LINE_NUMBER}
              fontFamily="monospace"
            >
              {line.lineNum}
            </text>
            {/* Tokens */}
            {line.tokens.map((tok, ti) => {
              const el = (
                <text
                  key={ti}
                  x={codeX + xOffset}
                  y={startY + li * lineHeight}
                  fontSize={11}
                  fill={colorMap[tok.type] || COLORS.CODE_PLAIN}
                  fontFamily="monospace"
                >
                  {tok.text}
                </text>
              );
              xOffset += tok.text.length * 6.6;
              return el;
            })}
          </g>
        );
      })}

      {/* Highlight bar on the patched line */}
      <rect
        x={x + 2}
        y={startY + 4 * lineHeight - 13}
        width={width - 4}
        height={lineHeight}
        fill={COLORS.PATCH_YELLOW}
        opacity={0.12}
        rx={2}
      />
    </g>
  );
};
