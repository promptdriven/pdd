import React from "react";
import {
  CODE_BLOCK_WIDTH,
  CODE_BLOCK_HEIGHT,
  CODE_BG_COLOR,
  CODE_FONT_SIZE,
  PYTHON_CODE_LINES,
} from "./constants";

interface CodeBlockProps {
  glowOpacity: number;
  glowColor: string;
  textOpacity: number;
  borderColor: string;
  overallOpacity: number;
}

const CodeBlock: React.FC<CodeBlockProps> = ({
  glowOpacity,
  glowColor,
  textOpacity,
  borderColor,
  overallOpacity,
}) => {
  return (
    <div
      style={{
        position: "absolute",
        top: 650,
        left: 1920 / 2 - CODE_BLOCK_WIDTH / 2,
        width: CODE_BLOCK_WIDTH,
        height: CODE_BLOCK_HEIGHT,
        opacity: overallOpacity,
      }}
    >
      {/* Glow layer behind block */}
      {glowOpacity > 0.001 && (
        <div
          style={{
            position: "absolute",
            top: -15,
            left: -15,
            right: -15,
            bottom: -15,
            borderRadius: 14,
            background: `radial-gradient(ellipse, ${glowColor}${Math.round(
              glowOpacity * 100
            )
              .toString(16)
              .padStart(2, "0")} 0%, transparent 70%)`,
            filter: `blur(15px)`,
            pointerEvents: "none",
          }}
        />
      )}

      {/* Code container */}
      <div
        style={{
          position: "relative",
          width: CODE_BLOCK_WIDTH,
          height: CODE_BLOCK_HEIGHT,
          backgroundColor: CODE_BG_COLOR,
          border: `1px solid ${borderColor}`,
          borderRadius: 8,
          padding: "16px 20px",
          boxSizing: "border-box",
          overflow: "hidden",
          boxShadow:
            glowOpacity > 0.001
              ? `0 0 ${15 + glowOpacity * 20}px ${glowColor}${Math.round(
                  glowOpacity * 180
                )
                  .toString(16)
                  .padStart(2, "0")}`
              : "none",
        }}
      >
        {/* Window dots */}
        <div
          style={{
            display: "flex",
            gap: 6,
            marginBottom: 12,
          }}
        >
          <div
            style={{
              width: 8,
              height: 8,
              borderRadius: "50%",
              backgroundColor: "#FF5F57",
              opacity: textOpacity * 0.7,
            }}
          />
          <div
            style={{
              width: 8,
              height: 8,
              borderRadius: "50%",
              backgroundColor: "#FEBC2E",
              opacity: textOpacity * 0.7,
            }}
          />
          <div
            style={{
              width: 8,
              height: 8,
              borderRadius: "50%",
              backgroundColor: "#28C840",
              opacity: textOpacity * 0.7,
            }}
          />
        </div>

        {/* Code lines */}
        <div
          style={{
            fontFamily:
              '"JetBrains Mono", "Fira Code", "SF Mono", "Consolas", monospace',
            fontSize: CODE_FONT_SIZE,
            lineHeight: 1.7,
          }}
        >
          {PYTHON_CODE_LINES.map((line, lineIdx) => (
            <div key={lineIdx} style={{ whiteSpace: "pre" }}>
              {/* Line number */}
              <span
                style={{
                  color: "#636D83",
                  opacity: textOpacity * 0.5,
                  marginRight: 16,
                  display: "inline-block",
                  width: 20,
                  textAlign: "right",
                  userSelect: "none",
                }}
              >
                {lineIdx + 1}
              </span>
              {/* Tokens */}
              {line.tokens.map((token, tokenIdx) => (
                <span
                  key={tokenIdx}
                  style={{
                    color: token.color,
                    opacity: textOpacity,
                  }}
                >
                  {token.text}
                </span>
              ))}
            </div>
          ))}
        </div>
      </div>
    </div>
  );
};

export default CodeBlock;
