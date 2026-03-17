import React from "react";
import { AbsoluteFill, useCurrentFrame, interpolate, Easing } from "remotion";
import {
  CODE_DIM_START,
  CODE_DIM_END,
  CODE_UNDERLAY_FINAL_OPACITY,
  REGENERATED_CODE_LINES,
} from "./constants";

/**
 * Dimmed code underlay — the regenerated code from the previous shot
 * fades from full visibility to near-invisible over frames 0-30.
 */
export const CodeUnderlay: React.FC = () => {
  const frame = useCurrentFrame();

  const opacity = interpolate(
    frame,
    [CODE_DIM_START, CODE_DIM_END],
    [0.6, CODE_UNDERLAY_FINAL_OPACITY],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.inOut(Easing.ease),
    }
  );

  return (
    <AbsoluteFill
      style={{
        opacity,
        display: "flex",
        alignItems: "center",
        justifyContent: "center",
        padding: "120px 400px",
      }}
    >
      <pre
        style={{
          fontFamily: '"JetBrains Mono", "Fira Code", monospace',
          fontSize: 14,
          lineHeight: 1.6,
          color: "#E2E8F0",
          margin: 0,
          whiteSpace: "pre",
          userSelect: "none",
        }}
      >
        {REGENERATED_CODE_LINES.map((line, i) => (
          <div key={i} style={{ minHeight: "1.6em" }}>
            <span style={{ color: "#6B7280", marginRight: 16, display: "inline-block", width: 24, textAlign: "right" }}>
              {i + 1}
            </span>
            <span>{colorizeCodeLine(line)}</span>
          </div>
        ))}
      </pre>
    </AbsoluteFill>
  );
};

/** Minimal syntax highlighting for the code underlay. */
function colorizeCodeLine(line: string): React.ReactNode {
  const keywords = /\b(import|from|export|const|interface|return|type)\b/g;
  const strings = /(["'`])(?:(?!\1).)*\1/g;
  const types = /\b(React|FC|FormProps|FormData|void)\b/g;

  // Simple approach: just render as-is with a muted color
  // Since this fades to 0.08 opacity, detailed highlighting isn't critical
  const parts: React.ReactNode[] = [];
  let lastIndex = 0;
  const combined = new RegExp(
    `(${keywords.source})|(${strings.source})|(${types.source})`,
    "g"
  );

  let match: RegExpExecArray | null;
  while ((match = combined.exec(line)) !== null) {
    if (match.index > lastIndex) {
      parts.push(line.slice(lastIndex, match.index));
    }
    const text = match[0];
    let color = "#E2E8F0";
    if (/^(import|from|export|const|interface|return|type)$/.test(text)) {
      color = "#C586C0";
    } else if (/^["'`]/.test(text)) {
      color = "#CE9178";
    } else if (/^(React|FC|FormProps|FormData|void)$/.test(text)) {
      color = "#4EC9B0";
    }
    parts.push(
      <span key={match.index} style={{ color }}>
        {text}
      </span>
    );
    lastIndex = match.index + text.length;
  }
  if (lastIndex < line.length) {
    parts.push(line.slice(lastIndex));
  }
  if (parts.length === 0) return line;
  return <>{parts}</>;
}
