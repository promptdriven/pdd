import React from "react";
import { interpolate, useCurrentFrame, Easing } from "remotion";
import {
  PANEL_W,
  PANEL_H,
  PANEL_BG,
  PANEL_BORDER,
  PANEL_RADIUS,
  HEADER_LABEL_COLOR,
  STATUS_GREEN,
  PANEL_SLIDE_DURATION,
  HIGHLIGHT_FRAME,
  HIGHLIGHT_SCALE_DURATION,
  DIM_DURATION,
  type CodeLine,
  type GenerationData,
} from "./constants";

interface CodePanelProps {
  gen: GenerationData;
  index: number;
  x: number;
  y: number;
  /** Frame at which this panel first appears */
  appearFrame: number;
}

export const CodePanel: React.FC<CodePanelProps> = ({
  gen,
  index,
  x,
  y,
  appearFrame,
}) => {
  const frame = useCurrentFrame();
  const localFrame = frame - appearFrame;

  // ── Slide-up + fade-in ──
  const slideProgress = interpolate(
    localFrame,
    [0, PANEL_SLIDE_DURATION],
    [0, 1],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp", easing: Easing.out(Easing.cubic) }
  );
  const translateY = interpolate(slideProgress, [0, 1], [30, 0]);
  const opacity = slideProgress; // fade-in tracks slide

  // ── Highlight / dim (frame 240+) ──
  const isWinner = index === 4;
  const dimProgress = interpolate(
    frame,
    [HIGHLIGHT_FRAME, HIGHLIGHT_FRAME + DIM_DURATION],
    [0, 1],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp", easing: Easing.out(Easing.quad) }
  );

  const panelOpacity = isWinner ? opacity : opacity * interpolate(dimProgress, [0, 1], [1, 0.4]);

  // ── Scale for winner ──
  const scale = isWinner
    ? interpolate(
        frame,
        [HIGHLIGHT_FRAME, HIGHLIGHT_FRAME + HIGHLIGHT_SCALE_DURATION],
        [1.0, 1.08],
        { extrapolateLeft: "clamp", extrapolateRight: "clamp", easing: Easing.out(Easing.quad) }
      )
    : 1;

  // ── Green glow pulse for winner ──
  const glowPulse = isWinner && frame >= 180
    ? 0.3 + 0.15 * Math.sin((frame - 180) * 0.08)
    : 0;

  const borderColor = isWinner && frame >= 180
    ? STATUS_GREEN
    : PANEL_BORDER;

  if (localFrame < 0) return null;

  return (
    <div
      style={{
        position: "absolute",
        left: x,
        top: y,
        width: PANEL_W,
        height: PANEL_H,
        opacity: panelOpacity,
        transform: `translateY(${translateY}px) scale(${scale})`,
        transformOrigin: "center center",
        willChange: "transform, opacity",
      }}
    >
      {/* Glow effect behind panel for winner */}
      {isWinner && frame >= 180 && (
        <div
          style={{
            position: "absolute",
            inset: -12,
            borderRadius: PANEL_RADIUS + 4,
            boxShadow: `0 0 24px 12px rgba(74, 222, 128, ${glowPulse})`,
            pointerEvents: "none",
          }}
        />
      )}

      {/* Panel body */}
      <div
        style={{
          width: PANEL_W,
          height: PANEL_H,
          backgroundColor: PANEL_BG,
          border: `1px solid ${borderColor}`,
          borderRadius: PANEL_RADIUS,
          overflow: "hidden",
          display: "flex",
          flexDirection: "column",
          boxShadow: isWinner && frame >= 180
            ? `0 0 12px rgba(74, 222, 128, ${glowPulse})`
            : "none",
        }}
      >
        {/* Header */}
        <div
          style={{
            padding: "8px 12px",
            borderBottom: `1px solid ${PANEL_BORDER}`,
            display: "flex",
            alignItems: "center",
          }}
        >
          {/* Fake window dots */}
          <div style={{ display: "flex", gap: 5, marginRight: 10 }}>
            <div style={{ width: 8, height: 8, borderRadius: "50%", backgroundColor: "#EF4444", opacity: 0.6 }} />
            <div style={{ width: 8, height: 8, borderRadius: "50%", backgroundColor: "#FBBF24", opacity: 0.6 }} />
            <div style={{ width: 8, height: 8, borderRadius: "50%", backgroundColor: "#22C55E", opacity: 0.6 }} />
          </div>
          <span
            style={{
              fontFamily: "Inter, sans-serif",
              fontSize: 11,
              fontWeight: 600,
              color: HEADER_LABEL_COLOR,
            }}
          >
            {gen.label}
          </span>
        </div>

        {/* Code area */}
        <div style={{ padding: "10px 12px", flex: 1, overflow: "hidden" }}>
          {gen.code.map((line: CodeLine, li: number) => {
            const isFail = gen.failLines.includes(li);
            return (
              <div
                key={li}
                style={{
                  display: "flex",
                  alignItems: "center",
                  height: 22,
                  paddingLeft: line.indent * 16,
                  backgroundColor: isFail ? "rgba(239, 68, 68, 0.08)" : "transparent",
                  borderLeft: isFail ? "2px solid rgba(239, 68, 68, 0.4)" : "2px solid transparent",
                }}
              >
                {/* Line number */}
                <span
                  style={{
                    fontFamily: "JetBrains Mono, monospace",
                    fontSize: 10,
                    color: "#3E4452",
                    width: 20,
                    textAlign: "right",
                    marginRight: 10,
                    userSelect: "none",
                    flexShrink: 0,
                  }}
                >
                  {li + 1}
                </span>
                {/* Tokens */}
                {line.tokens.map((tok, ti) => (
                  <span
                    key={ti}
                    style={{
                      fontFamily: "JetBrains Mono, monospace",
                      fontSize: 10,
                      color: tok.color,
                      whiteSpace: "pre",
                    }}
                  >
                    {tok.text}
                  </span>
                ))}
              </div>
            );
          })}
        </div>
      </div>
    </div>
  );
};
