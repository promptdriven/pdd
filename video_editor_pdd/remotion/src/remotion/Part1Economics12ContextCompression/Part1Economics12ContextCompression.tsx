import React from "react";
import {
  AbsoluteFill,
  useCurrentFrame,
  interpolate,
  Easing,
} from "remotion";

// ── Sub-components ──
import { ContextWindowFrame } from "./ContextWindowFrame";
import { ModuleBlocks } from "./ModuleBlocks";
import { OverflowIndicator } from "./OverflowIndicator";
import { RemainingSpace } from "./RemainingSpace";
import { PhaseLabels } from "./PhaseLabels";

// ── Constants (inline to avoid cross-file import issues) ──
const BG_COLOR = "#0A0F1A";

const MODULES = [
  "auth", "parser", "router", "validator", "logger",
  "cache", "queue", "mailer", "search", "analytics",
  "billing", "permissions", "notifications", "export",
  "import", "scheduler", "webhook", "api_client",
  "transformer", "serializer",
];

const CODE_BLOCK_HEIGHTS = [
  240, 310, 200, 280, 190, 340, 220, 260, 300, 180,
  350, 230, 270, 320, 210, 290, 250, 330, 195, 285,
];

const WINDOW_WIDTH = 500;
const WINDOW_HEIGHT = 700;
const WINDOW_CENTER_X = 960;
const WINDOW_CENTER_Y = 480;
const WINDOW_LEFT = WINDOW_CENTER_X - WINDOW_WIDTH / 2;
const WINDOW_TOP = WINDOW_CENTER_Y - WINDOW_HEIGHT / 2;

// ── Overflow glow/scrolling blocks (visible below the window during phase 1) ──
const OverflowBlocks: React.FC = () => {
  const frame = useCurrentFrame();

  // Compute cumulative Y positions of code blocks
  const CODE_GAP = 4;
  const yPositions: number[] = [];
  let y = 0;
  for (let i = 0; i < MODULES.length; i++) {
    yPositions.push(y);
    y += CODE_BLOCK_HEIGHTS[i] + CODE_GAP;
  }

  // Only show during phase 1 (60–420), fade out during compression
  const fadeOut = interpolate(
    frame,
    [420, 460],
    [1, 0],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
  );

  if (fadeOut <= 0) return null;

  // Show blocks that overflow below the window (indices 3..19)
  // Position them below the window bottom, offset by the overflow amount
  const overflowStartY = yPositions[3]; // where overflow begins
  const BLOCK_H_PAD = 16;
  const blockWidth = WINDOW_WIDTH - BLOCK_H_PAD * 2;

  return (
    <div
      style={{
        position: "absolute",
        left: WINDOW_LEFT,
        top: WINDOW_TOP + WINDOW_HEIGHT + 2,
        width: WINDOW_WIDTH,
        height: 300,
        overflow: "hidden",
        opacity: fadeOut * 0.35,
        maskImage: "linear-gradient(to bottom, rgba(0,0,0,0.6) 0%, transparent 100%)",
        WebkitMaskImage: "linear-gradient(to bottom, rgba(0,0,0,0.6) 0%, transparent 100%)",
      }}
    >
      {MODULES.slice(3).map((name, idx) => {
        const i = idx + 3;
        const slideStart = 60 + i * 12;
        const slideEnd = slideStart + 30;
        const slideProgress = interpolate(
          frame,
          [slideStart, slideEnd],
          [0, 1],
          { extrapolateLeft: "clamp", extrapolateRight: "clamp", easing: Easing.out(Easing.cubic) }
        );

        if (frame < slideStart) return null;

        const blockY = yPositions[i] - overflowStartY;
        const translateX = interpolate(slideProgress, [0, 1], [-WINDOW_WIDTH - 100, 0]);

        return (
          <div
            key={name}
            style={{
              position: "absolute",
              top: blockY,
              left: BLOCK_H_PAD,
              width: blockWidth,
              height: CODE_BLOCK_HEIGHTS[i],
              transform: `translateX(${translateX}px)`,
              backgroundColor: "#1E293B",
              border: "1px solid #334155",
              borderRadius: 4,
              display: "flex",
              alignItems: "center",
              justifyContent: "center",
            }}
          >
            <span
              style={{
                fontFamily: "Inter, sans-serif",
                fontSize: 11,
                color: "#64748B",
                letterSpacing: 0.5,
              }}
            >
              {name}
            </span>
          </div>
        );
      })}
    </div>
  );
};

// ── Decorative floating token counts ──
const TokenCounts: React.FC = () => {
  const frame = useCurrentFrame();

  // Code token count: visible during phase 1 (frame 200–420)
  const codeCountOpacity = interpolate(
    frame,
    [200, 230, 420, 450],
    [0, 0.8, 0.8, 0],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
  );

  // Prompt token count: visible during phase 2 (frame 600+)
  const promptCountOpacity = interpolate(
    frame,
    [600, 630],
    [0, 0.8],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
  );

  const windowRight = WINDOW_LEFT + WINDOW_WIDTH;

  return (
    <div style={{ position: "absolute", inset: 0, pointerEvents: "none" }}>
      {/* Code token count */}
      {codeCountOpacity > 0.01 && (
        <div
          style={{
            position: "absolute",
            left: windowRight + 24,
            top: WINDOW_TOP + 20,
            fontFamily: "Inter, sans-serif",
            fontSize: 13,
            fontWeight: 500,
            color: "#64748B",
            opacity: codeCountOpacity,
            lineHeight: 1.6,
          }}
        >
          <div style={{ color: "#94A3B8", fontSize: 11, marginBottom: 4 }}>
            Per module
          </div>
          <div>~750 tokens (code)</div>
          <div style={{ marginTop: 8, color: "#EF4444", fontWeight: 600 }}>
            Total: ~15,000 tokens
          </div>
          <div style={{ marginTop: 2, color: "#64748B", fontSize: 11 }}>
            Window: 4,000 tokens
          </div>
        </div>
      )}

      {/* Prompt token count */}
      {promptCountOpacity > 0.01 && (
        <div
          style={{
            position: "absolute",
            left: windowRight + 24,
            top: WINDOW_TOP + 20,
            fontFamily: "Inter, sans-serif",
            fontSize: 13,
            fontWeight: 500,
            color: "#94A3B8",
            opacity: promptCountOpacity,
            lineHeight: 1.6,
          }}
        >
          <div style={{ color: "#94A3B8", fontSize: 11, marginBottom: 4 }}>
            Per module
          </div>
          <div style={{ color: "#4A90D9" }}>~100 tokens (prompt)</div>
          <div style={{ marginTop: 8, color: "#5AAA6E", fontWeight: 600 }}>
            Total: ~2,000 tokens
          </div>
          <div style={{ marginTop: 2, color: "#64748B", fontSize: 11 }}>
            Window: 4,000 tokens
          </div>
        </div>
      )}
    </div>
  );
};

// ── Compression ratio indicator ──
const CompressionRatio: React.FC = () => {
  const frame = useCurrentFrame();

  // Appears during compression (420–600)
  const opacity = interpolate(
    frame,
    [480, 510, 580, 600],
    [0, 1, 1, 0],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
  );

  if (opacity <= 0.01) return null;

  const scale = interpolate(
    frame,
    [480, 520],
    [0.8, 1],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp", easing: Easing.out(Easing.back(1.2)) }
  );

  return (
    <div
      style={{
        position: "absolute",
        left: 0,
        top: WINDOW_CENTER_Y - 20,
        width: WINDOW_LEFT - 30,
        textAlign: "right",
        fontFamily: "Inter, sans-serif",
        fontSize: 36,
        fontWeight: 800,
        color: "#4A90D9",
        opacity,
        transform: `scale(${scale})`,
        letterSpacing: -1,
      }}
    >
      5-10×
      <div
        style={{
          fontSize: 13,
          fontWeight: 500,
          color: "#94A3B8",
          letterSpacing: 0,
          marginTop: 4,
        }}
      >
        compression
      </div>
    </div>
  );
};

export const defaultPart1Economics12ContextCompressionProps = {};

export const Part1Economics12ContextCompression: React.FC = () => {
  return (
    <AbsoluteFill
      style={{
        backgroundColor: BG_COLOR,
        overflow: "hidden",
      }}
    >
      {/* Context Window frame — draws in from frame 0 */}
      <ContextWindowFrame />

      {/* Module blocks — slide in and later compress */}
      <ModuleBlocks />

      {/* Overflow ghost blocks visible below the window during phase 1 */}
      <OverflowBlocks />

      {/* Red overflow indicator — frame 300–420 */}
      <OverflowIndicator />

      {/* Green remaining space — appears at frame 600 */}
      <RemainingSpace />

      {/* Compression ratio "5-10×" — during morph */}
      <CompressionRatio />

      {/* Token count annotations on the right */}
      <TokenCounts />

      {/* Phase labels at bottom */}
      <PhaseLabels />
    </AbsoluteFill>
  );
};

export default Part1Economics12ContextCompression;
