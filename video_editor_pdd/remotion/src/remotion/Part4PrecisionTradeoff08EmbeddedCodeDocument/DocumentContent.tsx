import React from "react";
import { interpolate, useCurrentFrame, Easing } from "remotion";
import {
  HEADING_COLOR,
  HEADING_SIZE,
  PROSE_COLOR,
  PROSE_OPACITY,
  PROSE_SIZE,
  CODE_BG,
  CODE_BORDER,
  CODE_ACCENT_COLOR,
  CODE_ACCENT_WIDTH,
  CODE_RADIUS,
  CODE_GLOW_COLOR,
  CODE_GLOW_OPACITY,
  CODE_TEXT_COLOR,
  CODE_SIZE,
  DOC_HEADING,
  PROSE_ABOVE_LINES,
  EMBEDDED_CODE_LINES,
  PROSE_BELOW_LINES,
  PROSE_TOP_START,
  PROSE_TOP_END,
  CODE_BLOCK_START,
  CODE_BLOCK_ANIM_END,
  CODE_GLOW_END,
  PROSE_BOTTOM_START,
  PROSE_BOTTOM_END,
} from "./constants";

// ── Helpers ─────────────────────────────────────────────────────────────────

/** Gradually reveal lines: returns how many lines should be visible. */
function visibleLineCount(
  frame: number,
  startFrame: number,
  endFrame: number,
  totalLines: number
): number {
  if (frame < startFrame) return 0;
  if (frame >= endFrame) return totalLines;
  const progress = (frame - startFrame) / (endFrame - startFrame);
  return Math.floor(progress * totalLines);
}

// ── Sub-components ──────────────────────────────────────────────────────────

const Heading: React.FC = () => (
  <div
    style={{
      fontFamily: "Inter, sans-serif",
      fontSize: HEADING_SIZE,
      fontWeight: 700,
      color: HEADING_COLOR,
      marginBottom: 16,
      lineHeight: 1.4,
    }}
  >
    {DOC_HEADING}
  </div>
);

interface ProseBlockProps {
  lines: string[];
  visibleCount: number;
}

const ProseBlock: React.FC<ProseBlockProps> = ({ lines, visibleCount }) => (
  <div
    style={{
      fontFamily: "Inter, sans-serif",
      fontSize: PROSE_SIZE,
      fontWeight: 400,
      color: PROSE_COLOR,
      opacity: PROSE_OPACITY,
      lineHeight: 1.6,
      marginBottom: 20,
      whiteSpace: "pre-wrap",
    }}
  >
    {lines.slice(0, visibleCount).map((line, i) => (
      <React.Fragment key={i}>
        {line}
        {i < visibleCount - 1 ? "\n" : ""}
      </React.Fragment>
    ))}
  </div>
);

interface CodeBlockProps {
  scaleProgress: number;
  glowProgress: number;
}

const CodeBlock: React.FC<CodeBlockProps> = ({
  scaleProgress,
  glowProgress,
}) => {
  const scale = interpolate(scaleProgress, [0, 1], [0.98, 1]);
  const codeOpacity = interpolate(scaleProgress, [0, 1], [0, 1]);
  const glowSpread = interpolate(glowProgress, [0, 1], [0, 8]);
  const glowAlpha = CODE_GLOW_OPACITY * glowProgress;

  return (
    <div
      style={{
        transform: `scale(${scale})`,
        opacity: codeOpacity,
        transformOrigin: "top left",
        background: CODE_BG,
        border: `1px solid ${CODE_BORDER}`,
        borderLeft: `${CODE_ACCENT_WIDTH}px solid ${CODE_ACCENT_COLOR}`,
        borderRadius: CODE_RADIUS,
        padding: "16px 20px",
        marginBottom: 20,
        boxShadow: `0 0 ${glowSpread}px ${CODE_GLOW_COLOR}${Math.round(glowAlpha * 255)
          .toString(16)
          .padStart(2, "0")}`,
      }}
    >
      <pre
        style={{
          fontFamily: "'JetBrains Mono', 'Fira Code', monospace",
          fontSize: CODE_SIZE,
          fontWeight: 400,
          color: CODE_TEXT_COLOR,
          lineHeight: 1.55,
          margin: 0,
          whiteSpace: "pre",
          overflow: "hidden",
        }}
      >
        {EMBEDDED_CODE_LINES.join("\n")}
      </pre>
    </div>
  );
};

// ── Main DocumentContent ────────────────────────────────────────────────────

const DocumentContent: React.FC = () => {
  const frame = useCurrentFrame();

  // Top prose reveal
  const topVisibleCount = visibleLineCount(
    frame,
    PROSE_TOP_START,
    PROSE_TOP_END,
    PROSE_ABOVE_LINES.length
  );

  // Heading visible from frame 0 so there is content immediately
  const headingOpacity = 1;

  // Code block animation
  const codeVisible = frame >= CODE_BLOCK_START;
  const codeScaleProgress = codeVisible
    ? interpolate(
        frame,
        [CODE_BLOCK_START, CODE_BLOCK_ANIM_END],
        [0, 1],
        {
          extrapolateLeft: "clamp",
          extrapolateRight: "clamp",
          easing: Easing.out(Easing.cubic),
        }
      )
    : 0;
  const codeGlowProgress = codeVisible
    ? interpolate(frame, [CODE_BLOCK_START, CODE_GLOW_END], [0, 1], {
        extrapolateLeft: "clamp",
        extrapolateRight: "clamp",
        easing: Easing.out(Easing.quad),
      })
    : 0;

  // Bottom prose reveal
  const bottomVisibleCount = visibleLineCount(
    frame,
    PROSE_BOTTOM_START,
    PROSE_BOTTOM_END,
    PROSE_BELOW_LINES.length
  );

  return (
    <div style={{ width: "100%", height: "100%", overflow: "hidden" }}>
      {/* Heading */}
      <div style={{ opacity: headingOpacity }}>
        <Heading />
      </div>

      {/* Prose above code */}
      {topVisibleCount > 0 && (
        <ProseBlock lines={PROSE_ABOVE_LINES} visibleCount={topVisibleCount} />
      )}

      {/* Embedded code block */}
      {codeVisible && (
        <CodeBlock
          scaleProgress={codeScaleProgress}
          glowProgress={codeGlowProgress}
        />
      )}

      {/* Prose below code */}
      {bottomVisibleCount > 0 && (
        <ProseBlock
          lines={PROSE_BELOW_LINES}
          visibleCount={bottomVisibleCount}
        />
      )}
    </div>
  );
};

export default DocumentContent;
