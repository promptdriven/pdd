import React from "react";
import { useCurrentFrame, interpolate, Easing, interpolateColors } from "remotion";
import { BEATS, COLORS, VERILOG_BLOCK, VERILOG_SOURCE, VERILOG_KEYWORDS } from "./constants";

/**
 * Renders Verilog code that morphs into a prompt document.
 * LEFT side (setup): Teal-colored Verilog code block from chip design context.
 * Morph: Code block reshapes and moves to RIGHT side, becomes white document.
 * RIGHT side (final): White prompt document with blue glow.
 */

// Syntax highlighting helper
const highlightVerilog = (source: string): React.ReactNode[] => {
  const lines = source.split("\n");
  return lines.map((line, lineIdx) => {
    const tokens: React.ReactNode[] = [];
    let remaining = line;
    let tokenIdx = 0;

    while (remaining.length > 0) {
      // Check for keywords
      let matched = false;
      for (const keyword of VERILOG_KEYWORDS) {
        if (
          remaining.startsWith(keyword) &&
          (remaining.length === keyword.length ||
            /\W/.test(remaining[keyword.length]))
        ) {
          tokens.push(
            <tspan key={`${lineIdx}-${tokenIdx}`} fill={COLORS.VERILOG_KEYWORD}>
              {keyword}
            </tspan>
          );
          remaining = remaining.slice(keyword.length);
          tokenIdx++;
          matched = true;
          break;
        }
      }
      if (matched) continue;

      // Check for numbers
      const numMatch = remaining.match(/^(\d+'b[01]+|\d+)/);
      if (numMatch) {
        tokens.push(
          <tspan key={`${lineIdx}-${tokenIdx}`} fill={COLORS.VERILOG_NUMBER}>
            {numMatch[0]}
          </tspan>
        );
        remaining = remaining.slice(numMatch[0].length);
        tokenIdx++;
        continue;
      }

      // Default: identifier
      tokens.push(
        <tspan key={`${lineIdx}-${tokenIdx}`} fill={COLORS.VERILOG_IDENTIFIER}>
          {remaining[0]}
        </tspan>
      );
      remaining = remaining.slice(1);
      tokenIdx++;
    }

    return { lineIdx, tokens: tokens.length > 0 ? tokens : ["\u00A0"] };
  });
};

export const VerilogBlock: React.FC = () => {
  const frame = useCurrentFrame();

  // Morph progress
  const morphProgress = interpolate(
    frame,
    [BEATS.MORPH_START, BEATS.MORPH_END],
    [0, 1],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.inOut(Easing.cubic),
    }
  );

  // Interpolate shape dimensions (LEFT → RIGHT)
  const x = interpolate(morphProgress, [0, 1], [VERILOG_BLOCK.initialX, VERILOG_BLOCK.finalX]);
  const y = interpolate(morphProgress, [0, 1], [VERILOG_BLOCK.initialY, VERILOG_BLOCK.finalY]);
  const width = interpolate(morphProgress, [0, 1], [VERILOG_BLOCK.initialWidth, VERILOG_BLOCK.finalWidth]);
  const height = interpolate(morphProgress, [0, 1], [VERILOG_BLOCK.initialHeight, VERILOG_BLOCK.finalHeight]);

  // Color transition: dark teal code background → white document
  const colorProgress = interpolate(
    frame,
    [BEATS.MORPH_START, BEATS.MORPH_END],
    [0, 1],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.out(Easing.quad),
    }
  );

  const bgColor = interpolateColors(
    colorProgress,
    [0, 1],
    [COLORS.CODE_BG, COLORS.PROMPT_BG]
  );

  const borderColor = interpolateColors(
    colorProgress,
    [0, 1],
    ["rgba(42, 161, 152, 0.3)", COLORS.PROMPT_BORDER]
  );

  // Verilog code visibility (fades out during morph)
  const codeOpacity = interpolate(
    morphProgress,
    [0, 0.5],
    [1, 0],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
    }
  );

  // Blue glow appears during labels phase
  const glowOpacity = interpolate(
    frame,
    [BEATS.LABELS_START, BEATS.LABELS_END],
    [0, 1],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.out(Easing.quad),
    }
  );

  // Document divider line (appears as morph completes)
  const dividerOpacity = interpolate(
    morphProgress,
    [0.7, 1],
    [0, 1],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
    }
  );

  const highlightedLines = highlightVerilog(VERILOG_SOURCE);

  return (
    <>
      <defs>
        <filter id="verilogPromptGlow" x="-30%" y="-30%" width="160%" height="160%">
          <feGaussianBlur stdDeviation="10" result="blur" />
          <feMerge>
            <feMergeNode in="blur" />
            <feMergeNode in="SourceGraphic" />
          </feMerge>
        </filter>
      </defs>

      {/* Blue glow layer (behind the document) */}
      {glowOpacity > 0 && (
        <rect
          x={x - 12}
          y={y - 12}
          width={width + 24}
          height={height + 24}
          rx={12}
          fill="none"
          stroke={COLORS.PROMPT_GLOW}
          strokeWidth={4}
          opacity={glowOpacity * 0.7}
          filter="url(#verilogPromptGlow)"
        />
      )}

      {/* Main shape: Verilog code block → Prompt document */}
      <rect
        x={x}
        y={y}
        width={width}
        height={height}
        rx={8}
        fill={bgColor}
        stroke={borderColor}
        strokeWidth={1}
      />

      {/* Verilog code text (visible during setup, fades during morph) */}
      {codeOpacity > 0 && (
        <g opacity={codeOpacity}>
          {highlightedLines.map(({ lineIdx, tokens }) => (
            <text
              key={lineIdx}
              x={x + 16}
              y={y + 26 + lineIdx * 18}
              fontSize={14}
              fontFamily="'JetBrains Mono', 'Fira Code', monospace"
              fontWeight={400}
            >
              {tokens}
            </text>
          ))}
        </g>
      )}

      {/* Document divider line (below title area) */}
      {dividerOpacity > 0 && (
        <line
          x1={x + 20}
          y1={y + 60}
          x2={x + width - 20}
          y2={y + 60}
          stroke={COLORS.PROMPT_BORDER}
          strokeWidth={1}
          opacity={dividerOpacity}
        />
      )}
    </>
  );
};
