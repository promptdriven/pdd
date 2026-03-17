import React from 'react';

interface PromptDocumentProps {
  lineCount: number;
  width: number;
  height: number;
  color: string;
}

/**
 * A miniature "prompt document" icon — a rounded rect with horizontal lines inside.
 */
export const PromptDocument: React.FC<PromptDocumentProps> = ({
  lineCount,
  width,
  height,
  color,
}) => {
  const padding = 6;
  const lineSpacing = (height - padding * 2) / Math.max(lineCount, 1);
  const clampedCount = Math.round(Math.max(1, Math.min(lineCount, 25)));

  return (
    <svg width={width} height={height} viewBox={`0 0 ${width} ${height}`}>
      {/* Document outline */}
      <rect
        x={1}
        y={1}
        width={width - 2}
        height={height - 2}
        rx={4}
        fill="none"
        stroke={color}
        strokeWidth={1.5}
        opacity={0.6}
      />
      {/* Lines */}
      {Array.from({ length: clampedCount }).map((_, i) => {
        const y = padding + i * lineSpacing + lineSpacing * 0.5;
        if (y > height - padding) return null;
        // Vary line widths for realism
        const lineWidth = width - padding * 2 - (i % 3 === 2 ? 10 : i % 2 === 0 ? 0 : 5);
        return (
          <rect
            key={i}
            x={padding}
            y={y}
            width={Math.max(lineWidth, 4)}
            height={1.5}
            rx={0.75}
            fill={color}
            opacity={0.5}
          />
        );
      })}
    </svg>
  );
};

export default PromptDocument;
