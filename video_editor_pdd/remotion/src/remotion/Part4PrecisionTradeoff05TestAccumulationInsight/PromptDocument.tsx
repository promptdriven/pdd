import React from 'react';
import { interpolate, useCurrentFrame, Easing } from 'remotion';

interface PromptDocumentProps {
  x: number;
  y: number;
  width: number;
  height: number;
  lineCount: number;
  lineColor: string;
  lineOpacity: number;
  animationStart: number;
  bgColor?: string;
}

export const PromptDocument: React.FC<PromptDocumentProps> = ({
  x,
  y,
  width,
  height,
  lineCount,
  lineColor,
  lineOpacity,
  animationStart,
  bgColor = '#1E293B',
}) => {
  const frame = useCurrentFrame();
  const padding = 10;
  const lineSpacing = (height - padding * 2) / (lineCount + 1);

  // Overall fade in for the document
  const docOpacity = interpolate(
    frame,
    [animationStart, animationStart + 20],
    [0, 1],
    { extrapolateLeft: 'clamp', extrapolateRight: 'clamp', easing: Easing.out(Easing.quad) }
  );

  return (
    <div
      style={{
        position: 'absolute',
        left: x,
        top: y,
        width,
        height,
        backgroundColor: bgColor,
        borderRadius: 4,
        opacity: docOpacity,
        overflow: 'hidden',
      }}
    >
      {Array.from({ length: lineCount }).map((_, i) => {
        // Stagger line drawing: 2 frames per line
        const lineStart = animationStart + 5 + i * 2;
        const lineProgress = interpolate(
          frame,
          [lineStart, lineStart + 8],
          [0, 1],
          { extrapolateLeft: 'clamp', extrapolateRight: 'clamp', easing: Easing.out(Easing.quad) }
        );

        // Vary line widths for realism
        const lineWidth = width - padding * 2 - (i % 3 === 0 ? 20 : i % 2 === 0 ? 10 : 0);

        return (
          <div
            key={i}
            style={{
              position: 'absolute',
              left: padding,
              top: padding + lineSpacing * (i + 1) - 1,
              width: lineWidth * lineProgress,
              height: 2,
              backgroundColor: lineColor,
              opacity: lineOpacity,
              borderRadius: 1,
            }}
          />
        );
      })}
    </div>
  );
};
