/**
 * DrawLine – a horizontal rule that draws outward from its center.
 * Used for the decorative rules above and below the text.
 */
import React from 'react';
import { useCurrentFrame, interpolate, Easing } from 'remotion';

interface DrawLineProps {
  /** Y position of the line */
  y: number;
  /** Total width the line should reach */
  lineWidth: number;
  /** Line thickness */
  thickness: number;
  /** Line color (CSS) */
  color: string;
  /** Line opacity (0-1) */
  lineOpacity: number;
  /** Frame at which drawing starts (absolute) */
  startFrame: number;
  /** Number of frames for the draw animation */
  drawDuration: number;
  /** Frame at which overall fade-out begins (absolute) */
  fadeOutStart: number;
  /** Duration of the fade-out in frames */
  fadeOutDuration: number;
  /** Canvas width for centering */
  canvasWidth: number;
}

const DrawLine: React.FC<DrawLineProps> = ({
  y,
  lineWidth,
  thickness,
  color,
  lineOpacity,
  startFrame,
  drawDuration,
  fadeOutStart,
  fadeOutDuration,
  canvasWidth,
}) => {
  const frame = useCurrentFrame();

  // Draw progress: 0 → 1 over drawDuration starting at startFrame
  const drawProgress = interpolate(
    frame,
    [startFrame, startFrame + drawDuration],
    [0, 1],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.inOut(Easing.quad),
    },
  );

  // Fade-out opacity
  const fadeOutOpacity = interpolate(
    frame,
    [fadeOutStart, fadeOutStart + fadeOutDuration],
    [1, 0],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.in(Easing.quad),
    },
  );

  const currentWidth = lineWidth * drawProgress;
  const leftOffset = (canvasWidth - currentWidth) / 2;

  return (
    <div
      style={{
        position: 'absolute',
        top: y,
        left: leftOffset,
        width: currentWidth,
        height: thickness,
        backgroundColor: color,
        opacity: lineOpacity * fadeOutOpacity,
      }}
    />
  );
};

export default DrawLine;
