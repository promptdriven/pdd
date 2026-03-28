import React from "react";
import { interpolate, useCurrentFrame, Easing } from "remotion";

interface TestIndicatorsProps {
  count: number;
  dotSize: number;
  color: string;
  dotOpacity: number;
  /** Center x of the prompt file the tests surround */
  centerX: number;
  /** Top y of the prompt file */
  topY: number;
  /** Width of the prompt file */
  promptW: number;
  /** Height of the prompt file */
  promptH: number;
  appearStart: number;
  fadeDuration: number;
}

const TestIndicators: React.FC<TestIndicatorsProps> = ({
  count,
  dotSize,
  color,
  dotOpacity,
  centerX,
  topY,
  promptW,
  promptH,
  appearStart,
  fadeDuration,
}) => {
  const frame = useCurrentFrame();

  const opacity = interpolate(
    frame,
    [appearStart, appearStart + fadeDuration],
    [0, 1],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.out(Easing.quad),
    }
  );

  // Generate positions around the prompt file
  const gap = 3;
  const margin = 12; // space between prompt edge and dots
  const left = centerX - promptW / 2 - margin;
  const right = centerX + promptW / 2 + margin;
  const top = topY - margin;
  const bottom = topY + promptH + margin;

  const positions: { x: number; y: number }[] = [];
  const step = dotSize + gap;

  // Top row
  for (let x = left; x <= right && positions.length < count; x += step) {
    positions.push({ x, y: top });
  }
  // Right column
  for (
    let y = top + step;
    y <= bottom - step && positions.length < count;
    y += step
  ) {
    positions.push({ x: right, y });
  }
  // Bottom row (right to left)
  for (let x = right; x >= left && positions.length < count; x -= step) {
    positions.push({ x, y: bottom });
  }
  // Left column (bottom to top)
  for (
    let y = bottom - step;
    y >= top + step && positions.length < count;
    y -= step
  ) {
    positions.push({ x: left, y });
  }

  // If still more to place, add a second ring
  const outerMargin = margin + step + 4;
  const outerLeft = centerX - promptW / 2 - outerMargin;
  const outerRight = centerX + promptW / 2 + outerMargin;
  const outerTop = topY - outerMargin;
  const outerBottom = topY + promptH + outerMargin;

  // Top outer
  for (
    let x = outerLeft;
    x <= outerRight && positions.length < count;
    x += step
  ) {
    positions.push({ x, y: outerTop });
  }
  // Right outer
  for (
    let y = outerTop + step;
    y <= outerBottom && positions.length < count;
    y += step
  ) {
    positions.push({ x: outerRight, y });
  }
  // Bottom outer
  for (
    let x = outerRight;
    x >= outerLeft && positions.length < count;
    x -= step
  ) {
    positions.push({ x, y: outerBottom });
  }
  // Left outer
  for (
    let y = outerBottom - step;
    y >= outerTop + step && positions.length < count;
    y -= step
  ) {
    positions.push({ x: outerLeft, y });
  }

  return (
    <div style={{ opacity }}>
      {positions.slice(0, count).map((pos, i) => (
        <div
          key={i}
          style={{
            position: "absolute",
            left: pos.x,
            top: pos.y,
            width: dotSize,
            height: dotSize,
            backgroundColor: color,
            opacity: dotOpacity,
            borderRadius: 1,
          }}
        />
      ))}
    </div>
  );
};

export default TestIndicators;
