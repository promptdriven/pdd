import React from 'react';
import { useCurrentFrame, interpolate, Easing } from 'remotion';
import {
  LABEL_FONT_FAMILY,
  LABEL_FONT_SIZE,
  LABEL_FONT_WEIGHT,
  LABEL_TEXT_COLOR,
  LABEL_PILL_COLOR,
  LABEL_PILL_OPACITY,
  LABEL_PILL_RADIUS,
  LABEL_PILL_PADDING_H,
  LABEL_CONNECTOR_COLOR,
  LABEL_CONNECTOR_OPACITY,
  LABEL_FADE_DURATION,
  CONNECTOR_DRAW_DURATION,
  WALL_SEGMENT_POSITIONS,
  CANVAS_WIDTH,
  CANVAS_HEIGHT,
} from './constants';

interface WallLabelProps {
  text: string;
  side: 'left' | 'right';
  segmentIndex: number;
}

/**
 * Renders a connector line + label pill for a wall segment.
 * Must be placed inside a <Sequence> so that useCurrentFrame()
 * returns the local frame relative to the label's appearance time.
 */
export const WallLabel: React.FC<WallLabelProps> = ({
  text,
  side,
  segmentIndex,
}) => {
  const localFrame = useCurrentFrame();
  const seg = WALL_SEGMENT_POSITIONS[segmentIndex];

  // Connector draws over CONNECTOR_DRAW_DURATION frames
  const connectorProgress = interpolate(
    localFrame,
    [0, CONNECTOR_DRAW_DURATION],
    [0, 1],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.out(Easing.quad),
    }
  );

  // Label text fades in over LABEL_FADE_DURATION frames,
  // starting 5 frames after the connector begins (handled by parent offset)
  const labelOpacity = interpolate(
    localFrame,
    [0, LABEL_FADE_DURATION],
    [0, 1],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.out(Easing.quad),
    }
  );

  // Connector geometry
  const connectorLength = 120;
  const connStartX = seg.labelAnchorX;
  const connStartY = seg.labelAnchorY;
  const connEndX =
    connStartX + (side === 'left' ? -connectorLength : connectorLength);

  // Animated connector endpoint
  const currentEndX = interpolate(
    connectorProgress,
    [0, 1],
    [connStartX, connEndX]
  );

  // Label pill sizing
  const pillWidth = text.length * 8.5 + LABEL_PILL_PADDING_H * 2 + 8;
  const pillHeight = 28;
  const pillX = side === 'left' ? connEndX - pillWidth - 4 : connEndX + 4;
  const pillY = connStartY - pillHeight / 2;

  return (
    <svg
      width={CANVAS_WIDTH}
      height={CANVAS_HEIGHT}
      style={{ position: 'absolute', top: 0, left: 0, pointerEvents: 'none' }}
    >
      {/* Dashed connector line */}
      <line
        x1={connStartX}
        y1={connStartY}
        x2={currentEndX}
        y2={connStartY}
        stroke={LABEL_CONNECTOR_COLOR}
        strokeWidth={1}
        strokeDasharray="4 3"
        opacity={LABEL_CONNECTOR_OPACITY * connectorProgress}
      />

      {/* Dot at wall anchor point */}
      <circle
        cx={connStartX}
        cy={connStartY}
        r={3}
        fill={LABEL_CONNECTOR_COLOR}
        opacity={LABEL_CONNECTOR_OPACITY * connectorProgress}
      />

      {/* Label pill background */}
      <rect
        x={pillX}
        y={pillY}
        width={pillWidth}
        height={pillHeight}
        fill={LABEL_PILL_COLOR}
        opacity={LABEL_PILL_OPACITY * labelOpacity}
        rx={LABEL_PILL_RADIUS}
        ry={LABEL_PILL_RADIUS}
      />

      {/* Label pill border */}
      <rect
        x={pillX}
        y={pillY}
        width={pillWidth}
        height={pillHeight}
        fill="none"
        stroke={LABEL_PILL_COLOR}
        strokeWidth={1}
        opacity={0.25 * labelOpacity}
        rx={LABEL_PILL_RADIUS}
        ry={LABEL_PILL_RADIUS}
      />

      {/* Label text */}
      <text
        x={pillX + pillWidth / 2}
        y={pillY + pillHeight / 2 + 1}
        fill={LABEL_TEXT_COLOR}
        fontFamily={LABEL_FONT_FAMILY}
        fontSize={LABEL_FONT_SIZE}
        fontWeight={LABEL_FONT_WEIGHT}
        textAnchor="middle"
        dominantBaseline="middle"
        opacity={labelOpacity}
      >
        {text}
      </text>
    </svg>
  );
};
