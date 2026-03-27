import React from 'react';
import { useCurrentFrame, interpolate, Easing } from 'remotion';
import {
  CANVAS_WIDTH,
  CANVAS_HEIGHT,
  WALL_COLOR,
  WALL_GLOW_MIN,
  WALL_GLOW_MAX,
  WALL_SEGMENT_WIDTH,
  LABEL_FONT_FAMILY,
  LABEL_FONT_SIZE,
  LABEL_FONT_WEIGHT,
  LABEL_TEXT_COLOR,
  LABEL_PILL_COLOR,
  LABEL_PILL_OPACITY,
  LABEL_PILL_RADIUS,
  LABEL_PILL_PADDING_H,
  LABEL_PILL_PADDING_V,
  CONNECTOR_COLOR,
  CONNECTOR_OPACITY,
  CONNECTOR_WIDTH,
  MOLD_INNER_WIDTH,
  MOLD_INNER_HEIGHT,
  SEGMENT_BRIGHTEN_DURATION,
  LABEL_FADE_DURATION,
  CONNECTOR_DRAW_DURATION,
  LABEL_DELAY_AFTER_SEGMENT,
} from './constants';

interface WallSegmentLabelProps {
  /** The label text to display */
  label: string;
  /** Which side the label appears on */
  side: 'left' | 'right';
  /** Frame when this segment starts animating (relative to component's Sequence) */
  segmentIndex: number;
  /** Vertical position offset from center */
  yOffset: number;
}

/**
 * A single wall segment with its connector line and label pill.
 * Animates: segment brightens → connector draws → label fades in.
 */
export const WallSegmentLabel: React.FC<WallSegmentLabelProps> = ({
  label,
  side,
  segmentIndex,
  yOffset,
}) => {
  const frame = useCurrentFrame();

  const cx = CANVAS_WIDTH / 2;
  const cy = CANVAS_HEIGHT / 2;
  const innerHalfW = MOLD_INNER_WIDTH / 2;
  const innerTop = cy - MOLD_INNER_HEIGHT / 2;

  // Wall segment position on the mold wall
  const wallX = side === 'left' ? cx - innerHalfW : cx + innerHalfW;
  const wallY = cy + yOffset;
  const segmentHalfHeight = 50; // Each wall segment spans 100px vertically

  // Segment glow animation (0 → SEGMENT_BRIGHTEN_DURATION frames)
  const segmentGlow = interpolate(
    frame,
    [0, SEGMENT_BRIGHTEN_DURATION],
    [WALL_GLOW_MIN, WALL_GLOW_MAX],
    {
      easing: Easing.out(Easing.quad),
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
    }
  );

  // Connector draw animation (starts after LABEL_DELAY_AFTER_SEGMENT)
  const connectorProgress = interpolate(
    frame,
    [LABEL_DELAY_AFTER_SEGMENT, LABEL_DELAY_AFTER_SEGMENT + CONNECTOR_DRAW_DURATION],
    [0, 1],
    {
      easing: Easing.out(Easing.quad),
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
    }
  );

  // Label fade-in animation (starts after LABEL_DELAY_AFTER_SEGMENT)
  const labelOpacity = interpolate(
    frame,
    [LABEL_DELAY_AFTER_SEGMENT, LABEL_DELAY_AFTER_SEGMENT + LABEL_FADE_DURATION],
    [0, 1],
    {
      easing: Easing.out(Easing.quad),
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
    }
  );

  // Label position: offset from wall
  const labelOffset = 140;
  const labelX = side === 'left' ? wallX - labelOffset : wallX + labelOffset;
  const labelY = wallY;

  // Connector endpoints
  const connectorStartX = wallX;
  const connectorEndX = side === 'left' ? wallX - labelOffset + 60 : wallX + labelOffset - 60;
  const currentEndX =
    connectorStartX + (connectorEndX - connectorStartX) * connectorProgress;

  return (
    <g>
      {/* Wall segment highlight */}
      <line
        x1={wallX}
        y1={wallY - segmentHalfHeight}
        x2={wallX}
        y2={wallY + segmentHalfHeight}
        stroke={WALL_COLOR}
        strokeWidth={WALL_SEGMENT_WIDTH}
        opacity={segmentGlow}
      >
        {/* Glow filter effect */}
      </line>

      {/* Glow overlay for the segment */}
      <line
        x1={wallX}
        y1={wallY - segmentHalfHeight}
        x2={wallX}
        y2={wallY + segmentHalfHeight}
        stroke={WALL_COLOR}
        strokeWidth={8}
        opacity={segmentGlow * 0.3}
        strokeLinecap="round"
      />

      {/* Connector dashed line */}
      <line
        x1={connectorStartX}
        y1={wallY}
        x2={currentEndX}
        y2={wallY}
        stroke={CONNECTOR_COLOR}
        strokeWidth={CONNECTOR_WIDTH}
        strokeDasharray="4 3"
        opacity={CONNECTOR_OPACITY * connectorProgress}
      />

      {/* Label pill */}
      <g opacity={labelOpacity}>
        {/* Pill background */}
        <rect
          x={side === 'left' ? labelX - 80 : labelX - 60}
          y={labelY - 14}
          width={label.length * 8.5 + LABEL_PILL_PADDING_H * 2}
          height={28}
          rx={LABEL_PILL_RADIUS}
          fill={LABEL_PILL_COLOR}
          fillOpacity={LABEL_PILL_OPACITY}
        />

        {/* Label text */}
        <text
          x={side === 'left' ? labelX - 80 + LABEL_PILL_PADDING_H : labelX - 60 + LABEL_PILL_PADDING_H}
          y={labelY + 5}
          fontFamily={LABEL_FONT_FAMILY}
          fontSize={LABEL_FONT_SIZE}
          fontWeight={LABEL_FONT_WEIGHT}
          fill={LABEL_TEXT_COLOR}
        >
          {label}
        </text>
      </g>
    </g>
  );
};
