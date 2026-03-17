import React from "react";
import { useCurrentFrame, interpolate, Easing } from "remotion";
import {
  WIDTH,
  HEIGHT,
  GRID_X,
  GRID_Y,
  GRID_W,
  GRID_H,
  GRID_CENTER_X,
  GRID_CENTER_Y,
  GRID_RIGHT,
  GRID_BOTTOM,
  BORDER_COLOR,
  GREEN,
  RED,
  FONT_FAMILY,
  GRID_DRAW_START,
  GRID_DRAW_END,
} from "./constants";

export const QuadrantGrid: React.FC = () => {
  const frame = useCurrentFrame();

  const drawProgress = interpolate(
    frame,
    [GRID_DRAW_START, GRID_DRAW_END],
    [0, 1],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.out(Easing.cubic),
    }
  );

  const labelOpacity = interpolate(
    frame,
    [GRID_DRAW_START + 20, GRID_DRAW_END],
    [0, 0.6],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.out(Easing.cubic),
    }
  );

  // Border perimeter for stroke-dashoffset animation
  const borderPerimeter = 2 * (GRID_W + GRID_H);
  const borderOffset = borderPerimeter * (1 - drawProgress);

  // Vertical divider: from center top to center bottom
  const vertDividerLength = GRID_H;
  const vertOffset = vertDividerLength * (1 - drawProgress);

  // Horizontal divider: from center left to center right
  const horizDividerLength = GRID_W;
  const horizOffset = horizDividerLength * (1 - drawProgress);

  return (
    <svg
      width={WIDTH}
      height={HEIGHT}
      viewBox={`0 0 ${WIDTH} ${HEIGHT}`}
      style={{ position: "absolute", top: 0, left: 0 }}
    >
      {/* Outer border */}
      <rect
        x={GRID_X}
        y={GRID_Y}
        width={GRID_W}
        height={GRID_H}
        fill="none"
        stroke={BORDER_COLOR}
        strokeWidth={2}
        opacity={0.3}
        strokeDasharray={`${borderPerimeter} ${borderPerimeter}`}
        strokeDashoffset={borderOffset}
      />

      {/* Vertical divider */}
      <line
        x1={GRID_CENTER_X}
        y1={GRID_Y}
        x2={GRID_CENTER_X}
        y2={GRID_BOTTOM}
        stroke={BORDER_COLOR}
        strokeWidth={1}
        opacity={0.2}
        strokeDasharray={`${vertDividerLength} ${vertDividerLength}`}
        strokeDashoffset={vertOffset}
      />

      {/* Horizontal divider */}
      <line
        x1={GRID_X}
        y1={GRID_CENTER_Y}
        x2={GRID_RIGHT}
        y2={GRID_CENTER_Y}
        stroke={BORDER_COLOR}
        strokeWidth={1}
        opacity={0.2}
        strokeDasharray={`${horizDividerLength} ${horizDividerLength}`}
        strokeDashoffset={horizOffset}
      />

      {/* X-axis labels */}
      <text
        x={GRID_X}
        y={GRID_BOTTOM + 30}
        fill={GREEN}
        fontSize={14}
        fontFamily={FONT_FAMILY}
        fontWeight={600}
        opacity={labelOpacity}
        textAnchor="start"
      >
        Greenfield
      </text>
      <text
        x={GRID_RIGHT}
        y={GRID_BOTTOM + 30}
        fill={RED}
        fontSize={14}
        fontFamily={FONT_FAMILY}
        fontWeight={600}
        opacity={labelOpacity}
        textAnchor="end"
      >
        Brownfield
      </text>

      {/* X-axis arrow */}
      <line
        x1={GRID_X + 90}
        y1={GRID_BOTTOM + 26}
        x2={GRID_RIGHT - 90}
        y2={GRID_BOTTOM + 26}
        stroke={BORDER_COLOR}
        strokeWidth={1}
        opacity={labelOpacity * 0.4}
        markerEnd="url(#arrowRight)"
      />
      <defs>
        <marker
          id="arrowRight"
          markerWidth={8}
          markerHeight={6}
          refX={8}
          refY={3}
          orient="auto"
        >
          <path d="M0,0 L8,3 L0,6" fill={BORDER_COLOR} opacity={0.4} />
        </marker>
        <marker
          id="arrowDown"
          markerWidth={6}
          markerHeight={8}
          refX={3}
          refY={8}
          orient="auto"
        >
          <path d="M0,0 L3,8 L6,0" fill={BORDER_COLOR} opacity={0.4} />
        </marker>
      </defs>

      {/* Y-axis labels */}
      <text
        x={GRID_X - 15}
        y={GRID_Y + 10}
        fill={GREEN}
        fontSize={14}
        fontFamily={FONT_FAMILY}
        fontWeight={600}
        opacity={labelOpacity}
        textAnchor="end"
        dominantBaseline="middle"
      >
        In-Distribution
      </text>
      <text
        x={GRID_X - 15}
        y={GRID_BOTTOM - 10}
        fill={RED}
        fontSize={14}
        fontFamily={FONT_FAMILY}
        fontWeight={600}
        opacity={labelOpacity}
        textAnchor="end"
        dominantBaseline="middle"
      >
        Out-of-Distribution
      </text>

      {/* Y-axis arrow */}
      <line
        x1={GRID_X - 15}
        y1={GRID_Y + 25}
        x2={GRID_X - 15}
        y2={GRID_BOTTOM - 25}
        stroke={BORDER_COLOR}
        strokeWidth={1}
        opacity={labelOpacity * 0.4}
        markerEnd="url(#arrowDown)"
      />
    </svg>
  );
};
