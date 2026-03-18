import React from "react";
import { interpolate, useCurrentFrame, Easing } from "remotion";
import { getIcon } from "./IconGlyphs";
import {
  COL_WIDTH,
  ROW_HEIGHT,
  CELL_PADDING,
  TEXT_COLOR,
  PATCHING_COLOR,
  PDD_COLOR,
  TABLE_BG,
  ROW_SLIDE_DURATION,
  CELL_STAGGER,
  GLOW_DURATION,
  PULSE_START,
  PULSE_DURATION,
} from "./constants";

interface TableRowProps {
  investment: string;
  icon: string;
  patching: string;
  pdd: string;
  pddGlow: number;
  pddOpacity: number;
  alternate: boolean;
  /** The absolute frame at which this row starts appearing */
  rowStart: number;
}

export const TableRow: React.FC<TableRowProps> = ({
  investment,
  icon,
  patching,
  pdd,
  pddGlow,
  pddOpacity,
  alternate,
  rowStart,
}) => {
  const frame = useCurrentFrame();
  const relFrame = frame - rowStart;

  // Row slide in from bottom
  const slideY = interpolate(relFrame, [0, ROW_SLIDE_DURATION], [15, 0], {
    easing: Easing.out(Easing.cubic),
    extrapolateLeft: "clamp",
    extrapolateRight: "clamp",
  });

  const rowOpacity = interpolate(relFrame, [0, ROW_SLIDE_DURATION], [0, 1], {
    easing: Easing.out(Easing.quad),
    extrapolateLeft: "clamp",
    extrapolateRight: "clamp",
  });

  // Patching cell staggered appearance
  const patchingOpacity = interpolate(
    relFrame,
    [CELL_STAGGER, CELL_STAGGER + ROW_SLIDE_DURATION],
    [0, 0.6],
    {
      easing: Easing.out(Easing.quad),
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
    }
  );

  // PDD cell staggered appearance
  const pddCellOpacity = interpolate(
    relFrame,
    [CELL_STAGGER * 2, CELL_STAGGER * 2 + GLOW_DURATION],
    [0, pddOpacity],
    {
      easing: Easing.out(Easing.quad),
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
    }
  );

  // PDD glow background
  const pddGlowOpacity = interpolate(
    relFrame,
    [CELL_STAGGER * 2, CELL_STAGGER * 2 + GLOW_DURATION],
    [0, pddGlow],
    {
      easing: Easing.out(Easing.quad),
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
    }
  );

  // PDD pulse (all rows pulse together at PULSE_START)
  const pulseRelFrame = frame - PULSE_START;
  const pulseOpacityDelta =
    pulseRelFrame >= 0 && pulseRelFrame <= PULSE_DURATION
      ? interpolate(
          pulseRelFrame,
          [0, PULSE_DURATION / 2, PULSE_DURATION],
          [0, 0.1, 0],
          {
            easing: Easing.inOut(Easing.sin),
            extrapolateLeft: "clamp",
            extrapolateRight: "clamp",
          }
        )
      : 0;

  // PDD glow pulse
  const pulseGlowDelta =
    pulseRelFrame >= 0 && pulseRelFrame <= PULSE_DURATION
      ? interpolate(
          pulseRelFrame,
          [0, PULSE_DURATION / 2, PULSE_DURATION],
          [0, 0.04, 0],
          {
            easing: Easing.inOut(Easing.sin),
            extrapolateLeft: "clamp",
            extrapolateRight: "clamp",
          }
        )
      : 0;

  if (relFrame < 0) return null;

  const bgColor = alternate
    ? `rgba(17, 24, 39, 0.3)`
    : TABLE_BG;

  return (
    <div
      style={{
        display: "flex",
        width: "100%",
        height: ROW_HEIGHT,
        background: bgColor,
        borderBottom: `1px solid rgba(30, 41, 59, 0.3)`,
        transform: `translateY(${slideY}px)`,
        opacity: rowOpacity,
      }}
    >
      {/* Investment cell */}
      <div
        style={{
          width: COL_WIDTH,
          height: ROW_HEIGHT,
          display: "flex",
          alignItems: "center",
          paddingLeft: CELL_PADDING,
          boxSizing: "border-box",
        }}
      >
        {getIcon(icon)}
        <span
          style={{
            fontFamily: "Inter, sans-serif",
            fontSize: 16,
            color: TEXT_COLOR,
            fontWeight: 400,
          }}
        >
          {investment}
        </span>
      </div>

      {/* Patching cell */}
      <div
        style={{
          width: COL_WIDTH,
          height: ROW_HEIGHT,
          display: "flex",
          alignItems: "center",
          justifyContent: "center",
          boxSizing: "border-box",
        }}
      >
        <span
          style={{
            fontFamily: "Inter, sans-serif",
            fontSize: 15,
            color: PATCHING_COLOR,
            opacity: patchingOpacity,
            fontWeight: 400,
          }}
        >
          {patching}
        </span>
      </div>

      {/* PDD cell */}
      <div
        style={{
          width: COL_WIDTH,
          height: ROW_HEIGHT,
          display: "flex",
          alignItems: "center",
          justifyContent: "center",
          boxSizing: "border-box",
          position: "relative",
        }}
      >
        {/* Glow background */}
        <div
          style={{
            position: "absolute",
            inset: 4,
            borderRadius: 6,
            backgroundColor: PDD_COLOR,
            opacity: pddGlowOpacity + pulseGlowDelta,
          }}
        />
        <span
          style={{
            fontFamily: "Inter, sans-serif",
            fontSize: 15,
            color: PDD_COLOR,
            opacity: pddCellOpacity + pulseOpacityDelta,
            fontWeight: 600,
            position: "relative",
            zIndex: 1,
          }}
        >
          {pdd}
        </span>
      </div>
    </div>
  );
};
