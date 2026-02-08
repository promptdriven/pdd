import React from "react";
import { AbsoluteFill, interpolate, useCurrentFrame, Easing } from "remotion";
import {
  COLORS,
  BEATS,
  TABLE_ROWS,
  InvestmentTablePropsType,
} from "./constants";

// ── Styles ───────────────────────────────────────────────────────────

const headerCellStyle: React.CSSProperties = {
  padding: "20px 28px",
  fontSize: 26,
  fontWeight: "bold",
  fontFamily: "system-ui, sans-serif",
  color: COLORS.LABEL_WHITE,
  textAlign: "center",
  borderBottom: `1px solid ${COLORS.BORDER}`,
};

const bodyCellStyle: React.CSSProperties = {
  padding: "22px 28px",
  fontSize: 24,
  fontFamily: "system-ui, sans-serif",
  textAlign: "center",
  borderBottom: `1px solid ${COLORS.BORDER}`,
};

// ── Sub-components ───────────────────────────────────────────────────

interface TableRowProps {
  investment: string;
  patching: string;
  pdd: string;
  progress: number;
  pddGlow: number;
  rowIndex: number;
  columnPulseProgress: number;
}

const TableRow: React.FC<TableRowProps> = ({
  investment,
  patching,
  pdd,
  progress,
  pddGlow,
  rowIndex,
  columnPulseProgress,
}) => {
  const slideX = interpolate(progress, [0, 1], [-30, 0]);
  const bgColor = rowIndex % 2 === 0 ? COLORS.ROW_DARK : COLORS.ROW_ALT;

  // Column pulse: each row lights up as the pulse passes through
  const pulsePosition = rowIndex / 3;
  const pulseActive =
    columnPulseProgress > pulsePosition &&
    columnPulseProgress < pulsePosition + 0.5;
  const pulseIntensity = pulseActive
    ? 0.15 * (1 - Math.abs(columnPulseProgress - pulsePosition - 0.25) * 4)
    : 0;

  return (
    <tr
      style={{
        opacity: progress,
        transform: `translateX(${slideX}px)`,
        backgroundColor: bgColor,
      }}
    >
      {/* Investment column */}
      <td
        style={{
          ...bodyCellStyle,
          color: `rgba(255, 255, 255, 0.9)`,
          fontWeight: 500,
          textAlign: "left",
          paddingLeft: 40,
        }}
      >
        {investment}
      </td>

      {/* Patching column (amber tint) */}
      <td
        style={{
          ...bodyCellStyle,
          color: `rgba(217, 148, 74, 0.8)`,
          borderLeft: `1px solid ${COLORS.BORDER}`,
          borderRight: `1px solid ${COLORS.BORDER}`,
        }}
      >
        {patching}
      </td>

      {/* PDD column (blue tint + glow) */}
      <td
        style={{
          ...bodyCellStyle,
          color: `rgba(74, 144, 217, 0.8)`,
          fontWeight: 600,
          backgroundColor: `rgba(74, 144, 217, ${Math.max(pddGlow * 0.2, pulseIntensity)})`,
          boxShadow:
            pddGlow > 0 || pulseIntensity > 0
              ? `inset 0 0 20px rgba(74, 144, 217, ${Math.max(pddGlow * 0.15, pulseIntensity)})`
              : "none",
        }}
      >
        {pdd}
      </td>
    </tr>
  );
};

// ── Main component ───────────────────────────────────────────────────

export const InvestmentTable: React.FC<InvestmentTablePropsType> = () => {
  const frame = useCurrentFrame();

  // Table fade-in
  const tableOpacity = interpolate(
    frame,
    [BEATS.TABLE_FADE_START, BEATS.TABLE_FADE_END],
    [0, 1],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.out(Easing.cubic),
    },
  );

  // Row slide-in progress (0 to 1 each)
  const row1Progress = interpolate(
    frame,
    [BEATS.ROW1_START, BEATS.ROW1_END],
    [0, 1],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.out(Easing.cubic),
    },
  );
  const row2Progress = interpolate(
    frame,
    [BEATS.ROW2_START, BEATS.ROW2_END],
    [0, 1],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.out(Easing.cubic),
    },
  );
  const row3Progress = interpolate(
    frame,
    [BEATS.ROW3_START, BEATS.ROW3_END],
    [0, 1],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.out(Easing.cubic),
    },
  );

  // PDD cell glow pulses (brief glow per row after it appears)
  const pddGlow1 = interpolate(
    frame,
    [BEATS.ROW1_END - 10, BEATS.ROW1_END + 10, BEATS.ROW1_END + 40],
    [0, 1, 0],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp" },
  );
  const pddGlow2 = interpolate(
    frame,
    [BEATS.ROW2_END - 10, BEATS.ROW2_END + 10, BEATS.ROW2_END + 40],
    [0, 1, 0],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp" },
  );
  const pddGlow3 = interpolate(
    frame,
    [BEATS.ROW3_END - 10, BEATS.ROW3_END + 10, BEATS.ROW3_END + 40],
    [0, 1, 0],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp" },
  );

  // Column-wide pulse
  const columnPulseProgress = interpolate(
    frame,
    [BEATS.PULSE_START, BEATS.PULSE_END],
    [0, 1],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.inOut(Easing.quad),
    },
  );

  const rowProgresses = [row1Progress, row2Progress, row3Progress];
  const pddGlows = [pddGlow1, pddGlow2, pddGlow3];

  return (
    <AbsoluteFill style={{ backgroundColor: COLORS.BACKGROUND }}>
      <div
        style={{
          opacity: tableOpacity,
          position: "absolute",
          left: "50%",
          top: "50%",
          transform: "translate(-50%, -50%)",
          width: 1200,
        }}
      >
        <table
          style={{
            width: "100%",
            borderCollapse: "separate",
            borderSpacing: 0,
            borderRadius: 8,
            overflow: "hidden",
            border: `1px solid ${COLORS.BORDER_OUTER}`,
          }}
        >
          <thead>
            <tr style={{ backgroundColor: COLORS.HEADER_BG }}>
              <th
                style={{
                  ...headerCellStyle,
                  textAlign: "left",
                  paddingLeft: 40,
                  width: "25%",
                }}
              >
                Investment
              </th>
              <th
                style={{
                  ...headerCellStyle,
                  width: "37.5%",
                  borderBottom: `3px solid ${COLORS.PATCHING_AMBER}`,
                  borderLeft: `1px solid ${COLORS.BORDER}`,
                  borderRight: `1px solid ${COLORS.BORDER}`,
                }}
              >
                Return (Patching)
              </th>
              <th
                style={{
                  ...headerCellStyle,
                  width: "37.5%",
                  borderBottom: `3px solid ${COLORS.PDD_BLUE}`,
                }}
              >
                Return (PDD)
              </th>
            </tr>
          </thead>
          <tbody>
            {TABLE_ROWS.map((row, i) => (
              <TableRow
                key={i}
                investment={row.investment}
                patching={row.patching}
                pdd={row.pdd}
                progress={rowProgresses[i]}
                pddGlow={pddGlows[i]}
                rowIndex={i}
                columnPulseProgress={columnPulseProgress}
              />
            ))}
          </tbody>
        </table>
      </div>
    </AbsoluteFill>
  );
};
