import React from "react";
import { AbsoluteFill, useCurrentFrame, interpolate, Easing } from "remotion";
import { FlowStageIcon, StageIconType } from "./FlowStageIcon";
import { FlowArrow } from "./FlowArrow";
import { DashedConnection } from "./DashedConnection";
import { EquivalenceSymbol } from "./EquivalenceSymbol";
import {
  BG_COLOR,
  UI_FONT,
  ROW_LABEL_SIZE,
  SUMMARY_SIZE,
  TEXT_COLOR,
  SYNOPSYS_COLOR,
  SYNOPSYS_OPACITY,
  PDD_COLOR,
  PDD_OPACITY,
  NEUTRAL_COLOR,
  NEUTRAL_OPACITY,
  VERIFY_COLOR,
  VERIFY_OPACITY,
  SYNOPSYS_LABEL_OPACITY,
  PDD_LABEL_OPACITY,
  TOP_ROW_Y,
  BOTTOM_ROW_Y,
  STAGE_X,
  ROW_LABEL_X,
  LABEL_FADE_START,
  LABEL_FADE_END,
  TOP_ROW_START,
  BOTTOM_ROW_START,
  STAGE_FADE_DURATION,
  STAGE_STAGGER,
  ARROW_DRAW_DURATION,
  DASHED_START,
  DASHED_DRAW_DURATION,
  DASHED_STAGGER,
  SUMMARY_FADE_START,
  SUMMARY_FADE_DURATION,
  SUMMARY_Y,
  CANVAS_WIDTH,
} from "./constants";

export const defaultPart2ParadigmShift08SynopsysPddEquivalenceProps = {};

interface StageConfig {
  label: string;
  iconType: StageIconType;
  x: number;
  color: string;
  opacity: number;
}

const synopsysStages: StageConfig[] = [
  { label: "Verilog spec", iconType: "document_code", x: STAGE_X[0], color: SYNOPSYS_COLOR, opacity: SYNOPSYS_OPACITY },
  { label: "Synthesis", iconType: "gear", x: STAGE_X[1], color: SYNOPSYS_COLOR, opacity: SYNOPSYS_OPACITY },
  { label: "Hardware", iconType: "gate_cluster", x: STAGE_X[2], color: NEUTRAL_COLOR, opacity: NEUTRAL_OPACITY },
  { label: "FEC verified", iconType: "shield_check", x: STAGE_X[3], color: VERIFY_COLOR, opacity: VERIFY_OPACITY },
];

const pddStages: StageConfig[] = [
  { label: "Prompt spec", iconType: "document_text", x: STAGE_X[0], color: PDD_COLOR, opacity: PDD_OPACITY },
  { label: "Generation", iconType: "neural_network", x: STAGE_X[1], color: PDD_COLOR, opacity: PDD_OPACITY },
  { label: "Software", iconType: "code_brackets", x: STAGE_X[2], color: NEUTRAL_COLOR, opacity: NEUTRAL_OPACITY },
  { label: "Tests pass", iconType: "shield_check", x: STAGE_X[3], color: VERIFY_COLOR, opacity: VERIFY_OPACITY },
];

// Arrow endpoints: between each pair of stages
const arrowGaps = [
  { from: STAGE_X[0] + 50, to: STAGE_X[1] - 40 },
  { from: STAGE_X[1] + 40, to: STAGE_X[2] - 50 },
  { from: STAGE_X[2] + 50, to: STAGE_X[3] - 35 },
];

export const Part2ParadigmShift08SynopsysPddEquivalence: React.FC = () => {
  const frame = useCurrentFrame();

  // Row label fade-in
  const labelOpacity = interpolate(
    frame,
    [LABEL_FADE_START, LABEL_FADE_END],
    [0, 1],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp", easing: Easing.out(Easing.quad) }
  );

  // Summary fade-in
  const summaryOpacity = interpolate(
    frame,
    [SUMMARY_FADE_START, SUMMARY_FADE_START + SUMMARY_FADE_DURATION],
    [0, 0.6],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp", easing: Easing.out(Easing.quad) }
  );

  return (
    <AbsoluteFill style={{ backgroundColor: BG_COLOR }}>
      {/* Row label: SYNOPSYS */}
      <div
        style={{
          position: "absolute",
          left: ROW_LABEL_X,
          top: TOP_ROW_Y - 8,
          fontFamily: UI_FONT,
          fontSize: ROW_LABEL_SIZE,
          fontWeight: 600,
          color: SYNOPSYS_COLOR,
          opacity: labelOpacity * SYNOPSYS_LABEL_OPACITY,
          letterSpacing: 2,
          pointerEvents: "none",
        }}
      >
        SYNOPSYS
      </div>

      {/* Row label: PDD */}
      <div
        style={{
          position: "absolute",
          left: ROW_LABEL_X,
          top: BOTTOM_ROW_Y - 8,
          fontFamily: UI_FONT,
          fontSize: ROW_LABEL_SIZE,
          fontWeight: 600,
          color: PDD_COLOR,
          opacity: labelOpacity * PDD_LABEL_OPACITY,
          letterSpacing: 2,
          pointerEvents: "none",
        }}
      >
        PDD
      </div>

      {/* Top row — Synopsys stages */}
      {synopsysStages.map((stage, i) => (
        <FlowStageIcon
          key={`syn-${i}`}
          x={stage.x}
          y={TOP_ROW_Y}
          iconType={stage.iconType}
          color={stage.color}
          opacity={stage.opacity}
          label={stage.label}
          fadeStart={TOP_ROW_START + i * STAGE_STAGGER}
          fadeDuration={STAGE_FADE_DURATION}
        />
      ))}

      {/* Top row — Arrows */}
      {arrowGaps.map((gap, i) => (
        <FlowArrow
          key={`syn-arrow-${i}`}
          fromX={gap.from}
          fromY={TOP_ROW_Y}
          toX={gap.to}
          toY={TOP_ROW_Y}
          drawStart={TOP_ROW_START + (i + 1) * STAGE_STAGGER - 5}
          drawDuration={ARROW_DRAW_DURATION}
        />
      ))}

      {/* Bottom row — PDD stages */}
      {pddStages.map((stage, i) => (
        <FlowStageIcon
          key={`pdd-${i}`}
          x={stage.x}
          y={BOTTOM_ROW_Y}
          iconType={stage.iconType}
          color={stage.color}
          opacity={stage.opacity}
          label={stage.label}
          fadeStart={BOTTOM_ROW_START + i * STAGE_STAGGER}
          fadeDuration={STAGE_FADE_DURATION}
        />
      ))}

      {/* Bottom row — Arrows */}
      {arrowGaps.map((gap, i) => (
        <FlowArrow
          key={`pdd-arrow-${i}`}
          fromX={gap.from}
          fromY={BOTTOM_ROW_Y}
          toX={gap.to}
          toY={BOTTOM_ROW_Y}
          drawStart={BOTTOM_ROW_START + (i + 1) * STAGE_STAGGER - 5}
          drawDuration={ARROW_DRAW_DURATION}
        />
      ))}

      {/* Vertical dashed connections between corresponding stages */}
      {STAGE_X.map((x, i) => (
        <DashedConnection
          key={`dash-${i}`}
          x={x}
          fromY={TOP_ROW_Y + 55}
          toY={BOTTOM_ROW_Y - 55}
          drawStart={DASHED_START + i * DASHED_STAGGER}
          drawDuration={DASHED_DRAW_DURATION}
        />
      ))}

      {/* Equivalence symbol ≡ */}
      <EquivalenceSymbol />

      {/* Summary text */}
      {frame >= SUMMARY_FADE_START && (
        <div
          style={{
            position: "absolute",
            left: 0,
            top: SUMMARY_Y,
            width: CANVAS_WIDTH,
            textAlign: "center",
            fontFamily: UI_FONT,
            fontSize: SUMMARY_SIZE,
            fontWeight: 600,
            color: TEXT_COLOR,
            opacity: summaryOpacity,
            pointerEvents: "none",
          }}
        >
          Specification in → verified artifact out
        </div>
      )}
    </AbsoluteFill>
  );
};

export default Part2ParadigmShift08SynopsysPddEquivalence;
