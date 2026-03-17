import React from "react";
import { AbsoluteFill, useCurrentFrame, interpolate, Easing } from "remotion";
import { WoodenChair } from "./WoodenChair";
import { MoldCrossSection } from "./MoldCrossSection";
import { ValueAura } from "./ValueAura";
import { PlasticPart } from "./PlasticPart";
import {
  BG_COLOR,
  LEFT_BG,
  RIGHT_BG,
  SPLIT_X,
  SPLIT_LINE_WIDTH,
  SPLIT_LINE_COLOR,
  SPLIT_LINE_OPACITY,
  LEFT_PANEL_WIDTH,
  RIGHT_PANEL_START,
  RIGHT_PANEL_WIDTH,
  CRAFT_ACCENT,
  MOLD_ACCENT,
  HEADER_FONT_SIZE,
  HEADER_FONT_WEIGHT,
  HEADER_LETTER_SPACING,
  HEADER_OPACITY,
  HEADER_Y,
  HEADER_FADE_START,
  HEADER_FADE_END,
  SPLIT_LINE_DRAW_START,
  SPLIT_LINE_DRAW_END,
  CHAIR_CENTER_X,
  CHAIR_CENTER_Y,
  CHAIR_WIDTH,
  CHAIR_HEIGHT,
  MOLD_CENTER_X,
  MOLD_CENTER_Y,
  MOLD_WIDTH,
  MOLD_HEIGHT,
  HISTORY_FONT_SIZE,
  HISTORY_OPACITY,
  HISTORY_STACK_X,
  HISTORY_STACK_Y,
  HISTORY_LABEL_START,
  HISTORY_LABEL_STAGGER,
  HISTORY_LABEL_COUNT,
  SUMMARY_Y,
  SUMMARY_FONT_SIZE,
  SUMMARY_OPACITY,
  SUMMARY_APPEAR_START,
  SUMMARY_APPEAR_END,
} from "./constants";

export const defaultPart2ParadigmShift05ValueMigrationSplitProps = {};

export const Part2ParadigmShift05ValueMigrationSplit: React.FC = () => {
  const frame = useCurrentFrame();

  // Split line draws from center outward (height)
  const splitLineHeight = interpolate(
    frame,
    [SPLIT_LINE_DRAW_START, SPLIT_LINE_DRAW_END],
    [0, 1080],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp", easing: Easing.out(Easing.cubic) }
  );

  // Panel headers fade in
  const headerOpacity = interpolate(
    frame,
    [HEADER_FADE_START, HEADER_FADE_END],
    [0, HEADER_OPACITY],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp", easing: Easing.out(Easing.quad) }
  );

  // Summary labels fade in
  const summaryOpacity = interpolate(
    frame,
    [SUMMARY_APPEAR_START, SUMMARY_APPEAR_END],
    [0, SUMMARY_OPACITY],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp", easing: Easing.out(Easing.quad) }
  );

  // History labels
  const historyLabels: Array<{ text: string; opacity: number }> = [];
  for (let i = 0; i < HISTORY_LABEL_COUNT; i++) {
    const labelFrame = HISTORY_LABEL_START + i * HISTORY_LABEL_STAGGER;
    const labelOpacity = interpolate(
      frame,
      [labelFrame, labelFrame + 8],
      [0, HISTORY_OPACITY],
      { extrapolateLeft: "clamp", extrapolateRight: "clamp", easing: Easing.out(Easing.quad) }
    );
    const cutNumber = i === HISTORY_LABEL_COUNT - 1 ? 47 : i + 1;
    historyLabels.push({ text: `cut ${cutNumber}`, opacity: labelOpacity });
  }

  return (
    <AbsoluteFill style={{ backgroundColor: BG_COLOR }}>
      {/* Left panel — Crafting */}
      <div
        style={{
          position: "absolute",
          left: 0,
          top: 0,
          width: LEFT_PANEL_WIDTH,
          height: 1080,
          backgroundColor: LEFT_BG,
          overflow: "hidden",
        }}
      >
        {/* CRAFTING header */}
        <div
          style={{
            position: "absolute",
            top: HEADER_Y,
            left: 0,
            right: 0,
            display: "flex",
            justifyContent: "center",
            fontFamily: "'Inter', sans-serif",
            fontWeight: HEADER_FONT_WEIGHT,
            fontSize: HEADER_FONT_SIZE,
            color: CRAFT_ACCENT,
            letterSpacing: HEADER_LETTER_SPACING,
            opacity: headerOpacity,
            textTransform: "uppercase" as const,
          }}
        >
          CRAFTING
        </div>

        {/* Value aura on the chair (object) */}
        <ValueAura
          centerX={CHAIR_CENTER_X}
          centerY={CHAIR_CENTER_Y}
          width={CHAIR_WIDTH}
          height={CHAIR_HEIGHT}
          color={CRAFT_ACCENT}
        />

        {/* Wooden chair SVG */}
        <WoodenChair />

        {/* History labels stacking */}
        <div
          style={{
            position: "absolute",
            left: HISTORY_STACK_X,
            top: HISTORY_STACK_Y,
            display: "flex",
            flexDirection: "column",
            gap: 3,
          }}
        >
          {historyLabels.map((label, i) => (
            <span
              key={`history-${i}`}
              style={{
                fontFamily: "'JetBrains Mono', 'Fira Code', monospace",
                fontSize: HISTORY_FONT_SIZE,
                color: CRAFT_ACCENT,
                opacity: label.opacity,
                whiteSpace: "nowrap" as const,
              }}
            >
              {label.text}
            </span>
          ))}
        </div>

        {/* Summary label */}
        <div
          style={{
            position: "absolute",
            top: SUMMARY_Y,
            left: 0,
            right: 0,
            display: "flex",
            justifyContent: "center",
            fontFamily: "'Inter', sans-serif",
            fontSize: SUMMARY_FONT_SIZE,
            color: CRAFT_ACCENT,
            opacity: summaryOpacity,
          }}
        >
          Value lives in the object
        </div>
      </div>

      {/* Split divider line — draws from center */}
      <div
        style={{
          position: "absolute",
          left: SPLIT_X - SPLIT_LINE_WIDTH / 2,
          top: 540 - splitLineHeight / 2,
          width: SPLIT_LINE_WIDTH,
          height: splitLineHeight,
          backgroundColor: SPLIT_LINE_COLOR,
          opacity: SPLIT_LINE_OPACITY,
        }}
      />

      {/* Right panel — Molding */}
      <div
        style={{
          position: "absolute",
          left: RIGHT_PANEL_START,
          top: 0,
          width: RIGHT_PANEL_WIDTH,
          height: 1080,
          backgroundColor: RIGHT_BG,
          overflow: "hidden",
        }}
      >
        {/* MOLDING header */}
        <div
          style={{
            position: "absolute",
            top: HEADER_Y,
            left: 0,
            right: 0,
            display: "flex",
            justifyContent: "center",
            fontFamily: "'Inter', sans-serif",
            fontWeight: HEADER_FONT_WEIGHT,
            fontSize: HEADER_FONT_SIZE,
            color: MOLD_ACCENT,
            letterSpacing: HEADER_LETTER_SPACING,
            opacity: headerOpacity,
            textTransform: "uppercase" as const,
          }}
        >
          MOLDING
        </div>

        {/* Value aura on the mold (specification) — NOT on the plastic part */}
        <ValueAura
          centerX={MOLD_CENTER_X}
          centerY={MOLD_CENTER_Y}
          width={MOLD_WIDTH}
          height={MOLD_HEIGHT}
          color={MOLD_ACCENT}
        />

        {/* Mold cross-section SVG */}
        <MoldCrossSection />

        {/* Plastic part with dissolve/regenerate */}
        <PlasticPart />

        {/* Summary label */}
        <div
          style={{
            position: "absolute",
            top: SUMMARY_Y,
            left: 0,
            right: 0,
            display: "flex",
            justifyContent: "center",
            fontFamily: "'Inter', sans-serif",
            fontSize: SUMMARY_FONT_SIZE,
            color: MOLD_ACCENT,
            opacity: summaryOpacity,
          }}
        >
          Value lives in the specification
        </div>
      </div>
    </AbsoluteFill>
  );
};

export default Part2ParadigmShift05ValueMigrationSplit;
