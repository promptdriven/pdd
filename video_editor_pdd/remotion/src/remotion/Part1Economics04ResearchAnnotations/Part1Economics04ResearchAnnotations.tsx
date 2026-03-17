/**
 * Part1Economics04ResearchAnnotations — Stacking the Evidence
 *
 * Continues the triple-line chart from spec 03. Research annotations
 * materialize one at a time, stacking evidence that faster patching
 * doesn't improve total throughput. Then the debt area splits into
 * "Code Complexity" and "Context Rot" layers.
 *
 * 900 frames (30s at 30fps).
 */
import React from "react";
import { AbsoluteFill } from "remotion";
import { ChartBase } from "./ChartBase";
import { AnnotationCallout } from "./AnnotationCallout";
import { DebtLayerSplit } from "./DebtLayerSplit";
import {
  BG_COLOR,
  BLUE_LINE_COLOR,
  AMBER_LINE_COLOR,
  RED_COLOR,
  ANN1_START,
  ANN1_FADE_DUR,
  ANN1_BOX_X,
  ANN1_BOX_Y,
  ANN1_TARGET_X,
  ANN1_TARGET_Y,
  ANN2_START,
  ANN2_FADE_DUR,
  ANN2_BOX_X,
  ANN2_BOX_Y,
  ANN2_TARGET_X,
  ANN2_TARGET_Y,
  ANN3_START,
  ANN3_FADE_DUR,
  ANN3_BOX_X,
  ANN3_BOX_Y,
  ANN3_TARGET_X,
  ANN3_TARGET_Y,
} from "./constants";
import "../_shared/load-inter-font";

export const defaultPart1Economics04ResearchAnnotationsProps = {};

export const Part1Economics04ResearchAnnotations: React.FC = () => {
  return (
    <AbsoluteFill style={{ backgroundColor: BG_COLOR }}>
      {/* Full chart from spec 03 — all lines drawn, debt area visible */}
      <ChartBase />

      {/* Annotation 1: GitHub Study — "Individual task: −55%" */}
      <AnnotationCallout
        startFrame={ANN1_START}
        fadeDuration={ANN1_FADE_DUR}
        boxX={ANN1_BOX_X}
        boxY={ANN1_BOX_Y}
        targetX={ANN1_TARGET_X}
        targetY={ANN1_TARGET_Y}
        title="Individual task: −55%"
        titleColor={BLUE_LINE_COLOR}
        borderColor={BLUE_LINE_COLOR}
        subtitle="GitHub, 2022 · 95 devs, one greenfield task"
      />

      {/* Annotation 2: Uplevel Study — "Overall throughput: ~0%" */}
      <AnnotationCallout
        startFrame={ANN2_START}
        fadeDuration={ANN2_FADE_DUR}
        boxX={ANN2_BOX_X}
        boxY={ANN2_BOX_Y}
        targetX={ANN2_TARGET_X}
        targetY={ANN2_TARGET_Y}
        title="Overall throughput: ~0%"
        titleColor={AMBER_LINE_COLOR}
        borderColor={AMBER_LINE_COLOR}
        subtitle="Uplevel, 2024 · 785 devs, one year"
        extra="+41% more bugs"
        extraColor={RED_COLOR}
      />

      {/* Annotation 3: GitClear Data — "Code churn: +44%" / "Refactoring: −60%" */}
      <AnnotationCallout
        startFrame={ANN3_START}
        fadeDuration={ANN3_FADE_DUR}
        boxX={ANN3_BOX_X}
        boxY={ANN3_BOX_Y}
        targetX={ANN3_TARGET_X}
        targetY={ANN3_TARGET_Y}
        title={["Code churn: +44%", "Refactoring: −60%"]}
        titleColor={RED_COLOR}
        borderColor={RED_COLOR}
        subtitle="GitClear, 2025 · 211M lines analyzed"
      />

      {/* Debt layer decomposition — splits at frame 540 */}
      <DebtLayerSplit />
    </AbsoluteFill>
  );
};

export default Part1Economics04ResearchAnnotations;
