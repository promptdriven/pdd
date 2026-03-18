import React from 'react';
import { AbsoluteFill, Sequence } from 'remotion';
import {
  BG_COLOR,
  BLUE,
  AMBER,
  RED,
  ANNOTATION_X,
  ANNOTATION_1_START,
  ANNOTATION_2_START,
  ANNOTATION_3_START,
  TOTAL_FRAMES,
} from './constants';
import TripleLineChart, { getTargetPoint } from './TripleLineChart';
import AnnotationCallout from './AnnotationCallout';
import DebtLayerSplit from './DebtLayerSplit';

export const defaultPart1Economics04ResearchAnnotationsProps = {};

/**
 * Section 1.3: Research Annotations — Stacking the Evidence
 *
 * Builds on the triple-line chart from the previous spec. Research annotations
 * materialize one at a time, stacking evidence that faster patching doesn't
 * improve total throughput.
 *
 * Duration: ~30s (900 frames @ 30fps)
 */
export const Part1Economics04ResearchAnnotations: React.FC = () => {
  // Annotation target points on the chart
  const githubTarget = getTargetPoint('immediate', 3); // 2022, index 3
  const uplevelTarget = getTargetPoint('total', 5); // 2024, index 5
  const gitclearTarget = getTargetPoint('debtArea', 5); // Debt area at 2024

  return (
    <AbsoluteFill style={{ backgroundColor: BG_COLOR }}>
      <Sequence from={0} durationInFrames={TOTAL_FRAMES}>
        {/* Base chart - visible from frame 0 */}
        <TripleLineChart />

        {/* Debt layer decomposition (renders its own timing internally) */}
        <DebtLayerSplit />

        {/* Annotation 1: GitHub Study — "Individual task: -55%" */}
        <AnnotationCallout
          startFrame={ANNOTATION_1_START}
          title="Individual task: \u221255%"
          titleColor={BLUE}
          subtitle="GitHub, 2022 \u2022 95 devs, one greenfield task"
          borderColor={BLUE}
          x={ANNOTATION_X}
          y={200}
          targetX={githubTarget.x}
          targetY={githubTarget.y}
        />

        {/* Annotation 2: Uplevel Study — "Overall throughput: ~0%" */}
        <AnnotationCallout
          startFrame={ANNOTATION_2_START}
          title="Overall throughput: ~0%"
          titleColor={AMBER}
          subtitle="Uplevel, 2024 \u2022 785 devs, one year"
          extra="+41% more bugs"
          extraColor={RED}
          borderColor={AMBER}
          x={ANNOTATION_X}
          y={340}
          targetX={uplevelTarget.x}
          targetY={uplevelTarget.y}
        />

        {/* Annotation 3: GitClear — churn + refactoring */}
        <AnnotationCallout
          startFrame={ANNOTATION_3_START}
          title={['Code churn: +44%', 'Refactoring: \u221260%']}
          titleColor={RED}
          subtitle="GitClear, 2025 \u2022 211M lines analyzed"
          borderColor={RED}
          x={ANNOTATION_X}
          y={500}
          targetX={gitclearTarget.x}
          targetY={gitclearTarget.y}
        />
      </Sequence>
    </AbsoluteFill>
  );
};

export default Part1Economics04ResearchAnnotations;
