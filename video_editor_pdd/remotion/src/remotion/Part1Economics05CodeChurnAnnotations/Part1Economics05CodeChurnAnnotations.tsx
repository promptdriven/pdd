import React from 'react';
import { AbsoluteFill, Sequence } from 'remotion';
import { ChartBackground } from './ChartBackground';
import { PreviousAnnotations } from './PreviousAnnotations';
import { AnnotationCallout } from './AnnotationCallout';

/**
 * Section 1.5: Code Churn & Refactoring Annotations — GitClear Data
 *
 * New annotations materialize on the existing code cost chart, replacing
 * or layering atop the GitHub/Uplevel annotations. These point to the
 * shaded debt area, making the technical debt story concrete with
 * GitClear's data.
 *
 * Duration: 840 frames (28s @ 30fps)
 */

const BG_COLOR = '#0A0F1A';
const TOTAL_FRAMES = 840;

// Chart coordinates helper — maps year to X position
function yearToX(year: number): number {
  const CHART_LEFT = 140;
  const CHART_RIGHT = 1300;
  const ratio = (year - 2020) / (2025 - 2020);
  return CHART_LEFT + ratio * (CHART_RIGHT - CHART_LEFT);
}

export const defaultPart1Economics05CodeChurnAnnotationsProps = {};

export const Part1Economics05CodeChurnAnnotations: React.FC = () => {
  return (
    <AbsoluteFill
      style={{
        backgroundColor: BG_COLOR,
        fontFamily: 'Inter, sans-serif',
      }}
    >
      {/* Underlying chart — always visible */}
      <Sequence from={0} durationInFrames={TOTAL_FRAMES} name="Chart Background">
        <ChartBackground />
      </Sequence>

      {/* Previous annotations (GitHub/Uplevel) — fade to 30% opacity */}
      <Sequence from={0} durationInFrames={TOTAL_FRAMES} name="Previous Annotations">
        <PreviousAnnotations />
      </Sequence>

      {/* Annotation 1: Code churn +44% — appears at frame 60 */}
      <Sequence from={0} durationInFrames={TOTAL_FRAMES} name="Code Churn Annotation">
        <AnnotationCallout
          startFrame={60}
          x={1380}
          y={340}
          mainText="Code churn: +44%"
          sourceText="(GitClear, 2025 — 211M lines analyzed)"
          accentColor="#EF4444"
          connectorTargetX={yearToX(2024.5)}
          connectorTargetY={550}
        />
      </Sequence>

      {/* Annotation 2: Refactoring −60% — appears at frame 360 */}
      <Sequence from={0} durationInFrames={TOTAL_FRAMES} name="Refactoring Annotation">
        <AnnotationCallout
          startFrame={360}
          x={1380}
          y={500}
          mainText="Refactoring: −60%"
          sourceText="(GitClear, 2025 — Code revised within 2 weeks)"
          accentColor="#F59E0B"
          connectorTargetX={yearToX(2024.5)}
          connectorTargetY={680}
        />
      </Sequence>
    </AbsoluteFill>
  );
};

export default Part1Economics05CodeChurnAnnotations;
