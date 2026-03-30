import React from 'react';
import {AbsoluteFill, Sequence} from 'remotion';
import BackgroundChart from './BackgroundChart';
import AnnotationCallout from './AnnotationCallout';
import ContrastLine from './ContrastLine';
import {
  BG_COLOR,
  TOTAL_FRAMES,
  ANNOTATION1_START,
  ANNOTATION1_BOX_X,
  ANNOTATION1_BOX_Y,
  ANNOTATION1_TARGET_X,
  ANNOTATION1_TARGET_Y,
  ANNOTATION2_START,
  ANNOTATION2_BOX_X,
  ANNOTATION2_BOX_Y,
  ANNOTATION2_TARGET_X,
  ANNOTATION2_TARGET_Y,
  BLUE_ACCENT,
  RED_ACCENT,
  CONTRAST_LINE_START,
  CONTRAST_LINE_DURATION,
  CONTRAST_LINE_COLOR,
  CONTRAST_LINE_OPACITY,
} from './constants';

export const defaultPart1Economics04ResearchAnnotationsProps = {};

export const Part1Economics04ResearchAnnotations: React.FC = () => {
  return (
    <AbsoluteFill
      style={{
        backgroundColor: BG_COLOR,
        fontFamily: 'Inter, sans-serif',
      }}
    >
      {/* Underlying chart – visible from frame 0 */}
      <Sequence from={0} durationInFrames={TOTAL_FRAMES}>
        <BackgroundChart />
      </Sequence>

      {/* ── Annotation 1: GitHub Study ────────────────────────────── */}
      <Sequence
        from={ANNOTATION1_START}
        durationInFrames={TOTAL_FRAMES - ANNOTATION1_START}
      >
        <AnnotationCallout
          borderColor={BLUE_ACCENT}
          mainText="Individual task: −55%"
          source="(GitHub, 2022)"
          finePrint="95 developers, one greenfield task"
          boxX={ANNOTATION1_BOX_X}
          boxY={ANNOTATION1_BOX_Y}
          targetX={ANNOTATION1_TARGET_X}
          targetY={ANNOTATION1_TARGET_Y}
        />
      </Sequence>

      {/* ── Annotation 2: Uplevel Study ───────────────────────────── */}
      <Sequence
        from={ANNOTATION2_START}
        durationInFrames={TOTAL_FRAMES - ANNOTATION2_START}
      >
        <AnnotationCallout
          borderColor={RED_ACCENT}
          mainText="Overall throughput: ~0%"
          source="(Uplevel, 2024)"
          finePrint="785 developers, one year"
          boxX={ANNOTATION2_BOX_X}
          boxY={ANNOTATION2_BOX_Y}
          targetX={ANNOTATION2_TARGET_X}
          targetY={ANNOTATION2_TARGET_Y}
        />
      </Sequence>

      {/* ── Contrast connector between the two callout boxes ──────── */}
      <Sequence
        from={CONTRAST_LINE_START}
        durationInFrames={TOTAL_FRAMES - CONTRAST_LINE_START}
      >
        <ContrastLine
          fromX={ANNOTATION1_BOX_X + 170}
          fromY={ANNOTATION1_BOX_Y}
          toX={ANNOTATION2_BOX_X + 170}
          toY={ANNOTATION2_BOX_Y + 110}
          color={CONTRAST_LINE_COLOR}
          lineOpacity={CONTRAST_LINE_OPACITY}
          drawDuration={CONTRAST_LINE_DURATION}
        />
      </Sequence>
    </AbsoluteFill>
  );
};

export default Part1Economics04ResearchAnnotations;
