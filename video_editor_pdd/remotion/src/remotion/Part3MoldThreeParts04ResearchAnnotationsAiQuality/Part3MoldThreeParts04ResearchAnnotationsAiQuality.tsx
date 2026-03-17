import React from 'react';
import { AbsoluteFill, Sequence } from 'remotion';
import { CANVAS, COLORS, TIMING } from './constants';
import { MoldCrossSection } from './MoldCrossSection';
import { DataCard } from './DataCard';
import { ConnectingArrow } from './ConnectingArrow';
import { VisualEquation } from './VisualEquation';

export const defaultPart3MoldThreeParts04ResearchAnnotationsAiQualityProps = {};

/**
 * Section 3.4: Research Annotations — AI Code Quality Data
 *
 * Research citation annotations materialize one by one overlaid on a dimmed
 * mold cross-section diagram. Two data cards (CodeRabbit and DORA) present
 * contrasting findings, connected by a visual equation showing that strong
 * tests (the "mold walls") are the differentiator.
 *
 * Duration: 450 frames @ 30fps (15s)
 */
export const Part3MoldThreeParts04ResearchAnnotationsAiQuality: React.FC = () => {
  return (
    <AbsoluteFill
      style={{
        backgroundColor: CANVAS.BG,
        fontFamily: 'Inter, system-ui, sans-serif',
      }}
    >
      {/* Dimmed mold cross-section background — visible from frame 0 */}
      <MoldCrossSection />

      {/* Card 1 — CodeRabbit: AI code quality deficit */}
      <Sequence from={TIMING.card1Start} durationInFrames={TIMING.totalFrames - TIMING.card1Start}>
        <DataCard
          startFrame={TIMING.card1Start}
          position={[200, 200]}
          size={[400, 220]}
          borderColor={COLORS.red}
          header="AI CODE QUALITY"
          mainStat="1.7× more issues"
          mainStatColor={COLORS.red}
          subStats={[
            { text: '75% more logic errors', color: COLORS.red },
            { text: '8× more performance problems', color: COLORS.red },
          ]}
          source="(CodeRabbit, 2025)"
        />
      </Sequence>

      {/* Card 2 — DORA: Tests amplify delivery */}
      <Sequence from={TIMING.card2Start} durationInFrames={TIMING.totalFrames - TIMING.card2Start}>
        <DataCard
          startFrame={TIMING.card2Start}
          position={[1320, 200]}
          size={[400, 180]}
          borderColor={COLORS.green}
          header="WITH STRONG TESTS"
          mainStat="Amplified delivery"
          mainStatColor={COLORS.green}
          subStats={[
            { text: 'AI + strong tests = accelerated', color: COLORS.green },
          ]}
          source="(DORA, 2025)"
        />
      </Sequence>

      {/* Connecting arrow from DORA card to mold walls */}
      <Sequence from={TIMING.card2ArrowStart} durationInFrames={TIMING.totalFrames - TIMING.card2ArrowStart}>
        <ConnectingArrow
          startFrame={TIMING.card2ArrowStart}
          from={[1520, 380]}
          to={[1100, 500]}
        />
      </Sequence>

      {/* Visual equation at bottom */}
      <Sequence from={TIMING.equationStart} durationInFrames={TIMING.totalFrames - TIMING.equationStart}>
        <VisualEquation />
      </Sequence>
    </AbsoluteFill>
  );
};

export default Part3MoldThreeParts04ResearchAnnotationsAiQuality;
