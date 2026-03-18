import React from 'react';
import { AbsoluteFill, useVideoConfig } from 'remotion';
import { COLORS, CARD1, CARD2, TIMING } from './constants';
import { MoldCrossSection } from './MoldCrossSection';
import { DataCard } from './DataCard';
import { ConnectingArrow } from './ConnectingArrow';
import { VisualEquation } from './VisualEquation';

export const defaultPart3MoldThreeParts04ResearchAnnotationsAiQualityProps = {};

export const Part3MoldThreeParts04ResearchAnnotationsAiQuality: React.FC = () => {
  const { fps } = useVideoConfig();

  return (
    <AbsoluteFill
      style={{
        backgroundColor: COLORS.background,
        fontFamily: 'Inter, sans-serif',
      }}
    >
      {/* Layer 1: Dimmed mold cross-section background */}
      <MoldCrossSection />

      {/* Layer 2: Card 1 — CodeRabbit research (upper-left) */}
      <DataCard
        x={CARD1.x}
        y={CARD1.y}
        width={CARD1.width}
        height={CARD1.height}
        borderColor={COLORS.red}
        headerText="AI CODE QUALITY"
        mainStat="1.7× more issues"
        mainColor={COLORS.red}
        subStats={[
          { text: '75% more logic errors', color: COLORS.red },
          { text: '8× more performance problems', color: COLORS.red },
        ]}
        sourceText="(CodeRabbit, 2025)"
        startFrame={TIMING.card1Start}
        fps={fps}
      />

      {/* Layer 3: Card 2 — DORA research (upper-right) */}
      <DataCard
        x={CARD2.x}
        y={CARD2.y}
        width={CARD2.width}
        height={CARD2.height}
        borderColor={COLORS.green}
        headerText="WITH STRONG TESTS"
        mainStat="Amplified delivery"
        mainColor={COLORS.green}
        subStats={[
          { text: 'AI + strong tests = accelerated', color: COLORS.green },
        ]}
        sourceText="(DORA, 2025)"
        startFrame={TIMING.card2Start}
        fps={fps}
      />

      {/* Layer 4: Connecting arrow from DORA card to mold walls */}
      <ConnectingArrow
        fromX={CARD2.x + CARD2.width / 2}
        fromY={CARD2.y + CARD2.height}
        toX={1100}
        toY={500}
        startFrame={TIMING.card2ArrowStart}
        drawDuration={TIMING.card2ArrowDuration}
        label="Tests are the walls"
      />

      {/* Layer 5: Visual equation at bottom */}
      <VisualEquation />
    </AbsoluteFill>
  );
};

export default Part3MoldThreeParts04ResearchAnnotationsAiQuality;
