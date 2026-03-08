import React from 'react';
import { AbsoluteFill, Sequence } from 'remotion';
import { COLORS, DIMENSIONS, MILESTONES, TYPOGRAPHY } from './constants';
import { TimelineBase } from './TimelineBase';
import { ProgressLine } from './ProgressLine';
import { TimelineNode } from './TimelineNode';
import { MilestoneCard } from './MilestoneCard';

export const VeoSection05AdoptionTimeline: React.FC = () => {
  return (
    <AbsoluteFill
      style={{
        background: `radial-gradient(circle, ${COLORS.background.center} 0%, ${COLORS.background.edge} 100%)`,
      }}
    >
      {/* Section title */}
      <div
        style={{
          position: 'absolute',
          left: DIMENSIONS.width / 2,
          top: 120,
          transform: 'translateX(-50%)',
          fontFamily: TYPOGRAPHY.title.fontFamily,
          fontWeight: TYPOGRAPHY.title.fontWeight,
          fontSize: TYPOGRAPHY.title.fontSize,
          color: TYPOGRAPHY.title.color,
          textAlign: 'center',
          whiteSpace: 'nowrap',
        }}
      >
        The Evolution of Video Creation
      </div>

      {/* Base Timeline */}
      <Sequence from={0}>
        <TimelineBase
          x1={DIMENSIONS.timeline.x1}
          x2={DIMENSIONS.timeline.x2}
          y={DIMENSIONS.timeline.y}
        />
      </Sequence>

      {/* 2020 Node - Traditional Video Tools */}
      <Sequence from={30}>
        <TimelineNode year={MILESTONES[0].year} x={MILESTONES[0].x} y={DIMENSIONS.timeline.y} />
        <MilestoneCard
          x={MILESTONES[0].x}
          y={MILESTONES[0].y}
          title={MILESTONES[0].title}
          stat={`${MILESTONES[0].adoption}% adoption`}
          delay={10}
        />
      </Sequence>

      {/* Progress to 2021 - Early AI Experiments */}
      <Sequence from={60}>
        <ProgressLine from={MILESTONES[0].x} to={MILESTONES[1].x} duration={30} />
        <TimelineNode year={MILESTONES[1].year} x={MILESTONES[1].x} y={DIMENSIONS.timeline.y} />
        <MilestoneCard
          x={MILESTONES[1].x}
          y={MILESTONES[1].y}
          title={MILESTONES[1].title}
          stat={`${MILESTONES[1].adoption}% adoption`}
          delay={10}
        />
      </Sequence>

      {/* Progress to 2022 - First Commercial AI Video */}
      <Sequence from={90}>
        <ProgressLine from={MILESTONES[1].x} to={MILESTONES[2].x} duration={30} />
        <TimelineNode year={MILESTONES[2].year} x={MILESTONES[2].x} y={DIMENSIONS.timeline.y} />
        <MilestoneCard
          x={MILESTONES[2].x}
          y={MILESTONES[2].y}
          title={MILESTONES[2].title}
          stat={`${MILESTONES[2].adoption}% adoption`}
          delay={10}
        />
      </Sequence>

      {/* Progress to 2024 - AI Video Goes Mainstream */}
      <Sequence from={120}>
        <ProgressLine from={MILESTONES[2].x} to={MILESTONES[3].x} duration={30} />
        <TimelineNode year={MILESTONES[3].year} x={MILESTONES[3].x} y={DIMENSIONS.timeline.y} />
        <MilestoneCard
          x={MILESTONES[3].x}
          y={MILESTONES[3].y}
          title={MILESTONES[3].title}
          stat={`${MILESTONES[3].adoption}% adoption`}
          delay={10}
        />
      </Sequence>

      {/* Progress to 2025 - VEO 2 Launch */}
      <Sequence from={150}>
        <ProgressLine from={MILESTONES[3].x} to={MILESTONES[4].x} duration={30} />
        <TimelineNode year={MILESTONES[4].year} x={MILESTONES[4].x} y={DIMENSIONS.timeline.y} />
        <MilestoneCard
          x={MILESTONES[4].x}
          y={MILESTONES[4].y}
          title={MILESTONES[4].title}
          stat={`${MILESTONES[4].adoption}% adoption`}
          delay={10}
          highlight={true}
        />
      </Sequence>
    </AbsoluteFill>
  );
};

export default VeoSection05AdoptionTimeline;

export const defaultVeoSection05AdoptionTimelineProps = {};
