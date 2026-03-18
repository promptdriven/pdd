import React from 'react';
import {
  AbsoluteFill,
  useCurrentFrame,
  Easing,
  interpolate,
  Sequence,
} from 'remotion';
import {
  BG_COLOR,
  GREEN,
  RED,
  AMBER,
  SUMMARY_COLOR,
  BR_CENTER,
  ENTERPRISE_CIRCLE_RADIUS,
  TIMING,
} from './constants';
import { QuadrantGrid } from './QuadrantGrid';
import { QuadrantContent } from './QuadrantContent';
import { DashedCircle } from './DashedCircle';

export const defaultPart1Economics06TwoByTwoGridProps = {};

export const Part1Economics06TwoByTwoGrid: React.FC = () => {
  const frame = useCurrentFrame();

  // === Title fade (visible from frame 0, subtle heading) ===
  const titleAlpha = interpolate(frame, [0, 20], [0.6, 0.8], {
    extrapolateLeft: 'clamp',
    extrapolateRight: 'clamp',
    easing: Easing.out(Easing.quad),
  });

  // === Summary line fade-in ===
  const summaryAlpha = interpolate(
    frame,
    [TIMING.summaryStart, TIMING.summaryStart + TIMING.summaryFadeDuration],
    [0, 0.7],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.out(Easing.quad),
    }
  );

  return (
    <AbsoluteFill
      style={{
        backgroundColor: BG_COLOR,
        fontFamily: 'Inter, sans-serif',
      }}
    >
      {/* Section title — visible from frame 0 */}
      <div
        style={{
          position: 'absolute',
          top: 60,
          left: 0,
          width: '100%',
          textAlign: 'center',
          fontFamily: 'Inter, sans-serif',
          fontSize: 22,
          fontWeight: 600,
          color: '#E2E8F0',
          opacity: titleAlpha,
          letterSpacing: 0.5,
        }}
      >
        Why Studies Contradict
      </div>

      {/* Subtitle — visible from frame 0 */}
      <div
        style={{
          position: 'absolute',
          top: 100,
          left: 0,
          width: '100%',
          textAlign: 'center',
          fontFamily: 'Inter, sans-serif',
          fontSize: 13,
          fontWeight: 400,
          color: '#94A3B8',
          opacity: titleAlpha * 0.5,
        }}
      >
        Task type × Codebase maturity
      </div>

      {/* Grid structure — draws in from frame 30 */}
      <QuadrantGrid
        startFrame={TIMING.gridStart}
        drawDuration={TIMING.gridDrawDuration}
      />

      {/* Top-Left Quadrant: GitHub study +55% */}
      <Sequence from={TIMING.githubStart}>
        <QuadrantContent
          quadrant="top-left"
          color={GREEN}
          bgOpacity={0.08}
          startFrame={TIMING.githubStart}
          scaleDuration={TIMING.githubScaleDuration}
          studyName="GitHub study"
          stat="+55%"
          subtext="95 devs, greenfield"
        />
      </Sequence>

      {/* Bottom-Right Quadrant: METR study −19% */}
      <Sequence from={TIMING.metrStart}>
        <QuadrantContent
          quadrant="bottom-right"
          color={RED}
          bgOpacity={0.08}
          startFrame={TIMING.metrStart}
          scaleDuration={TIMING.metrScaleDuration}
          studyName="METR study"
          stat="−19%"
          subtext="experienced devs, mature repos"
        />
      </Sequence>

      {/* Top-Right Quadrant: Mixed results (amber) */}
      <Sequence from={TIMING.amberStart}>
        <QuadrantContent
          quadrant="top-right"
          color={AMBER}
          bgOpacity={0.04}
          startFrame={TIMING.amberStart}
          scaleDuration={TIMING.amberFadeDuration}
          mixedLabel="Mixed results"
        />
      </Sequence>

      {/* Bottom-Left Quadrant: Mixed results (amber) */}
      <Sequence from={TIMING.amberStart}>
        <QuadrantContent
          quadrant="bottom-left"
          color={AMBER}
          bgOpacity={0.04}
          startFrame={TIMING.amberStart}
          scaleDuration={TIMING.amberFadeDuration}
          mixedLabel="Mixed results"
        />
      </Sequence>

      {/* Enterprise work dotted circle in bottom-right */}
      <DashedCircle
        cx={BR_CENTER.x}
        cy={BR_CENTER.y}
        radius={ENTERPRISE_CIRCLE_RADIUS}
        color={RED}
        strokeOpacity={0.3}
        strokeWidth={2}
        drawDuration={TIMING.circleDrawDuration}
        label="Most enterprise work"
        labelColor={RED}
        labelOpacity={0.5}
        startFrame={TIMING.circleStart}
      />

      {/* Summary line */}
      <div
        style={{
          position: 'absolute',
          top: 880,
          left: 0,
          width: '100%',
          textAlign: 'center',
          fontFamily: 'Inter, sans-serif',
          fontSize: 16,
          fontWeight: 400,
          color: SUMMARY_COLOR,
          opacity: summaryAlpha,
        }}
      >
        Every study is correct. They just measured different quadrants.
      </div>
    </AbsoluteFill>
  );
};

export default Part1Economics06TwoByTwoGrid;
