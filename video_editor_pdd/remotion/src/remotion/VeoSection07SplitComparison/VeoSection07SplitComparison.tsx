import React from 'react';
import { AbsoluteFill } from 'remotion';
import { COLORS, METRICS } from './constants';
import { HeaderTitle } from './HeaderTitle';
import { SplitPanel } from './SplitPanel';
import { DividerLine } from './DividerLine';
import { CenterBadge } from './CenterBadge';
import { MetricRow } from './MetricRow';

export const VeoSection07SplitComparison: React.FC = () => {
  return (
    <AbsoluteFill style={{ backgroundColor: COLORS.background }}>
      {/* Header title */}
      <HeaderTitle />

      {/* Left panel — ocean sunset */}
      <SplitPanel side="left" />

      {/* Right panel — forest canopy */}
      <SplitPanel side="right" />

      {/* Vertical divider wiping down */}
      <DividerLine />

      {/* Center "Veo 3.1" badge */}
      <CenterBadge />

      {/* Comparison metric rows */}
      {METRICS.map((metric, i) => (
        <MetricRow
          key={metric.label}
          label={metric.label}
          oceanValue={metric.oceanValue}
          forestValue={metric.forestValue}
          oceanPercent={metric.oceanPercent}
          forestPercent={metric.forestPercent}
          index={i}
        />
      ))}
    </AbsoluteFill>
  );
};

export const defaultVeoSection07SplitComparisonProps = {};

export default VeoSection07SplitComparison;
