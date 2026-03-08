import React from 'react';
import { AbsoluteFill, Sequence } from 'remotion';
import {
  COLORS,
  PLATFORM_DATA,
  SAVINGS,
  ANIMATION_TIMING,
  LAYOUT,
} from './constants';
import { GridPattern } from './GridPattern';
import { ColumnHeader } from './ColumnHeader';
import { MetricRow } from './MetricRow';
import { SavingsCallout } from './SavingsCallout';

export interface VeoSection07RoiCalculatorAnimationProps {
  // Props can be added here if needed
}

export const VeoSection07RoiCalculatorAnimation: React.FC<
  VeoSection07RoiCalculatorAnimationProps
> = () => {
  return (
    <AbsoluteFill
      style={{
        background: `linear-gradient(180deg, ${COLORS.background.top} 0%, ${COLORS.background.bottom} 100%)`,
      }}
    >
      {/* Grid Pattern Overlay */}
      <GridPattern opacity={0.1} />

      {/* Column Headers */}
      <Sequence from={ANIMATION_TIMING.headerSlideStart}>
        <ColumnHeader
          x={LAYOUT.columnHeader.positions[0]}
          text={PLATFORM_DATA[0].name}
          delay={0}
        />
        <ColumnHeader
          x={LAYOUT.columnHeader.positions[1]}
          text={PLATFORM_DATA[1].name}
          delay={5}
        />
        <ColumnHeader
          x={LAYOUT.columnHeader.positions[2]}
          text={PLATFORM_DATA[2].name}
          delay={10}
        />
      </Sequence>

      {/* Row 1: Production Time */}
      <Sequence from={ANIMATION_TIMING.row1Start}>
        <MetricRow
          label="Production Time"
          y={LAYOUT.metricRow.startY}
          values={[
            PLATFORM_DATA[0].productionTime,
            PLATFORM_DATA[1].productionTime,
            PLATFORM_DATA[2].productionTime,
          ]}
          unit="hours"
          colors={[
            PLATFORM_DATA[0].color,
            PLATFORM_DATA[1].color,
            PLATFORM_DATA[2].color,
          ]}
          duration={ANIMATION_TIMING.row1Duration}
        />
      </Sequence>

      {/* Row 2: Equipment Cost */}
      <Sequence from={ANIMATION_TIMING.row2Start}>
        <MetricRow
          label="Equipment Cost"
          y={LAYOUT.metricRow.startY + LAYOUT.metricRow.height + LAYOUT.metricRow.spacing}
          values={[
            PLATFORM_DATA[0].equipmentCost,
            PLATFORM_DATA[1].equipmentCost,
            PLATFORM_DATA[2].equipmentCost,
          ]}
          unit=""
          prefix="$"
          colors={[
            PLATFORM_DATA[0].color,
            PLATFORM_DATA[1].color,
            PLATFORM_DATA[2].color,
          ]}
          duration={ANIMATION_TIMING.row2Duration}
        />
      </Sequence>

      {/* Row 3: Team Size */}
      <Sequence from={ANIMATION_TIMING.row3Start}>
        <MetricRow
          label="Team Size"
          y={
            LAYOUT.metricRow.startY +
            2 * (LAYOUT.metricRow.height + LAYOUT.metricRow.spacing)
          }
          values={[
            PLATFORM_DATA[0].teamSize,
            PLATFORM_DATA[1].teamSize,
            PLATFORM_DATA[2].teamSize,
          ]}
          unit="people"
          colors={[
            PLATFORM_DATA[0].color,
            PLATFORM_DATA[1].color,
            PLATFORM_DATA[2].color,
          ]}
          duration={ANIMATION_TIMING.row3Duration}
        />
      </Sequence>

      {/* Row 4: Total Monthly Cost */}
      <Sequence from={ANIMATION_TIMING.row4Start}>
        <MetricRow
          label="Total Monthly Cost"
          y={
            LAYOUT.metricRow.startY +
            3 * (LAYOUT.metricRow.height + LAYOUT.metricRow.spacing)
          }
          values={[
            PLATFORM_DATA[0].monthlyCost,
            PLATFORM_DATA[1].monthlyCost,
            PLATFORM_DATA[2].monthlyCost,
          ]}
          unit="/mo"
          prefix="$"
          colors={[
            PLATFORM_DATA[0].color,
            PLATFORM_DATA[1].color,
            PLATFORM_DATA[2].color,
          ]}
          duration={ANIMATION_TIMING.row4Duration}
          showProgressBar={true}
        />
      </Sequence>

      {/* Savings Callout */}
      <Sequence from={ANIMATION_TIMING.savingsStart}>
        <SavingsCallout
          x={LAYOUT.savingsCallout.x}
          y={LAYOUT.savingsCallout.y}
          text={`SAVE $${SAVINGS.vsTraditional.toLocaleString()}/mo`}
          pulseStart={ANIMATION_TIMING.savingsSpringDuration}
        />
      </Sequence>
    </AbsoluteFill>
  );
};

export default VeoSection07RoiCalculatorAnimation;

export const defaultVeoSection07RoiCalculatorAnimationProps: VeoSection07RoiCalculatorAnimationProps =
  {};
