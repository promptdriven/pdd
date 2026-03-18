import React from "react";
import { AbsoluteFill, Sequence } from "remotion";
import { DonutChart } from "./DonutChart";
import { ResearchCallout } from "./ResearchCallout";
import {
  BG_COLOR,
  TOTAL_FRAMES,
  CALLOUT_X,
  MCKINSEY_Y,
  STRIPE_Y,
  MCKINSEY_SLIDE_START,
  MCKINSEY_SLIDE_DURATION,
  MCKINSEY_PULSE_START,
  MCKINSEY_PULSE_DURATION,
  STRIPE_SLIDE_START,
  STRIPE_SLIDE_DURATION,
  STRIPE_PULSE_START,
  STRIPE_PULSE_DURATION,
} from "./constants";

export const defaultPart5CompoundReturns02MaintenancePieChartProps = {};

export const Part5CompoundReturns02MaintenancePieChart: React.FC = () => {
  return (
    <AbsoluteFill
      style={{
        backgroundColor: BG_COLOR,
        fontFamily: "Inter, sans-serif",
      }}
    >
      <Sequence from={0} durationInFrames={TOTAL_FRAMES}>
        {/* Animated donut chart with segments */}
        <DonutChart />

        {/* McKinsey research callout */}
        <ResearchCallout
          x={CALLOUT_X}
          y={MCKINSEY_Y}
          icon="bar_chart"
          mainText="+40% maintenance cost"
          subText="with high technical debt"
          source="McKinsey Digital, 2024"
          slideStartFrame={MCKINSEY_SLIDE_START}
          slideDuration={MCKINSEY_SLIDE_DURATION}
          pulseStartFrame={MCKINSEY_PULSE_START}
          pulseDuration={MCKINSEY_PULSE_DURATION}
        />

        {/* Stripe research callout */}
        <ResearchCallout
          x={CALLOUT_X}
          y={STRIPE_Y}
          icon="clock"
          mainText="33% of work week"
          subText="spent on technical debt"
          source="Stripe Developer Coefficient, 2018"
          slideStartFrame={STRIPE_SLIDE_START}
          slideDuration={STRIPE_SLIDE_DURATION}
          pulseStartFrame={STRIPE_PULSE_START}
          pulseDuration={STRIPE_PULSE_DURATION}
        />
      </Sequence>
    </AbsoluteFill>
  );
};

export default Part5CompoundReturns02MaintenancePieChart;
