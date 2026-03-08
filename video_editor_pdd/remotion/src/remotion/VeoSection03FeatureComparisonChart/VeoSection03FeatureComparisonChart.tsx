import React from 'react';
import { AbsoluteFill } from 'remotion';
import { ChartGrid } from './ChartGrid';
import { ChartTitle } from './ChartTitle';
import { PlatformMetrics } from './PlatformMetrics';
import {
  CANVAS,
  PLATFORMS,
  ANIMATION_TIMING,
} from './constants';

export const VeoSection03FeatureComparisonChart: React.FC = () => {
  return (
    <AbsoluteFill style={{ backgroundColor: CANVAS.BACKGROUND }}>
      {/* Grid lines */}
      <ChartGrid />

      {/* Chart title */}
      <ChartTitle text="Platform Comparison" />

      {/* VEO 2 Platform */}
      <PlatformMetrics
        platformName={PLATFORMS.VEO_2.name}
        yPosition={PLATFORMS.VEO_2.yPosition}
        metrics={PLATFORMS.VEO_2.metrics}
        startFrame={ANIMATION_TIMING.VEO_START}
      />

      {/* Traditional Tools Platform */}
      <PlatformMetrics
        platformName={PLATFORMS.TRADITIONAL.name}
        yPosition={PLATFORMS.TRADITIONAL.yPosition}
        metrics={PLATFORMS.TRADITIONAL.metrics}
        startFrame={ANIMATION_TIMING.TRADITIONAL_START}
      />

      {/* AI Platform B */}
      <PlatformMetrics
        platformName={PLATFORMS.AI_PLATFORM_B.name}
        yPosition={PLATFORMS.AI_PLATFORM_B.yPosition}
        metrics={PLATFORMS.AI_PLATFORM_B.metrics}
        startFrame={ANIMATION_TIMING.AI_PLATFORM_START}
      />
    </AbsoluteFill>
  );
};

export default VeoSection03FeatureComparisonChart;

// Default props for the component
export const defaultVeoSection03FeatureComparisonChartProps = {};
