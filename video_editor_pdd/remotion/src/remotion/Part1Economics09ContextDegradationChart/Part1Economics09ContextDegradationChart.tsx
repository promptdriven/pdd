import React from "react";
import { AbsoluteFill, OffthreadVideo, staticFile } from "remotion";
import { ChartAxes } from "./ChartAxes";
import { AnimatedBar } from "./AnimatedBar";
import { TrendLine } from "./TrendLine";
import { CalloutBox } from "./CalloutBox";
import {
  BG_COLOR,
  BARS,
  BAR_POSITIONS,
  BAR_WIDTH,
  BAR_TOPS,
  BAR_STAGGER_START,
  BAR_STAGGER_INTERVAL,
  TREND_LINE_START,
  TREND_LINE_END,
  CALLOUT_START,
} from "./constants";

export const defaultPart1Economics09ContextDegradationChartProps = {};

export const Part1Economics09ContextDegradationChart: React.FC = () => {
  return (
    <AbsoluteFill style={{ backgroundColor: BG_COLOR }}>
      {/* Veo background video */}
      <AbsoluteFill>
        <OffthreadVideo
          src={staticFile("veo/part1_economics.mp4")}
          style={{ width: "100%", height: "100%", objectFit: "cover" }}
          muted
        />
      </AbsoluteFill>

      {/* Chart overlay */}
      <AbsoluteFill>
        {/* Axes — visible from frame 0 (starts at 15% opacity) */}
        <ChartAxes />

        {/* Bars — staggered growth starting at frame 30 */}
        {BARS.map((bar, i) => (
          <AnimatedBar
            key={bar.fillLevel}
            x={BAR_POSITIONS[i]}
            width={BAR_WIDTH}
            capability={bar.capability}
            color={bar.color}
            growStartFrame={BAR_STAGGER_START + i * BAR_STAGGER_INTERVAL}
          />
        ))}

        {/* Trend line connecting bar tops — draws frame 140-180 */}
        <TrendLine
          points={BAR_TOPS}
          drawStartFrame={TREND_LINE_START}
          drawEndFrame={TREND_LINE_END}
        />

        {/* Callout box — slides in at frame 180 */}
        <CalloutBox appearFrame={CALLOUT_START} />
      </AbsoluteFill>
    </AbsoluteFill>
  );
};

export default Part1Economics09ContextDegradationChart;
