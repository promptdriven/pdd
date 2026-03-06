import React from "react";
import {
  AbsoluteFill,
  OffthreadVideo,
  staticFile,
} from "remotion";
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
  BAR_STAGGER,
  BAR_FIRST_START,
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
        {/* Axes — visible from frame 0 */}
        <ChartAxes />

        {/* Bars — staggered growth */}
        {BARS.map((bar, i) => (
          <AnimatedBar
            key={bar.fillLevel}
            centerX={BAR_POSITIONS[i] + BAR_WIDTH / 2}
            capabilityPercent={bar.capability}
            color={bar.color}
            startFrame={BAR_FIRST_START + i * BAR_STAGGER}
            label={bar.fillLevel}
          />
        ))}

        {/* Trend line connecting bar tops */}
        <TrendLine
          points={BAR_TOPS}
          startFrame={TREND_LINE_START}
          endFrame={TREND_LINE_END}
        />

        {/* Callout box */}
        <CalloutBox startFrame={CALLOUT_START} />
      </AbsoluteFill>
    </AbsoluteFill>
  );
};

export default Part1Economics09ContextDegradationChart;
