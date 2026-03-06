import React from "react";
import {
  AbsoluteFill,
  OffthreadVideo,
  staticFile,
  useCurrentFrame,
} from "remotion";
import { ChartAxes } from "./ChartAxes";
import { AnimatedBar } from "./AnimatedBar";
import { TrendLine } from "./TrendLine";
import { CalloutBox } from "./CalloutBox";
import {
  BG_COLOR,
  BARS,
  BARS_START_X,
  BAR_WIDTH,
  BAR_GAP,
  BAR_STAGGER_START,
  BAR_STAGGER_INTERVAL,
  TREND_LINE_START,
  TREND_LINE_END,
  CALLOUT_START,
} from "./constants";

export const defaultPart1Economics09ContextDegradationChartProps = {};

export const Part1Economics09ContextDegradationChart: React.FC = () => {
  const frame = useCurrentFrame();

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
        {BARS.map((bar, i) => {
          const barX = BARS_START_X + i * (BAR_WIDTH + BAR_GAP);
          const growStart = BAR_STAGGER_START + i * BAR_STAGGER_INTERVAL;
          return (
            <AnimatedBar
              key={bar.fillLevel}
              x={barX}
              width={BAR_WIDTH}
              capability={bar.capability}
              color={bar.color}
              growStartFrame={growStart}
            />
          );
        })}

        {/* Trend line connecting bar tops */}
        <TrendLine
          capabilities={BARS.map((b) => b.capability)}
          drawStartFrame={TREND_LINE_START}
          drawEndFrame={TREND_LINE_END}
        />

        {/* Callout box */}
        <CalloutBox appearFrame={CALLOUT_START} />
      </AbsoluteFill>
    </AbsoluteFill>
  );
};

export default Part1Economics09ContextDegradationChart;
