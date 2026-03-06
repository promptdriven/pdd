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

// Bar data
const BARS = [
  { fillLevel: "10%", capability: 95, color: "#22C55E" },
  { fillLevel: "25%", capability: 82, color: "#84CC16" },
  { fillLevel: "50%", capability: 58, color: "#F59E0B" },
  { fillLevel: "75%", capability: 32, color: "#F97316" },
  { fillLevel: "100%", capability: 15, color: "#EF4444" },
];

// Layout
const CHART_X = 300;
const CHART_W = 1320;
const BAR_WIDTH = 120;
const BAR_GAP = 60;
const NUM_BARS = 5;
const TOTAL_BARS_WIDTH = NUM_BARS * BAR_WIDTH + (NUM_BARS - 1) * BAR_GAP;
const BARS_START_X = CHART_X + (CHART_W - TOTAL_BARS_WIDTH) / 2;

// Animation timing
const BAR_STAGGER_START = 30;
const BAR_STAGGER_INTERVAL = 20;
const TREND_LINE_START = 140;
const TREND_LINE_END = 180;
const CALLOUT_START = 180;

export const defaultPart1Economics09ContextDegradationChartProps = {};

export const Part1Economics09ContextDegradationChart: React.FC = () => {
  const frame = useCurrentFrame();

  return (
    <AbsoluteFill style={{ backgroundColor: "#0A1628" }}>
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
