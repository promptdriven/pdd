import { Composition, Folder } from "remotion";
import { Main } from "./MyComp/Main";
import {
  COMP_NAME,
  defaultMyCompProps,
  DURATION_IN_FRAMES,
  VIDEO_FPS,
  VIDEO_HEIGHT,
  VIDEO_WIDTH,
} from "../../types/constants";
import { NextLogo } from "./MyComp/NextLogo";
import {
  ColdOpenSplitScreen,
  COLD_OPEN_FPS,
  COLD_OPEN_DURATION_FRAMES,
  COLD_OPEN_WIDTH,
  COLD_OPEN_HEIGHT,
  defaultColdOpenProps,
} from "./01-ColdOpen";
import {
  SockPriceChart,
  SOCK_CHART_FPS,
  SOCK_CHART_DURATION_FRAMES,
  SOCK_CHART_WIDTH,
  SOCK_CHART_HEIGHT,
  defaultSockPriceChartProps,
} from "./02-SockPriceChart";
import {
  ThresholdHighlight,
  THRESHOLD_FPS,
  THRESHOLD_DURATION_FRAMES,
  THRESHOLD_WIDTH,
  THRESHOLD_HEIGHT,
  defaultThresholdHighlightProps,
} from "./03-ThresholdHighlight";
import {
  LinesDiverge,
  LINES_DIVERGE_FPS,
  LINES_DIVERGE_DURATION_FRAMES,
  LINES_DIVERGE_WIDTH,
  LINES_DIVERGE_HEIGHT,
  defaultLinesDivergeProps,
} from "./04-LinesDiverge";
import {
  CodeCostChart,
  CODE_CHART_FPS,
  CODE_CHART_DURATION_FRAMES,
  CODE_CHART_WIDTH,
  CODE_CHART_HEIGHT,
  defaultCodeCostChartProps,
} from "./05-CodeCostChart";
import {
  AIMilestones,
  AI_MILESTONES_FPS,
  AI_MILESTONES_DURATION_FRAMES,
  AI_MILESTONES_WIDTH,
  AI_MILESTONES_HEIGHT,
  defaultAIMilestonesProps,
} from "./06-AIMilestones";
import {
  CrossingPoint,
  CROSSING_POINT_FPS,
  CROSSING_POINT_DURATION_FRAMES,
  CROSSING_POINT_WIDTH,
  CROSSING_POINT_HEIGHT,
  defaultCrossingPointProps,
} from "./07-CrossingPoint";

export const RemotionRoot: React.FC = () => {
  return (
    <>
      <Folder name="01-ColdOpen">
        <Composition
          id="ColdOpenSplitScreen"
          component={ColdOpenSplitScreen}
          durationInFrames={COLD_OPEN_DURATION_FRAMES}
          fps={COLD_OPEN_FPS}
          width={COLD_OPEN_WIDTH}
          height={COLD_OPEN_HEIGHT}
          defaultProps={defaultColdOpenProps}
        />
      </Folder>
      <Folder name="02-SockPriceChart">
        <Composition
          id="SockPriceChart"
          component={SockPriceChart}
          durationInFrames={SOCK_CHART_DURATION_FRAMES}
          fps={SOCK_CHART_FPS}
          width={SOCK_CHART_WIDTH}
          height={SOCK_CHART_HEIGHT}
          defaultProps={defaultSockPriceChartProps}
        />
      </Folder>
      <Folder name="03-ThresholdHighlight">
        <Composition
          id="ThresholdHighlight"
          component={ThresholdHighlight}
          durationInFrames={THRESHOLD_DURATION_FRAMES}
          fps={THRESHOLD_FPS}
          width={THRESHOLD_WIDTH}
          height={THRESHOLD_HEIGHT}
          defaultProps={defaultThresholdHighlightProps}
        />
      </Folder>
      <Folder name="04-LinesDiverge">
        <Composition
          id="LinesDiverge"
          component={LinesDiverge}
          durationInFrames={LINES_DIVERGE_DURATION_FRAMES}
          fps={LINES_DIVERGE_FPS}
          width={LINES_DIVERGE_WIDTH}
          height={LINES_DIVERGE_HEIGHT}
          defaultProps={defaultLinesDivergeProps}
        />
      </Folder>
      <Folder name="05-CodeCostChart">
        <Composition
          id="CodeCostChart"
          component={CodeCostChart}
          durationInFrames={CODE_CHART_DURATION_FRAMES}
          fps={CODE_CHART_FPS}
          width={CODE_CHART_WIDTH}
          height={CODE_CHART_HEIGHT}
          defaultProps={defaultCodeCostChartProps}
        />
      </Folder>
      <Folder name="06-AIMilestones">
        <Composition
          id="AIMilestones"
          component={AIMilestones}
          durationInFrames={AI_MILESTONES_DURATION_FRAMES}
          fps={AI_MILESTONES_FPS}
          width={AI_MILESTONES_WIDTH}
          height={AI_MILESTONES_HEIGHT}
          defaultProps={defaultAIMilestonesProps}
        />
      </Folder>
      <Folder name="07-CrossingPoint">
        <Composition
          id="CrossingPoint"
          component={CrossingPoint}
          durationInFrames={CROSSING_POINT_DURATION_FRAMES}
          fps={CROSSING_POINT_FPS}
          width={CROSSING_POINT_WIDTH}
          height={CROSSING_POINT_HEIGHT}
          defaultProps={defaultCrossingPointProps}
        />
      </Folder>
      <Folder name="Examples">
        <Composition
          id={COMP_NAME}
          component={Main}
          durationInFrames={DURATION_IN_FRAMES}
          fps={VIDEO_FPS}
          width={VIDEO_WIDTH}
          height={VIDEO_HEIGHT}
          defaultProps={defaultMyCompProps}
        />
        <Composition
          id="NextLogo"
          component={NextLogo}
          durationInFrames={300}
          fps={30}
          width={140}
          height={140}
          defaultProps={{
            outProgress: 0,
          }}
        />
      </Folder>
    </>
  );
};
