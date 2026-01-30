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
  ContextRot,
  CONTEXT_ROT_FPS,
  CONTEXT_ROT_DURATION_FRAMES,
  CONTEXT_ROT_WIDTH,
  CONTEXT_ROT_HEIGHT,
  defaultContextRotProps,
} from "./07-ContextRot";
import {
  CrossingPoint,
  CROSSING_POINT_FPS,
  CROSSING_POINT_DURATION_FRAMES,
  CROSSING_POINT_WIDTH,
  CROSSING_POINT_HEIGHT,
  defaultCrossingPointProps,
} from "./08-CrossingPoint";
import {
  DeveloperEditZoomout,
  ZOOM_OUT_FPS,
  ZOOM_OUT_DURATION_FRAMES,
  ZOOM_OUT_WIDTH,
  ZOOM_OUT_HEIGHT,
  defaultDeveloperEditZoomoutProps,
} from "./09-DeveloperEditZoomout";
import {
  PieChart,
  PIE_CHART_FPS,
  PIE_CHART_DURATION_FRAMES,
  PIE_CHART_WIDTH,
  PIE_CHART_HEIGHT,
  defaultPieChartProps,
} from "./12-PieChart";
import {
  PieToCurve,
  PIE_TO_CURVE_FPS,
  PIE_TO_CURVE_DURATION_FRAMES,
  PIE_TO_CURVE_WIDTH,
  PIE_TO_CURVE_HEIGHT,
  defaultPieToCurveProps,
} from "./13-PieToCurve";
import {
  PartsEject,
  PARTS_EJECT_FPS,
  PARTS_EJECT_DURATION_FRAMES,
  PARTS_EJECT_WIDTH,
  PARTS_EJECT_HEIGHT,
  defaultPartsEjectProps,
} from "./14-PartsEject";
import {
  DefectDiscovered,
  DEFECT_FPS,
  DEFECT_DURATION_FRAMES,
  DEFECT_WIDTH,
  DEFECT_HEIGHT,
  defaultDefectDiscoveredProps,
} from "./15-DefectDiscovered";
import {
  PerfectParts,
  PERFECT_PARTS_FPS,
  PERFECT_PARTS_DURATION_FRAMES,
  PERFECT_PARTS_WIDTH,
  PERFECT_PARTS_HEIGHT,
  defaultPerfectPartsProps,
} from "./16-PerfectParts";
import {
  ValueAura,
  VALUE_AURA_FPS,
  VALUE_AURA_DURATION_FRAMES,
  VALUE_AURA_WIDTH,
  VALUE_AURA_HEIGHT,
  defaultValueAuraProps,
} from "./17-ValueAura";
import {
  PlasticRegenerates,
  PLASTIC_REGEN_FPS,
  PLASTIC_REGEN_DURATION_FRAMES,
  PLASTIC_REGEN_WIDTH,
  PLASTIC_REGEN_HEIGHT,
  defaultPlasticRegeneratesProps,
} from "./18-PlasticRegenerates";
import {
  MoldToPrompt,
  MOLD_TO_PROMPT_FPS,
  MOLD_TO_PROMPT_DURATION_FRAMES,
  MOLD_TO_PROMPT_WIDTH,
  MOLD_TO_PROMPT_HEIGHT,
  defaultMoldToPromptProps,
} from "./19-MoldToPrompt";
import {
  PromptGeneratesCode,
  PROMPT_CODE_FPS,
  PROMPT_CODE_DURATION_FRAMES,
  PROMPT_CODE_WIDTH,
  PROMPT_CODE_HEIGHT,
  defaultPromptGeneratesCodeProps,
} from "./20-PromptGeneratesCode";

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
      <Folder name="07-ContextRot">
        <Composition
          id="ContextRot"
          component={ContextRot}
          durationInFrames={CONTEXT_ROT_DURATION_FRAMES}
          fps={CONTEXT_ROT_FPS}
          width={CONTEXT_ROT_WIDTH}
          height={CONTEXT_ROT_HEIGHT}
          defaultProps={defaultContextRotProps}
        />
      </Folder>
      <Folder name="08-CrossingPoint">
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
      <Folder name="09-DeveloperEditZoomout">
        <Composition
          id="DeveloperEditZoomout"
          component={DeveloperEditZoomout}
          durationInFrames={ZOOM_OUT_DURATION_FRAMES}
          fps={ZOOM_OUT_FPS}
          width={ZOOM_OUT_WIDTH}
          height={ZOOM_OUT_HEIGHT}
          defaultProps={defaultDeveloperEditZoomoutProps}
        />
      </Folder>
      <Folder name="12-PieChart">
        <Composition
          id="PieChart"
          component={PieChart}
          durationInFrames={PIE_CHART_DURATION_FRAMES}
          fps={PIE_CHART_FPS}
          width={PIE_CHART_WIDTH}
          height={PIE_CHART_HEIGHT}
          defaultProps={defaultPieChartProps}
        />
      </Folder>
      <Folder name="13-PieToCurve">
        <Composition
          id="PieToCurve"
          component={PieToCurve}
          durationInFrames={PIE_TO_CURVE_DURATION_FRAMES}
          fps={PIE_TO_CURVE_FPS}
          width={PIE_TO_CURVE_WIDTH}
          height={PIE_TO_CURVE_HEIGHT}
          defaultProps={defaultPieToCurveProps}
        />
      </Folder>
      <Folder name="14-PartsEject">
        <Composition
          id="PartsEject"
          component={PartsEject}
          durationInFrames={PARTS_EJECT_DURATION_FRAMES}
          fps={PARTS_EJECT_FPS}
          width={PARTS_EJECT_WIDTH}
          height={PARTS_EJECT_HEIGHT}
          defaultProps={defaultPartsEjectProps}
        />
      </Folder>
      <Folder name="15-DefectDiscovered">
        <Composition
          id="DefectDiscovered"
          component={DefectDiscovered}
          durationInFrames={DEFECT_DURATION_FRAMES}
          fps={DEFECT_FPS}
          width={DEFECT_WIDTH}
          height={DEFECT_HEIGHT}
          defaultProps={defaultDefectDiscoveredProps}
        />
      </Folder>
      <Folder name="16-PerfectParts">
        <Composition
          id="PerfectParts"
          component={PerfectParts}
          durationInFrames={PERFECT_PARTS_DURATION_FRAMES}
          fps={PERFECT_PARTS_FPS}
          width={PERFECT_PARTS_WIDTH}
          height={PERFECT_PARTS_HEIGHT}
          defaultProps={defaultPerfectPartsProps}
        />
      </Folder>
      <Folder name="17-ValueAura">
        <Composition
          id="ValueAura"
          component={ValueAura}
          durationInFrames={VALUE_AURA_DURATION_FRAMES}
          fps={VALUE_AURA_FPS}
          width={VALUE_AURA_WIDTH}
          height={VALUE_AURA_HEIGHT}
          defaultProps={defaultValueAuraProps}
        />
      </Folder>
      <Folder name="18-PlasticRegenerates">
        <Composition
          id="PlasticRegenerates"
          component={PlasticRegenerates}
          durationInFrames={PLASTIC_REGEN_DURATION_FRAMES}
          fps={PLASTIC_REGEN_FPS}
          width={PLASTIC_REGEN_WIDTH}
          height={PLASTIC_REGEN_HEIGHT}
          defaultProps={defaultPlasticRegeneratesProps}
        />
      </Folder>
      <Folder name="19-MoldToPrompt">
        <Composition
          id="MoldToPrompt"
          component={MoldToPrompt}
          durationInFrames={MOLD_TO_PROMPT_DURATION_FRAMES}
          fps={MOLD_TO_PROMPT_FPS}
          width={MOLD_TO_PROMPT_WIDTH}
          height={MOLD_TO_PROMPT_HEIGHT}
          defaultProps={defaultMoldToPromptProps}
        />
      </Folder>
      <Folder name="20-PromptGeneratesCode">
        <Composition
          id="PromptGeneratesCode"
          component={PromptGeneratesCode}
          durationInFrames={PROMPT_CODE_DURATION_FRAMES}
          fps={PROMPT_CODE_FPS}
          width={PROMPT_CODE_WIDTH}
          height={PROMPT_CODE_HEIGHT}
          defaultProps={defaultPromptGeneratesCodeProps}
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
