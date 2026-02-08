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
  CodeCostChartMini,
  MINI_FPS,
  MINI_DURATION_FRAMES,
  MINI_WIDTH,
  MINI_HEIGHT,
  defaultCodeCostChartMiniProps,
} from "./05a-CodeCostChartMini";
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
  ChipDesignHistory,
  CHIP_DESIGN_FPS,
  CHIP_DESIGN_DURATION_FRAMES,
  CHIP_DESIGN_WIDTH,
  CHIP_DESIGN_HEIGHT,
  defaultChipDesignHistoryProps,
} from "./19a-ChipDesignHistory";
import {
  PromptGeneratesCode,
  PROMPT_CODE_FPS,
  PROMPT_CODE_DURATION_FRAMES,
  PROMPT_CODE_WIDTH,
  PROMPT_CODE_HEIGHT,
  defaultPromptGeneratesCodeProps,
} from "./20-PromptGeneratesCode";
import {
  CrossSectionIntro,
  CROSS_SECTION_FPS,
  CROSS_SECTION_DURATION_FRAMES,
  CROSS_SECTION_WIDTH,
  CROSS_SECTION_HEIGHT,
  defaultCrossSectionIntroProps,
} from "./21-CrossSectionIntro";
import {
  WallsIlluminate,
  WALLS_ILLUMINATE_FPS,
  WALLS_ILLUMINATE_DURATION_FRAMES,
  WALLS_ILLUMINATE_WIDTH,
  WALLS_ILLUMINATE_HEIGHT,
  defaultWallsIlluminateProps,
} from "./22-WallsIlluminate";
import {
  LiquidInjection,
  LIQUID_INJECTION_FPS,
  LIQUID_INJECTION_DURATION_FRAMES,
  LIQUID_INJECTION_WIDTH,
  LIQUID_INJECTION_HEIGHT,
  defaultLiquidInjectionProps,
} from "./23-LiquidInjection";
import {
  FocusSingleWall,
  FOCUS_WALL_FPS,
  FOCUS_WALL_DURATION_FRAMES,
  FOCUS_WALL_WIDTH,
  FOCUS_WALL_HEIGHT,
  defaultFocusSingleWallProps,
} from "./24-FocusSingleWall";
import {
  BugDiscovered,
  BUG_DISCOVERED_FPS,
  BUG_DISCOVERED_DURATION_FRAMES,
  BUG_DISCOVERED_WIDTH,
  BUG_DISCOVERED_HEIGHT,
  defaultBugDiscoveredProps,
} from "./25-BugDiscovered";
import {
  AddTestWall,
  ADD_TEST_WALL_FPS,
  ADD_TEST_WALL_DURATION_FRAMES,
  ADD_TEST_WALL_WIDTH,
  ADD_TEST_WALL_HEIGHT,
  defaultAddTestWallProps,
} from "./26-AddTestWall";
import {
  CodeRegenerates,
  CODE_REGEN_FPS,
  CODE_REGEN_DURATION_FRAMES,
  CODE_REGEN_WIDTH,
  CODE_REGEN_HEIGHT,
  defaultCodeRegeneratesProps,
} from "./27-CodeRegenerates";
import {
  RatchetTimelapse,
  RATCHET_FPS,
  RATCHET_DURATION_FRAMES,
  RATCHET_WIDTH,
  RATCHET_HEIGHT,
  defaultRatchetTimelapseProps,
} from "./28-RatchetTimelapse";
import {
  TraditionalVsPdd,
  TRADITIONAL_VS_PDD_FPS,
  TRADITIONAL_VS_PDD_DURATION_FRAMES,
  TRADITIONAL_VS_PDD_WIDTH,
  TRADITIONAL_VS_PDD_HEIGHT,
  defaultTraditionalVsPddProps,
} from "./29-TraditionalVsPdd";
import {
  InjectionNozzle,
  NOZZLE_FPS,
  NOZZLE_DURATION_FRAMES,
  NOZZLE_WIDTH,
  NOZZLE_HEIGHT,
  defaultInjectionNozzleProps,
} from "./30-InjectionNozzle";
import {
  PromptTextFlows,
  PROMPT_FLOW_FPS,
  PROMPT_FLOW_DURATION_FRAMES,
  PROMPT_FLOW_WIDTH,
  PROMPT_FLOW_HEIGHT,
  defaultPromptTextFlowsProps,
} from "./31-PromptTextFlows";
import {
  PromptVariations,
  PROMPT_VARIATIONS_FPS,
  PROMPT_VARIATIONS_DURATION_FRAMES,
  PROMPT_VARIATIONS_WIDTH,
  PROMPT_VARIATIONS_HEIGHT,
  defaultPromptVariationsProps,
} from "./32-PromptVariations";
import {
  PromptGovernsCode,
  PROMPT_GOVERNS_FPS,
  PROMPT_GOVERNS_DURATION_FRAMES,
  PROMPT_GOVERNS_WIDTH,
  PROMPT_GOVERNS_HEIGHT,
  defaultPromptGovernsCodeProps,
} from "./33-PromptGovernsCode";
import {
  GroundingPanel,
  GROUNDING_PANEL_FPS,
  GROUNDING_PANEL_DURATION_FRAMES,
  GROUNDING_PANEL_WIDTH,
  GROUNDING_PANEL_HEIGHT,
  defaultGroundingPanelProps,
} from "./34-GroundingPanel";
import {
  GroundingComparison,
  GROUNDING_COMPARISON_FPS,
  GROUNDING_COMPARISON_DURATION_FRAMES,
  GROUNDING_COMPARISON_WIDTH,
  GROUNDING_COMPARISON_HEIGHT,
  defaultGroundingComparisonProps,
} from "./35-GroundingComparison";
import {
  GroundingDatabase,
  GROUNDING_DB_FPS,
  GROUNDING_DB_DURATION_FRAMES,
  GROUNDING_DB_WIDTH,
  GROUNDING_DB_HEIGHT,
  defaultGroundingDatabaseProps,
} from "./36-GroundingDatabase";
import {
  ThreeComponents,
  THREE_COMPONENTS_FPS,
  THREE_COMPONENTS_DURATION_FRAMES,
  THREE_COMPONENTS_WIDTH,
  THREE_COMPONENTS_HEIGHT,
  defaultThreeComponentsProps,
} from "./37-ThreeComponents";
import {
  CodeOutputMoldGlows,
  CODE_OUTPUT_FPS,
  CODE_OUTPUT_DURATION_FRAMES,
  CODE_OUTPUT_WIDTH,
  CODE_OUTPUT_HEIGHT,
  defaultCodeOutputMoldGlowsProps,
} from "./38-CodeOutputMoldGlows";
import {
  PrinterFocus,
  PRINTER_FOCUS_FPS,
  PRINTER_FOCUS_DURATION_FRAMES,
  PRINTER_FOCUS_WIDTH,
  PRINTER_FOCUS_HEIGHT,
  defaultPrinterFocusProps,
} from "./39-3DPrinterFocus";
import {
  MoldFlowFocus,
  MOLD_FLOW_FOCUS_FPS,
  MOLD_FLOW_FOCUS_DURATION_FRAMES,
  MOLD_FLOW_FOCUS_WIDTH,
  MOLD_FLOW_FOCUS_HEIGHT,
  defaultMoldFlowFocusProps,
} from "./40-MoldFlowFocus";
import {
  PrecisionGraph,
  PRECISION_GRAPH_FPS,
  PRECISION_GRAPH_DURATION_FRAMES,
  PRECISION_GRAPH_WIDTH,
  PRECISION_GRAPH_HEIGHT,
  defaultPrecisionGraphProps,
} from "./41-PrecisionGraph";
import {
  GraphAnimateCurve,
  GRAPH_ANIMATE_FPS,
  GRAPH_ANIMATE_DURATION_FRAMES,
  GRAPH_ANIMATE_WIDTH,
  GRAPH_ANIMATE_HEIGHT,
  defaultGraphAnimateCurveProps,
} from "./42-GraphAnimateCurve";
import {
  LongPrompt,
  LONG_PROMPT_FPS,
  LONG_PROMPT_DURATION_FRAMES,
  LONG_PROMPT_WIDTH,
  LONG_PROMPT_HEIGHT,
  defaultLongPromptProps,
} from "./43-LongPrompt";
import {
  ShortPromptTests,
  SHORT_PROMPT_FPS,
  SHORT_PROMPT_DURATION_FRAMES,
  SHORT_PROMPT_WIDTH,
  SHORT_PROMPT_HEIGHT,
  defaultShortPromptTestsProps,
} from "./44-ShortPromptTests";
import {
  BothGenerateFinal,
  BOTH_GENERATE_FPS,
  BOTH_GENERATE_DURATION_FRAMES,
  BOTH_GENERATE_WIDTH,
  BOTH_GENERATE_HEIGHT,
  defaultBothGenerateFinalProps,
} from "./45-BothGenerateFinal";
import {
  Part1Economics,
  PART1_FPS,
  PART1_DURATION_FRAMES,
  PART1_WIDTH,
  PART1_HEIGHT,
  defaultPart1EconomicsProps,
} from "./S01-Economics";
import {
  Part2ParadigmShift,
  PART2_FPS,
  PART2_DURATION_FRAMES,
  PART2_WIDTH,
  PART2_HEIGHT,
  defaultPart2ParadigmShiftProps,
} from "./S02-ParadigmShift";
import {
  Part3MoldThreeParts,
  PART3_FPS,
  PART3_DURATION_FRAMES,
  PART3_WIDTH,
  PART3_HEIGHT,
  defaultPart3MoldThreePartsProps,
} from "./S03-MoldThreeParts";
import {
  Part4PrecisionTradeoff,
  PART4_FPS,
  PART4_DURATION_FRAMES,
  PART4_WIDTH,
  PART4_HEIGHT,
  defaultPart4PrecisionTradeoffProps,
} from "./S04-PrecisionTradeoff";
import {
  Part5CompoundReturns,
  PART5_FPS,
  PART5_DURATION_FRAMES,
  PART5_WIDTH,
  PART5_HEIGHT,
  defaultPart5CompoundReturnsProps,
} from "./S05-CompoundReturns";
import {
  ClosingSection,
  CLOSING_FPS,
  CLOSING_DURATION_FRAMES,
  CLOSING_WIDTH,
  CLOSING_HEIGHT,
  defaultClosingSectionProps,
} from "./S06-Closing";
import {
  ColdOpenSection,
  COLD_OPEN_FPS as COLD_OPEN_SECTION_FPS,
  COLD_OPEN_DURATION_FRAMES as COLD_OPEN_SECTION_DURATION_FRAMES,
  COLD_OPEN_WIDTH as COLD_OPEN_SECTION_WIDTH,
  COLD_OPEN_HEIGHT as COLD_OPEN_SECTION_HEIGHT,
  defaultColdOpenSectionProps,
} from "./S00-ColdOpen";

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
      <Folder name="05a-CodeCostChartMini">
        <Composition
          id="CodeCostChartMini"
          component={CodeCostChartMini}
          durationInFrames={MINI_DURATION_FRAMES}
          fps={MINI_FPS}
          width={MINI_WIDTH}
          height={MINI_HEIGHT}
          defaultProps={defaultCodeCostChartMiniProps}
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
      <Folder name="19a-ChipDesignHistory">
        <Composition
          id="ChipDesignHistory"
          component={ChipDesignHistory}
          durationInFrames={CHIP_DESIGN_DURATION_FRAMES}
          fps={CHIP_DESIGN_FPS}
          width={CHIP_DESIGN_WIDTH}
          height={CHIP_DESIGN_HEIGHT}
          defaultProps={defaultChipDesignHistoryProps}
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
      <Folder name="21-CrossSectionIntro">
        <Composition
          id="CrossSectionIntro"
          component={CrossSectionIntro}
          durationInFrames={CROSS_SECTION_DURATION_FRAMES}
          fps={CROSS_SECTION_FPS}
          width={CROSS_SECTION_WIDTH}
          height={CROSS_SECTION_HEIGHT}
          defaultProps={defaultCrossSectionIntroProps}
        />
      </Folder>
      <Folder name="22-WallsIlluminate">
        <Composition
          id="WallsIlluminate"
          component={WallsIlluminate}
          durationInFrames={WALLS_ILLUMINATE_DURATION_FRAMES}
          fps={WALLS_ILLUMINATE_FPS}
          width={WALLS_ILLUMINATE_WIDTH}
          height={WALLS_ILLUMINATE_HEIGHT}
          defaultProps={defaultWallsIlluminateProps}
        />
      </Folder>
      <Folder name="23-LiquidInjection">
        <Composition
          id="LiquidInjection"
          component={LiquidInjection}
          durationInFrames={LIQUID_INJECTION_DURATION_FRAMES}
          fps={LIQUID_INJECTION_FPS}
          width={LIQUID_INJECTION_WIDTH}
          height={LIQUID_INJECTION_HEIGHT}
          defaultProps={defaultLiquidInjectionProps}
        />
      </Folder>
      <Folder name="24-FocusSingleWall">
        <Composition
          id="FocusSingleWall"
          component={FocusSingleWall}
          durationInFrames={FOCUS_WALL_DURATION_FRAMES}
          fps={FOCUS_WALL_FPS}
          width={FOCUS_WALL_WIDTH}
          height={FOCUS_WALL_HEIGHT}
          defaultProps={defaultFocusSingleWallProps}
        />
      </Folder>
      <Folder name="25-BugDiscovered">
        <Composition
          id="BugDiscovered"
          component={BugDiscovered}
          durationInFrames={BUG_DISCOVERED_DURATION_FRAMES}
          fps={BUG_DISCOVERED_FPS}
          width={BUG_DISCOVERED_WIDTH}
          height={BUG_DISCOVERED_HEIGHT}
          defaultProps={defaultBugDiscoveredProps}
        />
      </Folder>
      <Folder name="26-AddTestWall">
        <Composition
          id="AddTestWall"
          component={AddTestWall}
          durationInFrames={ADD_TEST_WALL_DURATION_FRAMES}
          fps={ADD_TEST_WALL_FPS}
          width={ADD_TEST_WALL_WIDTH}
          height={ADD_TEST_WALL_HEIGHT}
          defaultProps={defaultAddTestWallProps}
        />
      </Folder>
      <Folder name="27-CodeRegenerates">
        <Composition
          id="CodeRegenerates"
          component={CodeRegenerates}
          durationInFrames={CODE_REGEN_DURATION_FRAMES}
          fps={CODE_REGEN_FPS}
          width={CODE_REGEN_WIDTH}
          height={CODE_REGEN_HEIGHT}
          defaultProps={defaultCodeRegeneratesProps}
        />
      </Folder>
      <Folder name="28-RatchetTimelapse">
        <Composition
          id="RatchetTimelapse"
          component={RatchetTimelapse}
          durationInFrames={RATCHET_DURATION_FRAMES}
          fps={RATCHET_FPS}
          width={RATCHET_WIDTH}
          height={RATCHET_HEIGHT}
          defaultProps={defaultRatchetTimelapseProps}
        />
      </Folder>
      <Folder name="29-TraditionalVsPdd">
        <Composition
          id="TraditionalVsPdd"
          component={TraditionalVsPdd}
          durationInFrames={TRADITIONAL_VS_PDD_DURATION_FRAMES}
          fps={TRADITIONAL_VS_PDD_FPS}
          width={TRADITIONAL_VS_PDD_WIDTH}
          height={TRADITIONAL_VS_PDD_HEIGHT}
          defaultProps={defaultTraditionalVsPddProps}
        />
      </Folder>
      <Folder name="30-InjectionNozzle">
        <Composition
          id="InjectionNozzle"
          component={InjectionNozzle}
          durationInFrames={NOZZLE_DURATION_FRAMES}
          fps={NOZZLE_FPS}
          width={NOZZLE_WIDTH}
          height={NOZZLE_HEIGHT}
          defaultProps={defaultInjectionNozzleProps}
        />
      </Folder>
      <Folder name="31-PromptTextFlows">
        <Composition
          id="PromptTextFlows"
          component={PromptTextFlows}
          durationInFrames={PROMPT_FLOW_DURATION_FRAMES}
          fps={PROMPT_FLOW_FPS}
          width={PROMPT_FLOW_WIDTH}
          height={PROMPT_FLOW_HEIGHT}
          defaultProps={defaultPromptTextFlowsProps}
        />
      </Folder>
      <Folder name="32-PromptVariations">
        <Composition
          id="PromptVariations"
          component={PromptVariations}
          durationInFrames={PROMPT_VARIATIONS_DURATION_FRAMES}
          fps={PROMPT_VARIATIONS_FPS}
          width={PROMPT_VARIATIONS_WIDTH}
          height={PROMPT_VARIATIONS_HEIGHT}
          defaultProps={defaultPromptVariationsProps}
        />
      </Folder>
      <Folder name="33-PromptGovernsCode">
        <Composition
          id="PromptGovernsCode"
          component={PromptGovernsCode}
          durationInFrames={PROMPT_GOVERNS_DURATION_FRAMES}
          fps={PROMPT_GOVERNS_FPS}
          width={PROMPT_GOVERNS_WIDTH}
          height={PROMPT_GOVERNS_HEIGHT}
          defaultProps={defaultPromptGovernsCodeProps}
        />
      </Folder>
      <Folder name="34-GroundingPanel">
        <Composition
          id="GroundingPanel"
          component={GroundingPanel}
          durationInFrames={GROUNDING_PANEL_DURATION_FRAMES}
          fps={GROUNDING_PANEL_FPS}
          width={GROUNDING_PANEL_WIDTH}
          height={GROUNDING_PANEL_HEIGHT}
          defaultProps={defaultGroundingPanelProps}
        />
      </Folder>
      <Folder name="35-GroundingComparison">
        <Composition
          id="GroundingComparison"
          component={GroundingComparison}
          durationInFrames={GROUNDING_COMPARISON_DURATION_FRAMES}
          fps={GROUNDING_COMPARISON_FPS}
          width={GROUNDING_COMPARISON_WIDTH}
          height={GROUNDING_COMPARISON_HEIGHT}
          defaultProps={defaultGroundingComparisonProps}
        />
      </Folder>
      <Folder name="36-GroundingDatabase">
        <Composition
          id="GroundingDatabase"
          component={GroundingDatabase}
          durationInFrames={GROUNDING_DB_DURATION_FRAMES}
          fps={GROUNDING_DB_FPS}
          width={GROUNDING_DB_WIDTH}
          height={GROUNDING_DB_HEIGHT}
          defaultProps={defaultGroundingDatabaseProps}
        />
      </Folder>
      <Folder name="37-ThreeComponents">
        <Composition
          id="ThreeComponents"
          component={ThreeComponents}
          durationInFrames={THREE_COMPONENTS_DURATION_FRAMES}
          fps={THREE_COMPONENTS_FPS}
          width={THREE_COMPONENTS_WIDTH}
          height={THREE_COMPONENTS_HEIGHT}
          defaultProps={defaultThreeComponentsProps}
        />
      </Folder>
      <Folder name="38-CodeOutputMoldGlows">
        <Composition
          id="CodeOutputMoldGlows"
          component={CodeOutputMoldGlows}
          durationInFrames={CODE_OUTPUT_DURATION_FRAMES}
          fps={CODE_OUTPUT_FPS}
          width={CODE_OUTPUT_WIDTH}
          height={CODE_OUTPUT_HEIGHT}
          defaultProps={defaultCodeOutputMoldGlowsProps}
        />
      </Folder>
      <Folder name="39-3DPrinterFocus">
        <Composition
          id="PrinterFocus"
          component={PrinterFocus}
          durationInFrames={PRINTER_FOCUS_DURATION_FRAMES}
          fps={PRINTER_FOCUS_FPS}
          width={PRINTER_FOCUS_WIDTH}
          height={PRINTER_FOCUS_HEIGHT}
          defaultProps={defaultPrinterFocusProps}
        />
      </Folder>
      <Folder name="40-MoldFlowFocus">
        <Composition
          id="MoldFlowFocus"
          component={MoldFlowFocus}
          durationInFrames={MOLD_FLOW_FOCUS_DURATION_FRAMES}
          fps={MOLD_FLOW_FOCUS_FPS}
          width={MOLD_FLOW_FOCUS_WIDTH}
          height={MOLD_FLOW_FOCUS_HEIGHT}
          defaultProps={defaultMoldFlowFocusProps}
        />
      </Folder>
      <Folder name="41-PrecisionGraph">
        <Composition
          id="PrecisionGraph"
          component={PrecisionGraph}
          durationInFrames={PRECISION_GRAPH_DURATION_FRAMES}
          fps={PRECISION_GRAPH_FPS}
          width={PRECISION_GRAPH_WIDTH}
          height={PRECISION_GRAPH_HEIGHT}
          defaultProps={defaultPrecisionGraphProps}
        />
      </Folder>
      <Folder name="42-GraphAnimateCurve">
        <Composition
          id="GraphAnimateCurve"
          component={GraphAnimateCurve}
          durationInFrames={GRAPH_ANIMATE_DURATION_FRAMES}
          fps={GRAPH_ANIMATE_FPS}
          width={GRAPH_ANIMATE_WIDTH}
          height={GRAPH_ANIMATE_HEIGHT}
          defaultProps={defaultGraphAnimateCurveProps}
        />
      </Folder>
      <Folder name="43-LongPrompt">
        <Composition
          id="LongPrompt"
          component={LongPrompt}
          durationInFrames={LONG_PROMPT_DURATION_FRAMES}
          fps={LONG_PROMPT_FPS}
          width={LONG_PROMPT_WIDTH}
          height={LONG_PROMPT_HEIGHT}
          defaultProps={defaultLongPromptProps}
        />
      </Folder>
      <Folder name="44-ShortPromptTests">
        <Composition
          id="ShortPromptTests"
          component={ShortPromptTests}
          durationInFrames={SHORT_PROMPT_DURATION_FRAMES}
          fps={SHORT_PROMPT_FPS}
          width={SHORT_PROMPT_WIDTH}
          height={SHORT_PROMPT_HEIGHT}
          defaultProps={defaultShortPromptTestsProps}
        />
      </Folder>
      <Folder name="45-BothGenerateFinal">
        <Composition
          id="BothGenerateFinal"
          component={BothGenerateFinal}
          durationInFrames={BOTH_GENERATE_DURATION_FRAMES}
          fps={BOTH_GENERATE_FPS}
          width={BOTH_GENERATE_WIDTH}
          height={BOTH_GENERATE_HEIGHT}
          defaultProps={defaultBothGenerateFinalProps}
        />
      </Folder>
      <Folder name="S00-ColdOpen">
        <Composition
          id="ColdOpenSection"
          component={ColdOpenSection}
          durationInFrames={COLD_OPEN_SECTION_DURATION_FRAMES}
          fps={COLD_OPEN_SECTION_FPS}
          width={COLD_OPEN_SECTION_WIDTH}
          height={COLD_OPEN_SECTION_HEIGHT}
          defaultProps={defaultColdOpenSectionProps}
        />
      </Folder>
      <Folder name="S01-Economics">
        <Composition
          id="Part1Economics"
          component={Part1Economics}
          durationInFrames={PART1_DURATION_FRAMES}
          fps={PART1_FPS}
          width={PART1_WIDTH}
          height={PART1_HEIGHT}
          defaultProps={defaultPart1EconomicsProps}
        />
      </Folder>
      <Folder name="S02-ParadigmShift">
        <Composition
          id="Part2ParadigmShift"
          component={Part2ParadigmShift}
          durationInFrames={PART2_DURATION_FRAMES}
          fps={PART2_FPS}
          width={PART2_WIDTH}
          height={PART2_HEIGHT}
          defaultProps={defaultPart2ParadigmShiftProps}
        />
      </Folder>
      <Folder name="S03-MoldThreeParts">
        <Composition
          id="Part3MoldThreeParts"
          component={Part3MoldThreeParts}
          durationInFrames={PART3_DURATION_FRAMES}
          fps={PART3_FPS}
          width={PART3_WIDTH}
          height={PART3_HEIGHT}
          defaultProps={defaultPart3MoldThreePartsProps}
        />
      </Folder>
      <Folder name="S04-PrecisionTradeoff">
        <Composition
          id="Part4PrecisionTradeoff"
          component={Part4PrecisionTradeoff}
          durationInFrames={PART4_DURATION_FRAMES}
          fps={PART4_FPS}
          width={PART4_WIDTH}
          height={PART4_HEIGHT}
          defaultProps={defaultPart4PrecisionTradeoffProps}
        />
      </Folder>
      <Folder name="S05-CompoundReturns">
        <Composition
          id="Part5CompoundReturns"
          component={Part5CompoundReturns}
          durationInFrames={PART5_DURATION_FRAMES}
          fps={PART5_FPS}
          width={PART5_WIDTH}
          height={PART5_HEIGHT}
          defaultProps={defaultPart5CompoundReturnsProps}
        />
      </Folder>
      <Folder name="S06-Closing">
        <Composition
          id="ClosingSection"
          component={ClosingSection}
          durationInFrames={CLOSING_DURATION_FRAMES}
          fps={CLOSING_FPS}
          width={CLOSING_WIDTH}
          height={CLOSING_HEIGHT}
          defaultProps={defaultClosingSectionProps}
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
