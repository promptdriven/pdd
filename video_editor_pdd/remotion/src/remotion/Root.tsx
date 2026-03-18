import React from "react";
import { Composition } from "remotion";
import { VisualMediaProvider, VisualContractProvider } from "./_shared/visual-runtime";

import { ColdOpenSection } from "./cold_open";
import { Part1EconomicsSection } from "./part1_economics";
import { Part2ParadigmShiftSection } from "./part2_paradigm_shift";
import { Part3MoldThreePartsSection } from "./part3_mold_three_parts";
import { Part4PrecisionTradeoffSection } from "./part4_precision_tradeoff";
import { Part5CompoundReturnsSection } from "./part5_compound_returns";
import { WhereToStartSection } from "./where_to_start";
import { ClosingSection } from "./closing";
import { ColdOpen01SplitScreenHook } from "./ColdOpen01SplitScreenHook";
import { ColdOpen02ZoomOutAccumulated } from "./ColdOpen02ZoomOutAccumulated";
import { ColdOpen05CodeBlink } from "./ColdOpen05CodeBlink";
import { ColdOpen06StillPatchingBeat } from "./ColdOpen06StillPatchingBeat";
import { ColdOpen07PddTitleCard } from "./ColdOpen07PddTitleCard";
import { Part1Economics01SectionTitleCard } from "./Part1Economics01SectionTitleCard";
import { Part1Economics02SockEconomicsChart } from "./Part1Economics02SockEconomicsChart";
import { Part1Economics03CodeCostTripleLine } from "./Part1Economics03CodeCostTripleLine";
import { Part1Economics04ResearchAnnotations } from "./Part1Economics04ResearchAnnotations";
import { Part1Economics05ContextWindowShrink } from "./Part1Economics05ContextWindowShrink";
import { Part1Economics06TwoByTwoGrid } from "./Part1Economics06TwoByTwoGrid";
import { Part1Economics07SplitContextComparison } from "./Part1Economics07SplitContextComparison";
import { Part1Economics09CrossingLinesMoment } from "./Part1Economics09CrossingLinesMoment";
import { Part1Economics10DoubleMeterInsight } from "./Part1Economics10DoubleMeterInsight";
import { Part2ParadigmShift01SectionTitleCard } from "./Part2ParadigmShift01SectionTitleCard";
import { Part2ParadigmShift04DefectFixTheMold } from "./Part2ParadigmShift04DefectFixTheMold";
import { Part2ParadigmShift05ValueMigrationSplit } from "./Part2ParadigmShift05ValueMigrationSplit";
import { Part2ParadigmShift07VerilogSynthesisTriple } from "./Part2ParadigmShift07VerilogSynthesisTriple";
import { Part2ParadigmShift08SynopsysPddEquivalence } from "./Part2ParadigmShift08SynopsysPddEquivalence";
import { Part2ParadigmShift09AbstractionStaircase } from "./Part2ParadigmShift09AbstractionStaircase";
import { Part2ParadigmShift10NetlistZoomUnreviewable } from "./Part2ParadigmShift10NetlistZoomUnreviewable";
import { Part2ParadigmShift11PromptReplacesReview } from "./Part2ParadigmShift11PromptReplacesReview";
import { Part3MoldThreeParts01SectionTitleCard } from "./Part3MoldThreeParts01SectionTitleCard";
import { Part3MoldThreeParts02MoldCrossSection } from "./Part3MoldThreeParts02MoldCrossSection";
import { Part3MoldThreeParts03TestWallsConstraint } from "./Part3MoldThreeParts03TestWallsConstraint";
import { Part3MoldThreeParts04ResearchAnnotationsAiQuality } from "./Part3MoldThreeParts04ResearchAnnotationsAiQuality";
import { Part3MoldThreeParts06RatchetSplitComparison } from "./Part3MoldThreeParts06RatchetSplitComparison";
import { Part3MoldThreeParts07FiveGenerationsZ3 } from "./Part3MoldThreeParts07FiveGenerationsZ3";
import { Part3MoldThreeParts08PromptCapitalSpecification } from "./Part3MoldThreeParts08PromptCapitalSpecification";
import { Part3MoldThreeParts10ThreeComponentsTable } from "./Part3MoldThreeParts10ThreeComponentsTable";
import { Part4PrecisionTradeoff01SectionTitleCard } from "./Part4PrecisionTradeoff01SectionTitleCard";
import { Part4PrecisionTradeoff02PrinterVsMoldSplit } from "./Part4PrecisionTradeoff02PrinterVsMoldSplit";
import { Part4PrecisionTradeoff03PrecisionTradeoffCurve } from "./Part4PrecisionTradeoff03PrecisionTradeoffCurve";
import { Part4PrecisionTradeoff04PromptComparisonSplit } from "./Part4PrecisionTradeoff04PromptComparisonSplit";
import { Part4PrecisionTradeoff05TestAccumulationInsight } from "./Part4PrecisionTradeoff05TestAccumulationInsight";
import { Part4PrecisionTradeoff06TakeawayCallout } from "./Part4PrecisionTradeoff06TakeawayCallout";
import { Part4PrecisionTradeoff07EmbeddedCodeDocument } from "./Part4PrecisionTradeoff07EmbeddedCodeDocument";
import { Part4PrecisionTradeoff08PromptCodeSpectrum } from "./Part4PrecisionTradeoff08PromptCodeSpectrum";
import { Part5CompoundReturns01SectionTitleCard } from "./Part5CompoundReturns01SectionTitleCard";
import { Part5CompoundReturns02MaintenancePieChart } from "./Part5CompoundReturns02MaintenancePieChart";
import { Part5CompoundReturns03CompoundDebtCurve } from "./Part5CompoundReturns03CompoundDebtCurve";
import { Part5CompoundReturns04DivergingCostCurves } from "./Part5CompoundReturns04DivergingCostCurves";
import { Part5CompoundReturns05InvestmentComparisonTable } from "./Part5CompoundReturns05InvestmentComparisonTable";
import { Part5CompoundReturns06SockCallbackSplit } from "./Part5CompoundReturns06SockCallbackSplit";
import { Part5CompoundReturns07EconomicsCrossingCallback } from "./Part5CompoundReturns07EconomicsCrossingCallback";
import { Part5CompoundReturns08ContrarianQuoteCard } from "./Part5CompoundReturns08ContrarianQuoteCard";
import { WhereToStart01SectionTitleCard } from "./WhereToStart01SectionTitleCard";
import { WhereToStart02LegacyCodebaseReveal } from "./WhereToStart02LegacyCodebaseReveal";
import { WhereToStart03ModuleHighlightUpdate } from "./WhereToStart03ModuleHighlightUpdate";
import { WhereToStart04SourceOfTruthShift } from "./WhereToStart04SourceOfTruthShift";
import { WhereToStart05RegenerateCompareLoop } from "./WhereToStart05RegenerateCompareLoop";
import { WhereToStart06SpreadingGlowMigration } from "./WhereToStart06SpreadingGlowMigration";
import { WhereToStart07NoBigBangCallout } from "./WhereToStart07NoBigBangCallout";
import { Closing01SockCallbackSplit } from "./Closing01SockCallbackSplit";
import { Closing03CodeRegenerateWorkflow } from "./Closing03CodeRegenerateWorkflow";
import { Closing04PddTriangle } from "./Closing04PddTriangle";
import { Closing05DissolveRegenerateLoop } from "./Closing05DissolveRegenerateLoop";
import { Closing06MoldGlowFinale } from "./Closing06MoldGlowFinale";
import { Closing07TheBeat } from "./Closing07TheBeat";
import { Closing08MoldIsWhatMatters } from "./Closing08MoldIsWhatMatters";
import { Closing09FinalTitleCard } from "./Closing09FinalTitleCard";

const PREVIEW_VISUAL_MEDIA: Record<string, Record<string, string>> = {
  "cold_open:05_code_blink": { defaultSrc: "veo/modern_sock_toss.mp4", backgroundSrc: "veo/modern_sock_toss.mp4", outputSrc: "veo/modern_sock_toss.mp4", baseSrc: "veo/modern_sock_toss.mp4" },
  "cold_open:06_still_patching_beat": { defaultSrc: "veo/modern_sock_toss.mp4", backgroundSrc: "veo/modern_sock_toss.mp4", outputSrc: "veo/modern_sock_toss.mp4", baseSrc: "veo/modern_sock_toss.mp4" },
  "cold_open:07_pdd_title_card": { defaultSrc: "veo/modern_sock_toss.mp4", backgroundSrc: "veo/modern_sock_toss.mp4", outputSrc: "veo/modern_sock_toss.mp4", baseSrc: "veo/modern_sock_toss.mp4" },
  "part1_economics:09_crossing_lines_moment": { defaultSrc: "veo/developer_patching_montage.mp4", backgroundSrc: "veo/developer_patching_montage.mp4", outputSrc: "veo/developer_patching_montage.mp4", baseSrc: "veo/developer_patching_montage.mp4" },
  "part1_economics:10_double_meter_insight": { defaultSrc: "veo/developer_patching_montage.mp4", backgroundSrc: "veo/developer_patching_montage.mp4", outputSrc: "veo/developer_patching_montage.mp4", baseSrc: "veo/developer_patching_montage.mp4" },
  "part2_paradigm_shift:04_defect_fix_the_mold": { defaultSrc: "veo/injection_molding_process.mp4", backgroundSrc: "veo/injection_molding_process.mp4", outputSrc: "veo/injection_molding_process.mp4", baseSrc: "veo/injection_molding_process.mp4" },
  "part2_paradigm_shift:05_value_migration_split": { defaultSrc: "veo/injection_molding_process.mp4", backgroundSrc: "veo/injection_molding_process.mp4", outputSrc: "veo/injection_molding_process.mp4", baseSrc: "veo/injection_molding_process.mp4" },
  "part2_paradigm_shift:07_verilog_synthesis_triple": { defaultSrc: "veo/chip_design_1980s_lab.mp4", backgroundSrc: "veo/chip_design_1980s_lab.mp4", outputSrc: "veo/chip_design_1980s_lab.mp4", baseSrc: "veo/chip_design_1980s_lab.mp4" },
  "part2_paradigm_shift:08_synopsys_pdd_equivalence": { defaultSrc: "veo/chip_design_1980s_lab.mp4", backgroundSrc: "veo/chip_design_1980s_lab.mp4", outputSrc: "veo/chip_design_1980s_lab.mp4", baseSrc: "veo/chip_design_1980s_lab.mp4" },
  "part2_paradigm_shift:09_abstraction_staircase": { defaultSrc: "veo/chip_design_1980s_lab.mp4", backgroundSrc: "veo/chip_design_1980s_lab.mp4", outputSrc: "veo/chip_design_1980s_lab.mp4", baseSrc: "veo/chip_design_1980s_lab.mp4" },
  "part2_paradigm_shift:10_netlist_zoom_unreviewable": { defaultSrc: "veo/chip_design_1980s_lab.mp4", backgroundSrc: "veo/chip_design_1980s_lab.mp4", outputSrc: "veo/chip_design_1980s_lab.mp4", baseSrc: "veo/chip_design_1980s_lab.mp4" },
  "part2_paradigm_shift:11_prompt_replaces_review": { defaultSrc: "veo/chip_design_1980s_lab.mp4", backgroundSrc: "veo/chip_design_1980s_lab.mp4", outputSrc: "veo/chip_design_1980s_lab.mp4", baseSrc: "veo/chip_design_1980s_lab.mp4" },
  "part3_mold_three_parts:06_ratchet_split_comparison": { defaultSrc: "veo/bug_adds_wall.mp4", backgroundSrc: "veo/bug_adds_wall.mp4", outputSrc: "veo/bug_adds_wall.mp4", baseSrc: "veo/bug_adds_wall.mp4" },
  "part3_mold_three_parts:07_five_generations_z3": { defaultSrc: "veo/bug_adds_wall.mp4", backgroundSrc: "veo/bug_adds_wall.mp4", outputSrc: "veo/bug_adds_wall.mp4", baseSrc: "veo/bug_adds_wall.mp4" },
  "part3_mold_three_parts:08_prompt_capital_specification": { defaultSrc: "veo/bug_adds_wall.mp4", backgroundSrc: "veo/bug_adds_wall.mp4", outputSrc: "veo/bug_adds_wall.mp4", baseSrc: "veo/bug_adds_wall.mp4" },
  "part3_mold_three_parts:10_three_components_table": { defaultSrc: "veo/grounding_feedback_loop.mp4", backgroundSrc: "veo/grounding_feedback_loop.mp4", outputSrc: "veo/grounding_feedback_loop.mp4", baseSrc: "veo/grounding_feedback_loop.mp4" },
  "closing:01_sock_callback_split": { defaultSrc: "veo/sock_final_discard.mp4", backgroundSrc: "veo/sock_final_discard.mp4", outputSrc: "veo/sock_final_discard.mp4", baseSrc: "veo/sock_final_discard.mp4" },
  "closing:03_code_regenerate_workflow": { defaultSrc: "veo/sock_final_discard.mp4", backgroundSrc: "veo/sock_final_discard.mp4", outputSrc: "veo/sock_final_discard.mp4", baseSrc: "veo/sock_final_discard.mp4" },
  "closing:04_pdd_triangle": { defaultSrc: "veo/sock_final_discard.mp4", backgroundSrc: "veo/sock_final_discard.mp4", outputSrc: "veo/sock_final_discard.mp4", baseSrc: "veo/sock_final_discard.mp4" },
  "closing:05_dissolve_regenerate_loop": { defaultSrc: "veo/sock_final_discard.mp4", backgroundSrc: "veo/sock_final_discard.mp4", outputSrc: "veo/sock_final_discard.mp4", baseSrc: "veo/sock_final_discard.mp4" },
  "closing:06_mold_glow_finale": { defaultSrc: "veo/sock_final_discard.mp4", backgroundSrc: "veo/sock_final_discard.mp4", outputSrc: "veo/sock_final_discard.mp4", baseSrc: "veo/sock_final_discard.mp4" },
  "closing:07_the_beat": { defaultSrc: "veo/sock_final_discard.mp4", backgroundSrc: "veo/sock_final_discard.mp4", outputSrc: "veo/sock_final_discard.mp4", baseSrc: "veo/sock_final_discard.mp4" },
  "closing:08_mold_is_what_matters": { defaultSrc: "veo/sock_final_discard.mp4", backgroundSrc: "veo/sock_final_discard.mp4", outputSrc: "veo/sock_final_discard.mp4", baseSrc: "veo/sock_final_discard.mp4" },
  "closing:09_final_title_card": { defaultSrc: "veo/sock_final_discard.mp4", backgroundSrc: "veo/sock_final_discard.mp4", outputSrc: "veo/sock_final_discard.mp4", baseSrc: "veo/sock_final_discard.mp4" },
};

const PREVIEW_VISUAL_CONTRACTS: Record<string, Record<string, unknown> | null> = {
  "cold_open:01_split_screen_hook": {"specBaseName": "01_split_screen_hook", "dataPoints": null, "overlayConfig": {"gradientOverlay": "bottom"}},
  "cold_open:02_zoom_out_accumulated": {"specBaseName": "02_zoom_out_accumulated", "dataPoints": null, "overlayConfig": null},
  "cold_open:05_code_blink": {"specBaseName": "05_code_blink", "dataPoints": null, "overlayConfig": null},
  "cold_open:06_still_patching_beat": {"specBaseName": "06_still_patching_beat", "dataPoints": null, "overlayConfig": null},
  "cold_open:07_pdd_title_card": {"specBaseName": "07_pdd_title_card", "dataPoints": null, "overlayConfig": null},
  "part1_economics:01_section_title_card": {"specBaseName": "01_section_title_card", "dataPoints": null, "overlayConfig": null},
  "part1_economics:02_sock_economics_chart": {"specBaseName": "02_sock_economics_chart", "dataPoints": null, "overlayConfig": null},
  "part1_economics:03_code_cost_triple_line": {"specBaseName": "03_code_cost_triple_line", "dataPoints": null, "overlayConfig": null},
  "part1_economics:04_research_annotations": {"specBaseName": "04_research_annotations", "dataPoints": null, "overlayConfig": null},
  "part1_economics:05_context_window_shrink": {"specBaseName": "05_context_window_shrink", "dataPoints": null, "overlayConfig": null},
  "part1_economics:06_two_by_two_grid": {"specBaseName": "06_two_by_two_grid", "dataPoints": null, "overlayConfig": null},
  "part1_economics:07_split_context_comparison": {"specBaseName": "07_split_context_comparison", "dataPoints": null, "overlayConfig": null},
  "part1_economics:09_crossing_lines_moment": {"specBaseName": "09_crossing_lines_moment", "dataPoints": null, "overlayConfig": null},
  "part1_economics:10_double_meter_insight": {"specBaseName": "10_double_meter_insight", "dataPoints": null, "overlayConfig": null},
  "part2_paradigm_shift:01_section_title_card": {"specBaseName": "01_section_title_card", "dataPoints": null, "overlayConfig": null},
  "part2_paradigm_shift:04_defect_fix_the_mold": {"specBaseName": "04_defect_fix_the_mold", "dataPoints": null, "overlayConfig": null},
  "part2_paradigm_shift:05_value_migration_split": {"specBaseName": "05_value_migration_split", "dataPoints": null, "overlayConfig": null},
  "part2_paradigm_shift:07_verilog_synthesis_triple": {"specBaseName": "07_verilog_synthesis_triple", "dataPoints": null, "overlayConfig": null},
  "part2_paradigm_shift:08_synopsys_pdd_equivalence": {"specBaseName": "08_synopsys_pdd_equivalence", "dataPoints": null, "overlayConfig": null},
  "part2_paradigm_shift:09_abstraction_staircase": {"specBaseName": "09_abstraction_staircase", "dataPoints": null, "overlayConfig": null},
  "part2_paradigm_shift:10_netlist_zoom_unreviewable": {"specBaseName": "10_netlist_zoom_unreviewable", "dataPoints": null, "overlayConfig": null},
  "part2_paradigm_shift:11_prompt_replaces_review": {"specBaseName": "11_prompt_replaces_review", "dataPoints": null, "overlayConfig": null},
  "part3_mold_three_parts:01_section_title_card": {"specBaseName": "01_section_title_card", "dataPoints": null, "overlayConfig": null},
  "part3_mold_three_parts:02_mold_cross_section": {"specBaseName": "02_mold_cross_section", "dataPoints": null, "overlayConfig": null},
  "part3_mold_three_parts:03_test_walls_constraint": {"specBaseName": "03_test_walls_constraint", "dataPoints": null, "overlayConfig": null},
  "part3_mold_three_parts:04_research_annotations_ai_quality": {"specBaseName": "04_research_annotations_ai_quality", "dataPoints": null, "overlayConfig": null},
  "part3_mold_three_parts:06_ratchet_split_comparison": {"specBaseName": "06_ratchet_split_comparison", "dataPoints": null, "overlayConfig": null},
  "part3_mold_three_parts:07_five_generations_z3": {"specBaseName": "07_five_generations_z3", "dataPoints": null, "overlayConfig": null},
  "part3_mold_three_parts:08_prompt_capital_specification": {"specBaseName": "08_prompt_capital_specification", "dataPoints": null, "overlayConfig": null},
  "part3_mold_three_parts:10_three_components_table": {"specBaseName": "10_three_components_table", "dataPoints": null, "overlayConfig": null},
  "part4_precision_tradeoff:01_section_title_card": {"specBaseName": "01_section_title_card", "dataPoints": null, "overlayConfig": null},
  "part4_precision_tradeoff:02_printer_vs_mold_split": {"specBaseName": "02_printer_vs_mold_split", "dataPoints": null, "overlayConfig": null},
  "part4_precision_tradeoff:03_precision_tradeoff_curve": {"specBaseName": "03_precision_tradeoff_curve", "dataPoints": null, "overlayConfig": null},
  "part4_precision_tradeoff:04_prompt_comparison_split": {"specBaseName": "04_prompt_comparison_split", "dataPoints": null, "overlayConfig": null},
  "part4_precision_tradeoff:05_test_accumulation_insight": {"specBaseName": "05_test_accumulation_insight", "dataPoints": null, "overlayConfig": null},
  "part4_precision_tradeoff:06_takeaway_callout": {"specBaseName": "06_takeaway_callout", "dataPoints": null, "overlayConfig": null},
  "part4_precision_tradeoff:07_embedded_code_document": {"specBaseName": "07_embedded_code_document", "dataPoints": null, "overlayConfig": null},
  "part4_precision_tradeoff:08_prompt_code_spectrum": {"specBaseName": "08_prompt_code_spectrum", "dataPoints": null, "overlayConfig": {"gradientOverlay": "bottom"}},
  "part5_compound_returns:01_section_title_card": {"specBaseName": "01_section_title_card", "dataPoints": null, "overlayConfig": null},
  "part5_compound_returns:02_maintenance_pie_chart": {"specBaseName": "02_maintenance_pie_chart", "dataPoints": null, "overlayConfig": null},
  "part5_compound_returns:03_compound_debt_curve": {"specBaseName": "03_compound_debt_curve", "dataPoints": null, "overlayConfig": null},
  "part5_compound_returns:04_diverging_cost_curves": {"specBaseName": "04_diverging_cost_curves", "dataPoints": null, "overlayConfig": null},
  "part5_compound_returns:05_investment_comparison_table": {"specBaseName": "05_investment_comparison_table", "dataPoints": null, "overlayConfig": null},
  "part5_compound_returns:06_sock_callback_split": {"specBaseName": "06_sock_callback_split", "dataPoints": null, "overlayConfig": {"gradientOverlay": "bottom"}},
  "part5_compound_returns:07_economics_crossing_callback": {"specBaseName": "07_economics_crossing_callback", "dataPoints": null, "overlayConfig": null},
  "part5_compound_returns:08_contrarian_quote_card": {"specBaseName": "08_contrarian_quote_card", "dataPoints": null, "overlayConfig": null},
  "where_to_start:01_section_title_card": {"specBaseName": "01_section_title_card", "dataPoints": null, "overlayConfig": null},
  "where_to_start:02_legacy_codebase_reveal": {"specBaseName": "02_legacy_codebase_reveal", "dataPoints": null, "overlayConfig": null},
  "where_to_start:03_module_highlight_update": {"specBaseName": "03_module_highlight_update", "dataPoints": null, "overlayConfig": null},
  "where_to_start:04_source_of_truth_shift": {"specBaseName": "04_source_of_truth_shift", "dataPoints": null, "overlayConfig": null},
  "where_to_start:05_regenerate_compare_loop": {"specBaseName": "05_regenerate_compare_loop", "dataPoints": null, "overlayConfig": null},
  "where_to_start:06_spreading_glow_migration": {"specBaseName": "06_spreading_glow_migration", "dataPoints": null, "overlayConfig": null},
  "where_to_start:07_no_big_bang_callout": {"specBaseName": "07_no_big_bang_callout", "dataPoints": null, "overlayConfig": null},
  "closing:01_sock_callback_split": {"specBaseName": "01_sock_callback_split", "dataPoints": null, "overlayConfig": {"gradientOverlay": "bottom"}},
  "closing:03_code_regenerate_workflow": {"specBaseName": "03_code_regenerate_workflow", "dataPoints": null, "overlayConfig": null},
  "closing:04_pdd_triangle": {"specBaseName": "04_pdd_triangle", "dataPoints": null, "overlayConfig": null},
  "closing:05_dissolve_regenerate_loop": {"specBaseName": "05_dissolve_regenerate_loop", "dataPoints": null, "overlayConfig": null},
  "closing:06_mold_glow_finale": {"specBaseName": "06_mold_glow_finale", "dataPoints": null, "overlayConfig": null},
  "closing:07_the_beat": {"specBaseName": "07_the_beat", "dataPoints": null, "overlayConfig": null},
  "closing:08_mold_is_what_matters": {"specBaseName": "08_mold_is_what_matters", "dataPoints": null, "overlayConfig": null},
  "closing:09_final_title_card": {"specBaseName": "09_final_title_card", "dataPoints": null, "overlayConfig": null},
};

const ColdOpen01SplitScreenHookPreview: React.FC = () => (
  <VisualContractProvider contract={PREVIEW_VISUAL_CONTRACTS["cold_open:01_split_screen_hook"] ?? null}>
    <VisualMediaProvider media={PREVIEW_VISUAL_MEDIA["cold_open:01_split_screen_hook"] ?? null}>
      <ColdOpen01SplitScreenHook />
    </VisualMediaProvider>
  </VisualContractProvider>
);
const ColdOpen02ZoomOutAccumulatedPreview: React.FC = () => (
  <VisualContractProvider contract={PREVIEW_VISUAL_CONTRACTS["cold_open:02_zoom_out_accumulated"] ?? null}>
    <VisualMediaProvider media={PREVIEW_VISUAL_MEDIA["cold_open:02_zoom_out_accumulated"] ?? null}>
      <ColdOpen02ZoomOutAccumulated />
    </VisualMediaProvider>
  </VisualContractProvider>
);
const ColdOpen05CodeBlinkPreview: React.FC = () => (
  <VisualContractProvider contract={PREVIEW_VISUAL_CONTRACTS["cold_open:05_code_blink"] ?? null}>
    <VisualMediaProvider media={PREVIEW_VISUAL_MEDIA["cold_open:05_code_blink"] ?? null}>
      <ColdOpen05CodeBlink />
    </VisualMediaProvider>
  </VisualContractProvider>
);
const ColdOpen06StillPatchingBeatPreview: React.FC = () => (
  <VisualContractProvider contract={PREVIEW_VISUAL_CONTRACTS["cold_open:06_still_patching_beat"] ?? null}>
    <VisualMediaProvider media={PREVIEW_VISUAL_MEDIA["cold_open:06_still_patching_beat"] ?? null}>
      <ColdOpen06StillPatchingBeat />
    </VisualMediaProvider>
  </VisualContractProvider>
);
const ColdOpen07PddTitleCardPreview: React.FC = () => (
  <VisualContractProvider contract={PREVIEW_VISUAL_CONTRACTS["cold_open:07_pdd_title_card"] ?? null}>
    <VisualMediaProvider media={PREVIEW_VISUAL_MEDIA["cold_open:07_pdd_title_card"] ?? null}>
      <ColdOpen07PddTitleCard />
    </VisualMediaProvider>
  </VisualContractProvider>
);
const Part1Economics01SectionTitleCardPreview: React.FC = () => (
  <VisualContractProvider contract={PREVIEW_VISUAL_CONTRACTS["part1_economics:01_section_title_card"] ?? null}>
    <VisualMediaProvider media={PREVIEW_VISUAL_MEDIA["part1_economics:01_section_title_card"] ?? null}>
      <Part1Economics01SectionTitleCard />
    </VisualMediaProvider>
  </VisualContractProvider>
);
const Part1Economics02SockEconomicsChartPreview: React.FC = () => (
  <VisualContractProvider contract={PREVIEW_VISUAL_CONTRACTS["part1_economics:02_sock_economics_chart"] ?? null}>
    <VisualMediaProvider media={PREVIEW_VISUAL_MEDIA["part1_economics:02_sock_economics_chart"] ?? null}>
      <Part1Economics02SockEconomicsChart />
    </VisualMediaProvider>
  </VisualContractProvider>
);
const Part1Economics03CodeCostTripleLinePreview: React.FC = () => (
  <VisualContractProvider contract={PREVIEW_VISUAL_CONTRACTS["part1_economics:03_code_cost_triple_line"] ?? null}>
    <VisualMediaProvider media={PREVIEW_VISUAL_MEDIA["part1_economics:03_code_cost_triple_line"] ?? null}>
      <Part1Economics03CodeCostTripleLine />
    </VisualMediaProvider>
  </VisualContractProvider>
);
const Part1Economics04ResearchAnnotationsPreview: React.FC = () => (
  <VisualContractProvider contract={PREVIEW_VISUAL_CONTRACTS["part1_economics:04_research_annotations"] ?? null}>
    <VisualMediaProvider media={PREVIEW_VISUAL_MEDIA["part1_economics:04_research_annotations"] ?? null}>
      <Part1Economics04ResearchAnnotations />
    </VisualMediaProvider>
  </VisualContractProvider>
);
const Part1Economics05ContextWindowShrinkPreview: React.FC = () => (
  <VisualContractProvider contract={PREVIEW_VISUAL_CONTRACTS["part1_economics:05_context_window_shrink"] ?? null}>
    <VisualMediaProvider media={PREVIEW_VISUAL_MEDIA["part1_economics:05_context_window_shrink"] ?? null}>
      <Part1Economics05ContextWindowShrink />
    </VisualMediaProvider>
  </VisualContractProvider>
);
const Part1Economics06TwoByTwoGridPreview: React.FC = () => (
  <VisualContractProvider contract={PREVIEW_VISUAL_CONTRACTS["part1_economics:06_two_by_two_grid"] ?? null}>
    <VisualMediaProvider media={PREVIEW_VISUAL_MEDIA["part1_economics:06_two_by_two_grid"] ?? null}>
      <Part1Economics06TwoByTwoGrid />
    </VisualMediaProvider>
  </VisualContractProvider>
);
const Part1Economics07SplitContextComparisonPreview: React.FC = () => (
  <VisualContractProvider contract={PREVIEW_VISUAL_CONTRACTS["part1_economics:07_split_context_comparison"] ?? null}>
    <VisualMediaProvider media={PREVIEW_VISUAL_MEDIA["part1_economics:07_split_context_comparison"] ?? null}>
      <Part1Economics07SplitContextComparison />
    </VisualMediaProvider>
  </VisualContractProvider>
);
const Part1Economics09CrossingLinesMomentPreview: React.FC = () => (
  <VisualContractProvider contract={PREVIEW_VISUAL_CONTRACTS["part1_economics:09_crossing_lines_moment"] ?? null}>
    <VisualMediaProvider media={PREVIEW_VISUAL_MEDIA["part1_economics:09_crossing_lines_moment"] ?? null}>
      <Part1Economics09CrossingLinesMoment />
    </VisualMediaProvider>
  </VisualContractProvider>
);
const Part1Economics10DoubleMeterInsightPreview: React.FC = () => (
  <VisualContractProvider contract={PREVIEW_VISUAL_CONTRACTS["part1_economics:10_double_meter_insight"] ?? null}>
    <VisualMediaProvider media={PREVIEW_VISUAL_MEDIA["part1_economics:10_double_meter_insight"] ?? null}>
      <Part1Economics10DoubleMeterInsight />
    </VisualMediaProvider>
  </VisualContractProvider>
);
const Part2ParadigmShift01SectionTitleCardPreview: React.FC = () => (
  <VisualContractProvider contract={PREVIEW_VISUAL_CONTRACTS["part2_paradigm_shift:01_section_title_card"] ?? null}>
    <VisualMediaProvider media={PREVIEW_VISUAL_MEDIA["part2_paradigm_shift:01_section_title_card"] ?? null}>
      <Part2ParadigmShift01SectionTitleCard />
    </VisualMediaProvider>
  </VisualContractProvider>
);
const Part2ParadigmShift04DefectFixTheMoldPreview: React.FC = () => (
  <VisualContractProvider contract={PREVIEW_VISUAL_CONTRACTS["part2_paradigm_shift:04_defect_fix_the_mold"] ?? null}>
    <VisualMediaProvider media={PREVIEW_VISUAL_MEDIA["part2_paradigm_shift:04_defect_fix_the_mold"] ?? null}>
      <Part2ParadigmShift04DefectFixTheMold />
    </VisualMediaProvider>
  </VisualContractProvider>
);
const Part2ParadigmShift05ValueMigrationSplitPreview: React.FC = () => (
  <VisualContractProvider contract={PREVIEW_VISUAL_CONTRACTS["part2_paradigm_shift:05_value_migration_split"] ?? null}>
    <VisualMediaProvider media={PREVIEW_VISUAL_MEDIA["part2_paradigm_shift:05_value_migration_split"] ?? null}>
      <Part2ParadigmShift05ValueMigrationSplit />
    </VisualMediaProvider>
  </VisualContractProvider>
);
const Part2ParadigmShift07VerilogSynthesisTriplePreview: React.FC = () => (
  <VisualContractProvider contract={PREVIEW_VISUAL_CONTRACTS["part2_paradigm_shift:07_verilog_synthesis_triple"] ?? null}>
    <VisualMediaProvider media={PREVIEW_VISUAL_MEDIA["part2_paradigm_shift:07_verilog_synthesis_triple"] ?? null}>
      <Part2ParadigmShift07VerilogSynthesisTriple />
    </VisualMediaProvider>
  </VisualContractProvider>
);
const Part2ParadigmShift08SynopsysPddEquivalencePreview: React.FC = () => (
  <VisualContractProvider contract={PREVIEW_VISUAL_CONTRACTS["part2_paradigm_shift:08_synopsys_pdd_equivalence"] ?? null}>
    <VisualMediaProvider media={PREVIEW_VISUAL_MEDIA["part2_paradigm_shift:08_synopsys_pdd_equivalence"] ?? null}>
      <Part2ParadigmShift08SynopsysPddEquivalence />
    </VisualMediaProvider>
  </VisualContractProvider>
);
const Part2ParadigmShift09AbstractionStaircasePreview: React.FC = () => (
  <VisualContractProvider contract={PREVIEW_VISUAL_CONTRACTS["part2_paradigm_shift:09_abstraction_staircase"] ?? null}>
    <VisualMediaProvider media={PREVIEW_VISUAL_MEDIA["part2_paradigm_shift:09_abstraction_staircase"] ?? null}>
      <Part2ParadigmShift09AbstractionStaircase />
    </VisualMediaProvider>
  </VisualContractProvider>
);
const Part2ParadigmShift10NetlistZoomUnreviewablePreview: React.FC = () => (
  <VisualContractProvider contract={PREVIEW_VISUAL_CONTRACTS["part2_paradigm_shift:10_netlist_zoom_unreviewable"] ?? null}>
    <VisualMediaProvider media={PREVIEW_VISUAL_MEDIA["part2_paradigm_shift:10_netlist_zoom_unreviewable"] ?? null}>
      <Part2ParadigmShift10NetlistZoomUnreviewable />
    </VisualMediaProvider>
  </VisualContractProvider>
);
const Part2ParadigmShift11PromptReplacesReviewPreview: React.FC = () => (
  <VisualContractProvider contract={PREVIEW_VISUAL_CONTRACTS["part2_paradigm_shift:11_prompt_replaces_review"] ?? null}>
    <VisualMediaProvider media={PREVIEW_VISUAL_MEDIA["part2_paradigm_shift:11_prompt_replaces_review"] ?? null}>
      <Part2ParadigmShift11PromptReplacesReview />
    </VisualMediaProvider>
  </VisualContractProvider>
);
const Part3MoldThreeParts01SectionTitleCardPreview: React.FC = () => (
  <VisualContractProvider contract={PREVIEW_VISUAL_CONTRACTS["part3_mold_three_parts:01_section_title_card"] ?? null}>
    <VisualMediaProvider media={PREVIEW_VISUAL_MEDIA["part3_mold_three_parts:01_section_title_card"] ?? null}>
      <Part3MoldThreeParts01SectionTitleCard />
    </VisualMediaProvider>
  </VisualContractProvider>
);
const Part3MoldThreeParts02MoldCrossSectionPreview: React.FC = () => (
  <VisualContractProvider contract={PREVIEW_VISUAL_CONTRACTS["part3_mold_three_parts:02_mold_cross_section"] ?? null}>
    <VisualMediaProvider media={PREVIEW_VISUAL_MEDIA["part3_mold_three_parts:02_mold_cross_section"] ?? null}>
      <Part3MoldThreeParts02MoldCrossSection />
    </VisualMediaProvider>
  </VisualContractProvider>
);
const Part3MoldThreeParts03TestWallsConstraintPreview: React.FC = () => (
  <VisualContractProvider contract={PREVIEW_VISUAL_CONTRACTS["part3_mold_three_parts:03_test_walls_constraint"] ?? null}>
    <VisualMediaProvider media={PREVIEW_VISUAL_MEDIA["part3_mold_three_parts:03_test_walls_constraint"] ?? null}>
      <Part3MoldThreeParts03TestWallsConstraint />
    </VisualMediaProvider>
  </VisualContractProvider>
);
const Part3MoldThreeParts04ResearchAnnotationsAiQualityPreview: React.FC = () => (
  <VisualContractProvider contract={PREVIEW_VISUAL_CONTRACTS["part3_mold_three_parts:04_research_annotations_ai_quality"] ?? null}>
    <VisualMediaProvider media={PREVIEW_VISUAL_MEDIA["part3_mold_three_parts:04_research_annotations_ai_quality"] ?? null}>
      <Part3MoldThreeParts04ResearchAnnotationsAiQuality />
    </VisualMediaProvider>
  </VisualContractProvider>
);
const Part3MoldThreeParts06RatchetSplitComparisonPreview: React.FC = () => (
  <VisualContractProvider contract={PREVIEW_VISUAL_CONTRACTS["part3_mold_three_parts:06_ratchet_split_comparison"] ?? null}>
    <VisualMediaProvider media={PREVIEW_VISUAL_MEDIA["part3_mold_three_parts:06_ratchet_split_comparison"] ?? null}>
      <Part3MoldThreeParts06RatchetSplitComparison />
    </VisualMediaProvider>
  </VisualContractProvider>
);
const Part3MoldThreeParts07FiveGenerationsZ3Preview: React.FC = () => (
  <VisualContractProvider contract={PREVIEW_VISUAL_CONTRACTS["part3_mold_three_parts:07_five_generations_z3"] ?? null}>
    <VisualMediaProvider media={PREVIEW_VISUAL_MEDIA["part3_mold_three_parts:07_five_generations_z3"] ?? null}>
      <Part3MoldThreeParts07FiveGenerationsZ3 />
    </VisualMediaProvider>
  </VisualContractProvider>
);
const Part3MoldThreeParts08PromptCapitalSpecificationPreview: React.FC = () => (
  <VisualContractProvider contract={PREVIEW_VISUAL_CONTRACTS["part3_mold_three_parts:08_prompt_capital_specification"] ?? null}>
    <VisualMediaProvider media={PREVIEW_VISUAL_MEDIA["part3_mold_three_parts:08_prompt_capital_specification"] ?? null}>
      <Part3MoldThreeParts08PromptCapitalSpecification />
    </VisualMediaProvider>
  </VisualContractProvider>
);
const Part3MoldThreeParts10ThreeComponentsTablePreview: React.FC = () => (
  <VisualContractProvider contract={PREVIEW_VISUAL_CONTRACTS["part3_mold_three_parts:10_three_components_table"] ?? null}>
    <VisualMediaProvider media={PREVIEW_VISUAL_MEDIA["part3_mold_three_parts:10_three_components_table"] ?? null}>
      <Part3MoldThreeParts10ThreeComponentsTable />
    </VisualMediaProvider>
  </VisualContractProvider>
);
const Part4PrecisionTradeoff01SectionTitleCardPreview: React.FC = () => (
  <VisualContractProvider contract={PREVIEW_VISUAL_CONTRACTS["part4_precision_tradeoff:01_section_title_card"] ?? null}>
    <VisualMediaProvider media={PREVIEW_VISUAL_MEDIA["part4_precision_tradeoff:01_section_title_card"] ?? null}>
      <Part4PrecisionTradeoff01SectionTitleCard />
    </VisualMediaProvider>
  </VisualContractProvider>
);
const Part4PrecisionTradeoff02PrinterVsMoldSplitPreview: React.FC = () => (
  <VisualContractProvider contract={PREVIEW_VISUAL_CONTRACTS["part4_precision_tradeoff:02_printer_vs_mold_split"] ?? null}>
    <VisualMediaProvider media={PREVIEW_VISUAL_MEDIA["part4_precision_tradeoff:02_printer_vs_mold_split"] ?? null}>
      <Part4PrecisionTradeoff02PrinterVsMoldSplit />
    </VisualMediaProvider>
  </VisualContractProvider>
);
const Part4PrecisionTradeoff03PrecisionTradeoffCurvePreview: React.FC = () => (
  <VisualContractProvider contract={PREVIEW_VISUAL_CONTRACTS["part4_precision_tradeoff:03_precision_tradeoff_curve"] ?? null}>
    <VisualMediaProvider media={PREVIEW_VISUAL_MEDIA["part4_precision_tradeoff:03_precision_tradeoff_curve"] ?? null}>
      <Part4PrecisionTradeoff03PrecisionTradeoffCurve />
    </VisualMediaProvider>
  </VisualContractProvider>
);
const Part4PrecisionTradeoff04PromptComparisonSplitPreview: React.FC = () => (
  <VisualContractProvider contract={PREVIEW_VISUAL_CONTRACTS["part4_precision_tradeoff:04_prompt_comparison_split"] ?? null}>
    <VisualMediaProvider media={PREVIEW_VISUAL_MEDIA["part4_precision_tradeoff:04_prompt_comparison_split"] ?? null}>
      <Part4PrecisionTradeoff04PromptComparisonSplit />
    </VisualMediaProvider>
  </VisualContractProvider>
);
const Part4PrecisionTradeoff05TestAccumulationInsightPreview: React.FC = () => (
  <VisualContractProvider contract={PREVIEW_VISUAL_CONTRACTS["part4_precision_tradeoff:05_test_accumulation_insight"] ?? null}>
    <VisualMediaProvider media={PREVIEW_VISUAL_MEDIA["part4_precision_tradeoff:05_test_accumulation_insight"] ?? null}>
      <Part4PrecisionTradeoff05TestAccumulationInsight />
    </VisualMediaProvider>
  </VisualContractProvider>
);
const Part4PrecisionTradeoff06TakeawayCalloutPreview: React.FC = () => (
  <VisualContractProvider contract={PREVIEW_VISUAL_CONTRACTS["part4_precision_tradeoff:06_takeaway_callout"] ?? null}>
    <VisualMediaProvider media={PREVIEW_VISUAL_MEDIA["part4_precision_tradeoff:06_takeaway_callout"] ?? null}>
      <Part4PrecisionTradeoff06TakeawayCallout />
    </VisualMediaProvider>
  </VisualContractProvider>
);
const Part4PrecisionTradeoff07EmbeddedCodeDocumentPreview: React.FC = () => (
  <VisualContractProvider contract={PREVIEW_VISUAL_CONTRACTS["part4_precision_tradeoff:07_embedded_code_document"] ?? null}>
    <VisualMediaProvider media={PREVIEW_VISUAL_MEDIA["part4_precision_tradeoff:07_embedded_code_document"] ?? null}>
      <Part4PrecisionTradeoff07EmbeddedCodeDocument />
    </VisualMediaProvider>
  </VisualContractProvider>
);
const Part4PrecisionTradeoff08PromptCodeSpectrumPreview: React.FC = () => (
  <VisualContractProvider contract={PREVIEW_VISUAL_CONTRACTS["part4_precision_tradeoff:08_prompt_code_spectrum"] ?? null}>
    <VisualMediaProvider media={PREVIEW_VISUAL_MEDIA["part4_precision_tradeoff:08_prompt_code_spectrum"] ?? null}>
      <Part4PrecisionTradeoff08PromptCodeSpectrum />
    </VisualMediaProvider>
  </VisualContractProvider>
);
const Part5CompoundReturns01SectionTitleCardPreview: React.FC = () => (
  <VisualContractProvider contract={PREVIEW_VISUAL_CONTRACTS["part5_compound_returns:01_section_title_card"] ?? null}>
    <VisualMediaProvider media={PREVIEW_VISUAL_MEDIA["part5_compound_returns:01_section_title_card"] ?? null}>
      <Part5CompoundReturns01SectionTitleCard />
    </VisualMediaProvider>
  </VisualContractProvider>
);
const Part5CompoundReturns02MaintenancePieChartPreview: React.FC = () => (
  <VisualContractProvider contract={PREVIEW_VISUAL_CONTRACTS["part5_compound_returns:02_maintenance_pie_chart"] ?? null}>
    <VisualMediaProvider media={PREVIEW_VISUAL_MEDIA["part5_compound_returns:02_maintenance_pie_chart"] ?? null}>
      <Part5CompoundReturns02MaintenancePieChart />
    </VisualMediaProvider>
  </VisualContractProvider>
);
const Part5CompoundReturns03CompoundDebtCurvePreview: React.FC = () => (
  <VisualContractProvider contract={PREVIEW_VISUAL_CONTRACTS["part5_compound_returns:03_compound_debt_curve"] ?? null}>
    <VisualMediaProvider media={PREVIEW_VISUAL_MEDIA["part5_compound_returns:03_compound_debt_curve"] ?? null}>
      <Part5CompoundReturns03CompoundDebtCurve />
    </VisualMediaProvider>
  </VisualContractProvider>
);
const Part5CompoundReturns04DivergingCostCurvesPreview: React.FC = () => (
  <VisualContractProvider contract={PREVIEW_VISUAL_CONTRACTS["part5_compound_returns:04_diverging_cost_curves"] ?? null}>
    <VisualMediaProvider media={PREVIEW_VISUAL_MEDIA["part5_compound_returns:04_diverging_cost_curves"] ?? null}>
      <Part5CompoundReturns04DivergingCostCurves />
    </VisualMediaProvider>
  </VisualContractProvider>
);
const Part5CompoundReturns05InvestmentComparisonTablePreview: React.FC = () => (
  <VisualContractProvider contract={PREVIEW_VISUAL_CONTRACTS["part5_compound_returns:05_investment_comparison_table"] ?? null}>
    <VisualMediaProvider media={PREVIEW_VISUAL_MEDIA["part5_compound_returns:05_investment_comparison_table"] ?? null}>
      <Part5CompoundReturns05InvestmentComparisonTable />
    </VisualMediaProvider>
  </VisualContractProvider>
);
const Part5CompoundReturns06SockCallbackSplitPreview: React.FC = () => (
  <VisualContractProvider contract={PREVIEW_VISUAL_CONTRACTS["part5_compound_returns:06_sock_callback_split"] ?? null}>
    <VisualMediaProvider media={PREVIEW_VISUAL_MEDIA["part5_compound_returns:06_sock_callback_split"] ?? null}>
      <Part5CompoundReturns06SockCallbackSplit />
    </VisualMediaProvider>
  </VisualContractProvider>
);
const Part5CompoundReturns07EconomicsCrossingCallbackPreview: React.FC = () => (
  <VisualContractProvider contract={PREVIEW_VISUAL_CONTRACTS["part5_compound_returns:07_economics_crossing_callback"] ?? null}>
    <VisualMediaProvider media={PREVIEW_VISUAL_MEDIA["part5_compound_returns:07_economics_crossing_callback"] ?? null}>
      <Part5CompoundReturns07EconomicsCrossingCallback />
    </VisualMediaProvider>
  </VisualContractProvider>
);
const Part5CompoundReturns08ContrarianQuoteCardPreview: React.FC = () => (
  <VisualContractProvider contract={PREVIEW_VISUAL_CONTRACTS["part5_compound_returns:08_contrarian_quote_card"] ?? null}>
    <VisualMediaProvider media={PREVIEW_VISUAL_MEDIA["part5_compound_returns:08_contrarian_quote_card"] ?? null}>
      <Part5CompoundReturns08ContrarianQuoteCard />
    </VisualMediaProvider>
  </VisualContractProvider>
);
const WhereToStart01SectionTitleCardPreview: React.FC = () => (
  <VisualContractProvider contract={PREVIEW_VISUAL_CONTRACTS["where_to_start:01_section_title_card"] ?? null}>
    <VisualMediaProvider media={PREVIEW_VISUAL_MEDIA["where_to_start:01_section_title_card"] ?? null}>
      <WhereToStart01SectionTitleCard />
    </VisualMediaProvider>
  </VisualContractProvider>
);
const WhereToStart02LegacyCodebaseRevealPreview: React.FC = () => (
  <VisualContractProvider contract={PREVIEW_VISUAL_CONTRACTS["where_to_start:02_legacy_codebase_reveal"] ?? null}>
    <VisualMediaProvider media={PREVIEW_VISUAL_MEDIA["where_to_start:02_legacy_codebase_reveal"] ?? null}>
      <WhereToStart02LegacyCodebaseReveal />
    </VisualMediaProvider>
  </VisualContractProvider>
);
const WhereToStart03ModuleHighlightUpdatePreview: React.FC = () => (
  <VisualContractProvider contract={PREVIEW_VISUAL_CONTRACTS["where_to_start:03_module_highlight_update"] ?? null}>
    <VisualMediaProvider media={PREVIEW_VISUAL_MEDIA["where_to_start:03_module_highlight_update"] ?? null}>
      <WhereToStart03ModuleHighlightUpdate />
    </VisualMediaProvider>
  </VisualContractProvider>
);
const WhereToStart04SourceOfTruthShiftPreview: React.FC = () => (
  <VisualContractProvider contract={PREVIEW_VISUAL_CONTRACTS["where_to_start:04_source_of_truth_shift"] ?? null}>
    <VisualMediaProvider media={PREVIEW_VISUAL_MEDIA["where_to_start:04_source_of_truth_shift"] ?? null}>
      <WhereToStart04SourceOfTruthShift />
    </VisualMediaProvider>
  </VisualContractProvider>
);
const WhereToStart05RegenerateCompareLoopPreview: React.FC = () => (
  <VisualContractProvider contract={PREVIEW_VISUAL_CONTRACTS["where_to_start:05_regenerate_compare_loop"] ?? null}>
    <VisualMediaProvider media={PREVIEW_VISUAL_MEDIA["where_to_start:05_regenerate_compare_loop"] ?? null}>
      <WhereToStart05RegenerateCompareLoop />
    </VisualMediaProvider>
  </VisualContractProvider>
);
const WhereToStart06SpreadingGlowMigrationPreview: React.FC = () => (
  <VisualContractProvider contract={PREVIEW_VISUAL_CONTRACTS["where_to_start:06_spreading_glow_migration"] ?? null}>
    <VisualMediaProvider media={PREVIEW_VISUAL_MEDIA["where_to_start:06_spreading_glow_migration"] ?? null}>
      <WhereToStart06SpreadingGlowMigration />
    </VisualMediaProvider>
  </VisualContractProvider>
);
const WhereToStart07NoBigBangCalloutPreview: React.FC = () => (
  <VisualContractProvider contract={PREVIEW_VISUAL_CONTRACTS["where_to_start:07_no_big_bang_callout"] ?? null}>
    <VisualMediaProvider media={PREVIEW_VISUAL_MEDIA["where_to_start:07_no_big_bang_callout"] ?? null}>
      <WhereToStart07NoBigBangCallout />
    </VisualMediaProvider>
  </VisualContractProvider>
);
const Closing01SockCallbackSplitPreview: React.FC = () => (
  <VisualContractProvider contract={PREVIEW_VISUAL_CONTRACTS["closing:01_sock_callback_split"] ?? null}>
    <VisualMediaProvider media={PREVIEW_VISUAL_MEDIA["closing:01_sock_callback_split"] ?? null}>
      <Closing01SockCallbackSplit />
    </VisualMediaProvider>
  </VisualContractProvider>
);
const Closing03CodeRegenerateWorkflowPreview: React.FC = () => (
  <VisualContractProvider contract={PREVIEW_VISUAL_CONTRACTS["closing:03_code_regenerate_workflow"] ?? null}>
    <VisualMediaProvider media={PREVIEW_VISUAL_MEDIA["closing:03_code_regenerate_workflow"] ?? null}>
      <Closing03CodeRegenerateWorkflow />
    </VisualMediaProvider>
  </VisualContractProvider>
);
const Closing04PddTrianglePreview: React.FC = () => (
  <VisualContractProvider contract={PREVIEW_VISUAL_CONTRACTS["closing:04_pdd_triangle"] ?? null}>
    <VisualMediaProvider media={PREVIEW_VISUAL_MEDIA["closing:04_pdd_triangle"] ?? null}>
      <Closing04PddTriangle />
    </VisualMediaProvider>
  </VisualContractProvider>
);
const Closing05DissolveRegenerateLoopPreview: React.FC = () => (
  <VisualContractProvider contract={PREVIEW_VISUAL_CONTRACTS["closing:05_dissolve_regenerate_loop"] ?? null}>
    <VisualMediaProvider media={PREVIEW_VISUAL_MEDIA["closing:05_dissolve_regenerate_loop"] ?? null}>
      <Closing05DissolveRegenerateLoop />
    </VisualMediaProvider>
  </VisualContractProvider>
);
const Closing06MoldGlowFinalePreview: React.FC = () => (
  <VisualContractProvider contract={PREVIEW_VISUAL_CONTRACTS["closing:06_mold_glow_finale"] ?? null}>
    <VisualMediaProvider media={PREVIEW_VISUAL_MEDIA["closing:06_mold_glow_finale"] ?? null}>
      <Closing06MoldGlowFinale />
    </VisualMediaProvider>
  </VisualContractProvider>
);
const Closing07TheBeatPreview: React.FC = () => (
  <VisualContractProvider contract={PREVIEW_VISUAL_CONTRACTS["closing:07_the_beat"] ?? null}>
    <VisualMediaProvider media={PREVIEW_VISUAL_MEDIA["closing:07_the_beat"] ?? null}>
      <Closing07TheBeat />
    </VisualMediaProvider>
  </VisualContractProvider>
);
const Closing08MoldIsWhatMattersPreview: React.FC = () => (
  <VisualContractProvider contract={PREVIEW_VISUAL_CONTRACTS["closing:08_mold_is_what_matters"] ?? null}>
    <VisualMediaProvider media={PREVIEW_VISUAL_MEDIA["closing:08_mold_is_what_matters"] ?? null}>
      <Closing08MoldIsWhatMatters />
    </VisualMediaProvider>
  </VisualContractProvider>
);
const Closing09FinalTitleCardPreview: React.FC = () => (
  <VisualContractProvider contract={PREVIEW_VISUAL_CONTRACTS["closing:09_final_title_card"] ?? null}>
    <VisualMediaProvider media={PREVIEW_VISUAL_MEDIA["closing:09_final_title_card"] ?? null}>
      <Closing09FinalTitleCard />
    </VisualMediaProvider>
  </VisualContractProvider>
);

const PREVIEW_DURATION = 150; // 5s at 30fps

export const RemotionRoot: React.FC = () => {
  return (
    <>
      <Composition
        id="ColdOpenSection"
        component={ColdOpenSection}
        durationInFrames={9}
        fps={30}
        width={1920}
        height={1080}
      />
      <Composition
        id="Part1EconomicsSection"
        component={Part1EconomicsSection}
        durationInFrames={11}
        fps={30}
        width={1920}
        height={1080}
      />
      <Composition
        id="Part2ParadigmShiftSection"
        component={Part2ParadigmShiftSection}
        durationInFrames={6842}
        fps={30}
        width={1920}
        height={1080}
      />
      <Composition
        id="Part3MoldThreePartsSection"
        component={Part3MoldThreePartsSection}
        durationInFrames={10332}
        fps={30}
        width={1920}
        height={1080}
      />
      <Composition
        id="Part4PrecisionTradeoffSection"
        component={Part4PrecisionTradeoffSection}
        durationInFrames={3361}
        fps={30}
        width={1920}
        height={1080}
      />
      <Composition
        id="Part5CompoundReturnsSection"
        component={Part5CompoundReturnsSection}
        durationInFrames={3460}
        fps={30}
        width={1920}
        height={1080}
      />
      <Composition
        id="WhereToStartSection"
        component={WhereToStartSection}
        durationInFrames={978}
        fps={30}
        width={1920}
        height={1080}
      />
      <Composition
        id="ClosingSection"
        component={ClosingSection}
        durationInFrames={628}
        fps={30}
        width={1920}
        height={1080}
      />
      <Composition
        id="cold-open01-split-screen-hook"
        component={ColdOpen01SplitScreenHookPreview}
        durationInFrames={PREVIEW_DURATION}
        fps={30}
        width={1920}
        height={1080}
      />
      <Composition
        id="cold-open02-zoom-out-accumulated"
        component={ColdOpen02ZoomOutAccumulatedPreview}
        durationInFrames={PREVIEW_DURATION}
        fps={30}
        width={1920}
        height={1080}
      />
      <Composition
        id="cold-open05-code-blink"
        component={ColdOpen05CodeBlinkPreview}
        durationInFrames={PREVIEW_DURATION}
        fps={30}
        width={1920}
        height={1080}
      />
      <Composition
        id="cold-open06-still-patching-beat"
        component={ColdOpen06StillPatchingBeatPreview}
        durationInFrames={PREVIEW_DURATION}
        fps={30}
        width={1920}
        height={1080}
      />
      <Composition
        id="cold-open07-pdd-title-card"
        component={ColdOpen07PddTitleCardPreview}
        durationInFrames={PREVIEW_DURATION}
        fps={30}
        width={1920}
        height={1080}
      />
      <Composition
        id="part1-economics01-section-title-card"
        component={Part1Economics01SectionTitleCardPreview}
        durationInFrames={PREVIEW_DURATION}
        fps={30}
        width={1920}
        height={1080}
      />
      <Composition
        id="part1-economics02-sock-economics-chart"
        component={Part1Economics02SockEconomicsChartPreview}
        durationInFrames={PREVIEW_DURATION}
        fps={30}
        width={1920}
        height={1080}
      />
      <Composition
        id="part1-economics03-code-cost-triple-line"
        component={Part1Economics03CodeCostTripleLinePreview}
        durationInFrames={PREVIEW_DURATION}
        fps={30}
        width={1920}
        height={1080}
      />
      <Composition
        id="part1-economics04-research-annotations"
        component={Part1Economics04ResearchAnnotationsPreview}
        durationInFrames={PREVIEW_DURATION}
        fps={30}
        width={1920}
        height={1080}
      />
      <Composition
        id="part1-economics05-context-window-shrink"
        component={Part1Economics05ContextWindowShrinkPreview}
        durationInFrames={PREVIEW_DURATION}
        fps={30}
        width={1920}
        height={1080}
      />
      <Composition
        id="part1-economics06-two-by-two-grid"
        component={Part1Economics06TwoByTwoGridPreview}
        durationInFrames={PREVIEW_DURATION}
        fps={30}
        width={1920}
        height={1080}
      />
      <Composition
        id="part1-economics07-split-context-comparison"
        component={Part1Economics07SplitContextComparisonPreview}
        durationInFrames={PREVIEW_DURATION}
        fps={30}
        width={1920}
        height={1080}
      />
      <Composition
        id="part1-economics09-crossing-lines-moment"
        component={Part1Economics09CrossingLinesMomentPreview}
        durationInFrames={PREVIEW_DURATION}
        fps={30}
        width={1920}
        height={1080}
      />
      <Composition
        id="part1-economics10-double-meter-insight"
        component={Part1Economics10DoubleMeterInsightPreview}
        durationInFrames={PREVIEW_DURATION}
        fps={30}
        width={1920}
        height={1080}
      />
      <Composition
        id="part2-paradigm-shift01-section-title-card"
        component={Part2ParadigmShift01SectionTitleCardPreview}
        durationInFrames={PREVIEW_DURATION}
        fps={30}
        width={1920}
        height={1080}
      />
      <Composition
        id="part2-paradigm-shift04-defect-fix-the-mold"
        component={Part2ParadigmShift04DefectFixTheMoldPreview}
        durationInFrames={PREVIEW_DURATION}
        fps={30}
        width={1920}
        height={1080}
      />
      <Composition
        id="part2-paradigm-shift05-value-migration-split"
        component={Part2ParadigmShift05ValueMigrationSplitPreview}
        durationInFrames={PREVIEW_DURATION}
        fps={30}
        width={1920}
        height={1080}
      />
      <Composition
        id="part2-paradigm-shift07-verilog-synthesis-triple"
        component={Part2ParadigmShift07VerilogSynthesisTriplePreview}
        durationInFrames={PREVIEW_DURATION}
        fps={30}
        width={1920}
        height={1080}
      />
      <Composition
        id="part2-paradigm-shift08-synopsys-pdd-equivalence"
        component={Part2ParadigmShift08SynopsysPddEquivalencePreview}
        durationInFrames={PREVIEW_DURATION}
        fps={30}
        width={1920}
        height={1080}
      />
      <Composition
        id="part2-paradigm-shift09-abstraction-staircase"
        component={Part2ParadigmShift09AbstractionStaircasePreview}
        durationInFrames={PREVIEW_DURATION}
        fps={30}
        width={1920}
        height={1080}
      />
      <Composition
        id="part2-paradigm-shift10-netlist-zoom-unreviewable"
        component={Part2ParadigmShift10NetlistZoomUnreviewablePreview}
        durationInFrames={PREVIEW_DURATION}
        fps={30}
        width={1920}
        height={1080}
      />
      <Composition
        id="part2-paradigm-shift11-prompt-replaces-review"
        component={Part2ParadigmShift11PromptReplacesReviewPreview}
        durationInFrames={PREVIEW_DURATION}
        fps={30}
        width={1920}
        height={1080}
      />
      <Composition
        id="part3-mold-three-parts01-section-title-card"
        component={Part3MoldThreeParts01SectionTitleCardPreview}
        durationInFrames={PREVIEW_DURATION}
        fps={30}
        width={1920}
        height={1080}
      />
      <Composition
        id="part3-mold-three-parts02-mold-cross-section"
        component={Part3MoldThreeParts02MoldCrossSectionPreview}
        durationInFrames={PREVIEW_DURATION}
        fps={30}
        width={1920}
        height={1080}
      />
      <Composition
        id="part3-mold-three-parts03-test-walls-constraint"
        component={Part3MoldThreeParts03TestWallsConstraintPreview}
        durationInFrames={PREVIEW_DURATION}
        fps={30}
        width={1920}
        height={1080}
      />
      <Composition
        id="part3-mold-three-parts04-research-annotations-ai-quality"
        component={Part3MoldThreeParts04ResearchAnnotationsAiQualityPreview}
        durationInFrames={PREVIEW_DURATION}
        fps={30}
        width={1920}
        height={1080}
      />
      <Composition
        id="part3-mold-three-parts06-ratchet-split-comparison"
        component={Part3MoldThreeParts06RatchetSplitComparisonPreview}
        durationInFrames={PREVIEW_DURATION}
        fps={30}
        width={1920}
        height={1080}
      />
      <Composition
        id="part3-mold-three-parts07-five-generations-z3"
        component={Part3MoldThreeParts07FiveGenerationsZ3Preview}
        durationInFrames={PREVIEW_DURATION}
        fps={30}
        width={1920}
        height={1080}
      />
      <Composition
        id="part3-mold-three-parts08-prompt-capital-specification"
        component={Part3MoldThreeParts08PromptCapitalSpecificationPreview}
        durationInFrames={PREVIEW_DURATION}
        fps={30}
        width={1920}
        height={1080}
      />
      <Composition
        id="part3-mold-three-parts10-three-components-table"
        component={Part3MoldThreeParts10ThreeComponentsTablePreview}
        durationInFrames={PREVIEW_DURATION}
        fps={30}
        width={1920}
        height={1080}
      />
      <Composition
        id="part4-precision-tradeoff01-section-title-card"
        component={Part4PrecisionTradeoff01SectionTitleCardPreview}
        durationInFrames={PREVIEW_DURATION}
        fps={30}
        width={1920}
        height={1080}
      />
      <Composition
        id="part4-precision-tradeoff02-printer-vs-mold-split"
        component={Part4PrecisionTradeoff02PrinterVsMoldSplitPreview}
        durationInFrames={PREVIEW_DURATION}
        fps={30}
        width={1920}
        height={1080}
      />
      <Composition
        id="part4-precision-tradeoff03-precision-tradeoff-curve"
        component={Part4PrecisionTradeoff03PrecisionTradeoffCurvePreview}
        durationInFrames={PREVIEW_DURATION}
        fps={30}
        width={1920}
        height={1080}
      />
      <Composition
        id="part4-precision-tradeoff04-prompt-comparison-split"
        component={Part4PrecisionTradeoff04PromptComparisonSplitPreview}
        durationInFrames={PREVIEW_DURATION}
        fps={30}
        width={1920}
        height={1080}
      />
      <Composition
        id="part4-precision-tradeoff05-test-accumulation-insight"
        component={Part4PrecisionTradeoff05TestAccumulationInsightPreview}
        durationInFrames={PREVIEW_DURATION}
        fps={30}
        width={1920}
        height={1080}
      />
      <Composition
        id="part4-precision-tradeoff06-takeaway-callout"
        component={Part4PrecisionTradeoff06TakeawayCalloutPreview}
        durationInFrames={PREVIEW_DURATION}
        fps={30}
        width={1920}
        height={1080}
      />
      <Composition
        id="part4-precision-tradeoff07-embedded-code-document"
        component={Part4PrecisionTradeoff07EmbeddedCodeDocumentPreview}
        durationInFrames={PREVIEW_DURATION}
        fps={30}
        width={1920}
        height={1080}
      />
      <Composition
        id="part4-precision-tradeoff08-prompt-code-spectrum"
        component={Part4PrecisionTradeoff08PromptCodeSpectrumPreview}
        durationInFrames={PREVIEW_DURATION}
        fps={30}
        width={1920}
        height={1080}
      />
      <Composition
        id="part5-compound-returns01-section-title-card"
        component={Part5CompoundReturns01SectionTitleCardPreview}
        durationInFrames={PREVIEW_DURATION}
        fps={30}
        width={1920}
        height={1080}
      />
      <Composition
        id="part5-compound-returns02-maintenance-pie-chart"
        component={Part5CompoundReturns02MaintenancePieChartPreview}
        durationInFrames={PREVIEW_DURATION}
        fps={30}
        width={1920}
        height={1080}
      />
      <Composition
        id="part5-compound-returns03-compound-debt-curve"
        component={Part5CompoundReturns03CompoundDebtCurvePreview}
        durationInFrames={PREVIEW_DURATION}
        fps={30}
        width={1920}
        height={1080}
      />
      <Composition
        id="part5-compound-returns04-diverging-cost-curves"
        component={Part5CompoundReturns04DivergingCostCurvesPreview}
        durationInFrames={PREVIEW_DURATION}
        fps={30}
        width={1920}
        height={1080}
      />
      <Composition
        id="part5-compound-returns05-investment-comparison-table"
        component={Part5CompoundReturns05InvestmentComparisonTablePreview}
        durationInFrames={PREVIEW_DURATION}
        fps={30}
        width={1920}
        height={1080}
      />
      <Composition
        id="part5-compound-returns06-sock-callback-split"
        component={Part5CompoundReturns06SockCallbackSplitPreview}
        durationInFrames={PREVIEW_DURATION}
        fps={30}
        width={1920}
        height={1080}
      />
      <Composition
        id="part5-compound-returns07-economics-crossing-callback"
        component={Part5CompoundReturns07EconomicsCrossingCallbackPreview}
        durationInFrames={PREVIEW_DURATION}
        fps={30}
        width={1920}
        height={1080}
      />
      <Composition
        id="part5-compound-returns08-contrarian-quote-card"
        component={Part5CompoundReturns08ContrarianQuoteCardPreview}
        durationInFrames={PREVIEW_DURATION}
        fps={30}
        width={1920}
        height={1080}
      />
      <Composition
        id="where-to-start01-section-title-card"
        component={WhereToStart01SectionTitleCardPreview}
        durationInFrames={PREVIEW_DURATION}
        fps={30}
        width={1920}
        height={1080}
      />
      <Composition
        id="where-to-start02-legacy-codebase-reveal"
        component={WhereToStart02LegacyCodebaseRevealPreview}
        durationInFrames={PREVIEW_DURATION}
        fps={30}
        width={1920}
        height={1080}
      />
      <Composition
        id="where-to-start03-module-highlight-update"
        component={WhereToStart03ModuleHighlightUpdatePreview}
        durationInFrames={PREVIEW_DURATION}
        fps={30}
        width={1920}
        height={1080}
      />
      <Composition
        id="where-to-start04-source-of-truth-shift"
        component={WhereToStart04SourceOfTruthShiftPreview}
        durationInFrames={PREVIEW_DURATION}
        fps={30}
        width={1920}
        height={1080}
      />
      <Composition
        id="where-to-start05-regenerate-compare-loop"
        component={WhereToStart05RegenerateCompareLoopPreview}
        durationInFrames={PREVIEW_DURATION}
        fps={30}
        width={1920}
        height={1080}
      />
      <Composition
        id="where-to-start06-spreading-glow-migration"
        component={WhereToStart06SpreadingGlowMigrationPreview}
        durationInFrames={PREVIEW_DURATION}
        fps={30}
        width={1920}
        height={1080}
      />
      <Composition
        id="where-to-start07-no-big-bang-callout"
        component={WhereToStart07NoBigBangCalloutPreview}
        durationInFrames={PREVIEW_DURATION}
        fps={30}
        width={1920}
        height={1080}
      />
      <Composition
        id="closing01-sock-callback-split"
        component={Closing01SockCallbackSplitPreview}
        durationInFrames={PREVIEW_DURATION}
        fps={30}
        width={1920}
        height={1080}
      />
      <Composition
        id="closing03-code-regenerate-workflow"
        component={Closing03CodeRegenerateWorkflowPreview}
        durationInFrames={PREVIEW_DURATION}
        fps={30}
        width={1920}
        height={1080}
      />
      <Composition
        id="closing04-pdd-triangle"
        component={Closing04PddTrianglePreview}
        durationInFrames={PREVIEW_DURATION}
        fps={30}
        width={1920}
        height={1080}
      />
      <Composition
        id="closing05-dissolve-regenerate-loop"
        component={Closing05DissolveRegenerateLoopPreview}
        durationInFrames={PREVIEW_DURATION}
        fps={30}
        width={1920}
        height={1080}
      />
      <Composition
        id="closing06-mold-glow-finale"
        component={Closing06MoldGlowFinalePreview}
        durationInFrames={PREVIEW_DURATION}
        fps={30}
        width={1920}
        height={1080}
      />
      <Composition
        id="closing07-the-beat"
        component={Closing07TheBeatPreview}
        durationInFrames={PREVIEW_DURATION}
        fps={30}
        width={1920}
        height={1080}
      />
      <Composition
        id="closing08-mold-is-what-matters"
        component={Closing08MoldIsWhatMattersPreview}
        durationInFrames={PREVIEW_DURATION}
        fps={30}
        width={1920}
        height={1080}
      />
      <Composition
        id="closing09-final-title-card"
        component={Closing09FinalTitleCardPreview}
        durationInFrames={PREVIEW_DURATION}
        fps={30}
        width={1920}
        height={1080}
      />
    </>
  );
};
