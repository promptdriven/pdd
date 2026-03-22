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
import { ColdOpen06CodeBlinkPatched } from "./ColdOpen06CodeBlinkPatched";
import { ColdOpen07CodeRegeneration } from "./ColdOpen07CodeRegeneration";
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
  "cold_open:01_split_screen_hook": { defaultSrc: "veo/developer_ai_edit.mp4", backgroundSrc: "veo/developer_ai_edit.mp4", outputSrc: "veo/developer_ai_edit.mp4", baseSrc: "veo/developer_ai_edit.mp4" },
  "cold_open:06_code_blink_patched": { defaultSrc: "veo/sock_toss.mp4", backgroundSrc: "veo/sock_toss.mp4", outputSrc: "veo/sock_toss.mp4", baseSrc: "veo/sock_toss.mp4" },
  "cold_open:07_code_regeneration": { defaultSrc: "veo/sock_toss.mp4", backgroundSrc: "veo/sock_toss.mp4", outputSrc: "veo/sock_toss.mp4", baseSrc: "veo/sock_toss.mp4" },
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
  "closing:01_sock_callback_split": { leftSrc: "veo/sock_final_discard.mp4", defaultSrc: "veo/sock_final_discard.mp4", backgroundSrc: "veo/sock_final_discard.mp4", outputSrc: "veo/sock_final_discard.mp4", baseSrc: "veo/sock_final_discard.mp4" },
  "closing:03_code_regenerate_workflow": { defaultSrc: "veo/sock_final_discard.mp4", backgroundSrc: "veo/sock_final_discard.mp4", outputSrc: "veo/sock_final_discard.mp4", baseSrc: "veo/sock_final_discard.mp4" },
  "closing:04_pdd_triangle": { defaultSrc: "veo/sock_final_discard.mp4", backgroundSrc: "veo/sock_final_discard.mp4", outputSrc: "veo/sock_final_discard.mp4", baseSrc: "veo/sock_final_discard.mp4" },
  "closing:05_dissolve_regenerate_loop": { defaultSrc: "veo/sock_final_discard.mp4", backgroundSrc: "veo/sock_final_discard.mp4", outputSrc: "veo/sock_final_discard.mp4", baseSrc: "veo/sock_final_discard.mp4" },
  "closing:06_mold_glow_finale": { defaultSrc: "veo/sock_final_discard.mp4", backgroundSrc: "veo/sock_final_discard.mp4", outputSrc: "veo/sock_final_discard.mp4", baseSrc: "veo/sock_final_discard.mp4" },
  "closing:07_the_beat": { defaultSrc: "veo/sock_final_discard.mp4", backgroundSrc: "veo/sock_final_discard.mp4", outputSrc: "veo/sock_final_discard.mp4", baseSrc: "veo/sock_final_discard.mp4" },
  "closing:08_mold_is_what_matters": { defaultSrc: "veo/sock_final_discard.mp4", backgroundSrc: "veo/sock_final_discard.mp4", outputSrc: "veo/sock_final_discard.mp4", baseSrc: "veo/sock_final_discard.mp4" },
  "closing:09_final_title_card": { defaultSrc: "veo/sock_final_discard.mp4", backgroundSrc: "veo/sock_final_discard.mp4", outputSrc: "veo/sock_final_discard.mp4", baseSrc: "veo/sock_final_discard.mp4" },
};

const PREVIEW_VISUAL_CONTRACTS: Record<string, Record<string, unknown> | null> = {
  "cold_open:01_split_screen_hook": {"specBaseName": "01_split_screen_hook", "dataPoints": {"type": "split_screen", "layout": "vertical_50_50", "leftClipId": "developer_ai_edit", "rightClipId": "grandmother_darning", "divider": {"width": 1, "color": "#FFFFFF20"}}, "overlayConfig": null, "renderMode": "component"},
  "cold_open:06_code_blink_patched": {"specBaseName": "06_code_blink_patched", "dataPoints": {"type": "code_editor", "language": "typescript", "theme": "vscode_dark", "annotations": [{"line": 4, "text": "// FIXME: edge case from PR #847", "color": "#F44747"}, {"line": 12, "text": "// patched — original logic broke on null", "color": "#F44747"}, {"line": 18, "text": "// TODO: refactor this entire block", "color": "#F4A347"}], "cursorPosition": {"line": 23, "column": 0}, "cursorBlinkMs": 530}, "overlayConfig": null, "renderMode": "component"},
  "cold_open:07_code_regeneration": {"specBaseName": "07_code_regeneration", "dataPoints": {"type": "code_regeneration", "language": "typescript", "theme": "vscode_dark", "patchedLineCount": 23, "cleanLineCount": 16, "generationGlow": "#00D9FF15", "terminalCommand": "pdd generate", "streamRate": "2_lines_per_frame"}, "overlayConfig": null, "renderMode": "component"},
  "part1_economics:01_section_title_card": {"specBaseName": "01_section_title_card", "dataPoints": {"type": "title_card", "sectionNumber": 1, "sectionLabel": "Part 1", "title": "The Economics of Darning", "titleColor": "#D9944A", "subtitle": "Why patching was rational — and when it stopped.", "subtitleColor": "#94A3B8", "backgroundColor": "#0D1117", "narrationSegments": ["part1_economics_001"]}, "overlayConfig": null, "renderMode": "component"},
  "part1_economics:02_sock_economics_chart": {"specBaseName": "02_sock_economics_chart", "dataPoints": {"type": "animated_chart", "chartType": "dual_line_crossover", "xAxis": {"label": "Year", "range": [1950, 1975], "majorInterval": 5, "minorInterval": 1}, "yAxis": {"label": "Cost (% of hourly wage)", "range": [0, 100], "majorInterval": 25}, "series": [{"id": "labor_cost_darn", "label": "Cost to darn (time)", "color": "#D9944A", "data": [{"x": 1950, "y": 35}, {"x": 1955, "y": 34}, {"x": 1960, "y": 33}, {"x": 1965, "y": 33}, {"x": 1970, "y": 32}, {"x": 1975, "y": 32}]}, {"id": "new_sock_cost", "label": "Cost of new socks", "color": "#4A90D9", "data": [{"x": 1950, "y": 80}, {"x": 1955, "y": 55}, {"x": 1960, "y": 38}, {"x": 1962, "y": 33}, {"x": 1965, "y": 25}, {"x": 1970, "y": 18}, {"x": 1975, "y": 14}]}], "crossingPoint": {"x": 1962, "y": 33, "label": "The Threshold"}, "backgroundColor": "#0D1117", "narrationSegments": ["part1_economics_002", "part1_economics_004"]}, "overlayConfig": null, "renderMode": "component"},
  "part1_economics:03_code_cost_triple_line": {"specBaseName": "03_code_cost_triple_line", "dataPoints": {"type": "animated_chart", "chartType": "triple_line_debt_reveal", "xAxis": {"label": "Year", "range": [2015, 2025], "majorInterval": 2, "minorInterval": 1}, "yAxis": {"label": "Cost (Developer Hours)", "range": [0, 20], "majorInterval": 5}, "milestones": [{"x": 2021, "label": "Codex"}, {"x": 2022, "label": "Copilot"}, {"x": 2023, "label": "GPT-4 / Claude"}, {"x": 2024, "label": "Cursor / Claude Code"}], "series": [{"id": "cost_to_generate", "label": "Cost to generate", "color": "#4A90D9", "strokeWidth": 3, "style": "solid", "data": [{"x": 2015, "y": 18}, {"x": 2018, "y": 17.5}, {"x": 2020, "y": 17}, {"x": 2021, "y": 16}, {"x": 2022, "y": 14}, {"x": 2023, "y": 10}, {"x": 2024, "y": 6}, {"x": 2025, "y": 4}]}, {"id": "immediate_patch_cost", "label": "Immediate patch cost", "color": "#D9944A", "strokeWidth": 3, "style": "solid", "data": [{"x": 2015, "y": 8}, {"x": 2018, "y": 7.5}, {"x": 2020, "y": 7}, {"x": 2021, "y": 6}, {"x": 2022, "y": 5}, {"x": 2023, "y": 4}, {"x": 2024, "y": 3}, {"x": 2025, "y": 2}]}, {"id": "total_cost_with_debt", "label": "Total cost (with debt)", "color": "#D9944A", "strokeWidth": 2, "style": "dashed", "data": [{"x": 2015, "y": 14}, {"x": 2018, "y": 14}, {"x": 2020, "y": 13.5}, {"x": 2021, "y": 13.5}, {"x": 2022, "y": 13}, {"x": 2023, "y": 13}, {"x": 2024, "y": 13}, {"x": 2025, "y": 13}]}], "debtShadedArea": {"upperSeries": "total_cost_with_debt", "lowerSeries": "immediate_patch_cost", "color": "#D9944A", "opacity": 0.08}, "backgroundColor": "#0D1117", "narrationSegments": ["part1_economics_005", "part1_economics_006", "part1_economics_008", "part1_economics_009", "part1_economics_011", "part1_economics_012"]}, "overlayConfig": null, "renderMode": "component"},
  "part1_economics:04_research_annotations": {"specBaseName": "04_research_annotations", "dataPoints": {"type": "animated_chart_overlay", "chartType": "annotation_stack", "annotations": [{"id": "github_study", "title": "Individual task: −55%", "source": "GitHub, 2022", "detail": "95 developers, one greenfield task", "color": "#4A90D9", "targetSeries": "immediate_patch_cost", "targetX": 2022}, {"id": "uplevel_study", "title": "Overall throughput: ~0%", "source": "Uplevel, 2024", "detail": "785 developers, one year", "extra": "+41% more bugs", "color": "#D9944A", "targetSeries": "total_cost_with_debt", "targetX": 2024}, {"id": "gitclear_study", "title": ["Code churn: +44%", "Refactoring: −60%"], "source": "GitClear, 2025", "detail": "211M lines analyzed", "color": "#E74C3C", "targetArea": "debt_shaded_area"}], "debtDecomposition": {"upperLayer": {"label": "Code Complexity", "color": "#D9944A", "opacity": 0.1}, "lowerLayer": {"label": "Context Rot", "color": "#D9944A", "opacity": 0.05, "noiseTexture": true}}, "backgroundColor": "#0D1117", "narrationSegments": ["part1_economics_013", "part1_economics_014", "part1_economics_015", "part1_economics_016"]}, "overlayConfig": null, "renderMode": "component"},
  "part1_economics:05_context_window_shrink": {"specBaseName": "05_context_window_shrink", "dataPoints": {"type": "spatial_visualization", "chartType": "context_window_shrink", "gridStages": [{"size": 4, "coverage": 0.8, "coverageColor": "#5AAA6E"}, {"size": 8, "coverage": 0.4, "coverageColor": "#D9C44A"}, {"size": 16, "coverage": 0.1, "coverageColor": "#D9944A"}, {"size": 32, "coverage": 0.02, "coverageColor": "#E74C3C"}], "contextWindow": {"fixedSize": {"width": 480, "height": 480}, "borderColor": "#4A90D9", "glowColor": "#4A90D9"}, "highlights": {"irrelevantInsideWindow": {"count": 4, "color": "#E74C3C"}, "neededOutsideWindow": {"count": 6, "color": "#5AAA6E"}}, "insetGraph": {"title": "Performance vs. Context Length", "citation": "EMNLP, 2025", "degradationRange": "14% to 85%", "lineColor": "#E74C3C"}, "backgroundColor": "#0D1117", "narrationSegments": ["part1_economics_017", "part1_economics_018", "part1_economics_019", "part1_economics_020"]}, "overlayConfig": null, "renderMode": "component"},
  "part1_economics:06_two_by_two_grid": {"specBaseName": "06_two_by_two_grid", "dataPoints": {"type": "quadrant_grid", "chartType": "two_by_two_study_comparison", "axes": {"x": {"left": "Greenfield", "right": "Brownfield"}, "y": {"top": "In-Distribution", "bottom": "Out-of-Distribution"}}, "quadrants": [{"position": "top-left", "study": "GitHub, 2022", "stat": "+55%", "color": "#5AAA6E", "detail": "95 devs, greenfield"}, {"position": "bottom-right", "study": "METR, 2025", "stat": "−19%", "color": "#E74C3C", "detail": "experienced devs, mature repos"}, {"position": "top-right", "label": "Mixed results", "color": "#D9944A"}, {"position": "bottom-left", "label": "Mixed results", "color": "#D9944A"}], "enterpriseIndicator": {"quadrant": "bottom-right", "label": "Most enterprise work", "radius": 100, "color": "#E74C3C"}, "summary": "Every study is correct. They just measured different quadrants.", "backgroundColor": "#0D1117", "narrationSegments": ["part1_economics_021", "part1_economics_022"]}, "overlayConfig": null, "renderMode": "component"},
  "part1_economics:07_split_context_comparison": {"specBaseName": "07_split_context_comparison", "dataPoints": {"type": "split_screen", "layout": "vertical_split", "splitPosition": 960, "leftPanel": {"label": "Agentic Patching", "labelColor": "#D9944A", "content": "dense_code_context_window", "tokenCount": 15000, "irrelevantPercent": 60, "fillPercent": 100, "highlights": {"irrelevant": {"count": 5, "color": "#E74C3C"}, "relevant": {"percent": 8, "color": "#5AAA6E"}}}, "rightPanel": {"label": "PDD Regeneration", "labelColor": "#4A90D9", "content": "prompt_context_window", "tokenCount": 2300, "sections": [{"type": "prompt", "lines": 15, "color": "#4A90D9"}, {"type": "tests", "lines": 12, "color": "#5AAA6E"}, {"type": "grounding", "lines": 6, "color": "#94A3B8"}], "fillPercent": 25, "qualityNote": "100% author-curated"}, "backgroundColor": "#000000", "narrationSegments": ["part1_economics_024", "part1_economics_025"]}, "overlayConfig": null, "renderMode": "component"},
  "part1_economics:09_crossing_lines_moment": {"specBaseName": "09_crossing_lines_moment", "dataPoints": {"type": "animated_chart", "chartType": "forked_line_crossing", "forkedLine": {"forkPoint": {"x": 2020, "y": 7}, "lowerFork": {"id": "small_codebase", "label": "Small codebase", "color": "#5AAA6E", "data": [{"x": 2020, "y": 7}, {"x": 2022, "y": 4}, {"x": 2024, "y": 2}, {"x": 2025, "y": 1}]}, "upperFork": {"id": "large_codebase", "label": "Large codebase", "color": "#E74C3C", "data": [{"x": 2020, "y": 7}, {"x": 2022, "y": 10}, {"x": 2024, "y": 11}, {"x": 2025, "y": 12}]}}, "crossingLabel": "We are here.", "metrAnnotation": {"perceived": "+20%", "actual": "−19%", "perceptionGap": "39 points"}, "accumulationArrow": {"label": "Every patch adds code", "from": "lower_fork", "to": "upper_fork"}, "terminalBreadcrumb": "pdd generate", "backgroundColor": "#0D1117", "narrationSegments": ["part1_economics_025", "part1_economics_026", "part1_economics_032", "part1_economics_033"]}, "overlayConfig": null, "renderMode": "component"},
  "part1_economics:10_double_meter_insight": {"specBaseName": "10_double_meter_insight", "dataPoints": {"type": "double_meter", "chartType": "key_insight_dual_meter", "meters": [{"id": "effective_context_window", "label": "Effective Context Window", "color": "#4A90D9", "position": "left", "scaleMarkers": ["1×", "5×", "10×"], "maxValue": 10, "unit": "×", "citations": ["MIT CSAIL, 2024", "prompt compression ratio 5:1 to 10:1"]}, {"id": "model_performance", "label": "Model Performance", "color": "#5AAA6E", "position": "right", "scaleMarkers": ["baseline", "+50%", "+89%"], "maxValue": 89, "unit": "%", "citations": ["MIT CSAIL: NL context +59-89%", "ACL 2024: NL comments +41% HumanEval"]}], "centerText": "Bigger window AND smarter model.", "summary": "Not one or the other. Both. That's a category shift.", "challenge": "Try it yourself.", "backgroundColor": "#0D1117", "narrationSegments": ["part1_economics_032", "part1_economics_033"]}, "overlayConfig": null, "renderMode": "component"},
  "part2_paradigm_shift:01_section_title_card": {"specBaseName": "01_section_title_card", "dataPoints": {"type": "title_card", "sectionNumber": 2, "sectionLabel": "PART 2", "titleLine1": "THE PARADIGM", "titleLine2": "SHIFT", "backgroundColor": "#0A0F1A", "ghostElements": [{"shape": "mold_cavity_outline", "color": "#D9944A", "component": "injection_mold"}, {"shape": "circuit_schematic", "color": "#4A90D9", "component": "chip_design"}], "narrationSegments": ["part2_001"]}, "overlayConfig": null, "renderMode": "component"},
  "part2_paradigm_shift:04_defect_fix_the_mold": {"specBaseName": "04_defect_fix_the_mold", "dataPoints": {"type": "animated_diagram", "diagramId": "defect_fix_mold", "acts": [{"name": "defect", "frames": [60, 100], "element": "red_pulse_on_part"}, {"name": "rejected_patch", "frames": [100, 140], "element": "ghost_tool_red_x"}, {"name": "fix_mold", "frames": [140, 200], "element": "wall_adjustment_amber"}, {"name": "fixed_parts", "frames": [200, 340], "element": "green_checkmark_parts"}], "colors": {"defect": "#EF4444", "mold_wall": "#D9944A", "fixed": "#5AAA6E", "part": "#94A3B8"}, "backgroundColor": "#0A0F1A", "narrationSegments": ["part2_004"]}, "overlayConfig": null, "renderMode": "component"},
  "part2_paradigm_shift:05_value_migration_split": {"specBaseName": "05_value_migration_split", "dataPoints": {"type": "split_screen", "layout": "vertical_split", "splitPosition": 960, "leftPanel": {"label": "CRAFTING", "concept": "Value lives in the object — history accumulates, loss is permanent", "summaryLabel": "Value lives in the object", "auraTarget": "object", "auraColor": "#C4956A", "background": "#0F172A"}, "rightPanel": {"label": "MOLDING", "concept": "Value lives in the specification — parts are disposable, regenerated at will", "summaryLabel": "Value lives in the specification", "auraTarget": "mold", "auraColor": "#D9944A", "partDissolveAndRegenerate": true, "background": "#0A0F1A"}, "backgroundColor": "#000000", "narrationSegments": ["part2_005"]}, "overlayConfig": null, "renderMode": "component"},
  "part2_paradigm_shift:07_verilog_synthesis_triple": {"specBaseName": "07_verilog_synthesis_triple", "dataPoints": {"type": "animated_diagram", "diagramId": "verilog_synthesis_triple", "phases": [{"name": "schematic_to_verilog", "frames": [0, 180], "elements": ["dissolving_schematic", "verilog_code", "compiler", "single_netlist"]}, {"name": "triple_synthesis", "frames": [180, 540], "elements": ["shared_code", "three_compilers", "three_netlists", "equivalence_checkmarks"]}], "verilogCode": "module counter(\n  input clk, rst,\n  output reg [7:0] count\n);\n  always @(posedge clk)\n    if (rst) count <= 0;\n    else count <= count + 1;\nendmodule", "netlists": [{"id": "netlist_a", "gateCount": 6, "layout": "horizontal_compact"}, {"id": "netlist_b", "gateCount": 8, "layout": "vertical_long"}, {"id": "netlist_c", "gateCount": 5, "layout": "mixed_optimized"}], "equivalence": true, "colors": {"code_keywords": "#C792EA", "code_text": "#E2E8F0", "compiler": "#4A90D9", "gates": "#94A3B8", "checkmark": "#5AAA6E"}, "backgroundColor": "#0A0F1A", "narrationSegments": ["part2_007"]}, "overlayConfig": null, "renderMode": "component"},
  "part2_paradigm_shift:08_synopsys_pdd_equivalence": {"specBaseName": "08_synopsys_pdd_equivalence", "dataPoints": {"type": "animated_diagram", "diagramId": "synopsys_pdd_equivalence", "rows": [{"label": "SYNOPSYS", "color": "#4A90D9", "y": 280, "stages": [{"name": "Verilog spec", "icon": "document_code", "x": 260}, {"name": "Synthesis", "icon": "gear", "x": 560}, {"name": "Hardware", "icon": "gate_cluster", "x": 860, "color": "#94A3B8"}, {"name": "FEC verified", "icon": "shield_check", "x": 1160, "color": "#5AAA6E"}]}, {"label": "PDD", "color": "#D9944A", "y": 680, "stages": [{"name": "Prompt spec", "icon": "document_text", "x": 260}, {"name": "Generation", "icon": "neural_network", "x": 560}, {"name": "Software", "icon": "code_brackets", "x": 860, "color": "#94A3B8"}, {"name": "Tests pass", "icon": "shield_check", "x": 1160, "color": "#5AAA6E"}]}], "equivalenceSymbol": "≡", "summaryText": "Specification in → verified artifact out", "backgroundColor": "#0A0F1A", "narrationSegments": ["part2_008"]}, "overlayConfig": null, "renderMode": "component"},
  "part2_paradigm_shift:09_abstraction_staircase": {"specBaseName": "09_abstraction_staircase", "dataPoints": {"type": "animated_diagram", "diagramId": "abstraction_staircase", "steps": [{"level": 1, "label": "Transistors", "decade": "1970s", "position": [120, 800], "color": "#64748B"}, {"level": 2, "label": "Schematics", "decade": "1980s", "position": [400, 680], "color": "#7A8FA3"}, {"level": 3, "label": "RTL / Verilog", "decade": "1990s", "position": [680, 560], "color": "#94A3B8"}, {"level": 4, "label": "Behavioral / HLS", "decade": "2010s", "position": [960, 440], "color": "#B0BEC5"}, {"level": 5, "label": "Natural Language → Code", "decade": "2020s", "position": [1240, 320], "color": "#D9944A", "active": true}], "transitionArrows": {"label": "Couldn't scale", "color": "#EF4444"}, "citations": ["IEEE 1364-1995 (Verilog standardization)", "Accellera 2010 (90% behavioral IP)", "Microsoft Research 2007+ (Z3 SMT solver)"], "backgroundColor": "#0A0F1A", "narrationSegments": ["part2_009"]}, "overlayConfig": null, "renderMode": "component"},
  "part2_paradigm_shift:10_netlist_zoom_unreviewable": {"specBaseName": "10_netlist_zoom_unreviewable", "dataPoints": {"type": "animated_diagram", "diagramId": "netlist_zoom_unreviewable", "phases": [{"name": "chip_layout_zoom", "frames": [0, 240], "zoomLevels": [1, 2, 4, 8], "gateCount": "~2.4 billion", "colors": {"metal": "#4A90D9", "polysilicon": "#D9944A", "diffusion": "#5AAA6E", "vias": "#E2E8F0"}}, {"name": "code_diff_scroll", "frames": [240, 480], "linesChanged": 10247, "scrollSpeedRange": [2, 30], "addedColor": "#5AAA6E", "deletedColor": "#EF4444"}], "argument": "Code review at AI generation scale is as futile as reviewing a gate-level netlist", "backgroundColor": "#0A0F1A", "narrationSegments": ["part2_010"]}, "overlayConfig": null, "renderMode": "component"},
  "part2_paradigm_shift:11_prompt_replaces_review": {"specBaseName": "11_prompt_replaces_review", "dataPoints": {"type": "split_screen", "layout": "vertical_split", "splitPosition": 960, "leftPanel": {"label": "REVIEW THE CODE", "concept": "Impossible at scale — code review becomes netlist review", "cognitiveLoad": "OVERLOADED", "loadPercent": 100, "background": "#0F172A"}, "rightPanel": {"label": "REVIEW THE SPEC", "concept": "Verify output against spec — review the prompt, run the tests", "cognitiveLoad": "MANAGEABLE", "loadPercent": 25, "tests": ["test_handles_null_input", "test_returns_correct_format", "test_unicode_support", "test_edge_case_empty", "test_performance_under_100ms", "test_idempotent_behavior"], "background": "#0A0F1A"}, "backgroundColor": "#000000", "narrationSegments": ["part2_011"]}, "overlayConfig": null, "renderMode": "component"},
  "part3_mold_three_parts:01_section_title_card": {"specBaseName": "01_section_title_card", "dataPoints": {"type": "title_card", "sectionNumber": 3, "sectionLabel": "PART 3", "titleLine1": "THE MOLD HAS", "titleLine2": "THREE PARTS", "backgroundColor": "#0A0F1A", "ghostElements": [{"shape": "wall_segment", "color": "#D9944A", "component": "tests"}, {"shape": "injection_nozzle", "color": "#4A90D9", "component": "prompts"}, {"shape": "material_swatch", "color": "#5AAA6E", "component": "grounding"}], "narrationSegments": ["part3_001"]}, "overlayConfig": null, "renderMode": "component"},
  "part3_mold_three_parts:02_mold_cross_section": {"specBaseName": "02_mold_cross_section", "dataPoints": {"type": "technical_diagram", "diagramId": "mold_cross_section", "regions": [{"id": "walls", "label": "Test Capital", "color": "#D9944A", "labels": ["null → None", "empty string → ''", "handles unicode", "latency < 100ms"]}, {"id": "nozzle", "label": "Prompt Capital", "color": "#4A90D9", "labels": ["intent", "requirements", "constraints"]}, {"id": "cavity", "label": "Grounding Capital", "color": "#5AAA6E", "labels": ["style", "patterns", "conventions"]}], "backgroundColor": "#0A0F1A", "narrationSegments": ["part3_002"]}, "overlayConfig": null, "renderMode": "component"},
  "part3_mold_three_parts:03_test_walls_constraint": {"specBaseName": "03_test_walls_constraint", "dataPoints": {"type": "fluid_simulation", "diagramId": "test_walls_constraint", "particleCount": 200, "liquidColor": "#4A90D9", "wallColor": "#D9944A", "focusWall": "null → None", "collisionEffects": ["flash", "ripple", "screen_shake"], "terminalCommands": ["pdd generate user_parser", "Generating...", "✓ All 12 tests passing"], "backgroundColor": "#0A0F1A", "narrationSegments": ["part3_003"]}, "overlayConfig": null, "renderMode": "component"},
  "part3_mold_three_parts:04_research_annotations_ai_quality": {"specBaseName": "04_research_annotations_ai_quality", "dataPoints": {"type": "research_annotations", "annotations": [{"id": "coderabbit_2025", "mainText": "1.7× more issues", "color": "#EF4444", "subStats": ["75% more logic errors", "8× more performance problems"], "source": "CodeRabbit, 2025", "finding": "AI-generated code quality deficit"}, {"id": "dora_2025", "mainText": "Amplified delivery", "color": "#5AAA6E", "subStats": ["AI + strong tests = accelerated"], "source": "DORA, 2025", "finding": "Tests transform AI from liability to accelerant"}], "equation": {"left": "AI code + No tests = 1.7× issues", "right": "AI code + Strong tests = Amplified delivery", "differentiator": "The walls"}, "backgroundColor": "#0A0F1A", "narrationSegments": ["part3_004"]}, "overlayConfig": null, "renderMode": "component"},
  "part3_mold_three_parts:06_ratchet_split_comparison": {"specBaseName": "06_ratchet_split_comparison", "dataPoints": {"type": "split_screen", "layout": "vertical_split", "splitPosition": 960, "leftPanel": {"label": "TRADITIONAL", "concept": "Bug → Patch → Repeat forever", "rows": ["Bug: null crash → Patch: add null check", "Same bug: different module → Patch again", "New bug: unicode → Patch: encode input", "Regression → Patch: add condition", "Performance bug → Patch: optimize", "Another null crash → Patch again..."], "background": "#0F172A", "statusColor": "#EF4444"}, "rightPanel": {"label": "PDD", "concept": "Bug → Add wall → Regenerate → Bug impossible forever", "rows": ["Bug found: null crash", "pdd bug user_parser → test wall added", "pdd fix user_parser → All tests pass ✓"], "background": "#0A0F1A", "statusColor": "#5AAA6E"}, "timelineBar": {"left": {"type": "rising_line", "label": "Patching effort"}, "right": {"type": "ratchet_staircase", "label": "Test accumulation"}}, "callout": "A bug fix helps one place. A test prevents that bug everywhere, forever.", "backgroundColor": "#000000", "narrationSegments": ["part3_006"]}, "overlayConfig": null, "renderMode": "component"},
  "part3_mold_three_parts:07_five_generations_z3": {"specBaseName": "07_five_generations_z3", "dataPoints": {"type": "multi_beat", "beats": [{"id": "five_generations", "type": "code_panel_array", "panelCount": 5, "testResults": [{"panel": 1, "result": "fail", "reason": "2 tests failed"}, {"panel": 2, "result": "warning", "reason": "Performance warning"}, {"panel": 3, "result": "pass", "reason": "All 12 tests pass", "winner": true}, {"panel": 4, "result": "fail", "reason": "Null handling error"}, {"panel": 5, "result": "warning", "reason": "Style violations"}], "caption": "Generate five. Pick the one that passes all tests."}, {"id": "z3_formal_proof", "type": "proof_notation", "property": "∀ input ∈ String: parse(input) ∈ {Valid(id), None}", "solver": "Z3 SMT Solver", "comparison": "Synopsys Formality — chip verification", "result": "PROVEN", "annotation": "Not sampling. Mathematical proof."}], "backgroundColor": "#0A0F1A", "narrationSegments": ["part3_007"]}, "overlayConfig": null, "renderMode": "component"},
  "part3_mold_three_parts:08_prompt_capital_specification": {"specBaseName": "08_prompt_capital_specification", "dataPoints": {"type": "multi_beat", "beats": [{"id": "nozzle_labels", "type": "mold_region_focus", "region": "nozzle", "color": "#4A90D9", "promptContent": "Parse user IDs from untrusted input. Return None on failure, never throw. Handle unicode.", "file": "user_parser.prompt"}, {"id": "two_generations", "type": "code_comparison", "variants": ["class UserParser (OOP)", "def parse_user_id (functional)"], "sharedResult": "All tests pass", "caption": "What's locked is the behavior. The code is flexible; the contract is fixed."}, {"id": "compression_ratio", "type": "size_comparison", "ratio": "1:5 to 1:10", "promptLines": 12, "codeLines": 200, "contextAdvantage": "5-10×", "leftWindow": {"tokens": 15000, "content": "raw code"}, "rightWindow": {"tokens": 15000, "content": "10 module prompts"}}], "backgroundColor": "#0A0F1A", "narrationSegments": ["part3_008"]}, "overlayConfig": null, "renderMode": "component"},
  "part3_mold_three_parts:10_three_components_table": {"specBaseName": "10_three_components_table", "dataPoints": {"type": "summary_table", "tableId": "three_components", "rows": [{"component": "Prompt", "encodes": "WHAT (intent)", "owner": "Developer", "color": "#4A90D9"}, {"component": "Grounding", "encodes": "HOW (style)", "owner": "Automatic", "color": "#5AAA6E"}, {"component": "Tests", "encodes": "CORRECTNESS", "owner": "Accumulated", "color": "#D9944A", "emphasized": true}], "conflictRule": "When these conflict, tests win. Always.", "hierarchy": ["Tests", "Prompt", "Grounding"], "closingLine": "The code is output. The mold is what matters.", "backgroundColor": "#0A0F1A", "narrationSegments": ["part3_010"]}, "overlayConfig": null, "renderMode": "component"},
  "part4_precision_tradeoff:01_section_title_card": {"specBaseName": "01_section_title_card", "dataPoints": {"type": "title_card", "sectionNumber": 4, "sectionLabel": "PART 4", "titleLine1": "THE PRECISION", "titleLine2": "TRADEOFF", "backgroundColor": "#0A0F1A", "ghostElements": [{"shape": "dot_matrix", "color": "#94A3B8", "component": "coordinate_precision"}, {"shape": "mold_outline", "color": "#D9944A", "component": "wall_precision"}], "narrationSegments": ["part4_precision_tradeoff_001"]}, "overlayConfig": null, "renderMode": "component"},
  "part4_precision_tradeoff:02_printer_vs_mold_split": {"specBaseName": "02_printer_vs_mold_split", "dataPoints": {"type": "split_screen", "layout": "vertical_split", "splitPosition": 960, "leftPanel": {"label": "3D PRINTING", "concept": "Specify every point — exhaustive precision", "grid": {"rows": 20, "cols": 20, "totalPoints": 400}, "background": "#0F172A", "accentColor": "#94A3B8"}, "rightPanel": {"label": "INJECTION MOLDING", "concept": "Define walls — constraint-based precision", "wallCount": 4, "background": "#0A0F1A", "accentColor": "#D9944A"}, "callout": "Precision through specification vs. precision through constraint", "backgroundColor": "#000000", "narrationSegments": ["part4_precision_tradeoff_002", "part4_precision_tradeoff_003"]}, "overlayConfig": null, "renderMode": "component"},
  "part4_precision_tradeoff:03_precision_tradeoff_curve": {"specBaseName": "03_precision_tradeoff_curve", "dataPoints": {"type": "animated_chart", "chartType": "inverse_curve", "title": "THE PRECISION TRADEOFF", "xAxis": {"label": "Number of Tests", "range": [0, 50], "ticks": [0, 10, 20, 30, 40, 50]}, "yAxis": {"label": "Required Prompt Precision", "range": ["Low", "High"]}, "curve": {"type": "inverse_hyperbola", "color": "#4A90D9", "equation": "y = 180 + 580 * (1 / (1 + 0.08 * x))"}, "zones": [{"label": "Detailed prompt required", "range": [0, 10], "color": "#D9944A"}, {"label": "Intent is enough", "range": [35, 50], "color": "#5AAA6E"}], "backgroundColor": "#0A0F1A", "narrationSegments": ["part4_precision_tradeoff_004", "part4_precision_tradeoff_005", "part4_precision_tradeoff_006"]}, "overlayConfig": null, "renderMode": "component"},
  "part4_precision_tradeoff:04_prompt_comparison_split": {"specBaseName": "04_prompt_comparison_split", "dataPoints": {"type": "split_screen", "layout": "vertical_split", "splitPosition": 960, "leftPanel": {"label": "FEW TESTS", "filename": "parser_v1.prompt", "lineCount": 50, "concept": "Prompt must specify everything — edge cases, errors, constraints", "background": "#0F172A", "accentColor": "#D9944A"}, "rightPanel": {"label": "MANY TESTS", "filename": "parser_v2.prompt", "lineCount": 10, "testCount": 47, "concept": "Prompt only needs intent — tests carry the precision", "background": "#0A0F1A", "accentColor": "#5AAA6E", "terminalCommand": "pdd test parser"}, "callout": "Same output. Different specification strategy.", "backgroundColor": "#000000", "narrationSegments": ["part4_precision_tradeoff_005", "part4_precision_tradeoff_006"]}, "overlayConfig": null, "renderMode": "component"},
  "part4_precision_tradeoff:05_test_accumulation_insight": {"specBaseName": "05_test_accumulation_insight", "dataPoints": {"type": "stage_progression", "title": "TEST ACCUMULATION OVER TIME", "stages": [{"label": "DAY 1", "promptLines": 30, "wallCount": 3, "description": "Prompt carries the weight", "color": "#D9944A"}, {"label": "MONTH 1", "promptLines": 15, "wallCount": 15, "description": "Tests take over", "color": "#94A3B8"}, {"label": "MONTH 6", "promptLines": 5, "wallCount": 40, "description": "Intent is enough", "color": "#5AAA6E"}], "callout": "Not just about catching bugs. It's about making prompts simpler and regeneration safer over time.", "backgroundColor": "#0A0F1A", "narrationSegments": ["part4_precision_tradeoff_007"]}, "overlayConfig": null, "renderMode": "component"},
  "part4_precision_tradeoff:06_takeaway_callout": {"specBaseName": "06_takeaway_callout", "dataPoints": {"type": "callout_text", "lines": [{"text": "The more walls you have,", "emphasis": {"word": "walls", "color": "#D9944A"}}, {"text": "the less you need to specify.", "emphasis": {"word": "less", "scale": 1.1}}, {"text": "The mold does the precision work.", "emphasis": {"word": "mold", "color": "#D9944A", "glow": true}}], "miniAnimation": {"promptLines": {"from": 20, "to": 5}, "wallCount": {"from": 3, "to": 15}}, "backgroundColor": "#080C14", "narrationSegments": ["part4_precision_tradeoff_008"]}, "overlayConfig": null, "renderMode": "component"},
  "part4_precision_tradeoff:07_embedded_code_document": {"specBaseName": "07_embedded_code_document", "dataPoints": {"type": "document_visualization", "filename": "ad_latency_optimizer.prompt", "sections": [{"type": "natural_language", "lines": "1-8", "label": "Intent (natural language)", "color": "#4A90D9"}, {"type": "embedded_code", "lines": "9-18", "label": "Critical algorithm (code)", "color": "#94A3B8", "language": "python"}, {"type": "natural_language", "lines": "19-24", "label": "Constraints (natural language)", "color": "#4A90D9"}], "annotation": "Stay in prompt space as long as possible. Dip into code when you must.", "backgroundColor": "#0A0F1A", "narrationSegments": ["part4_precision_tradeoff_009"]}, "overlayConfig": null, "renderMode": "component"},
  "part4_precision_tradeoff:08_prompt_code_spectrum": {"specBaseName": "08_prompt_code_spectrum", "dataPoints": {"type": "spectrum_visualization", "title": "Prompt-Code Spectrum", "spectrum": {"leftLabel": "Pure natural language", "leftColor": "#4A90D9", "rightLabel": "Pure code", "rightColor": "#94A3B8", "sliderPosition": 0.25}, "regions": [{"label": "Architecture, intent, constraints", "position": 0.12, "color": "#4A90D9"}, {"label": "Edge cases, error handling", "position": 0.35, "color": "#6B8AB5"}, {"label": "Algorithm choice, tuning", "position": 0.66, "color": "#8094A8"}, {"label": "Bit-level ops, inner loops", "position": 0.91, "color": "#94A3B8"}], "codeDipNotches": [0.7, 0.83, 0.95], "keyQuestion": "The question isn't prompts OR code. It's how far into prompt space can you stay?", "answer": "For most of the specification — further than you'd think.", "backgroundColor": "#0A0F1A", "narrationSegments": ["part4_precision_tradeoff_010"]}, "overlayConfig": {"gradientOverlay": "bottom"}, "renderMode": "component"},
  "part5_compound_returns:01_section_title_card": {"specBaseName": "01_section_title_card", "dataPoints": {"type": "title_card", "sectionNumber": 5, "sectionLabel": "PART 5", "titleLine1": "COMPOUND", "titleLine2": "RETURNS", "backgroundColor": "#0A0F1A", "ghostElements": [{"shape": "exponential_curve", "color": "#D9944A", "component": "debt_growth"}, {"shape": "flat_curve", "color": "#4A90D9", "component": "pdd_flat"}], "narrationSegments": ["part5_001"]}, "overlayConfig": null, "renderMode": "component"},
  "part5_compound_returns:02_maintenance_pie_chart": {"specBaseName": "02_maintenance_pie_chart", "dataPoints": {"type": "animated_chart", "chartId": "maintenance_pie", "chartType": "donut", "segments": [{"label": "Initial Development", "percentage": [10, 20], "color": "#4A90D9"}, {"label": "Maintenance", "percentage": [80, 90], "color": "#D9944A"}], "researchCallouts": [{"source": "McKinsey Digital, 2024", "stat": "+40% maintenance cost", "context": "organizations with high technical debt"}, {"source": "Stripe Developer Coefficient, 2018", "stat": "33% of work week", "context": "spent on technical debt"}], "backgroundColor": "#0F172A", "narrationSegments": ["part5_002"]}, "overlayConfig": null, "renderMode": "component"},
  "part5_compound_returns:03_compound_debt_curve": {"specBaseName": "03_compound_debt_curve", "dataPoints": {"type": "animated_chart", "chartId": "compound_debt_curve", "curves": [{"name": "Technical Debt (exponential)", "color": "#D9944A", "formula": "Debt × (1 + Rate)^Time", "dataPoints": [{"x": 1, "y": 1.0}, {"x": 2, "y": 1.4}, {"x": 3, "y": 2.1}, {"x": 5, "y": 4.2}, {"x": 7, "y": 8.5}, {"x": 10, "y": 24.0}]}, {"name": "Regeneration cost (sawtooth)", "color": "#4A90D9", "pattern": "sawtooth", "baseline": 1.0, "peakHeight": 1.5, "resetCycles": 5}], "callout": {"stat": "$1.52T", "context": "annual US tech debt cost", "source": "CISQ, 2022"}, "backgroundColor": "#0F172A", "narrationSegments": ["part5_003"]}, "overlayConfig": null, "renderMode": "component"},
  "part5_compound_returns:04_diverging_cost_curves": {"specBaseName": "04_diverging_cost_curves", "dataPoints": {"type": "animated_chart", "chartId": "diverging_cost_curves", "xAxis": {"label": "Time (years)", "range": [0, 10]}, "yAxis": {"label": "Cumulative Cost", "range": [0, 25]}, "series": [{"name": "Patching", "color": "#D9944A", "pattern": "exponential", "dataPoints": [{"x": 0, "y": 1.0}, {"x": 1, "y": 1.5}, {"x": 2, "y": 2.3}, {"x": 3, "y": 3.5}, {"x": 4, "y": 5.5}, {"x": 5, "y": 8.5}, {"x": 6, "y": 12.0}, {"x": 7, "y": 16.0}, {"x": 8, "y": 20.0}, {"x": 10, "y": 24.0}], "annotation": "Each patch adds debt"}, {"name": "PDD", "color": "#4A90D9", "pattern": "flat_declining", "dataPoints": [{"x": 0, "y": 1.0}, {"x": 1, "y": 1.1}, {"x": 2, "y": 1.0}, {"x": 3, "y": 0.95}, {"x": 5, "y": 0.85}, {"x": 7, "y": 0.8}, {"x": 10, "y": 0.75}], "annotation": "Each test constrains all future generations"}], "gapLabel": "The compounding gap", "origin": {"x": 0, "y": 1.0, "label": "Today"}, "backgroundColor": "#0F172A", "narrationSegments": ["part5_004"]}, "overlayConfig": null, "renderMode": "component"},
  "part5_compound_returns:05_investment_comparison_table": {"specBaseName": "05_investment_comparison_table", "dataPoints": {"type": "comparison_table", "chartId": "investment_comparison", "columns": ["Investment", "Patching", "PDD"], "rows": [{"investment": "Fix a bug", "icon": "bug", "patching": "One place, once", "pdd": "Impossible forever", "pddGlowIntensity": 0.04}, {"investment": "Improve code", "icon": "code_arrow", "patching": "One version", "pdd": "All future versions", "pddGlowIntensity": 0.06}, {"investment": "Document intent", "icon": "document", "patching": "One snapshot", "pdd": "Living specification", "pddGlowIntensity": 0.08}], "summary": "One side compounds against you. The other compounds for you.", "colors": {"patching": "#D9944A", "pdd": "#4A90D9", "text": "#E2E8F0"}, "backgroundColor": "#0F172A", "narrationSegments": ["part5_005"]}, "overlayConfig": null, "renderMode": "component"},
  "part5_compound_returns:06_sock_callback_split": {"specBaseName": "06_sock_callback_split", "dataPoints": {"type": "split_screen", "layout": "vertical_split", "splitPosition": 960, "leftPanel": {"label": "1960", "content": "grandmother_callback_veo", "colorGrade": {"color": "#D4A043", "opacity": 0.04}, "caption": "The economics made it rational.", "crossedOutIcon": "darning_needle", "background": "#000000"}, "rightPanel": {"label": "NOW", "content": "developer_callback_veo", "colorGrade": {"color": "#4A90D9", "opacity": 0.03}, "caption": "Until now, the economics made it rational.", "crossedOutIcon": "patch", "background": "#000000"}, "sharedMoment": {"type": "realization_flash", "frame": 180, "peakOpacity": 0.03}, "embeddedVeoClips": ["grandmother_callback", "developer_callback"], "backgroundColor": "#000000", "narrationSegments": ["part5_006"]}, "overlayConfig": {"gradientOverlay": "bottom"}, "renderMode": "component"},
  "part5_compound_returns:07_economics_crossing_callback": {"specBaseName": "07_economics_crossing_callback", "dataPoints": {"type": "animated_chart", "chartId": "economics_crossing_callback", "callback_from": "sock_economics", "morphSequence": {"initial": {"xRange": [1950, 2020], "line1": {"label": "Labor cost (per hour)", "color": "#D9944A"}, "line2": {"label": "Sock cost", "color": "#4A90D9"}, "crossingYear": 1962, "crossingLabel": "The Threshold"}, "final": {"xRange": [2020, 2030], "line1": {"label": "Patching cost (per fix)", "color": "#D9944A"}, "line2": {"label": "Generation cost", "color": "#4A90D9"}, "crossingYear": 2024, "crossingLabel": "Now"}}, "punchlineIcon": {"type": "darning_needle_strikethrough", "position": [1400, 600]}, "backgroundColor": "#0F172A", "narrationSegments": ["part5_007"]}, "overlayConfig": null, "renderMode": "component"},
  "part5_compound_returns:08_contrarian_quote_card": {"specBaseName": "08_contrarian_quote_card", "dataPoints": {"type": "quote_card", "quote": "This is either the way of the future or it's going to crash and burn spectacularly.", "attribution": "Research engineer, after seeing PDD for the first time", "highlightedPhrases": [{"text": "the way of the future", "color": "#4A90D9", "sentiment": "positive"}, {"text": "crash and burn", "color": "#D9944A", "sentiment": "negative"}, {"text": "spectacularly", "color": "#D9944A", "sentiment": "negative_emphasis"}], "reframe": "He's right — it's a contrarian bet. But the economics are on our side.", "reframeHighlight": {"word": "economics", "color": "#4A90D9"}, "backgroundColor": "#0A0F1A", "narrationSegments": ["part5_008"]}, "overlayConfig": null, "renderMode": "component"},
  "where_to_start:01_section_title_card": {"specBaseName": "01_section_title_card", "dataPoints": {"type": "title_card", "sectionNumber": 6, "sectionLabel": "WHERE TO START", "titleLine1": "WHERE TO", "titleLine2": "START", "backgroundColor": "#0A0F1A", "ghostElements": [{"shape": "network_graph", "color": "#94A3B8", "component": "codebase_topology"}, {"shape": "highlighted_node", "color": "#4A90D9", "component": "starting_point"}], "narrationSegments": ["where_to_start_001"]}, "overlayConfig": null, "renderMode": "component"},
  "where_to_start:02_legacy_codebase_reveal": {"specBaseName": "02_legacy_codebase_reveal", "dataPoints": {"type": "codebase_visualization", "blockCount": 40, "edgeCount": 60, "debtRatio": 0.3, "annotations": [{"text": "// don't touch", "position": [380, 320]}, {"text": "// here be dragons", "position": [1100, 250]}, {"text": "// legacy", "position": [720, 580]}, {"text": "// temporary fix (2019)", "position": [1350, 650]}], "colorScheme": {"clean": "#1E293B", "debt": "#2A1F1F", "annotation": "#EF4444"}, "backgroundColor": "#0A0F1A", "narrationSegments": ["where_to_start_001"]}, "overlayConfig": null, "renderMode": "component"},
  "where_to_start:03_module_highlight_update": {"specBaseName": "03_module_highlight_update", "dataPoints": {"type": "workflow_animation", "workflow": "pdd_update", "sourceFile": "auth_handler.py", "outputFile": "auth_handler.prompt", "promptLines": ["# Auth Handler", "Authenticate incoming requests using JWT.", "Validate token signature and expiration.", "Extract user_id and role from claims.", "Return None on invalid or expired tokens."], "terminalCommands": ["pdd update auth_handler.py", "✓ Created auth_handler.prompt"], "particleStream": {"from": [640, 420], "to": [1100, 380], "count": 25}, "backgroundColor": "#0A0F1A", "narrationSegments": ["where_to_start_002"]}, "overlayConfig": null, "renderMode": "component"},
  "where_to_start:04_source_of_truth_shift": {"specBaseName": "04_source_of_truth_shift", "dataPoints": {"type": "value_migration", "before": {"sourceOfTruth": "auth_handler.py", "role": "code", "state": "active"}, "after": {"sourceOfTruth": "auth_handler.prompt", "role": "specification", "state": "glowing"}, "tests": [{"name": "JWT verify", "status": "passing"}, {"name": "expiry check", "status": "passing"}, {"name": "null safety", "status": "passing"}], "terminalCommand": "pdd test auth_handler", "terminalResult": "3/3 passing", "callout": "The prompt is your new source of truth.", "backgroundColor": "#0A0F1A", "narrationSegments": ["where_to_start_002"]}, "overlayConfig": null, "renderMode": "component"},
  "where_to_start:05_regenerate_compare_loop": {"specBaseName": "05_regenerate_compare_loop", "dataPoints": {"type": "workflow_pipeline", "steps": [{"label": "Generate prompt", "command": "pdd update", "icon": "prompt_doc"}, {"label": "Add tests", "command": "pdd bug", "icon": "wall_icons"}, {"label": "Regenerate", "command": "pdd fix", "icon": "terminal"}, {"label": "Compare", "command": "pdd test", "icon": "diff_view"}], "loopFrom": 3, "loopTo": 1, "loopLabel": "iterate", "progressBar": true, "backgroundColor": "#0A0F1A", "narrationSegments": ["where_to_start_002"]}, "overlayConfig": null, "renderMode": "component"},
  "where_to_start:06_spreading_glow_migration": {"specBaseName": "06_spreading_glow_migration", "dataPoints": {"type": "migration_animation", "totalModules": 40, "conversionWaves": [{"frame": 0, "modules": ["auth_handler"], "cumulative": 1}, {"frame": 20, "modules": ["session_manager", "token_validator"], "cumulative": 3}, {"frame": 60, "modules": ["user_parser", "role_checker"], "cumulative": 5}, {"frame": 110, "modules": ["api_router", "middleware_chain", "rate_limiter"], "cumulative": 8}], "moduleStates": {"unconverted": {"fill": "#1E293B", "border": "#334155"}, "converting": {"border": "#4A90D9", "glowOpacity": 0.2}, "converted": {"fill": "#0F172A", "border": "#4A90D9", "glowOpacity": 0.08}}, "backgroundColor": "#0A0F1A", "narrationSegments": ["where_to_start_003"]}, "overlayConfig": null, "renderMode": "component"},
  "where_to_start:07_no_big_bang_callout": {"specBaseName": "07_no_big_bang_callout", "dataPoints": {"type": "callout_card", "lines": [{"text": "One module at a time.", "weight": 600, "size": 28}, {"text": "No big bang. No rewrite.", "weight": 400, "size": 22}, {"text": "A gradual migration of where value lives — from code to specification.", "weight": 400, "size": 18, "highlights": [{"word": "code", "color": "#64748B"}, {"word": "specification", "color": "#4A90D9", "glow": true}]}], "ghostBackground": "codebase_topology_blurred", "backgroundColor": "#0A0F1A", "narrationSegments": ["where_to_start_003"]}, "overlayConfig": null, "renderMode": "component"},
  "closing:01_sock_callback_split": {"specBaseName": "01_sock_callback_split", "dataPoints": {"type": "split_screen", "layout": "vertical_split", "splitPosition": 960, "leftPanel": {"label": "DISCARD", "content": "sock_final_discard_veo", "colorGrade": {"color": "#D4A043", "opacity": 0.03}, "costLabel": "$2", "costSubLabel": "new pair", "background": "#000000"}, "rightPanel": {"label": "REGENERATE", "content": "code_regenerate_callback_veo", "colorGrade": {"color": "#4A90D9", "opacity": 0.02}, "costLabel": "~30s", "costSubLabel": "regenerated", "terminalSnippet": "pdd bug → pdd fix → ✓", "background": "#000000"}, "embeddedVeoClips": ["sock_final_discard", "code_regenerate_callback"], "backgroundColor": "#000000", "narrationSegments": ["closing_001"]}, "overlayConfig": {"gradientOverlay": "bottom"}, "renderMode": "component"},
  "closing:03_code_regenerate_workflow": {"specBaseName": "03_code_regenerate_workflow", "dataPoints": {"type": "terminal_demo", "demoId": "closing_regenerate_workflow", "zones": {"codeBlock": {"file": "user_parser.py", "language": "python", "bugLine": 12, "action": "dissolve_and_regenerate"}, "testPanel": {"file": "test_user_parser.py", "existingTests": 4, "newTest": "test_null_injection", "finalStatus": "all_pass"}, "terminal": {"commands": ["pdd bug user_parser", "pdd fix user_parser"], "finalOutput": "All tests passing."}}, "annotation": "Never opened the file.", "backgroundColor": "#0A1628", "narrationSegments": ["closing_002"]}, "overlayConfig": null, "renderMode": "component"},
  "closing:04_pdd_triangle": {"specBaseName": "04_pdd_triangle", "dataPoints": {"type": "geometric_diagram", "diagramId": "pdd_triangle", "shape": "equilateral_triangle", "center": [960, 520], "sideLength": 500, "nodes": [{"id": "prompt", "label": "PROMPT", "descriptor": "Encodes intent", "position": "top", "coordinates": [960, 280], "color": "#4A90D9"}, {"id": "tests", "label": "TESTS", "descriptor": "Preserve behavior", "position": "bottom_left", "coordinates": [710, 713], "color": "#D9944A"}, {"id": "grounding", "label": "GROUNDING", "descriptor": "Maintains style", "position": "bottom_right", "coordinates": [1210, 713], "color": "#5AAA6E"}], "centerContent": "generated_code_lines", "backgroundColor": "#0A1225", "narrationSegments": ["closing_003"]}, "overlayConfig": null, "renderMode": "component"},
  "closing:05_dissolve_regenerate_loop": {"specBaseName": "05_dissolve_regenerate_loop", "dataPoints": {"type": "animated_loop", "diagramId": "dissolve_regenerate_loop", "baseTriangle": "pdd_triangle", "cycles": [{"id": 1, "duration_frames": 60, "speed": "slow"}, {"id": 2, "duration_frames": 50, "speed": "medium"}, {"id": 3, "duration_frames": 40, "speed": "fast"}], "particleEffect": {"type": "radial_scatter", "particlesPerLine": [6, 5, 4], "driftRadius": [120, 100, 80]}, "terminalHeartbeat": {"command": "pdd generate", "successMark": "✓"}, "backgroundColor": "#0A1225", "narrationSegments": ["closing_004"]}, "overlayConfig": null, "renderMode": "component"},
  "closing:06_mold_glow_finale": {"specBaseName": "06_mold_glow_finale", "dataPoints": {"type": "animated_diagram", "diagramId": "mold_glow_finale", "baseTriangle": "pdd_triangle", "glowIntensification": {"edgeLayers": 3, "nodeGrowth": {"from": 20, "to": 24}, "nodeColors": {"prompt": {"from": "#4A90D9", "to": "#6AB0F0"}, "tests": {"from": "#D9944A", "to": "#F0B86A"}, "grounding": {"from": "#5AAA6E", "to": "#7CC98E"}}}, "codeDimming": {"from": 0.15, "to": 0.04}, "thesisText": "The code is just plastic.", "particleField": {"count": 35, "colors": ["#4A90D9", "#D9944A", "#5AAA6E"], "direction": "up"}, "backgroundColor": "#080E1A", "narrationSegments": ["closing_005"]}, "overlayConfig": null, "renderMode": "component"},
  "closing:07_the_beat": {"specBaseName": "07_the_beat", "dataPoints": {"type": "dramatic_pause", "diagramId": "the_beat", "baseTriangle": "pdd_triangle", "ghostState": {"edgeOpacity": 0.08, "edgeWidth": 1, "nodeRadius": 12, "nodeOpacity": 0.06}, "singleParticle": {"from": [960, 650], "to": [960, 350], "glintY": 520, "glintPeakOpacity": 0.25}, "narration": null, "backgroundColor": "#060A12", "vignette": {"edgeOpacity": 0.5}, "narrationSegments": ["closing_006"]}, "overlayConfig": null, "renderMode": "component"},
  "closing:08_mold_is_what_matters": {"specBaseName": "08_mold_is_what_matters", "dataPoints": {"type": "title_card", "diagramId": "mold_is_what_matters", "baseTriangle": "pdd_triangle", "triangleState": "reignited_peak", "centerContent": null, "nodes": {"prompt": {"color": "#6AB0F0", "glowColor": "#4A90D9", "glowOpacity": 0.15}, "tests": {"color": "#F0B86A", "glowColor": "#D9944A", "glowOpacity": 0.15}, "grounding": {"color": "#7CC98E", "glowColor": "#5AAA6E", "glowOpacity": 0.15}}, "thesisText": "The mold is what matters.", "backgroundColor": "#060A12", "narrationSegments": ["closing_007"]}, "overlayConfig": null, "renderMode": "component"},
  "closing:09_final_title_card": {"specBaseName": "09_final_title_card", "dataPoints": {"type": "title_card", "cardId": "final_title_card", "title": "Prompt-Driven Development", "commands": ["uv tool install pdd-cli", "pdd update your_module.py"], "url": "pdd.dev", "ghostTriangle": {"edgeOpacity": 0.04, "nodeOpacity": 0.02}, "backgroundColor": "#060A12", "narrationSegments": ["closing_008"]}, "overlayConfig": null, "renderMode": "component"},
};

const ColdOpen01SplitScreenHookPreview: React.FC = () => (
  <VisualContractProvider contract={PREVIEW_VISUAL_CONTRACTS["cold_open:01_split_screen_hook"] ?? null}>
    <VisualMediaProvider media={PREVIEW_VISUAL_MEDIA["cold_open:01_split_screen_hook"] ?? null}>
      <ColdOpen01SplitScreenHook />
    </VisualMediaProvider>
  </VisualContractProvider>
);
const ColdOpen06CodeBlinkPatchedPreview: React.FC = () => (
  <VisualContractProvider contract={PREVIEW_VISUAL_CONTRACTS["cold_open:06_code_blink_patched"] ?? null}>
    <VisualMediaProvider media={PREVIEW_VISUAL_MEDIA["cold_open:06_code_blink_patched"] ?? null}>
      <ColdOpen06CodeBlinkPatched />
    </VisualMediaProvider>
  </VisualContractProvider>
);
const ColdOpen07CodeRegenerationPreview: React.FC = () => (
  <VisualContractProvider contract={PREVIEW_VISUAL_CONTRACTS["cold_open:07_code_regeneration"] ?? null}>
    <VisualMediaProvider media={PREVIEW_VISUAL_MEDIA["cold_open:07_code_regeneration"] ?? null}>
      <ColdOpen07CodeRegeneration />
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

export const RemotionRoot: React.FC = () => {
  return (
    <>
      <Composition
        id="ColdOpenSection"
        component={ColdOpenSection}
        durationInFrames={527}
        fps={30}
        width={1920}
        height={1080}
      />
      <Composition
        id="Part1EconomicsSection"
        component={Part1EconomicsSection}
        durationInFrames={13664}
        fps={30}
        width={1920}
        height={1080}
      />
      <Composition
        id="Part2ParadigmShiftSection"
        component={Part2ParadigmShiftSection}
        durationInFrames={6825}
        fps={30}
        width={1920}
        height={1080}
      />
      <Composition
        id="Part3MoldThreePartsSection"
        component={Part3MoldThreePartsSection}
        durationInFrames={10325}
        fps={30}
        width={1920}
        height={1080}
      />
      <Composition
        id="Part4PrecisionTradeoffSection"
        component={Part4PrecisionTradeoffSection}
        durationInFrames={3356}
        fps={30}
        width={1920}
        height={1080}
      />
      <Composition
        id="Part5CompoundReturnsSection"
        component={Part5CompoundReturnsSection}
        durationInFrames={3453}
        fps={30}
        width={1920}
        height={1080}
      />
      <Composition
        id="WhereToStartSection"
        component={WhereToStartSection}
        durationInFrames={963}
        fps={30}
        width={1920}
        height={1080}
      />
      <Composition
        id="ClosingSection"
        component={ClosingSection}
        durationInFrames={620}
        fps={30}
        width={1920}
        height={1080}
      />
      <Composition
        id="cold-open01-split-screen-hook"
        component={ColdOpen01SplitScreenHookPreview}
        durationInFrames={240}
        fps={30}
        width={1920}
        height={1080}
      />
      <Composition
        id="cold-open06-code-blink-patched"
        component={ColdOpen06CodeBlinkPatchedPreview}
        durationInFrames={150}
        fps={30}
        width={1920}
        height={1080}
      />
      <Composition
        id="cold-open07-code-regeneration"
        component={ColdOpen07CodeRegenerationPreview}
        durationInFrames={270}
        fps={30}
        width={1920}
        height={1080}
      />
      <Composition
        id="part1-economics01-section-title-card"
        component={Part1Economics01SectionTitleCardPreview}
        durationInFrames={120}
        fps={30}
        width={1920}
        height={1080}
      />
      <Composition
        id="part1-economics02-sock-economics-chart"
        component={Part1Economics02SockEconomicsChartPreview}
        durationInFrames={540}
        fps={30}
        width={1920}
        height={1080}
      />
      <Composition
        id="part1-economics03-code-cost-triple-line"
        component={Part1Economics03CodeCostTripleLinePreview}
        durationInFrames={1050}
        fps={30}
        width={1920}
        height={1080}
      />
      <Composition
        id="part1-economics04-research-annotations"
        component={Part1Economics04ResearchAnnotationsPreview}
        durationInFrames={900}
        fps={30}
        width={1920}
        height={1080}
      />
      <Composition
        id="part1-economics05-context-window-shrink"
        component={Part1Economics05ContextWindowShrinkPreview}
        durationInFrames={900}
        fps={30}
        width={1920}
        height={1080}
      />
      <Composition
        id="part1-economics06-two-by-two-grid"
        component={Part1Economics06TwoByTwoGridPreview}
        durationInFrames={750}
        fps={30}
        width={1920}
        height={1080}
      />
      <Composition
        id="part1-economics07-split-context-comparison"
        component={Part1Economics07SplitContextComparisonPreview}
        durationInFrames={600}
        fps={30}
        width={1920}
        height={1080}
      />
      <Composition
        id="part1-economics09-crossing-lines-moment"
        component={Part1Economics09CrossingLinesMomentPreview}
        durationInFrames={750}
        fps={30}
        width={1920}
        height={1080}
      />
      <Composition
        id="part1-economics10-double-meter-insight"
        component={Part1Economics10DoubleMeterInsightPreview}
        durationInFrames={750}
        fps={30}
        width={1920}
        height={1080}
      />
      <Composition
        id="part2-paradigm-shift01-section-title-card"
        component={Part2ParadigmShift01SectionTitleCardPreview}
        durationInFrames={120}
        fps={30}
        width={1920}
        height={1080}
      />
      <Composition
        id="part2-paradigm-shift04-defect-fix-the-mold"
        component={Part2ParadigmShift04DefectFixTheMoldPreview}
        durationInFrames={420}
        fps={30}
        width={1920}
        height={1080}
      />
      <Composition
        id="part2-paradigm-shift05-value-migration-split"
        component={Part2ParadigmShift05ValueMigrationSplitPreview}
        durationInFrames={480}
        fps={30}
        width={1920}
        height={1080}
      />
      <Composition
        id="part2-paradigm-shift07-verilog-synthesis-triple"
        component={Part2ParadigmShift07VerilogSynthesisTriplePreview}
        durationInFrames={540}
        fps={30}
        width={1920}
        height={1080}
      />
      <Composition
        id="part2-paradigm-shift08-synopsys-pdd-equivalence"
        component={Part2ParadigmShift08SynopsysPddEquivalencePreview}
        durationInFrames={360}
        fps={30}
        width={1920}
        height={1080}
      />
      <Composition
        id="part2-paradigm-shift09-abstraction-staircase"
        component={Part2ParadigmShift09AbstractionStaircasePreview}
        durationInFrames={480}
        fps={30}
        width={1920}
        height={1080}
      />
      <Composition
        id="part2-paradigm-shift10-netlist-zoom-unreviewable"
        component={Part2ParadigmShift10NetlistZoomUnreviewablePreview}
        durationInFrames={480}
        fps={30}
        width={1920}
        height={1080}
      />
      <Composition
        id="part2-paradigm-shift11-prompt-replaces-review"
        component={Part2ParadigmShift11PromptReplacesReviewPreview}
        durationInFrames={360}
        fps={30}
        width={1920}
        height={1080}
      />
      <Composition
        id="part3-mold-three-parts01-section-title-card"
        component={Part3MoldThreeParts01SectionTitleCardPreview}
        durationInFrames={120}
        fps={30}
        width={1920}
        height={1080}
      />
      <Composition
        id="part3-mold-three-parts02-mold-cross-section"
        component={Part3MoldThreeParts02MoldCrossSectionPreview}
        durationInFrames={300}
        fps={30}
        width={1920}
        height={1080}
      />
      <Composition
        id="part3-mold-three-parts03-test-walls-constraint"
        component={Part3MoldThreeParts03TestWallsConstraintPreview}
        durationInFrames={360}
        fps={30}
        width={1920}
        height={1080}
      />
      <Composition
        id="part3-mold-three-parts04-research-annotations-ai-quality"
        component={Part3MoldThreeParts04ResearchAnnotationsAiQualityPreview}
        durationInFrames={450}
        fps={30}
        width={1920}
        height={1080}
      />
      <Composition
        id="part3-mold-three-parts06-ratchet-split-comparison"
        component={Part3MoldThreeParts06RatchetSplitComparisonPreview}
        durationInFrames={480}
        fps={30}
        width={1920}
        height={1080}
      />
      <Composition
        id="part3-mold-three-parts07-five-generations-z3"
        component={Part3MoldThreeParts07FiveGenerationsZ3Preview}
        durationInFrames={540}
        fps={30}
        width={1920}
        height={1080}
      />
      <Composition
        id="part3-mold-three-parts08-prompt-capital-specification"
        component={Part3MoldThreeParts08PromptCapitalSpecificationPreview}
        durationInFrames={600}
        fps={30}
        width={1920}
        height={1080}
      />
      <Composition
        id="part3-mold-three-parts10-three-components-table"
        component={Part3MoldThreeParts10ThreeComponentsTablePreview}
        durationInFrames={480}
        fps={30}
        width={1920}
        height={1080}
      />
      <Composition
        id="part4-precision-tradeoff01-section-title-card"
        component={Part4PrecisionTradeoff01SectionTitleCardPreview}
        durationInFrames={120}
        fps={30}
        width={1920}
        height={1080}
      />
      <Composition
        id="part4-precision-tradeoff02-printer-vs-mold-split"
        component={Part4PrecisionTradeoff02PrinterVsMoldSplitPreview}
        durationInFrames={600}
        fps={30}
        width={1920}
        height={1080}
      />
      <Composition
        id="part4-precision-tradeoff03-precision-tradeoff-curve"
        component={Part4PrecisionTradeoff03PrecisionTradeoffCurvePreview}
        durationInFrames={450}
        fps={30}
        width={1920}
        height={1080}
      />
      <Composition
        id="part4-precision-tradeoff04-prompt-comparison-split"
        component={Part4PrecisionTradeoff04PromptComparisonSplitPreview}
        durationInFrames={420}
        fps={30}
        width={1920}
        height={1080}
      />
      <Composition
        id="part4-precision-tradeoff05-test-accumulation-insight"
        component={Part4PrecisionTradeoff05TestAccumulationInsightPreview}
        durationInFrames={300}
        fps={30}
        width={1920}
        height={1080}
      />
      <Composition
        id="part4-precision-tradeoff06-takeaway-callout"
        component={Part4PrecisionTradeoff06TakeawayCalloutPreview}
        durationInFrames={180}
        fps={30}
        width={1920}
        height={1080}
      />
      <Composition
        id="part4-precision-tradeoff07-embedded-code-document"
        component={Part4PrecisionTradeoff07EmbeddedCodeDocumentPreview}
        durationInFrames={480}
        fps={30}
        width={1920}
        height={1080}
      />
      <Composition
        id="part4-precision-tradeoff08-prompt-code-spectrum"
        component={Part4PrecisionTradeoff08PromptCodeSpectrumPreview}
        durationInFrames={360}
        fps={30}
        width={1920}
        height={1080}
      />
      <Composition
        id="part5-compound-returns01-section-title-card"
        component={Part5CompoundReturns01SectionTitleCardPreview}
        durationInFrames={120}
        fps={30}
        width={1920}
        height={1080}
      />
      <Composition
        id="part5-compound-returns02-maintenance-pie-chart"
        component={Part5CompoundReturns02MaintenancePieChartPreview}
        durationInFrames={420}
        fps={30}
        width={1920}
        height={1080}
      />
      <Composition
        id="part5-compound-returns03-compound-debt-curve"
        component={Part5CompoundReturns03CompoundDebtCurvePreview}
        durationInFrames={360}
        fps={30}
        width={1920}
        height={1080}
      />
      <Composition
        id="part5-compound-returns04-diverging-cost-curves"
        component={Part5CompoundReturns04DivergingCostCurvesPreview}
        durationInFrames={420}
        fps={30}
        width={1920}
        height={1080}
      />
      <Composition
        id="part5-compound-returns05-investment-comparison-table"
        component={Part5CompoundReturns05InvestmentComparisonTablePreview}
        durationInFrames={420}
        fps={30}
        width={1920}
        height={1080}
      />
      <Composition
        id="part5-compound-returns06-sock-callback-split"
        component={Part5CompoundReturns06SockCallbackSplitPreview}
        durationInFrames={360}
        fps={30}
        width={1920}
        height={1080}
      />
      <Composition
        id="part5-compound-returns07-economics-crossing-callback"
        component={Part5CompoundReturns07EconomicsCrossingCallbackPreview}
        durationInFrames={300}
        fps={30}
        width={1920}
        height={1080}
      />
      <Composition
        id="part5-compound-returns08-contrarian-quote-card"
        component={Part5CompoundReturns08ContrarianQuoteCardPreview}
        durationInFrames={300}
        fps={30}
        width={1920}
        height={1080}
      />
      <Composition
        id="where-to-start01-section-title-card"
        component={WhereToStart01SectionTitleCardPreview}
        durationInFrames={120}
        fps={30}
        width={1920}
        height={1080}
      />
      <Composition
        id="where-to-start02-legacy-codebase-reveal"
        component={WhereToStart02LegacyCodebaseRevealPreview}
        durationInFrames={150}
        fps={30}
        width={1920}
        height={1080}
      />
      <Composition
        id="where-to-start03-module-highlight-update"
        component={WhereToStart03ModuleHighlightUpdatePreview}
        durationInFrames={240}
        fps={30}
        width={1920}
        height={1080}
      />
      <Composition
        id="where-to-start04-source-of-truth-shift"
        component={WhereToStart04SourceOfTruthShiftPreview}
        durationInFrames={180}
        fps={30}
        width={1920}
        height={1080}
      />
      <Composition
        id="where-to-start05-regenerate-compare-loop"
        component={WhereToStart05RegenerateCompareLoopPreview}
        durationInFrames={180}
        fps={30}
        width={1920}
        height={1080}
      />
      <Composition
        id="where-to-start06-spreading-glow-migration"
        component={WhereToStart06SpreadingGlowMigrationPreview}
        durationInFrames={240}
        fps={30}
        width={1920}
        height={1080}
      />
      <Composition
        id="where-to-start07-no-big-bang-callout"
        component={WhereToStart07NoBigBangCalloutPreview}
        durationInFrames={150}
        fps={30}
        width={1920}
        height={1080}
      />
      <Composition
        id="closing01-sock-callback-split"
        component={Closing01SockCallbackSplitPreview}
        durationInFrames={240}
        fps={30}
        width={1920}
        height={1080}
      />
      <Composition
        id="closing03-code-regenerate-workflow"
        component={Closing03CodeRegenerateWorkflowPreview}
        durationInFrames={300}
        fps={30}
        width={1920}
        height={1080}
      />
      <Composition
        id="closing04-pdd-triangle"
        component={Closing04PddTrianglePreview}
        durationInFrames={300}
        fps={30}
        width={1920}
        height={1080}
      />
      <Composition
        id="closing05-dissolve-regenerate-loop"
        component={Closing05DissolveRegenerateLoopPreview}
        durationInFrames={240}
        fps={30}
        width={1920}
        height={1080}
      />
      <Composition
        id="closing06-mold-glow-finale"
        component={Closing06MoldGlowFinalePreview}
        durationInFrames={240}
        fps={30}
        width={1920}
        height={1080}
      />
      <Composition
        id="closing07-the-beat"
        component={Closing07TheBeatPreview}
        durationInFrames={120}
        fps={30}
        width={1920}
        height={1080}
      />
      <Composition
        id="closing08-mold-is-what-matters"
        component={Closing08MoldIsWhatMattersPreview}
        durationInFrames={180}
        fps={30}
        width={1920}
        height={1080}
      />
      <Composition
        id="closing09-final-title-card"
        component={Closing09FinalTitleCardPreview}
        durationInFrames={240}
        fps={30}
        width={1920}
        height={1080}
      />
    </>
  );
};
