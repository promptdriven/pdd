import React from "react";
import { Composition } from "remotion";
import { VisualMediaProvider, VisualContractProvider } from "./_shared/visual-runtime";
import { GeneratedContractVisual } from "./_shared/GeneratedContractVisual";

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
import { ColdOpen07PddTitleCard } from "./ColdOpen07PddTitleCard";
import { Part1Economics01SectionTitleCard } from "./Part1Economics01SectionTitleCard";
import { Part1Economics04ResearchAnnotations } from "./Part1Economics04ResearchAnnotations";
import { Part1Economics05ContextWindowShrink } from "./Part1Economics05ContextWindowShrink";
import { Part1Economics06TwoByTwoGrid } from "./Part1Economics06TwoByTwoGrid";
import { Part1Economics09CrossingLinesMoment } from "./Part1Economics09CrossingLinesMoment";
import { Part1Economics10DoubleMeterInsight } from "./Part1Economics10DoubleMeterInsight";
import { Part2ParadigmShift01SectionTitleCard } from "./Part2ParadigmShift01SectionTitleCard";
import { Part2ParadigmShift07VerilogSynthesisTriple } from "./Part2ParadigmShift07VerilogSynthesisTriple";
import { Part2ParadigmShift08SynopsysPddEquivalence } from "./Part2ParadigmShift08SynopsysPddEquivalence";
import { Part2ParadigmShift09AbstractionStaircase } from "./Part2ParadigmShift09AbstractionStaircase";
import { Part2ParadigmShift11PromptReplacesReview } from "./Part2ParadigmShift11PromptReplacesReview";
import { Part3MoldThreeParts01SectionTitleCard } from "./Part3MoldThreeParts01SectionTitleCard";
import { Part3MoldThreeParts02MoldCrossSection } from "./Part3MoldThreeParts02MoldCrossSection";
import { Part3MoldThreeParts10ThreeComponentsTable } from "./Part3MoldThreeParts10ThreeComponentsTable";
import { Part4PrecisionTradeoff01SectionTitleCard } from "./Part4PrecisionTradeoff01SectionTitleCard";
import { Part4PrecisionTradeoff02PrinterVsMoldSplit } from "./Part4PrecisionTradeoff02PrinterVsMoldSplit";
import { Part4PrecisionTradeoff03PrecisionTradeoffCurve } from "./Part4PrecisionTradeoff03PrecisionTradeoffCurve";
import { Part4PrecisionTradeoff07EmbeddedCodeDocument } from "./Part4PrecisionTradeoff07EmbeddedCodeDocument";
import { Part4PrecisionTradeoff08PromptCodeSpectrum } from "./Part4PrecisionTradeoff08PromptCodeSpectrum";
import { Part5CompoundReturns01SectionTitleCard } from "./Part5CompoundReturns01SectionTitleCard";
import { Part5CompoundReturns02MaintenancePieChart } from "./Part5CompoundReturns02MaintenancePieChart";
import { Part5CompoundReturns03CompoundDebtCurve } from "./Part5CompoundReturns03CompoundDebtCurve";
import { Part5CompoundReturns04DivergingCostCurves } from "./Part5CompoundReturns04DivergingCostCurves";
import { Part5CompoundReturns05InvestmentComparisonTable } from "./Part5CompoundReturns05InvestmentComparisonTable";
import { Part5CompoundReturns07EconomicsCrossingCallback } from "./Part5CompoundReturns07EconomicsCrossingCallback";
import { Part5CompoundReturns08ContrarianQuoteCard } from "./Part5CompoundReturns08ContrarianQuoteCard";
import { WhereToStart01SectionTitleCard } from "./WhereToStart01SectionTitleCard";
import { WhereToStart02LegacyCodebaseReveal } from "./WhereToStart02LegacyCodebaseReveal";
import { WhereToStart04SourceOfTruthShift } from "./WhereToStart04SourceOfTruthShift";
import { WhereToStart07NoBigBangCallout } from "./WhereToStart07NoBigBangCallout";
import { Closing03CodeRegenerateWorkflow } from "./Closing03CodeRegenerateWorkflow";
import { Closing04PddTriangle } from "./Closing04PddTriangle";
import { Closing05DissolveRegenerateLoop } from "./Closing05DissolveRegenerateLoop";
import { Closing07TheBeat } from "./Closing07TheBeat";
import { Closing09FinalTitleCard } from "./Closing09FinalTitleCard";

const PREVIEW_VISUAL_MEDIA: Record<string, Record<string, string>> = {
  "cold_open:01_split_screen_hook": { leftSrc: "veo/developer_ai_edit.mp4", defaultSrc: "veo/developer_ai_edit.mp4", rightSrc: "veo/grandmother_darning.mp4", backgroundSrc: "veo/developer_ai_edit.mp4", outputSrc: "veo/developer_ai_edit.mp4", baseSrc: "veo/developer_ai_edit.mp4", revealSrc: "veo/grandmother_darning.mp4" },
};

const PREVIEW_VISUAL_CONTRACTS: Record<string, Record<string, unknown> | null> = {
  "cold_open:01_split_screen_hook": {"specBaseName": "01_split_screen_hook", "dataPoints": {"type": "split_screen", "layout": "vertical_split", "splitPosition": 960, "leftPanel": {"content": "veo_clip_then_zoom_out", "clipId": "developer_ai_edit", "zoomOutReveals": "massive_codebase_with_patches", "thematicRole": "modern_developer_patching"}, "rightPanel": {"content": "veo_clip_then_zoom_out", "clipId": "grandmother_darning", "zoomOutReveals": "drawer_of_mended_garments", "thematicRole": "grandmother_darning_socks"}, "backgroundColor": "#000000", "narrationSegments": ["cold_open_001", "cold_open_002", "cold_open_003"]}, "overlayConfig": null, "renderMode": "component"},
  "cold_open:05_code_blink_patched": {"specBaseName": "05_code_blink_patched", "dataPoints": {"type": "code_display", "language": "python", "filename": "auth_handler.py", "lineCount": 24, "patchComments": [{"line": 3, "text": "# patched 2024-01 — handle None case"}, {"line": 8, "text": "# workaround: upstream API sometimes returns 403"}, {"line": 14, "text": "# TODO: clean this up after migration"}, {"line": 19, "text": "# edge case fix (see ticket #4721)"}], "cursorPosition": {"line": 14, "column": 48}, "theme": "dark_ide", "backgroundColor": "#0D1117", "narrationSegments": ["cold_open_005"]}, "overlayConfig": null, "renderMode": "component"},
  "cold_open:06_code_regeneration": {"specBaseName": "06_code_regeneration", "dataPoints": {"type": "code_regeneration", "filename": "auth_handler.py", "deletedLines": 24, "generatedLines": 16, "deletionDurationFrames": 36, "generationDurationFrames": 16, "terminal": {"command": "pdd generate auth_handler", "result": "Generated in 0.8s", "position": "bottom_right"}, "theme": "dark_ide", "backgroundColor": "#0D1117", "narrationSegments": ["cold_open_005"]}, "overlayConfig": null, "renderMode": "component"},
  "cold_open:07_pdd_title_card": {"specBaseName": "07_pdd_title_card", "dataPoints": {"type": "title_card", "sectionNumber": 0, "sectionLabel": "Cold Open", "title": "Prompt-Driven Development", "titleColor": "#4A90D9", "subtitle": "So why are we still patching?", "subtitleColor": "#94A3B8", "backgroundColor": "#0D1117", "codeUnderlay": true, "underlayOpacity": 0.15, "narrationSegments": ["cold_open_006"]}, "overlayConfig": null, "renderMode": "component"},
  "part1_economics:01_section_title_card": {"specBaseName": "01_section_title_card", "dataPoints": {"type": "title_card", "sectionNumber": 1, "sectionLabel": "PART 1", "titleLine1": "THE ECONOMICS", "titleLine2": "OF DARNING", "backgroundColor": "#0A0F1A", "ghostElements": [{"shape": "quadratic_curve", "color": "#D9944A", "component": "descending_cost"}, {"shape": "quadratic_curve", "color": "#4A90D9", "component": "ascending_cost"}, {"shape": "crossing_point", "color": "#E2E8F0", "component": "threshold"}], "narrationSegments": ["part1_economics_001", "part1_economics_002"]}, "overlayConfig": null, "renderMode": "component"},
  "part1_economics:02_sock_price_chart": {"specBaseName": "02_sock_price_chart", "dataPoints": {"type": "animated_chart", "chartId": "sock_economics", "chartType": "dual_line", "xAxis": {"label": "Year", "range": [1950, 2020], "majorTick": 10}, "yAxis": {"label": "Cost (Relative to Hourly Wage)", "range": [0, 100]}, "series": [{"id": "labor_cost", "label": "Labor cost (darning)", "color": "#D9944A", "dataPoints": [{"x": 1950, "y": 45}, {"x": 1960, "y": 47}, {"x": 1970, "y": 48}, {"x": 1980, "y": 48}, {"x": 1990, "y": 49}, {"x": 2000, "y": 49}, {"x": 2010, "y": 50}, {"x": 2020, "y": 50}]}, {"id": "sock_cost", "label": "Cost of new socks", "color": "#4A90D9", "dataPoints": [{"x": 1950, "y": 80}, {"x": 1955, "y": 65}, {"x": 1960, "y": 52}, {"x": 1965, "y": 40}, {"x": 1970, "y": 28}, {"x": 1980, "y": 15}, {"x": 1990, "y": 8}, {"x": 2000, "y": 4}, {"x": 2010, "y": 2}, {"x": 2020, "y": 1}]}], "threshold": {"x": 1962, "y": 47, "label": "The Threshold"}, "backgroundColor": "#0A0F1A", "narrationSegments": ["part1_economics_005", "part1_economics_006", "part1_economics_007"]}, "overlayConfig": null, "renderMode": "component"},
  "part1_economics:03_code_cost_chart": {"specBaseName": "03_code_cost_chart", "dataPoints": {"type": "animated_chart", "chartId": "code_cost_triple_line", "chartType": "triple_line", "xAxis": {"label": "Year", "range": [2000, 2025], "majorTick": 5}, "yAxis": {"label": "Cost (Developer Hours)", "range": [0, 100]}, "series": [{"id": "generate_cost", "label": "Cost to generate", "color": "#4A90D9", "style": "solid", "dataPoints": [{"x": 2000, "y": 85}, {"x": 2005, "y": 85}, {"x": 2010, "y": 84}, {"x": 2015, "y": 83}, {"x": 2020, "y": 82}, {"x": 2021, "y": 78}, {"x": 2022, "y": 75}, {"x": 2023, "y": 50}, {"x": 2024, "y": 25}, {"x": 2025, "y": 15}]}, {"id": "immediate_patch", "label": "Immediate patch cost", "color": "#D9944A", "style": "solid", "dataPoints": [{"x": 2000, "y": 40}, {"x": 2005, "y": 39}, {"x": 2010, "y": 38}, {"x": 2015, "y": 37}, {"x": 2020, "y": 35}, {"x": 2021, "y": 32}, {"x": 2022, "y": 28}, {"x": 2023, "y": 24}, {"x": 2024, "y": 22}, {"x": 2025, "y": 20}]}, {"id": "total_cost_debt", "label": "Total cost (with debt)", "color": "#D9944A", "style": "dashed", "dataPoints": [{"x": 2000, "y": 55}, {"x": 2005, "y": 55}, {"x": 2010, "y": 56}, {"x": 2015, "y": 56}, {"x": 2020, "y": 57}, {"x": 2021, "y": 57}, {"x": 2022, "y": 58}, {"x": 2023, "y": 59}, {"x": 2024, "y": 60}, {"x": 2025, "y": 60}]}], "keyDates": [{"year": 2021, "label": "Codex"}, {"year": 2023, "label": "GPT-4"}, {"year": 2023.5, "label": "Claude"}, {"year": 2024, "label": "Gemini"}], "debtShading": {"between": ["total_cost_debt", "immediate_patch"], "color": "#D9944A"}, "backgroundColor": "#0A0F1A", "narrationSegments": ["part1_economics_008", "part1_economics_009", "part1_economics_010", "part1_economics_011", "part1_economics_012", "part1_economics_013"]}, "overlayConfig": null, "renderMode": "component"},
  "part1_economics:04_research_annotations": {"specBaseName": "04_research_annotations", "dataPoints": {"type": "annotation_overlay", "chartId": "code_cost_triple_line", "annotations": [{"id": "github_individual", "header": "Individual task: −55%", "source": "GitHub, 2022", "finePrint": "95 developers, one greenfield task", "color": "#4ADE80", "target": "immediate_patch_line", "wave": 1}, {"id": "uplevel_overall", "header": "Overall throughput: ~0%", "source": "Uplevel, 2024", "finePrint": "785 developers, one year", "color": "#EF4444", "target": "total_cost_line", "wave": 1}, {"id": "gitclear_churn", "header": "Code churn: +44%", "source": "GitClear, 2025", "finePrint": "211M lines analyzed", "color": "#EF4444", "target": "debt_shading", "wave": 2}, {"id": "gitclear_refactoring", "header": "Refactoring: −60%", "source": "GitClear, 2025", "finePrint": "Developers aren't cleaning up. They're piling on.", "color": "#EF4444", "target": "debt_gap", "wave": 2}], "backgroundColor": "#0A0F1A", "narrationSegments": ["part1_economics_014", "part1_economics_015", "part1_economics_016"]}, "overlayConfig": null, "renderMode": "component"},
  "part1_economics:05_context_window_shrink": {"specBaseName": "05_context_window_shrink", "dataPoints": {"type": "animated_diagram", "diagramId": "context_window_shrink", "stages": [{"gridSize": 4, "blockPx": 60, "coveragePercent": 80, "color": "#4ADE80"}, {"gridSize": 8, "blockPx": 30, "coveragePercent": 40, "color": "#FBBF24"}, {"gridSize": 16, "blockPx": 15, "coveragePercent": 10, "color": "#EF4444"}, {"gridSize": 32, "blockPx": 7.5, "coveragePercent": 2, "color": "#DC2626"}], "contextWindow": {"width": 260, "height": 260, "color": "#4A90D9"}, "retrievalErrors": {"irrelevantInside": 3, "neededOutside": 5, "irrelevantColor": "#EF4444", "neededColor": "#4ADE80"}, "backgroundColor": "#0A0F1A", "narrationSegments": ["part1_economics_017", "part1_economics_018", "part1_economics_019", "part1_economics_020"]}, "overlayConfig": null, "renderMode": "component"},
  "part1_economics:06_performance_vs_context": {"specBaseName": "06_performance_vs_context", "dataPoints": {"type": "inset_chart", "chartId": "performance_vs_context", "chartType": "single_line_degradation", "xAxis": {"label": "Context Length"}, "yAxis": {"label": "Model Performance"}, "series": [{"id": "performance_degradation", "color": "#EF4444", "degradationRange": {"min": 14, "max": 85}, "source": "EMNLP, 2025"}], "causalChain": ["Faster patching", "faster growth", "faster rot"], "backgroundColor": "#0A0F1A", "narrationSegments": ["part1_economics_021", "part1_economics_022"]}, "overlayConfig": null, "renderMode": "component"},
  "part1_economics:07_two_by_two_grid": {"specBaseName": "07_two_by_two_grid", "dataPoints": {"type": "two_by_two_grid", "diagramId": "productivity_quadrant", "axes": {"x": {"start": "Greenfield", "end": "Brownfield"}, "y": {"start": "In-Distribution", "end": "Out-of-Distribution"}}, "quadrants": [{"position": "top-left", "label": "GitHub study", "value": "+55%", "color": "#4ADE80", "source": "GitHub, 2022"}, {"position": "bottom-right", "label": "METR study", "value": "−19%", "color": "#EF4444", "source": "METR, 2025"}, {"position": "top-right", "label": "Mixed", "color": "#64748B"}, {"position": "bottom-left", "label": "Mixed", "color": "#64748B"}], "summary": "Every study is correct. They just measured different quadrants.", "backgroundColor": "#0A0F1A", "narrationSegments": ["part1_economics_023"]}, "overlayConfig": null, "renderMode": "component"},
  "part1_economics:08_fork_codebase_size": {"specBaseName": "08_fork_codebase_size", "dataPoints": {"type": "forking_chart", "chartId": "codebase_size_fork", "forkYear": 2020, "forks": [{"id": "small_codebase", "label": "Small codebase", "color": "#4ADE80", "dataPoints": [{"x": 2020, "y": 35}, {"x": 2021, "y": 28}, {"x": 2022, "y": 22}, {"x": 2023, "y": 15}, {"x": 2024, "y": 12}, {"x": 2025, "y": 10}]}, {"id": "large_codebase", "label": "Large codebase", "color": "#EF4444", "dataPoints": [{"x": 2020, "y": 35}, {"x": 2021, "y": 35}, {"x": 2022, "y": 34}, {"x": 2023, "y": 34}, {"x": 2024, "y": 33}, {"x": 2025, "y": 32}]}], "annotations": [{"text": "METR, 2025: experienced devs 19% slower on mature repos", "color": "#EF4444"}, {"text": "Developers believed AI saved 20%. It cost 19%.", "color": "#EF4444", "emphasis": true}], "trapArrow": {"label": "Every patch adds code.", "color": "#D9944A"}, "backgroundColor": "#0A0F1A", "narrationSegments": ["part1_economics_024", "part1_economics_025", "part1_economics_026"]}, "overlayConfig": null, "renderMode": "component"},
  "part1_economics:09_patching_vs_regeneration_split": {"specBaseName": "09_patching_vs_regeneration_split", "dataPoints": {"type": "split_screen", "layout": "vertical_split", "splitPosition": 960, "leftPanel": {"label": "AGENTIC PATCHING", "content": "context_window_cluttered", "tokenCount": 15000, "relevantPercent": 5, "color": "#EF4444", "background": "#0A0F1A"}, "rightPanel": {"label": "PDD REGENERATION", "content": "context_window_clean", "tokenCount": 2500, "relevantPercent": 95, "sections": [{"label": "Prompt", "tokens": 300, "color": "#4A90D9"}, {"label": "Tests", "tokens": 2000, "color": "#D9944A"}, {"label": "Grounding", "tokens": 200, "color": "#5AAA6E"}], "color": "#4ADE80", "background": "#0A0F1A"}, "backgroundColor": "#000000", "narrationSegments": ["part1_economics_027", "part1_economics_028"]}, "overlayConfig": null, "renderMode": "component"},
  "part1_economics:10_context_compression": {"specBaseName": "10_context_compression", "dataPoints": {"type": "animated_diagram", "diagramId": "context_compression", "moduleCount": 20, "codeBlockSize": {"width": 120, "height": 80}, "promptBlockSize": {"width": 50, "height": 30}, "compressionRatio": "5-10×", "contextWindow": {"width": 600, "height": 500}, "overflowCount": 12, "resultLabel": "Same system. 5-10× more fits.", "backgroundColor": "#0A0F1A", "narrationSegments": ["part1_economics_029", "part1_economics_030"]}, "overlayConfig": null, "renderMode": "component"},
  "part1_economics:11_crossing_lines_moment": {"specBaseName": "11_crossing_lines_moment", "dataPoints": {"type": "chart_event", "chartId": "code_cost_triple_line", "event": "crossing_moment", "crossings": [{"id": "generate_crosses_total", "year": 2024, "y": 35, "radius": 8}, {"id": "generate_crosses_immediate", "year": 2025, "y": 20, "radius": 10}], "label": "We are here.", "debtResetNote": "Debt resets with each generation.", "backgroundColor": "#0A0F1A", "narrationSegments": ["part1_economics_031"]}, "overlayConfig": null, "renderMode": "component"},
  "part1_economics:12_developer_darning_split": {"specBaseName": "12_developer_darning_split", "dataPoints": {"type": "split_screen", "layout": "vertical_split", "splitPosition": 960, "leftPanel": {"label": "CURSOR", "content": "developer_cursor_coding", "colorGrade": {"color": "#4A90D9", "opacity": 0.03}, "codeComments": ["// don't touch this", "// legacy", "// temporary fix (2019)"], "background": "#000000"}, "rightPanel": {"label": "DARNING NEEDLE", "content": "grandmother_darning_expert", "colorGrade": {"color": "#D4A043", "opacity": 0.04}, "background": "#000000"}, "embeddedVeoClips": ["developer_cursor_coding", "grandmother_darning_expert"], "backgroundColor": "#000000", "narrationSegments": ["part1_economics_032", "part1_economics_033"]}, "overlayConfig": null, "renderMode": "component"},
  "part1_economics:15_key_insight_stillness": {"specBaseName": "15_key_insight_stillness", "dataPoints": {"type": "title_card", "sectionNumber": "1.key", "sectionLabel": "THE KEY INSIGHT", "style": "stillness_beat", "backgroundColor": "#0A0F1A", "breathing": true, "narrationSegments": []}, "overlayConfig": null, "renderMode": "component"},
  "part1_economics:16_double_meter_insight": {"specBaseName": "16_double_meter_insight", "dataPoints": {"type": "dual_meter", "diagramId": "double_meter_insight", "meters": [{"id": "context_window", "label": "Effective Context Window", "color": "#4A90D9", "scale": ["1×", "5×", "10×"], "fillFrom": 0.2, "fillTo": 1.0}, {"id": "model_performance", "label": "Model Performance", "color": "#4ADE80", "scale": ["Baseline", "Optimal"], "fillFrom": 0.2, "fillTo": 1.0}], "peakText": "Bigger window AND smarter model.", "subtext": "Not one or the other. Both. That's a category shift.", "backgroundColor": "#0A0F1A", "narrationSegments": []}, "overlayConfig": null, "renderMode": "component"},
  "part1_economics:17_try_it_yourself": {"specBaseName": "17_try_it_yourself", "dataPoints": {"type": "title_card", "sectionNumber": "1.end", "style": "handwritten_challenge", "challenge": "Try it yourself.", "supportingText": ["Take your favorite LLM.", "Give it a hard coding problem as code,", "then as natural language.", "The natural language version will win."], "font": "Caveat", "backgroundColor": "#0A0F1A", "narrationSegments": []}, "overlayConfig": null, "renderMode": "component"},
  "part2_paradigm_shift:01_section_title_card": {"specBaseName": "01_section_title_card", "dataPoints": {"type": "title_card", "sectionNumber": 2, "sectionLabel": "PART 2", "titleLine1": "THE PARADIGM", "titleLine2": "SHIFT", "backgroundColor": "#0A0F1A", "ghostElements": [{"shape": "mold_nozzle", "color": "#4A90D9", "component": "injection_nozzle"}, {"shape": "mold_cavity", "color": "#4A90D9", "component": "rectangular_cavity"}, {"shape": "mold_walls", "color": "#D9944A", "component": "constraint_walls"}], "narrationSegments": ["part2_paradigm_shift_001"]}, "overlayConfig": null, "renderMode": "component"},
  "part2_paradigm_shift:02_double_meter_insight": {"specBaseName": "02_double_meter_insight", "dataPoints": {"type": "dual_meter_animation", "diagramId": "double_meter_insight", "meters": [{"id": "context_window", "label": "Effective Context Window", "position": "left", "scaleMin": "1×", "scaleMax": "10×", "fillGradient": ["#4A90D9", "#38BDF8"]}, {"id": "model_performance", "label": "Model Performance", "position": "right", "scaleMin": "Base", "scaleMax": "+89%", "fillGradient": ["#4ADE80", "#22D3EE"]}], "insightText": "Bigger window AND smarter model.", "challengeText": "Try it yourself.", "backgroundColor": "#0A0F1A", "narrationSegments": ["part2_paradigm_shift_002", "part2_paradigm_shift_003", "part2_paradigm_shift_004"]}, "overlayConfig": null, "renderMode": "component"},
  "part2_paradigm_shift:05_mold_defect_fix": {"specBaseName": "05_mold_defect_fix", "dataPoints": {"type": "animated_diagram", "diagramId": "mold_defect_fix", "elements": {"mold": {"type": "cross_section", "wallColor": "#D9944A"}, "conveyor": {"type": "belt", "direction": "left_to_right"}, "parts": {"normalColor": "#4A90D9", "defectColor": "#EF4444"}, "engineer": {"color": "#E2E8F0", "toolColor": "#FBBF24"}, "counter": {"maxValue": "10000+", "color": "#4ADE80"}}, "narrativeArc": "defect_found → fix_mold → all_future_parts_perfect", "backgroundColor": "#0A0F1A", "narrationSegments": ["part2_paradigm_shift_008", "part2_paradigm_shift_009", "part2_paradigm_shift_010"]}, "overlayConfig": null, "renderMode": "component"},
  "part2_paradigm_shift:06_craftsman_vs_mold": {"specBaseName": "06_craftsman_vs_mold", "dataPoints": {"type": "split_screen", "layout": "vertical_split", "splitPosition": 960, "leftPanel": {"content": "veo_clip_with_aura", "clipId": "craftsman_carving", "aura": {"color": "#FFB347", "target": "wooden_chair"}, "label": "Value lives in the object", "thematicRole": "crafting_value_in_object"}, "rightPanel": {"content": "veo_clip_with_aura", "clipId": "mold_producing_parts", "aura": {"color": "#4A90D9", "target": "injection_mold"}, "label": "Value lives in the specification", "partDissolves": true, "thematicRole": "molding_value_in_spec"}, "backgroundColor": "#000000", "narrationSegments": ["part2_paradigm_shift_010", "part2_paradigm_shift_011", "part2_paradigm_shift_012"]}, "overlayConfig": null, "renderMode": "component"},
  "part2_paradigm_shift:10_verilog_synthesis_triple": {"specBaseName": "10_verilog_synthesis_triple", "dataPoints": {"type": "animated_diagram", "diagramId": "verilog_synthesis_triple", "phases": [{"id": "single_synthesis", "elements": ["verilog_code", "synthesis_icon", "gate_netlist"]}, {"id": "triple_synthesis", "elements": ["three_code_blocks", "three_netlists", "three_checkmarks"]}], "netlists": [{"id": "run_1", "layout": "diamond", "color": "#4ADE80"}, {"id": "run_2", "layout": "grid", "color": "#38BDF8"}, {"id": "run_3", "layout": "tree", "color": "#FBBF24"}], "equivalenceLabel": "Functionally equivalent", "equivalenceColor": "#4ADE80", "backgroundColor": "#0A0F1A", "narrationSegments": ["part2_paradigm_shift_015", "part2_paradigm_shift_016"]}, "overlayConfig": null, "renderMode": "component"},
  "part2_paradigm_shift:11_synopsys_pdd_equivalence": {"specBaseName": "11_synopsys_pdd_equivalence", "dataPoints": {"type": "text_overlay_with_morph", "diagramId": "synopsys_pdd_equivalence", "comparisons": [{"domain": "Synopsys", "domainColor": "#4A90D9", "input": "specification", "output": "verified hardware"}, {"domain": "PDD", "domainColor": "#4ADE80", "input": "prompt", "output": "verified software"}], "morphPairs": [{"from": "verilog_code", "to": "prompt_document"}, {"from": "synopsys_checkmark", "to": "test_suite"}, {"from": "gate_netlist", "to": "software_code"}], "sharedLabel": "Same architecture", "backgroundColor": "#0A0F1A", "narrationSegments": ["part2_paradigm_shift_017"]}, "overlayConfig": null, "renderMode": "component"},
  "part2_paradigm_shift:12_abstraction_staircase": {"specBaseName": "12_abstraction_staircase", "dataPoints": {"type": "animated_diagram", "diagramId": "abstraction_staircase", "steps": [{"id": "transistors", "label": "Transistors", "decade": "1970s", "color": "#D9944A"}, {"id": "schematics", "label": "Schematics", "decade": "1980s", "color": "#F59E0B"}, {"id": "rtl_verilog", "label": "RTL / Verilog", "decade": "1990s", "color": "#4A90D9"}, {"id": "behavioral_hls", "label": "Behavioral / HLS", "decade": "2010s", "color": "#2DD4BF"}, {"id": "natural_language", "label": "Natural language → Code", "decade": "2020s", "color": "#4ADE80", "pulsing": true}], "transitionLabel": "Couldn't scale", "transitionColor": "#EF4444", "chipLayout": {"label": "Billions of gates", "gateCount": "billions"}, "backgroundColor": "#0A0F1A", "narrationSegments": ["part2_paradigm_shift_018", "part2_paradigm_shift_019"]}, "overlayConfig": null, "renderMode": "component"},
  "part2_paradigm_shift:13_prompt_replaces_review": {"specBaseName": "13_prompt_replaces_review", "dataPoints": {"type": "animated_diagram", "diagramId": "prompt_replaces_review", "phases": [{"id": "spec_and_tests", "elements": ["prompt_document", "test_suite", "review_label"]}, {"id": "mold_metaphor", "elements": ["prompt_source", "code_stream", "test_walls"]}], "promptDocument": {"label": "PROMPT", "glowColor": "#4ADE80", "lineCount": 8}, "testSuite": {"label": "TESTS", "testCount": 6, "checkColor": "#4ADE80"}, "reviewLabel": "Review the spec. Verify the output.", "moldAnimation": {"codeColor": "#94A3B8", "wallColor": "#D9944A"}, "backgroundColor": "#0A0F1A", "narrationSegments": ["part2_paradigm_shift_019"]}, "overlayConfig": null, "renderMode": "component"},
  "part3_mold_three_parts:01_section_title_card": {"specBaseName": "01_section_title_card", "dataPoints": {"type": "title_card", "sectionNumber": 3, "sectionLabel": "PART 3", "titleLine1": "THE MOLD HAS", "titleLine2": "THREE PARTS", "backgroundColor": "#0A0F1A", "ghostElements": [{"shape": "mold_shell", "color": "#4A90D9", "component": "outer_shell"}, {"shape": "mold_walls", "color": "#D9944A", "component": "test_walls"}, {"shape": "mold_nozzle", "color": "#2DD4BF", "component": "prompt_nozzle"}, {"shape": "mold_material", "color": "#A78BFA", "component": "grounding_material"}], "narrationSegments": ["part3_mold_three_parts_001", "part3_mold_three_parts_002", "part3_mold_three_parts_003"]}, "overlayConfig": null, "renderMode": "component"},
  "part3_mold_three_parts:02_mold_cross_section": {"specBaseName": "02_mold_cross_section", "dataPoints": {"type": "animated_diagram", "diagramId": "mold_cross_section", "regions": [{"id": "walls", "label": "Tests: The Walls", "color": "#D9944A", "role": "constraints"}, {"id": "nozzle", "label": "Prompt: The Specification", "color": "#2DD4BF", "role": "specification"}, {"id": "material", "label": "Grounding: The Material", "color": "#A78BFA", "role": "style"}], "backgroundColor": "#0A0F1A", "narrationSegments": ["part3_mold_three_parts_004", "part3_mold_three_parts_005", "part3_mold_three_parts_006"]}, "overlayConfig": null, "renderMode": "component"},
  "part3_mold_three_parts:03_test_walls_illuminate": {"specBaseName": "03_test_walls_illuminate", "dataPoints": {"type": "animated_diagram", "diagramId": "test_walls_illuminate", "walls": [{"id": "wall_null", "label": "null → None"}, {"id": "wall_empty", "label": "empty string → ''"}, {"id": "wall_unicode", "label": "handles unicode"}, {"id": "wall_latency", "label": "latency < 100ms"}, {"id": "wall_no_throw", "label": "no exceptions thrown"}, {"id": "wall_idempotent", "label": "idempotent"}], "wallColor": "#D9944A", "liquidGradient": ["#4A90D9", "#A78BFA"], "backgroundColor": "#0A0F1A", "narrationSegments": ["part3_mold_three_parts_007", "part3_mold_three_parts_008"]}, "overlayConfig": null, "renderMode": "component"},
  "part3_mold_three_parts:05_research_annotations": {"specBaseName": "05_research_annotations", "dataPoints": {"type": "annotation_overlay", "diagramId": "research_annotations", "annotations": [{"id": "coderabbit_stat", "type": "warning", "stat": "1.7×", "text": "AI code: 1.7× more issues", "source": "CodeRabbit, 2025", "detail": "75% more logic errors, 8× more perf problems", "color": "#EF4444"}, {"id": "dora_stat", "type": "positive", "text": "AI + strong tests = amplified delivery", "source": "DORA, 2025", "color": "#4ADE80"}], "backgroundColor": "#0A0F1A", "narrationSegments": ["part3_mold_three_parts_009", "part3_mold_three_parts_010"]}, "overlayConfig": null, "renderMode": "component"},
  "part3_mold_three_parts:06_bug_add_wall": {"specBaseName": "06_bug_add_wall", "dataPoints": {"type": "animated_diagram", "diagramId": "bug_add_wall", "phases": [{"id": "bug_found", "action": "highlight_bug_line", "color": "#EF4444"}, {"id": "add_wall", "action": "materialize_wall", "label": "handles_null_userid", "color": "#D9944A"}, {"id": "regenerate", "action": "dissolve_and_regenerate_code"}, {"id": "permanent", "action": "wall_glows_permanently"}], "terminalCommands": ["pdd bug user_parser", "pdd fix user_parser"], "backgroundColor": "#0A0F1A", "narrationSegments": ["part3_mold_three_parts_011", "part3_mold_three_parts_012", "part3_mold_three_parts_013"]}, "overlayConfig": null, "renderMode": "component"},
  "part3_mold_three_parts:07_ratchet_timelapse": {"specBaseName": "07_ratchet_timelapse", "dataPoints": {"type": "animated_diagram", "diagramId": "ratchet_timelapse", "wallTimeline": [{"frame": 0, "count": 4, "phase": "initial"}, {"frame": 90, "count": 7, "phase": "early_growth"}, {"frame": 180, "count": 12, "phase": "mid_growth"}, {"frame": 270, "count": 18, "phase": "acceleration"}, {"frame": 330, "count": 25, "phase": "mature"}], "wallColor": "#D9944A", "ratchetMetaphor": true, "backgroundColor": "#0A0F1A", "narrationSegments": ["part3_mold_three_parts_014", "part3_mold_three_parts_015"]}, "overlayConfig": null, "renderMode": "component"},
  "part3_mold_three_parts:08_traditional_vs_pdd_split": {"specBaseName": "08_traditional_vs_pdd_split", "dataPoints": {"type": "split_screen", "layout": "vertical_split", "splitPosition": 960, "leftPanel": {"header": "TRADITIONAL", "headerColor": "#EF4444", "steps": [{"text": "Bug found", "opacity": 0.8}, {"text": "→ Patch code", "opacity": 0.8}, {"text": "Similar bug elsewhere", "opacity": 0.7}, {"text": "→ Patch again", "opacity": 0.6}, {"text": "Different bug", "opacity": 0.5}, {"text": "→ Patch again...", "opacity": 0.4}, {"text": "...", "opacity": 0.2}], "thematicRole": "endless_cycle"}, "rightPanel": {"header": "PDD", "headerColor": "#4ADE80", "steps": [{"text": "Bug found"}, {"text": "→ Add test (pdd bug)"}, {"text": "→ Regenerate (pdd fix)"}, {"text": "Bug impossible forever", "icon": "lock", "glow": true}], "thematicRole": "permanent_fix"}, "backgroundColor": "#0A0F1A", "narrationSegments": ["part3_mold_three_parts_015", "part3_mold_three_parts_016"]}, "overlayConfig": null, "renderMode": "component"},
  "part3_mold_three_parts:09_bug_fork_diagram": {"specBaseName": "09_bug_fork_diagram", "dataPoints": {"type": "animated_diagram", "diagramId": "bug_fork", "root": {"label": "Bug found", "color": "#EF4444"}, "branches": [{"id": "code_bug", "label": "Code bug — add a wall", "color": "#D9944A", "action": "add_test", "file": "test_user_parser.py"}, {"id": "prompt_defect", "label": "Prompt defect — change the mold", "color": "#2DD4BF", "action": "fix_specification", "file": "user_parser.prompt"}], "convergence": {"label": "Regenerate", "color": "#4ADE80"}, "backgroundColor": "#0A0F1A", "narrationSegments": ["part3_mold_three_parts_016"]}, "overlayConfig": null, "renderMode": "component"},
  "part3_mold_three_parts:10_five_generations": {"specBaseName": "10_five_generations", "dataPoints": {"type": "animated_diagram", "diagramId": "five_generations", "panels": [{"id": "gen_1", "status": "fail", "color": "#EF4444", "statusDelay": 0}, {"id": "gen_2", "status": "warn", "color": "#F59E0B", "statusDelay": 60}, {"id": "gen_3", "status": "fail", "color": "#EF4444", "statusDelay": 0}, {"id": "gen_4", "status": "warn", "color": "#F59E0B", "statusDelay": 60}, {"id": "gen_5", "status": "pass", "color": "#4ADE80", "statusDelay": 120}], "label": "Generate five. Pick the one that passes all tests.", "backgroundColor": "#0A0F1A", "narrationSegments": ["part3_mold_three_parts_017"]}, "overlayConfig": null, "renderMode": "component"},
  "part3_mold_three_parts:11_z3_formal_proof": {"specBaseName": "11_z3_formal_proof", "dataPoints": {"type": "annotation_overlay", "diagramId": "z3_formal_proof", "comparison": {"left": {"label": "Synopsys Formality", "domain": "chip_verification", "color": "#4A90D9"}, "right": {"label": "PDD + Z3", "domain": "code_verification", "color": "#2DD4BF"}, "equivalence": {"symbol": "≡", "color": "#A78BFA"}}, "emphasisLine": "Not sampling. Mathematical proof.", "backgroundColor": "#0A0F1A", "narrationSegments": ["part3_mold_three_parts_018"]}, "overlayConfig": null, "renderMode": "component"},
  "part3_mold_three_parts:12_module_level_aside": {"specBaseName": "12_module_level_aside", "dataPoints": {"type": "animated_diagram", "diagramId": "module_level_aside", "modules": [{"id": "auth", "label": "auth"}, {"id": "users", "label": "users"}, {"id": "payments", "label": "payments"}, {"id": "api", "label": "api"}, {"id": "parser", "label": "parser", "highlighted": true}, {"id": "events", "label": "events"}, {"id": "cache", "label": "cache"}, {"id": "queue", "label": "queue"}, {"id": "config", "label": "config"}], "limitations": ["race conditions", "cascading failures", "architectural mismatches"], "pddModule": "parser", "backgroundColor": "#0A0F1A", "narrationSegments": ["part3_mold_three_parts_019"]}, "overlayConfig": null, "renderMode": "component"},
  "part3_mold_three_parts:13_prompt_nozzle": {"specBaseName": "13_prompt_nozzle", "dataPoints": {"type": "animated_diagram", "diagramId": "prompt_nozzle", "nozzleLabels": ["intent", "requirements", "constraints"], "promptText": ["Parse user IDs from untrusted input.", "Return None on failure, never throw.", "Handle unicode."], "promptFile": "user_parser.prompt", "dualGeneration": true, "nozzleColor": "#2DD4BF", "backgroundColor": "#0A0F1A", "narrationSegments": ["part3_mold_three_parts_020", "part3_mold_three_parts_021", "part3_mold_three_parts_022"]}, "overlayConfig": null, "renderMode": "component"},
  "part3_mold_three_parts:14_prompt_ratio": {"specBaseName": "14_prompt_ratio", "dataPoints": {"type": "animated_diagram", "diagramId": "prompt_ratio", "promptSize": "~12 lines", "codeSize": "~200 lines", "ratio": "1:5 to 1:10", "analogy": {"prompt": "header file", "code": "OBJ file"}, "promptColor": "#2DD4BF", "backgroundColor": "#0A0F1A", "narrationSegments": ["part3_mold_three_parts_023"]}, "overlayConfig": null, "renderMode": "component"},
  "part3_mold_three_parts:15_context_window_comparison": {"specBaseName": "15_context_window_comparison", "dataPoints": {"type": "split_screen", "layout": "vertical_split", "splitPosition": 960, "leftPanel": {"header": "RAW CODE CONTEXT", "headerColor": "#94A3B8", "content": "dense_code", "tokenCount": 15000, "scope": "1 module's implementation", "thematicRole": "overwhelming_code"}, "rightPanel": {"header": "PROMPT CONTEXT", "headerColor": "#2DD4BF", "content": "prompt_blocks", "tokenCount": 15000, "scope": "10 modules' specifications", "thematicRole": "curated_prompts"}, "multiplier": "10×", "backgroundColor": "#0A0F1A", "narrationSegments": ["part3_mold_three_parts_024"]}, "overlayConfig": null, "renderMode": "component"},
  "part3_mold_three_parts:17_grounding_feedback_loop": {"specBaseName": "17_grounding_feedback_loop", "dataPoints": {"type": "animated_diagram", "diagramId": "grounding_feedback_loop", "phases": [{"id": "dual_grounding", "paths": [{"label": "OOP grounding", "style": "classes_with_methods", "color": "#4A90D9"}, {"label": "Functional grounding", "style": "pure_functions", "color": "#4ADE80"}]}, {"id": "feedback", "flow": "(prompt, code) → Grounding Database", "color": "#A78BFA"}, {"id": "pipeline", "stages": ["Prompt", "Grounding", "Mold", "Test Walls", "Code"]}], "backgroundColor": "#0A0F1A", "narrationSegments": ["part3_mold_three_parts_026", "part3_mold_three_parts_027", "part3_mold_three_parts_028"]}, "overlayConfig": null, "renderMode": "component"},
  "part3_mold_three_parts:18_three_components_table": {"specBaseName": "18_three_components_table", "dataPoints": {"type": "animated_diagram", "diagramId": "three_components_table", "table": {"columns": ["Component", "Encodes", "Owner"], "rows": [{"component": "Prompt", "encodes": "WHAT (intent)", "owner": "Developer", "color": "#2DD4BF"}, {"component": "Grounding", "encodes": "HOW (style)", "owner": "Automatic", "color": "#A78BFA"}, {"component": "Tests", "encodes": "CORRECTNESS", "owner": "Accumulated", "color": "#D9944A"}]}, "priorityRule": "When these conflict, tests win. Always.", "hierarchy": ["Tests", "Prompt", "Grounding"], "backgroundColor": "#0A0F1A", "narrationSegments": ["part3_mold_three_parts_029", "part3_mold_three_parts_030"]}, "overlayConfig": null, "renderMode": "component"},
  "part4_precision_tradeoff:01_section_title_card": {"specBaseName": "01_section_title_card", "dataPoints": {"type": "title_card", "sectionNumber": 4, "sectionLabel": "PART 4", "titleLine1": "THE PRECISION", "titleLine2": "TRADEOFF", "backgroundColor": "#0A0F1A", "ghostElements": [{"shape": "printer_nozzle", "color": "#60A5FA", "side": "left"}, {"shape": "coordinate_grid", "color": "#60A5FA", "side": "left"}, {"shape": "mold_outline", "color": "#D9944A", "side": "right"}, {"shape": "flow_curves", "color": "#A78BFA", "side": "right"}], "narrationSegments": ["part4_precision_tradeoff_001"]}, "overlayConfig": null, "renderMode": "component"},
  "part4_precision_tradeoff:02_printer_vs_mold_split": {"specBaseName": "02_printer_vs_mold_split", "dataPoints": {"type": "split_screen", "layout": "vertical_split", "splitPosition": 960, "leftPanel": {"header": "3D PRINTING", "headerColor": "#60A5FA", "elements": [{"type": "coordinate_grid", "spacing": 40, "color": "#60A5FA"}, {"type": "printer_nozzle", "layers": 3, "pointsPerLayer": 8}, {"type": "coordinate_labels", "font": "JetBrains Mono", "size": 8}], "caption": "Every point must be specified", "thematicRole": "explicit_precision"}, "rightPanel": {"header": "INJECTION MOLDING", "headerColor": "#D9944A", "elements": [{"type": "mold_walls", "strokeWidth": 4, "color": "#D9944A"}, {"type": "liquid_flow", "color": "#A78BFA"}, {"type": "wall_glow_on_impact", "glowColor": "#D9944A"}], "caption": "Walls do the precision work", "thematicRole": "emergent_precision"}, "backgroundColor": "#0A0F1A", "narrationSegments": ["part4_precision_tradeoff_002", "part4_precision_tradeoff_003"]}, "overlayConfig": null, "renderMode": "component"},
  "part4_precision_tradeoff:03_precision_tradeoff_curve": {"specBaseName": "03_precision_tradeoff_curve", "dataPoints": {"type": "animated_chart", "chartId": "precision_tradeoff_curve", "axes": {"x": {"label": "Number of Tests", "range": [0, 50], "ticks": ["0", "10", "20", "30", "40", "50+"]}, "y": {"label": "Required Prompt Precision", "range": ["Low", "High"], "ticks": ["Low", "Medium", "High"]}}, "curve": {"type": "inverse_hyperbolic", "color": "#2DD4BF", "strokeWidth": 3}, "annotations": {"left": {"label": "parser_v1.prompt — 50 lines", "description": "Dense prompt, few tests", "position": "high_precision"}, "right": {"label": "parser_v2.prompt — 10 lines", "description": "Minimal prompt, 47 tests", "testCount": 47, "position": "low_precision"}}, "introText": "This maps directly to PDD.", "backgroundColor": "#0A0F1A", "narrationSegments": ["part4_precision_tradeoff_004", "part4_precision_tradeoff_005", "part4_precision_tradeoff_006"]}, "overlayConfig": null, "renderMode": "component"},
  "part4_precision_tradeoff:04_code_generation_comparison": {"specBaseName": "04_code_generation_comparison", "dataPoints": {"type": "animated_diagram", "diagramId": "code_generation_comparison", "scenarios": [{"side": "left", "promptFile": "parser_v1.prompt", "promptLines": 50, "testCount": 5, "result": "correct", "emphasis": "prompt_heavy"}, {"side": "right", "promptFile": "parser_v2.prompt", "promptLines": 10, "testCount": 47, "result": "correct", "emphasis": "test_heavy", "preferred": true}], "takeaway": {"line1": "More tests, less prompt.", "line2": "The walls do the precision work."}, "backgroundColor": "#0A0F1A", "narrationSegments": ["part4_precision_tradeoff_007", "part4_precision_tradeoff_008"]}, "overlayConfig": null, "renderMode": "component"},
  "part4_precision_tradeoff:05_embedded_code_document": {"specBaseName": "05_embedded_code_document", "dataPoints": {"type": "animated_diagram", "diagramId": "embedded_code_document", "document": {"naturalLanguageBlocks": 5, "embeddedCodeBlocks": 1, "totalLines": 18, "codeLines": 4, "nlLines": 14}, "codeBlock": {"language": "python", "function": "hash_id", "purpose": "Performance-critical hashing implementation"}, "annotations": {"nlLabel": "Architecture, intent, constraints → natural language", "codeLabel": "Algorithm choice, performance-critical logic → code"}, "bottomLabel": "The boundary between prompt and code is fluid.", "colors": {"naturalLanguage": "#2DD4BF", "code": "#60A5FA", "background": "#0A0F1A"}, "narrationSegments": ["part4_precision_tradeoff_009"]}, "overlayConfig": null, "renderMode": "component"},
  "part4_precision_tradeoff:06_prompt_code_spectrum": {"specBaseName": "06_prompt_code_spectrum", "dataPoints": {"type": "animated_diagram", "diagramId": "prompt_code_spectrum", "spectrum": {"leftEnd": {"label": "Pure natural language", "color": "#2DD4BF"}, "rightEnd": {"label": "Pure code", "color": "#475569"}, "width": 1520}, "slider": {"position": 0.25, "label": "Most work lives here"}, "notches": [{"position": 0.6, "label": "Algorithm choice"}, {"position": 0.75, "label": "Bit-level ops"}, {"position": 0.9, "label": "Performance loops"}], "annotations": [{"position": 0.15, "label": "Architecture", "color": "#2DD4BF"}, {"position": 0.25, "label": "Intent", "color": "#2DD4BF"}, {"position": 0.35, "label": "Constraints / Edge cases", "color": "#2DD4BF"}, {"position": 0.65, "label": "Algorithm choice", "color": "#94A3B8"}, {"position": 0.85, "label": "Bit-level ops / Perf. loops", "color": "#64748B"}], "bottomLabel": {"line1": "Stay in prompt space as long as possible.", "line2": "Dip into code when you must."}, "backgroundColor": "#0A0F1A", "narrationSegments": ["part4_precision_tradeoff_010"]}, "overlayConfig": null, "renderMode": "component"},
  "part5_compound_returns:01_section_title_card": {"specBaseName": "01_section_title_card", "dataPoints": {"type": "title_card", "sectionId": "part5_compound_returns", "title": "COMPOUND RETURNS", "tagline": "Why the economics compound for you.", "backgroundColor": "#0A0F1A", "narrationSegments": ["part5_compound_returns_001"]}, "overlayConfig": null, "renderMode": "component"},
  "part5_compound_returns:02_maintenance_pie_chart": {"specBaseName": "02_maintenance_pie_chart", "dataPoints": {"type": "pie_chart", "chartId": "maintenance_cost_pie", "slices": [{"label": "Maintenance", "range": "80-90%", "color": "#F59E0B", "pullOut": 8}, {"label": "Initial Development", "range": "10-20%", "color": "#4ADE80"}], "callouts": [{"text": "40% more on maintenance", "source": "McKinsey", "color": "#F59E0B"}, {"text": "⅓ of dev time on debt", "source": "Stripe", "color": "#F59E0B"}], "backgroundColor": "#0A0F1A", "narrationSegments": ["part5_compound_returns_002"]}, "overlayConfig": null, "renderMode": "component"},
  "part5_compound_returns:03_compound_debt_curve": {"specBaseName": "03_compound_debt_curve", "dataPoints": {"type": "animated_chart", "chartId": "compound_debt_curve", "morphFrom": "maintenance_cost_pie", "curves": [{"id": "debt_exponential", "formula": "base * (1 + 0.25)^x", "color": "#F59E0B", "strokeWidth": 3, "label": "Debt × (1 + Rate)^Time", "fill": true}, {"id": "regeneration_flat", "formula": "constant", "color": "#4ADE80", "strokeWidth": 2.5, "dashed": true, "label": "Regeneration cost (debt resets each cycle)"}], "stats": [{"value": "$1.52T", "label": "annually", "source": "CISQ", "color": "#F59E0B"}], "backgroundColor": "#0A0F1A", "narrationSegments": ["part5_compound_returns_003"]}, "overlayConfig": {"gradientOverlay": "bottom"}, "renderMode": "component"},
  "part5_compound_returns:04_diverging_cost_curves": {"specBaseName": "04_diverging_cost_curves", "dataPoints": {"type": "animated_chart", "chartId": "diverging_cost_curves", "curves": [{"id": "patching_exponential", "label": "Patching", "color": "#F59E0B", "type": "exponential", "direction": "up", "annotations": ["+debt", "+debt", "+debt", "+debt", "+debt"]}, {"id": "pdd_flat", "label": "PDD", "color": "#4ADE80", "type": "flat", "annotations": ["+test", "+test", "+test", "+test", "+test", "+test", "+test", "+test"]}], "xAxis": ["Now", "6 months", "1 year", "2 years", "5 years"], "pivotLabel": "Tests accrue compound returns", "backgroundColor": "#0A0F1A", "narrationSegments": ["part5_compound_returns_004", "part5_compound_returns_005"]}, "overlayConfig": null, "renderMode": "component"},
  "part5_compound_returns:05_investment_comparison_table": {"specBaseName": "05_investment_comparison_table", "dataPoints": {"type": "comparison_table", "tableId": "investment_comparison", "columns": ["Investment", "Patching", "PDD"], "columnColors": ["#E2E8F0", "#F59E0B", "#4ADE80"], "rows": [{"investment": "Fix a bug", "patching": "One place, once", "pdd": "Impossible forever"}, {"investment": "Improve code", "patching": "One version", "pdd": "All future versions"}, {"investment": "Document intent", "patching": "One snapshot", "pdd": "Living specification"}], "backgroundColor": "#0A0F1A", "narrationSegments": ["part5_compound_returns_006"]}, "overlayConfig": null, "renderMode": "component"},
  "part5_compound_returns:08_economics_crossing_callback": {"specBaseName": "08_economics_crossing_callback", "dataPoints": {"type": "chart_callback", "chartId": "code_cost_triple_line", "callbackTo": "part1_economics/11_crossing_lines_moment", "event": "crossing_reprise", "crossingPoint": {"radius": 12, "glowRadius": 24, "pulseRange": [0.85, 1.15], "pulsePeriod": 45}, "newAnnotation": "When economics change, rational behavior changes.", "backgroundColor": "#0A0F1A", "narrationSegments": ["part5_compound_returns_009"]}, "overlayConfig": null, "renderMode": "component"},
  "part5_compound_returns:09_contrarian_quote_card": {"specBaseName": "09_contrarian_quote_card", "dataPoints": {"type": "quote_card", "cardId": "contrarian_quote", "quote": "This is either the way of the future or it's going to crash and burn spectacularly.", "attribution": "Research engineer, after seeing PDD for the first time", "accentColor": "#4A90D9", "backgroundColor": "#0A0F1A", "narrationSegments": ["part5_compound_returns_010"]}, "overlayConfig": null, "renderMode": "component"},
  "part5_compound_returns:10_transition_out": {"specBaseName": "10_transition_out", "dataPoints": {"type": "transition", "transitionId": "compound_returns_out", "echoes": [{"source": "diverging_cost_curves", "opacity": 0.08}], "backgroundColor": "#0A0F1A", "narrationSegments": ["part5_compound_returns_011"]}, "overlayConfig": null, "renderMode": "component"},
  "where_to_start:01_section_title_card": {"specBaseName": "01_section_title_card", "dataPoints": {"type": "title_card", "sectionId": "where_to_start", "sectionNumber": 6, "sectionLabel": "PART 6", "title": "WHERE TO START", "backgroundColor": "#0A0F1A", "ghostElements": [{"shape": "codebase_tree", "color": "#334155", "style": "file_tree"}], "narrationSegments": ["where_to_start_001"]}, "overlayConfig": null, "renderMode": "component"},
  "where_to_start:02_legacy_codebase_reveal": {"specBaseName": "02_legacy_codebase_reveal", "dataPoints": {"type": "code_visualization", "chartId": "legacy_codebase_reveal", "panels": 5, "fileNames": ["auth_handler.py", "payment_processor.py", "user_service.py", "legacy_router.py", "config.py"], "warningComments": ["// don't touch", "// here be dragons", "// TODO: fix this someday", "// nobody knows why this works"], "lineCount": "~47,000", "backgroundColor": "#0A0F1A", "narrationSegments": ["where_to_start_001"]}, "overlayConfig": null, "renderMode": "component"},
  "where_to_start:03_module_highlight_terminal": {"specBaseName": "03_module_highlight_terminal", "dataPoints": {"type": "code_transformation", "chartId": "module_highlight_terminal", "highlightedModule": "auth_handler.py", "terminalCommand": "pdd update auth_handler.py", "terminalOutput": "✓ Prompt generated: auth_handler.prompt.md", "promptFile": "auth_handler.prompt.md", "transformation": {"code": {"role": "artifact", "color": "#64748B", "opacity": 0.4}, "prompt": {"role": "source_of_truth", "color": "#60A5FA", "opacity": 1.0}}, "backgroundColor": "#0A0F1A", "narrationSegments": ["where_to_start_001"]}, "overlayConfig": null, "renderMode": "component"},
  "where_to_start:04_source_of_truth_shift": {"specBaseName": "04_source_of_truth_shift", "dataPoints": {"type": "code_transformation", "chartId": "source_of_truth_shift", "transformedModules": [{"name": "auth_handler.py", "state": "complete"}, {"name": "payment_processor.py", "state": "animating"}], "pendingModules": ["user_service.py", "legacy_router.py", "config.py", "db_connector.py", "email_sender.py", "cache_layer.py"], "workflow": ["module", "prompt", "tests", "regenerate", "compare"], "backgroundColor": "#0A0F1A", "narrationSegments": ["where_to_start_002"]}, "overlayConfig": null, "renderMode": "component"},
  "where_to_start:05_module_glow_spread": {"specBaseName": "05_module_glow_spread", "dataPoints": {"type": "network_graph", "chartId": "module_glow_spread", "totalModules": 14, "migrationSequence": [{"name": "auth_handler.py", "frame": 0, "position": [400, 350]}, {"name": "payment_processor.py", "frame": 0, "position": [600, 420]}, {"name": "user_service.py", "frame": 20, "position": [820, 310]}, {"name": "config.py", "frame": 45, "position": [350, 550]}, {"name": "db_connector.py", "frame": 65, "position": [650, 580]}, {"name": "email_sender.py", "frame": 85, "position": [1050, 400]}, {"name": "cache_layer.py", "frame": 105, "position": [900, 550]}], "unmigrated": ["legacy_router.py", "reporting.py", "webhook_handler.py", "session_manager.py", "rate_limiter.py", "notification_service.py", "data_exporter.py"], "counterSteps": [15, 22, 29, 36, 43, 50], "colors": {"migrated": "#60A5FA", "unmigrated": "#1E293B", "dependency_migrated": "#60A5FA", "dependency_unmigrated": "#334155"}, "backgroundColor": "#0A0F1A", "narrationSegments": ["where_to_start_002"]}, "overlayConfig": null, "renderMode": "component"},
  "where_to_start:06_no_big_bang_callout": {"specBaseName": "06_no_big_bang_callout", "dataPoints": {"type": "quote_card", "chartId": "no_big_bang_callout", "quoteLine1": "You don't patch socks", "quoteLine2": "because socks got cheap.", "quoteLine2Color": "#D9944A", "secondaryText": "The economics made patching irrational.", "callback": "sock_metaphor", "backgroundColor": "#0A0F1A", "narrationSegments": ["where_to_start_003"]}, "overlayConfig": null, "renderMode": "component"},
  "where_to_start:07_transition_to_closing": {"specBaseName": "07_transition_to_closing", "dataPoints": {"type": "transition", "transitionId": "where_to_start_to_closing", "echoes": [{"source": "no_big_bang_callout", "opacity": 0.06}, {"source": "sock_metaphor", "opacity": 0.05}], "backgroundColor": "#0A0F1A", "narrationSegments": ["where_to_start_003"]}, "overlayConfig": null, "renderMode": "component"},
  "closing:02_code_regenerate_workflow": {"specBaseName": "02_code_regenerate_workflow", "dataPoints": {"type": "code_animation", "chartId": "code_regenerate_workflow", "phases": [{"id": "bug_highlight", "frame": 0, "description": "Buggy code with red highlight on line 7"}, {"id": "test_add", "frame": 30, "description": "New test_edge_case fades in"}, {"id": "terminal_commands", "frame": 60, "description": "pdd bug → pdd fix sequence"}, {"id": "dissolve_regen", "frame": 90, "description": "Code dissolves, regenerates clean"}, {"id": "all_pass", "frame": 120, "description": "All tests passing checkmark"}], "terminalCommands": ["pdd bug user_parser", "pdd fix user_parser", "✓ All tests passing"], "backgroundColor": "#0A0F1A", "narrationSegments": ["closing_001", "closing_002"]}, "overlayConfig": null, "renderMode": "component"},
  "closing:04_pdd_triangle": {"specBaseName": "04_pdd_triangle", "dataPoints": {"type": "animated_diagram", "chartId": "pdd_triangle", "vertices": [{"id": "prompt", "label": "PROMPT", "position": [960, 200], "color": "#60A5FA", "descriptor": "encode intent"}, {"id": "tests", "label": "TESTS", "position": [480, 750], "color": "#4ADE80", "descriptor": "preserve behavior"}, {"id": "grounding", "label": "GROUNDING", "position": [1440, 750], "color": "#D9944A", "descriptor": "maintain style"}], "centerElement": {"type": "generated_code", "position": [960, 520], "font": "JetBrains Mono"}, "backgroundColor": "#0A0F1A", "narrationSegments": ["closing_002"]}, "overlayConfig": null, "renderMode": "component"},
  "closing:05_dissolve_regenerate_loop": {"specBaseName": "05_dissolve_regenerate_loop", "dataPoints": {"type": "animated_diagram", "chartId": "dissolve_regenerate_loop", "cycles": 3, "cycleTints": ["#60A5FA", "#4ADE80", "#D9944A"], "triangle": {"persistent": true, "source": "pdd_triangle"}, "terminal": {"command": "pdd generate", "successIndicator": "✓"}, "backgroundColor": "#0A0F1A", "narrationSegments": ["closing_003", "closing_004"]}, "overlayConfig": null, "renderMode": "component"},
  "closing:07_the_beat": {"specBaseName": "07_the_beat", "dataPoints": {"type": "beat", "chartId": "the_beat", "startAnchor": {"type": "segmentEnd", "segmentId": "closing_004"}, "endAnchor": {"type": "segmentStart", "segmentId": "closing_005"}, "ghostElements": [{"source": "pdd_triangle", "opacity": 0.02}], "backgroundColor": "#0A0F1A", "narrationSegments": []}, "overlayConfig": null, "renderMode": "component"},
  "closing:08_final_title_card": {"specBaseName": "08_final_title_card", "dataPoints": {"type": "title_card", "chartId": "final_title_card", "title": "Prompt-Driven Development", "titleFont": {"family": "Inter", "size": 52, "weight": 700, "color": "#E2E8F0"}, "titleGlow": {"color": "#D9944A", "opacity": 0.08, "blur": 60}, "url": "promptdrivendevelopment.com", "commands": ["uv tool install pdd-cli", "pdd update your_module.py"], "commandFont": {"family": "JetBrains Mono", "size": 16, "color": "#64748B"}, "ghostElements": [{"source": "pdd_triangle", "opacity": 0.03, "scale": 0.4}], "backgroundColor": "#0A0F1A", "narrationSegments": ["closing_005"]}, "overlayConfig": null, "renderMode": "component"},
};

const ColdOpen01SplitScreenHookPreview: React.FC = () => (
  <VisualContractProvider contract={PREVIEW_VISUAL_CONTRACTS["cold_open:01_split_screen_hook"] ?? null}>
    <VisualMediaProvider media={PREVIEW_VISUAL_MEDIA["cold_open:01_split_screen_hook"] ?? null}>
      <ColdOpen01SplitScreenHook />
    </VisualMediaProvider>
  </VisualContractProvider>
);
const ColdOpen06CodeBlinkPatchedPreview: React.FC = () => (
  <VisualContractProvider contract={PREVIEW_VISUAL_CONTRACTS["cold_open:05_code_blink_patched"] ?? null}>
    <VisualMediaProvider media={PREVIEW_VISUAL_MEDIA["cold_open:05_code_blink_patched"] ?? null}>
      <ColdOpen06CodeBlinkPatched />
    </VisualMediaProvider>
  </VisualContractProvider>
);
const ColdOpen07CodeRegenerationPreview: React.FC = () => (
  <VisualContractProvider contract={PREVIEW_VISUAL_CONTRACTS["cold_open:06_code_regeneration"] ?? null}>
    <VisualMediaProvider media={PREVIEW_VISUAL_MEDIA["cold_open:06_code_regeneration"] ?? null}>
      <ColdOpen07CodeRegeneration />
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
const Part1Economics02SockPriceChartPreview: React.FC = () => (
  <VisualContractProvider contract={PREVIEW_VISUAL_CONTRACTS["part1_economics:02_sock_price_chart"] ?? null}>
    <VisualMediaProvider media={PREVIEW_VISUAL_MEDIA["part1_economics:02_sock_price_chart"] ?? null}>
      <GeneratedContractVisual />
    </VisualMediaProvider>
  </VisualContractProvider>
);
const Part1Economics03CodeCostChartPreview: React.FC = () => (
  <VisualContractProvider contract={PREVIEW_VISUAL_CONTRACTS["part1_economics:03_code_cost_chart"] ?? null}>
    <VisualMediaProvider media={PREVIEW_VISUAL_MEDIA["part1_economics:03_code_cost_chart"] ?? null}>
      <GeneratedContractVisual />
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
const Part1Economics06PerformanceVsContextPreview: React.FC = () => (
  <VisualContractProvider contract={PREVIEW_VISUAL_CONTRACTS["part1_economics:06_performance_vs_context"] ?? null}>
    <VisualMediaProvider media={PREVIEW_VISUAL_MEDIA["part1_economics:06_performance_vs_context"] ?? null}>
      <GeneratedContractVisual />
    </VisualMediaProvider>
  </VisualContractProvider>
);
const Part1Economics06TwoByTwoGridPreview: React.FC = () => (
  <VisualContractProvider contract={PREVIEW_VISUAL_CONTRACTS["part1_economics:07_two_by_two_grid"] ?? null}>
    <VisualMediaProvider media={PREVIEW_VISUAL_MEDIA["part1_economics:07_two_by_two_grid"] ?? null}>
      <Part1Economics06TwoByTwoGrid />
    </VisualMediaProvider>
  </VisualContractProvider>
);
const Part1Economics08ForkCodebaseSizePreview: React.FC = () => (
  <VisualContractProvider contract={PREVIEW_VISUAL_CONTRACTS["part1_economics:08_fork_codebase_size"] ?? null}>
    <VisualMediaProvider media={PREVIEW_VISUAL_MEDIA["part1_economics:08_fork_codebase_size"] ?? null}>
      <GeneratedContractVisual />
    </VisualMediaProvider>
  </VisualContractProvider>
);
const Part1Economics09PatchingVsRegenerationSplitPreview: React.FC = () => (
  <VisualContractProvider contract={PREVIEW_VISUAL_CONTRACTS["part1_economics:09_patching_vs_regeneration_split"] ?? null}>
    <VisualMediaProvider media={PREVIEW_VISUAL_MEDIA["part1_economics:09_patching_vs_regeneration_split"] ?? null}>
      <GeneratedContractVisual />
    </VisualMediaProvider>
  </VisualContractProvider>
);
const Part1Economics10ContextCompressionPreview: React.FC = () => (
  <VisualContractProvider contract={PREVIEW_VISUAL_CONTRACTS["part1_economics:10_context_compression"] ?? null}>
    <VisualMediaProvider media={PREVIEW_VISUAL_MEDIA["part1_economics:10_context_compression"] ?? null}>
      <GeneratedContractVisual />
    </VisualMediaProvider>
  </VisualContractProvider>
);
const Part1Economics09CrossingLinesMomentPreview: React.FC = () => (
  <VisualContractProvider contract={PREVIEW_VISUAL_CONTRACTS["part1_economics:11_crossing_lines_moment"] ?? null}>
    <VisualMediaProvider media={PREVIEW_VISUAL_MEDIA["part1_economics:11_crossing_lines_moment"] ?? null}>
      <Part1Economics09CrossingLinesMoment />
    </VisualMediaProvider>
  </VisualContractProvider>
);
const Part1Economics12DeveloperDarningSplitPreview: React.FC = () => (
  <VisualContractProvider contract={PREVIEW_VISUAL_CONTRACTS["part1_economics:12_developer_darning_split"] ?? null}>
    <VisualMediaProvider media={PREVIEW_VISUAL_MEDIA["part1_economics:12_developer_darning_split"] ?? null}>
      <GeneratedContractVisual />
    </VisualMediaProvider>
  </VisualContractProvider>
);
const Part1Economics15KeyInsightStillnessPreview: React.FC = () => (
  <VisualContractProvider contract={PREVIEW_VISUAL_CONTRACTS["part1_economics:15_key_insight_stillness"] ?? null}>
    <VisualMediaProvider media={PREVIEW_VISUAL_MEDIA["part1_economics:15_key_insight_stillness"] ?? null}>
      <GeneratedContractVisual />
    </VisualMediaProvider>
  </VisualContractProvider>
);
const Part1Economics10DoubleMeterInsightPreview: React.FC = () => (
  <VisualContractProvider contract={PREVIEW_VISUAL_CONTRACTS["part1_economics:16_double_meter_insight"] ?? null}>
    <VisualMediaProvider media={PREVIEW_VISUAL_MEDIA["part1_economics:16_double_meter_insight"] ?? null}>
      <Part1Economics10DoubleMeterInsight />
    </VisualMediaProvider>
  </VisualContractProvider>
);
const Part1Economics17TryItYourselfPreview: React.FC = () => (
  <VisualContractProvider contract={PREVIEW_VISUAL_CONTRACTS["part1_economics:17_try_it_yourself"] ?? null}>
    <VisualMediaProvider media={PREVIEW_VISUAL_MEDIA["part1_economics:17_try_it_yourself"] ?? null}>
      <GeneratedContractVisual />
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
const Part2ParadigmShift02DoubleMeterInsightPreview: React.FC = () => (
  <VisualContractProvider contract={PREVIEW_VISUAL_CONTRACTS["part2_paradigm_shift:02_double_meter_insight"] ?? null}>
    <VisualMediaProvider media={PREVIEW_VISUAL_MEDIA["part2_paradigm_shift:02_double_meter_insight"] ?? null}>
      <GeneratedContractVisual />
    </VisualMediaProvider>
  </VisualContractProvider>
);
const Part2ParadigmShift05MoldDefectFixPreview: React.FC = () => (
  <VisualContractProvider contract={PREVIEW_VISUAL_CONTRACTS["part2_paradigm_shift:05_mold_defect_fix"] ?? null}>
    <VisualMediaProvider media={PREVIEW_VISUAL_MEDIA["part2_paradigm_shift:05_mold_defect_fix"] ?? null}>
      <GeneratedContractVisual />
    </VisualMediaProvider>
  </VisualContractProvider>
);
const Part2ParadigmShift06CraftsmanVsMoldPreview: React.FC = () => (
  <VisualContractProvider contract={PREVIEW_VISUAL_CONTRACTS["part2_paradigm_shift:06_craftsman_vs_mold"] ?? null}>
    <VisualMediaProvider media={PREVIEW_VISUAL_MEDIA["part2_paradigm_shift:06_craftsman_vs_mold"] ?? null}>
      <GeneratedContractVisual />
    </VisualMediaProvider>
  </VisualContractProvider>
);
const Part2ParadigmShift07VerilogSynthesisTriplePreview: React.FC = () => (
  <VisualContractProvider contract={PREVIEW_VISUAL_CONTRACTS["part2_paradigm_shift:10_verilog_synthesis_triple"] ?? null}>
    <VisualMediaProvider media={PREVIEW_VISUAL_MEDIA["part2_paradigm_shift:10_verilog_synthesis_triple"] ?? null}>
      <Part2ParadigmShift07VerilogSynthesisTriple />
    </VisualMediaProvider>
  </VisualContractProvider>
);
const Part2ParadigmShift08SynopsysPddEquivalencePreview: React.FC = () => (
  <VisualContractProvider contract={PREVIEW_VISUAL_CONTRACTS["part2_paradigm_shift:11_synopsys_pdd_equivalence"] ?? null}>
    <VisualMediaProvider media={PREVIEW_VISUAL_MEDIA["part2_paradigm_shift:11_synopsys_pdd_equivalence"] ?? null}>
      <Part2ParadigmShift08SynopsysPddEquivalence />
    </VisualMediaProvider>
  </VisualContractProvider>
);
const Part2ParadigmShift09AbstractionStaircasePreview: React.FC = () => (
  <VisualContractProvider contract={PREVIEW_VISUAL_CONTRACTS["part2_paradigm_shift:12_abstraction_staircase"] ?? null}>
    <VisualMediaProvider media={PREVIEW_VISUAL_MEDIA["part2_paradigm_shift:12_abstraction_staircase"] ?? null}>
      <Part2ParadigmShift09AbstractionStaircase />
    </VisualMediaProvider>
  </VisualContractProvider>
);
const Part2ParadigmShift11PromptReplacesReviewPreview: React.FC = () => (
  <VisualContractProvider contract={PREVIEW_VISUAL_CONTRACTS["part2_paradigm_shift:13_prompt_replaces_review"] ?? null}>
    <VisualMediaProvider media={PREVIEW_VISUAL_MEDIA["part2_paradigm_shift:13_prompt_replaces_review"] ?? null}>
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
const Part3MoldThreeParts03TestWallsIlluminatePreview: React.FC = () => (
  <VisualContractProvider contract={PREVIEW_VISUAL_CONTRACTS["part3_mold_three_parts:03_test_walls_illuminate"] ?? null}>
    <VisualMediaProvider media={PREVIEW_VISUAL_MEDIA["part3_mold_three_parts:03_test_walls_illuminate"] ?? null}>
      <GeneratedContractVisual />
    </VisualMediaProvider>
  </VisualContractProvider>
);
const Part3MoldThreeParts05ResearchAnnotationsPreview: React.FC = () => (
  <VisualContractProvider contract={PREVIEW_VISUAL_CONTRACTS["part3_mold_three_parts:05_research_annotations"] ?? null}>
    <VisualMediaProvider media={PREVIEW_VISUAL_MEDIA["part3_mold_three_parts:05_research_annotations"] ?? null}>
      <GeneratedContractVisual />
    </VisualMediaProvider>
  </VisualContractProvider>
);
const Part3MoldThreeParts06BugAddWallPreview: React.FC = () => (
  <VisualContractProvider contract={PREVIEW_VISUAL_CONTRACTS["part3_mold_three_parts:06_bug_add_wall"] ?? null}>
    <VisualMediaProvider media={PREVIEW_VISUAL_MEDIA["part3_mold_three_parts:06_bug_add_wall"] ?? null}>
      <GeneratedContractVisual />
    </VisualMediaProvider>
  </VisualContractProvider>
);
const Part3MoldThreeParts07RatchetTimelapsePreview: React.FC = () => (
  <VisualContractProvider contract={PREVIEW_VISUAL_CONTRACTS["part3_mold_three_parts:07_ratchet_timelapse"] ?? null}>
    <VisualMediaProvider media={PREVIEW_VISUAL_MEDIA["part3_mold_three_parts:07_ratchet_timelapse"] ?? null}>
      <GeneratedContractVisual />
    </VisualMediaProvider>
  </VisualContractProvider>
);
const Part3MoldThreeParts08TraditionalVsPddSplitPreview: React.FC = () => (
  <VisualContractProvider contract={PREVIEW_VISUAL_CONTRACTS["part3_mold_three_parts:08_traditional_vs_pdd_split"] ?? null}>
    <VisualMediaProvider media={PREVIEW_VISUAL_MEDIA["part3_mold_three_parts:08_traditional_vs_pdd_split"] ?? null}>
      <GeneratedContractVisual />
    </VisualMediaProvider>
  </VisualContractProvider>
);
const Part3MoldThreeParts09BugForkDiagramPreview: React.FC = () => (
  <VisualContractProvider contract={PREVIEW_VISUAL_CONTRACTS["part3_mold_three_parts:09_bug_fork_diagram"] ?? null}>
    <VisualMediaProvider media={PREVIEW_VISUAL_MEDIA["part3_mold_three_parts:09_bug_fork_diagram"] ?? null}>
      <GeneratedContractVisual />
    </VisualMediaProvider>
  </VisualContractProvider>
);
const Part3MoldThreeParts10FiveGenerationsPreview: React.FC = () => (
  <VisualContractProvider contract={PREVIEW_VISUAL_CONTRACTS["part3_mold_three_parts:10_five_generations"] ?? null}>
    <VisualMediaProvider media={PREVIEW_VISUAL_MEDIA["part3_mold_three_parts:10_five_generations"] ?? null}>
      <GeneratedContractVisual />
    </VisualMediaProvider>
  </VisualContractProvider>
);
const Part3MoldThreeParts11Z3FormalProofPreview: React.FC = () => (
  <VisualContractProvider contract={PREVIEW_VISUAL_CONTRACTS["part3_mold_three_parts:11_z3_formal_proof"] ?? null}>
    <VisualMediaProvider media={PREVIEW_VISUAL_MEDIA["part3_mold_three_parts:11_z3_formal_proof"] ?? null}>
      <GeneratedContractVisual />
    </VisualMediaProvider>
  </VisualContractProvider>
);
const Part3MoldThreeParts12ModuleLevelAsidePreview: React.FC = () => (
  <VisualContractProvider contract={PREVIEW_VISUAL_CONTRACTS["part3_mold_three_parts:12_module_level_aside"] ?? null}>
    <VisualMediaProvider media={PREVIEW_VISUAL_MEDIA["part3_mold_three_parts:12_module_level_aside"] ?? null}>
      <GeneratedContractVisual />
    </VisualMediaProvider>
  </VisualContractProvider>
);
const Part3MoldThreeParts13PromptNozzlePreview: React.FC = () => (
  <VisualContractProvider contract={PREVIEW_VISUAL_CONTRACTS["part3_mold_three_parts:13_prompt_nozzle"] ?? null}>
    <VisualMediaProvider media={PREVIEW_VISUAL_MEDIA["part3_mold_three_parts:13_prompt_nozzle"] ?? null}>
      <GeneratedContractVisual />
    </VisualMediaProvider>
  </VisualContractProvider>
);
const Part3MoldThreeParts14PromptRatioPreview: React.FC = () => (
  <VisualContractProvider contract={PREVIEW_VISUAL_CONTRACTS["part3_mold_three_parts:14_prompt_ratio"] ?? null}>
    <VisualMediaProvider media={PREVIEW_VISUAL_MEDIA["part3_mold_three_parts:14_prompt_ratio"] ?? null}>
      <GeneratedContractVisual />
    </VisualMediaProvider>
  </VisualContractProvider>
);
const Part3MoldThreeParts15ContextWindowComparisonPreview: React.FC = () => (
  <VisualContractProvider contract={PREVIEW_VISUAL_CONTRACTS["part3_mold_three_parts:15_context_window_comparison"] ?? null}>
    <VisualMediaProvider media={PREVIEW_VISUAL_MEDIA["part3_mold_three_parts:15_context_window_comparison"] ?? null}>
      <GeneratedContractVisual />
    </VisualMediaProvider>
  </VisualContractProvider>
);
const Part3MoldThreeParts17GroundingFeedbackLoopPreview: React.FC = () => (
  <VisualContractProvider contract={PREVIEW_VISUAL_CONTRACTS["part3_mold_three_parts:17_grounding_feedback_loop"] ?? null}>
    <VisualMediaProvider media={PREVIEW_VISUAL_MEDIA["part3_mold_three_parts:17_grounding_feedback_loop"] ?? null}>
      <GeneratedContractVisual />
    </VisualMediaProvider>
  </VisualContractProvider>
);
const Part3MoldThreeParts10ThreeComponentsTablePreview: React.FC = () => (
  <VisualContractProvider contract={PREVIEW_VISUAL_CONTRACTS["part3_mold_three_parts:18_three_components_table"] ?? null}>
    <VisualMediaProvider media={PREVIEW_VISUAL_MEDIA["part3_mold_three_parts:18_three_components_table"] ?? null}>
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
const Part4PrecisionTradeoff04CodeGenerationComparisonPreview: React.FC = () => (
  <VisualContractProvider contract={PREVIEW_VISUAL_CONTRACTS["part4_precision_tradeoff:04_code_generation_comparison"] ?? null}>
    <VisualMediaProvider media={PREVIEW_VISUAL_MEDIA["part4_precision_tradeoff:04_code_generation_comparison"] ?? null}>
      <GeneratedContractVisual />
    </VisualMediaProvider>
  </VisualContractProvider>
);
const Part4PrecisionTradeoff07EmbeddedCodeDocumentPreview: React.FC = () => (
  <VisualContractProvider contract={PREVIEW_VISUAL_CONTRACTS["part4_precision_tradeoff:05_embedded_code_document"] ?? null}>
    <VisualMediaProvider media={PREVIEW_VISUAL_MEDIA["part4_precision_tradeoff:05_embedded_code_document"] ?? null}>
      <Part4PrecisionTradeoff07EmbeddedCodeDocument />
    </VisualMediaProvider>
  </VisualContractProvider>
);
const Part4PrecisionTradeoff08PromptCodeSpectrumPreview: React.FC = () => (
  <VisualContractProvider contract={PREVIEW_VISUAL_CONTRACTS["part4_precision_tradeoff:06_prompt_code_spectrum"] ?? null}>
    <VisualMediaProvider media={PREVIEW_VISUAL_MEDIA["part4_precision_tradeoff:06_prompt_code_spectrum"] ?? null}>
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
const Part5CompoundReturns07EconomicsCrossingCallbackPreview: React.FC = () => (
  <VisualContractProvider contract={PREVIEW_VISUAL_CONTRACTS["part5_compound_returns:08_economics_crossing_callback"] ?? null}>
    <VisualMediaProvider media={PREVIEW_VISUAL_MEDIA["part5_compound_returns:08_economics_crossing_callback"] ?? null}>
      <Part5CompoundReturns07EconomicsCrossingCallback />
    </VisualMediaProvider>
  </VisualContractProvider>
);
const Part5CompoundReturns08ContrarianQuoteCardPreview: React.FC = () => (
  <VisualContractProvider contract={PREVIEW_VISUAL_CONTRACTS["part5_compound_returns:09_contrarian_quote_card"] ?? null}>
    <VisualMediaProvider media={PREVIEW_VISUAL_MEDIA["part5_compound_returns:09_contrarian_quote_card"] ?? null}>
      <Part5CompoundReturns08ContrarianQuoteCard />
    </VisualMediaProvider>
  </VisualContractProvider>
);
const Part5CompoundReturns10TransitionOutPreview: React.FC = () => (
  <VisualContractProvider contract={PREVIEW_VISUAL_CONTRACTS["part5_compound_returns:10_transition_out"] ?? null}>
    <VisualMediaProvider media={PREVIEW_VISUAL_MEDIA["part5_compound_returns:10_transition_out"] ?? null}>
      <GeneratedContractVisual />
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
const WhereToStart03ModuleHighlightTerminalPreview: React.FC = () => (
  <VisualContractProvider contract={PREVIEW_VISUAL_CONTRACTS["where_to_start:03_module_highlight_terminal"] ?? null}>
    <VisualMediaProvider media={PREVIEW_VISUAL_MEDIA["where_to_start:03_module_highlight_terminal"] ?? null}>
      <GeneratedContractVisual />
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
const WhereToStart05ModuleGlowSpreadPreview: React.FC = () => (
  <VisualContractProvider contract={PREVIEW_VISUAL_CONTRACTS["where_to_start:05_module_glow_spread"] ?? null}>
    <VisualMediaProvider media={PREVIEW_VISUAL_MEDIA["where_to_start:05_module_glow_spread"] ?? null}>
      <GeneratedContractVisual />
    </VisualMediaProvider>
  </VisualContractProvider>
);
const WhereToStart07NoBigBangCalloutPreview: React.FC = () => (
  <VisualContractProvider contract={PREVIEW_VISUAL_CONTRACTS["where_to_start:06_no_big_bang_callout"] ?? null}>
    <VisualMediaProvider media={PREVIEW_VISUAL_MEDIA["where_to_start:06_no_big_bang_callout"] ?? null}>
      <WhereToStart07NoBigBangCallout />
    </VisualMediaProvider>
  </VisualContractProvider>
);
const WhereToStart07TransitionToClosingPreview: React.FC = () => (
  <VisualContractProvider contract={PREVIEW_VISUAL_CONTRACTS["where_to_start:07_transition_to_closing"] ?? null}>
    <VisualMediaProvider media={PREVIEW_VISUAL_MEDIA["where_to_start:07_transition_to_closing"] ?? null}>
      <GeneratedContractVisual />
    </VisualMediaProvider>
  </VisualContractProvider>
);
const Closing03CodeRegenerateWorkflowPreview: React.FC = () => (
  <VisualContractProvider contract={PREVIEW_VISUAL_CONTRACTS["closing:02_code_regenerate_workflow"] ?? null}>
    <VisualMediaProvider media={PREVIEW_VISUAL_MEDIA["closing:02_code_regenerate_workflow"] ?? null}>
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
const Closing07TheBeatPreview: React.FC = () => (
  <VisualContractProvider contract={PREVIEW_VISUAL_CONTRACTS["closing:07_the_beat"] ?? null}>
    <VisualMediaProvider media={PREVIEW_VISUAL_MEDIA["closing:07_the_beat"] ?? null}>
      <Closing07TheBeat />
    </VisualMediaProvider>
  </VisualContractProvider>
);
const Closing09FinalTitleCardPreview: React.FC = () => (
  <VisualContractProvider contract={PREVIEW_VISUAL_CONTRACTS["closing:08_final_title_card"] ?? null}>
    <VisualMediaProvider media={PREVIEW_VISUAL_MEDIA["closing:08_final_title_card"] ?? null}>
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
        id="cold-open05-code-blink-patched"
        component={ColdOpen06CodeBlinkPatchedPreview}
        durationInFrames={150}
        fps={30}
        width={1920}
        height={1080}
      />
      <Composition
        id="cold-open06-code-regeneration"
        component={ColdOpen07CodeRegenerationPreview}
        durationInFrames={270}
        fps={30}
        width={1920}
        height={1080}
      />
      <Composition
        id="cold-open07-pdd-title-card"
        component={ColdOpen07PddTitleCardPreview}
        durationInFrames={150}
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
        id="part1-economics02-sock-price-chart"
        component={Part1Economics02SockPriceChartPreview}
        durationInFrames={900}
        fps={30}
        width={1920}
        height={1080}
      />
      <Composition
        id="part1-economics03-code-cost-chart"
        component={Part1Economics03CodeCostChartPreview}
        durationInFrames={1260}
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
        id="part1-economics06-performance-vs-context"
        component={Part1Economics06PerformanceVsContextPreview}
        durationInFrames={540}
        fps={30}
        width={1920}
        height={1080}
      />
      <Composition
        id="part1-economics07-two-by-two-grid"
        component={Part1Economics06TwoByTwoGridPreview}
        durationInFrames={750}
        fps={30}
        width={1920}
        height={1080}
      />
      <Composition
        id="part1-economics08-fork-codebase-size"
        component={Part1Economics08ForkCodebaseSizePreview}
        durationInFrames={1200}
        fps={30}
        width={1920}
        height={1080}
      />
      <Composition
        id="part1-economics09-patching-vs-regeneration-split"
        component={Part1Economics09PatchingVsRegenerationSplitPreview}
        durationInFrames={660}
        fps={30}
        width={1920}
        height={1080}
      />
      <Composition
        id="part1-economics10-context-compression"
        component={Part1Economics10ContextCompressionPreview}
        durationInFrames={600}
        fps={30}
        width={1920}
        height={1080}
      />
      <Composition
        id="part1-economics11-crossing-lines-moment"
        component={Part1Economics09CrossingLinesMomentPreview}
        durationInFrames={750}
        fps={30}
        width={1920}
        height={1080}
      />
      <Composition
        id="part1-economics12-developer-darning-split"
        component={Part1Economics12DeveloperDarningSplitPreview}
        durationInFrames={420}
        fps={30}
        width={1920}
        height={1080}
      />
      <Composition
        id="part1-economics15-key-insight-stillness"
        component={Part1Economics15KeyInsightStillnessPreview}
        durationInFrames={180}
        fps={30}
        width={1920}
        height={1080}
      />
      <Composition
        id="part1-economics16-double-meter-insight"
        component={Part1Economics10DoubleMeterInsightPreview}
        durationInFrames={750}
        fps={30}
        width={1920}
        height={1080}
      />
      <Composition
        id="part1-economics17-try-it-yourself"
        component={Part1Economics17TryItYourselfPreview}
        durationInFrames={180}
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
        id="part2-paradigm-shift02-double-meter-insight"
        component={Part2ParadigmShift02DoubleMeterInsightPreview}
        durationInFrames={1020}
        fps={30}
        width={1920}
        height={1080}
      />
      <Composition
        id="part2-paradigm-shift05-mold-defect-fix"
        component={Part2ParadigmShift05MoldDefectFixPreview}
        durationInFrames={510}
        fps={30}
        width={1920}
        height={1080}
      />
      <Composition
        id="part2-paradigm-shift06-craftsman-vs-mold"
        component={Part2ParadigmShift06CraftsmanVsMoldPreview}
        durationInFrames={600}
        fps={30}
        width={1920}
        height={1080}
      />
      <Composition
        id="part2-paradigm-shift10-verilog-synthesis-triple"
        component={Part2ParadigmShift07VerilogSynthesisTriplePreview}
        durationInFrames={540}
        fps={30}
        width={1920}
        height={1080}
      />
      <Composition
        id="part2-paradigm-shift11-synopsys-pdd-equivalence"
        component={Part2ParadigmShift08SynopsysPddEquivalencePreview}
        durationInFrames={390}
        fps={30}
        width={1920}
        height={1080}
      />
      <Composition
        id="part2-paradigm-shift12-abstraction-staircase"
        component={Part2ParadigmShift09AbstractionStaircasePreview}
        durationInFrames={480}
        fps={30}
        width={1920}
        height={1080}
      />
      <Composition
        id="part2-paradigm-shift13-prompt-replaces-review"
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
        id="part3-mold-three-parts03-test-walls-illuminate"
        component={Part3MoldThreeParts03TestWallsIlluminatePreview}
        durationInFrames={300}
        fps={30}
        width={1920}
        height={1080}
      />
      <Composition
        id="part3-mold-three-parts05-research-annotations"
        component={Part3MoldThreeParts05ResearchAnnotationsPreview}
        durationInFrames={540}
        fps={30}
        width={1920}
        height={1080}
      />
      <Composition
        id="part3-mold-three-parts06-bug-add-wall"
        component={Part3MoldThreeParts06BugAddWallPreview}
        durationInFrames={540}
        fps={30}
        width={1920}
        height={1080}
      />
      <Composition
        id="part3-mold-three-parts07-ratchet-timelapse"
        component={Part3MoldThreeParts07RatchetTimelapsePreview}
        durationInFrames={420}
        fps={30}
        width={1920}
        height={1080}
      />
      <Composition
        id="part3-mold-three-parts08-traditional-vs-pdd-split"
        component={Part3MoldThreeParts08TraditionalVsPddSplitPreview}
        durationInFrames={540}
        fps={30}
        width={1920}
        height={1080}
      />
      <Composition
        id="part3-mold-three-parts09-bug-fork-diagram"
        component={Part3MoldThreeParts09BugForkDiagramPreview}
        durationInFrames={360}
        fps={30}
        width={1920}
        height={1080}
      />
      <Composition
        id="part3-mold-three-parts10-five-generations"
        component={Part3MoldThreeParts10FiveGenerationsPreview}
        durationInFrames={540}
        fps={30}
        width={1920}
        height={1080}
      />
      <Composition
        id="part3-mold-three-parts11-z3-formal-proof"
        component={Part3MoldThreeParts11Z3FormalProofPreview}
        durationInFrames={720}
        fps={30}
        width={1920}
        height={1080}
      />
      <Composition
        id="part3-mold-three-parts12-module-level-aside"
        component={Part3MoldThreeParts12ModuleLevelAsidePreview}
        durationInFrames={720}
        fps={30}
        width={1920}
        height={1080}
      />
      <Composition
        id="part3-mold-three-parts13-prompt-nozzle"
        component={Part3MoldThreeParts13PromptNozzlePreview}
        durationInFrames={540}
        fps={30}
        width={1920}
        height={1080}
      />
      <Composition
        id="part3-mold-three-parts14-prompt-ratio"
        component={Part3MoldThreeParts14PromptRatioPreview}
        durationInFrames={540}
        fps={30}
        width={1920}
        height={1080}
      />
      <Composition
        id="part3-mold-three-parts15-context-window-comparison"
        component={Part3MoldThreeParts15ContextWindowComparisonPreview}
        durationInFrames={810}
        fps={30}
        width={1920}
        height={1080}
      />
      <Composition
        id="part3-mold-three-parts17-grounding-feedback-loop"
        component={Part3MoldThreeParts17GroundingFeedbackLoopPreview}
        durationInFrames={660}
        fps={30}
        width={1920}
        height={1080}
      />
      <Composition
        id="part3-mold-three-parts18-three-components-table"
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
        id="part4-precision-tradeoff04-code-generation-comparison"
        component={Part4PrecisionTradeoff04CodeGenerationComparisonPreview}
        durationInFrames={511}
        fps={30}
        width={1920}
        height={1080}
      />
      <Composition
        id="part4-precision-tradeoff05-embedded-code-document"
        component={Part4PrecisionTradeoff07EmbeddedCodeDocumentPreview}
        durationInFrames={480}
        fps={30}
        width={1920}
        height={1080}
      />
      <Composition
        id="part4-precision-tradeoff06-prompt-code-spectrum"
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
        id="part5-compound-returns08-economics-crossing-callback"
        component={Part5CompoundReturns07EconomicsCrossingCallbackPreview}
        durationInFrames={300}
        fps={30}
        width={1920}
        height={1080}
      />
      <Composition
        id="part5-compound-returns09-contrarian-quote-card"
        component={Part5CompoundReturns08ContrarianQuoteCardPreview}
        durationInFrames={300}
        fps={30}
        width={1920}
        height={1080}
      />
      <Composition
        id="part5-compound-returns10-transition-out"
        component={Part5CompoundReturns10TransitionOutPreview}
        durationInFrames={120}
        fps={30}
        width={1920}
        height={1080}
      />
      <Composition
        id="where-to-start01-section-title-card"
        component={WhereToStart01SectionTitleCardPreview}
        durationInFrames={90}
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
        id="where-to-start03-module-highlight-terminal"
        component={WhereToStart03ModuleHighlightTerminalPreview}
        durationInFrames={150}
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
        id="where-to-start05-module-glow-spread"
        component={WhereToStart05ModuleGlowSpreadPreview}
        durationInFrames={180}
        fps={30}
        width={1920}
        height={1080}
      />
      <Composition
        id="where-to-start06-no-big-bang-callout"
        component={WhereToStart07NoBigBangCalloutPreview}
        durationInFrames={90}
        fps={30}
        width={1920}
        height={1080}
      />
      <Composition
        id="where-to-start07-transition-to-closing"
        component={WhereToStart07TransitionToClosingPreview}
        durationInFrames={90}
        fps={30}
        width={1920}
        height={1080}
      />
      <Composition
        id="closing02-code-regenerate-workflow"
        component={Closing03CodeRegenerateWorkflowPreview}
        durationInFrames={300}
        fps={30}
        width={1920}
        height={1080}
      />
      <Composition
        id="closing04-pdd-triangle"
        component={Closing04PddTrianglePreview}
        durationInFrames={210}
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
        id="closing07-the-beat"
        component={Closing07TheBeatPreview}
        durationInFrames={120}
        fps={30}
        width={1920}
        height={1080}
      />
      <Composition
        id="closing08-final-title-card"
        component={Closing09FinalTitleCardPreview}
        durationInFrames={240}
        fps={30}
        width={1920}
        height={1080}
      />
    </>
  );
};
