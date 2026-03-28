import React from "react";
import { Composition } from "remotion";
import { VisualMediaProvider, VisualContractProvider } from "./_shared/visual-runtime";
import { GeneratedContractVisual } from "./_shared/GeneratedContractVisual";

import { ColdOpenSection } from "./cold_open";
import { Part1EconomicsSection } from "./part1_economics";
import { Part2ParadigmShiftSection } from "./part2_paradigm_shift";
import { Part3MoldPartsSection } from "./part3_mold_parts";
import { Part4PrecisionTradeoffSection } from "./part4_precision_tradeoff";
import { Part5CompoundReturnsSection } from "./part5_compound_returns";
import { WhereToStartSection } from "./where_to_start";
import { ClosingSection } from "./closing";
import { ColdOpen07CodeCursorBlink } from "./ColdOpen07CodeCursorBlink";
import { Part1Economics02SockPriceChart } from "./Part1Economics02SockPriceChart";
import { Part1Economics03CodeCostChart } from "./Part1Economics03CodeCostChart";
import { Part1Economics06DebtLayersZoom } from "./Part1Economics06DebtLayersZoom";
import { Part1Economics07ContextWindowShrink } from "./Part1Economics07ContextWindowShrink";
import { Part1Economics08PerformanceVsContext } from "./Part1Economics08PerformanceVsContext";
import { Part1Economics09TwoByTwoGrid } from "./Part1Economics09TwoByTwoGrid";
import { Part1Economics10ForkCodebaseSize } from "./Part1Economics10ForkCodebaseSize";
import { Part1Economics11PatchingVsRegeneration } from "./Part1Economics11PatchingVsRegeneration";
import { Part1Economics12ContextCompression } from "./Part1Economics12ContextCompression";
import { Part1Economics13CrossingLinesMoment } from "./Part1Economics13CrossingLinesMoment";
import { Part1Economics18KeyInsightStillness } from "./Part1Economics18KeyInsightStillness";
import { Part1Economics19DoubleMeterInsight } from "./Part1Economics19DoubleMeterInsight";
import { Part1Economics20TryItYourself } from "./Part1Economics20TryItYourself";
import { Part2ParadigmShift04MoldProductionCounter } from "./Part2ParadigmShift04MoldProductionCounter";
import { Part2ParadigmShift11SchematicDensityZoom } from "./Part2ParadigmShift11SchematicDensityZoom";
import { Part2ParadigmShift12VerilogSynthesis } from "./Part2ParadigmShift12VerilogSynthesis";
import { Part2ParadigmShift13TripleSynthesisEquivalence } from "./Part2ParadigmShift13TripleSynthesisEquivalence";
import { Part2ParadigmShift14SynopsysPddEquivalence } from "./Part2ParadigmShift14SynopsysPddEquivalence";
import { Part2ParadigmShift15AbstractionStaircase } from "./Part2ParadigmShift15AbstractionStaircase";
import { Part2ParadigmShift16BillionGateUnreviewable } from "./Part2ParadigmShift16BillionGateUnreviewable";
import { Part2ParadigmShift17ReviewSpecVerifyOutput } from "./Part2ParadigmShift17ReviewSpecVerifyOutput";
import { Part2ParadigmShift18PromptMoldFinale } from "./Part2ParadigmShift18PromptMoldFinale";
import { Part3MoldParts02MoldCrossSection } from "./Part3MoldParts02MoldCrossSection";
import { Part3MoldParts03MoldWallsIlluminate } from "./Part3MoldParts03MoldWallsIlluminate";
import { Part3MoldParts04LiquidInjection } from "./Part3MoldParts04LiquidInjection";
import { Part3MoldParts05BugAddsWall } from "./Part3MoldParts05BugAddsWall";
import { Part3MoldParts06RatchetTimelapse } from "./Part3MoldParts06RatchetTimelapse";
import { Part3MoldParts08BugForkRoad } from "./Part3MoldParts08BugForkRoad";
import { Part3MoldParts09FiveGenerations } from "./Part3MoldParts09FiveGenerations";
import { Part3MoldParts10Z3FormalProof } from "./Part3MoldParts10Z3FormalProof";
import { Part3MoldParts11ModuleBoundary } from "./Part3MoldParts11ModuleBoundary";
import { Part3MoldParts12PromptNozzle } from "./Part3MoldParts12PromptNozzle";
import { Part3MoldParts13PromptRatio } from "./Part3MoldParts13PromptRatio";
import { Part3MoldParts15GroundingStyles } from "./Part3MoldParts15GroundingStyles";
import { Part3MoldParts16ThreeComponentsPullback } from "./Part3MoldParts16ThreeComponentsPullback";
import { Part3MoldParts17ComponentTable } from "./Part3MoldParts17ComponentTable";
import { Part3MoldParts18CodeOutputFinale } from "./Part3MoldParts18CodeOutputFinale";
import { Part4PrecisionTradeoff04DetailedPromptFile } from "./Part4PrecisionTradeoff04DetailedPromptFile";
import { Part4PrecisionTradeoff05MinimalPromptWithTests } from "./Part4PrecisionTradeoff05MinimalPromptWithTests";
import { Part4PrecisionTradeoff06DualGenerationComparison } from "./Part4PrecisionTradeoff06DualGenerationComparison";
import { Part4PrecisionTradeoff07KeyInsightWalls } from "./Part4PrecisionTradeoff07KeyInsightWalls";
import { Part4PrecisionTradeoff08EmbeddedCodeDocument } from "./Part4PrecisionTradeoff08EmbeddedCodeDocument";
import { Part4PrecisionTradeoff09PromptCodeSpectrum } from "./Part4PrecisionTradeoff09PromptCodeSpectrum";
import { Part5CompoundReturns02MaintenancePieChart } from "./Part5CompoundReturns02MaintenancePieChart";
import { Part5CompoundReturns03CompoundDebtCurve } from "./Part5CompoundReturns03CompoundDebtCurve";
import { Part5CompoundReturns04DivergingCostCurves } from "./Part5CompoundReturns04DivergingCostCurves";
import { Part5CompoundReturns05InvestmentComparisonTable } from "./Part5CompoundReturns05InvestmentComparisonTable";
import { WhereToStart02LegacyCodebaseReveal } from "./WhereToStart02LegacyCodebaseReveal";
import { WhereToStart04SourceOfTruthLabel } from "./WhereToStart04SourceOfTruthLabel";
import { WhereToStart05ModuleGlowSpread } from "./WhereToStart05ModuleGlowSpread";
import { WhereToStart06NoBigBangCallout } from "./WhereToStart06NoBigBangCallout";
import { WhereToStart07GradualMigrationInsight } from "./WhereToStart07GradualMigrationInsight";
import { Closing03PddTriangle } from "./Closing03PddTriangle";
import { Closing04DissolveRegenerateLoop } from "./Closing04DissolveRegenerateLoop";
import { Closing06TheBeat } from "./Closing06TheBeat";
import { Closing07FinalTitleCard } from "./Closing07FinalTitleCard";

const PREVIEW_VISUAL_MEDIA: Record<string, Record<string, string>> = {
  "cold_open:01_split_screen_darning": { defaultSrc: "veo/developer_cursor_edit.mp4", backgroundSrc: "veo/developer_cursor_edit.mp4", outputSrc: "veo/developer_cursor_edit.mp4", baseSrc: "veo/developer_cursor_edit.mp4" },
  "part1_economics:14_split_developer_grandma": { defaultSrc: "veo/developer_cursor_p1.mp4", backgroundSrc: "veo/developer_cursor_p1.mp4", outputSrc: "veo/developer_cursor_p1.mp4", baseSrc: "veo/developer_cursor_p1.mp4" },
  "part2_paradigm_shift:07_split_craftsman_vs_mold": { defaultSrc: "veo/craftsman_carving.mp4", backgroundSrc: "veo/craftsman_carving.mp4", outputSrc: "veo/craftsman_carving.mp4", baseSrc: "veo/craftsman_carving.mp4" },
};

const PREVIEW_VISUAL_CONTRACTS: Record<string, Record<string, unknown> | null> = {
  "cold_open:01_split_screen_darning": {"specBaseName": "01_split_screen_darning", "dataPoints": {"type": "split_screen", "layout": "vertical_50_50", "divider": {"color": "#FFFFFF", "width": 2, "opacity": 0.4}, "panels": {"left": {"clips": ["developer_cursor_edit", "developer_codebase_zoomout"], "label": "Developer patching code"}, "right": {"clips": ["grandmother_darning", "grandmother_drawer_zoomout"], "label": "Grandmother darning socks"}}, "narrationSegments": ["cold_open_001", "cold_open_002", "cold_open_003"], "durationSeconds": 9.0}, "mediaAliases": {"defaultSrc": "veo/developer_cursor_edit.mp4", "backgroundSrc": "veo/developer_cursor_edit.mp4", "outputSrc": "veo/developer_cursor_edit.mp4", "baseSrc": "veo/developer_cursor_edit.mp4"}, "overlayConfig": null, "renderMode": "component"},
  "cold_open:07_code_cursor_blink": {"specBaseName": "07_code_cursor_blink", "dataPoints": {"type": "code_editor", "language": "python", "theme": "catppuccin-mocha", "functionName": "process_order", "totalLines": 40, "patchComments": [{"line": 5, "text": "// PATCH: fixed null check", "age": "old"}, {"line": 12, "text": "// TODO: refactor this block", "age": "old"}, {"line": 18, "text": "// HOTFIX: edge case #1247", "age": "medium"}, {"line": 23, "text": "// PATCH: handle empty list", "age": "recent"}, {"line": 31, "text": "// PATCH: timezone fix", "age": "medium"}, {"line": 37, "text": "// HOTFIX: race condition", "age": "recent"}], "cursor": {"line": 23, "column": 4, "blinkMs": 500}, "narrationSegments": ["cold_open_005"], "durationSeconds": 1.6}, "mediaAliases": {}, "overlayConfig": null, "renderMode": "component"},
  "cold_open:08_code_regeneration": {"specBaseName": "08_code_regeneration", "dataPoints": {"type": "code_regeneration", "language": "python", "theme": "catppuccin-mocha", "functionName": "process_order", "originalLines": 40, "regeneratedLines": 30, "patchCommentsRemoved": 6, "terminalCommand": "pdd generate process_order", "phases": [{"name": "select", "startFrame": 0, "endFrame": 8}, {"name": "delete", "startFrame": 8, "endFrame": 12}, {"name": "void", "startFrame": 12, "endFrame": 14}, {"name": "regenerate", "startFrame": 14, "endFrame": 44}, {"name": "terminal", "startFrame": 38, "endFrame": 48}, {"name": "hold", "startFrame": 48, "endFrame": 60}], "narrationSegments": ["cold_open_006"], "durationSeconds": 2.0}, "mediaAliases": {}, "overlayConfig": null, "renderMode": "component"},
  "cold_open:09_title_card_pdd": {"specBaseName": "09_title_card_pdd", "dataPoints": {"type": "title_card", "sectionNumber": 0, "titleLine1": "PROMPT-DRIVEN", "titleLine2": "DEVELOPMENT", "backgroundColor": "#1E1E2E", "backgroundLayer": "regenerated_code_at_15_percent", "accentColor": "#89B4FA", "narrationSegments": ["cold_open_006"], "durationSeconds": 2.0}, "mediaAliases": {}, "overlayConfig": null, "renderMode": "component"},
  "part1_economics:01_section_title_card": {"specBaseName": "01_section_title_card", "dataPoints": {"type": "title_card", "sectionNumber": 1, "sectionLabel": "PART 1", "titleLine1": "THE ECONOMICS", "titleLine2": "OF DARNING", "backgroundColor": "#0A0F1A", "ghostElements": [{"shape": "crossing_lines", "colors": ["#D9944A", "#4A90D9"], "role": "cost_crossing_preview"}], "narrationSegments": ["part1_economics_001", "part1_economics_002", "part1_economics_003"]}, "mediaAliases": {}, "overlayConfig": {"fadeOutFrames": 60}, "renderMode": "component"},
  "part1_economics:02_sock_price_chart": {"specBaseName": "02_sock_price_chart", "dataPoints": {"type": "line_chart", "chartId": "sock_price_vs_labor", "xAxis": {"label": "Year", "range": [1950, 2020], "tickInterval": 10}, "yAxis": {"label": "Cost (relative to hourly wage)", "range": [0, 1]}, "series": [{"id": "labor_cost", "label": "Labor cost", "color": "#D9944A", "data": [{"x": 1950, "y": 0.2}, {"x": 1960, "y": 0.35}, {"x": 1970, "y": 0.5}, {"x": 1980, "y": 0.6}, {"x": 1990, "y": 0.7}, {"x": 2000, "y": 0.78}, {"x": 2010, "y": 0.82}, {"x": 2020, "y": 0.85}]}, {"id": "garment_cost", "label": "Garment cost (relative)", "color": "#4A90D9", "data": [{"x": 1950, "y": 0.8}, {"x": 1960, "y": 0.5}, {"x": 1965, "y": 0.35}, {"x": 1970, "y": 0.25}, {"x": 1980, "y": 0.18}, {"x": 1990, "y": 0.12}, {"x": 2000, "y": 0.1}, {"x": 2020, "y": 0.08}]}], "annotations": [{"type": "crossing_point", "x": 1962, "label": "The Threshold"}], "narrationSegments": ["part1_economics_004", "part1_economics_005"]}, "mediaAliases": {}, "overlayConfig": {"fadeInFrames": 30}, "renderMode": "component"},
  "part1_economics:03_code_cost_chart": {"specBaseName": "03_code_cost_chart", "dataPoints": {"type": "multi_line_chart", "chartId": "code_cost_generate_vs_patch", "xAxis": {"label": "Year", "range": [2000, 2026]}, "yAxis": {"label": "Cost (Developer Hours)"}, "series": [{"id": "generate_cost", "label": "Cost to generate", "color": "#4A90D9", "strokeStyle": "solid", "data": [{"x": 2000, "y": 0.9}, {"x": 2010, "y": 0.88}, {"x": 2020, "y": 0.85}, {"x": 2021, "y": 0.82}, {"x": 2022, "y": 0.78}, {"x": 2023, "y": 0.65}, {"x": 2024, "y": 0.35}, {"x": 2025, "y": 0.18}, {"x": 2026, "y": 0.1}]}, {"id": "immediate_patch", "label": "Immediate patch cost", "color": "#D9944A", "strokeStyle": "solid", "data": [{"x": 2000, "y": 0.55}, {"x": 2010, "y": 0.52}, {"x": 2020, "y": 0.48}, {"x": 2021, "y": 0.42}, {"x": 2022, "y": 0.35}, {"x": 2023, "y": 0.28}, {"x": 2024, "y": 0.22}, {"x": 2025, "y": 0.18}, {"x": 2026, "y": 0.15}]}, {"id": "total_cost_debt", "label": "Total cost (with debt)", "color": "#D9944A", "strokeStyle": "dashed", "data": [{"x": 2000, "y": 0.6}, {"x": 2010, "y": 0.62}, {"x": 2020, "y": 0.65}, {"x": 2021, "y": 0.66}, {"x": 2022, "y": 0.68}, {"x": 2023, "y": 0.7}, {"x": 2024, "y": 0.72}, {"x": 2025, "y": 0.73}, {"x": 2026, "y": 0.74}]}], "shadedArea": {"upper": "total_cost_debt", "lower": "immediate_patch", "color": "#D9944A", "opacity": 0.12, "label": "Technical debt"}, "dateMarkers": ["Codex (2021)", "GPT-4 (2023)", "Claude (2023)", "Gemini (2024)"], "narrationSegments": ["part1_economics_006", "part1_economics_007", "part1_economics_008", "part1_economics_009"]}, "mediaAliases": {}, "overlayConfig": null, "renderMode": "component"},
  "part1_economics:04_research_annotations": {"specBaseName": "04_research_annotations", "dataPoints": {"type": "annotation_overlay", "chartRef": "code_cost_generate_vs_patch", "annotations": [{"id": "github_study", "mainText": "Individual task: −55%", "source": "GitHub, 2022", "finePrint": "95 developers, one greenfield task", "targetLine": "immediate_patch", "accentColor": "#4A90D9", "direction": "positive"}, {"id": "uplevel_study", "mainText": "Overall throughput: ~0%", "source": "Uplevel, 2024", "finePrint": "785 developers, one year", "targetLine": "total_cost_debt", "accentColor": "#EF4444", "direction": "flat"}], "narrationSegments": ["part1_economics_010", "part1_economics_011"]}, "mediaAliases": {}, "overlayConfig": null, "renderMode": "component"},
  "part1_economics:05_code_churn_annotations": {"specBaseName": "05_code_churn_annotations", "dataPoints": {"type": "annotation_overlay", "chartRef": "code_cost_generate_vs_patch", "annotations": [{"id": "gitclear_churn", "mainText": "Code churn: +44%", "source": "GitClear, 2025", "finePrint": "211M lines analyzed", "targetArea": "debt_area", "accentColor": "#EF4444"}, {"id": "gitclear_refactoring", "mainText": "Refactoring: −60%", "source": "GitClear, 2025", "finePrint": "Code revised within 2 weeks", "targetArea": "debt_gap", "accentColor": "#F59E0B"}], "narrationSegments": ["part1_economics_012", "part1_economics_013"]}, "mediaAliases": {}, "overlayConfig": null, "renderMode": "component"},
  "part1_economics:06_debt_layers_zoom": {"specBaseName": "06_debt_layers_zoom", "dataPoints": {"type": "debt_layer_zoom", "chartRef": "code_cost_generate_vs_patch", "layers": [{"id": "code_complexity", "label": "Code Complexity", "color": "#D9944A", "opacity": 0.18, "position": "lower", "description": "Traditional technical debt: spaghetti code, dependency tangles"}, {"id": "context_rot", "label": "Context Rot", "color": "#F59E0B", "opacity": 0.12, "position": "upper", "noiseTexture": true, "description": "AI-specific: model performance degrades as codebase exceeds context window"}], "narrationSegments": ["part1_economics_013", "part1_economics_014"]}, "mediaAliases": {}, "overlayConfig": null, "renderMode": "component"},
  "part1_economics:07_context_window_shrink": {"specBaseName": "07_context_window_shrink", "dataPoints": {"type": "context_window_visualization", "chartId": "context_window_shrink", "growthStages": [{"gridSize": "4x4", "coverage": 0.8, "coverageColor": "#5AAA6E"}, {"gridSize": "8x8", "coverage": 0.4, "coverageColor": "#F59E0B"}, {"gridSize": "16x16", "coverage": 0.1, "coverageColor": "#EF4444"}, {"gridSize": "32x32", "coverage": 0.02, "coverageColor": "#DC2626"}], "contextWindow": {"width": 280, "height": 240, "borderColor": "#4A90D9", "fixed": true}, "mismatchPhase": {"irrelevantInsideCount": 4, "neededOutsideCount": 6}, "narrationSegments": ["part1_economics_014", "part1_economics_015", "part1_economics_016"]}, "mediaAliases": {}, "overlayConfig": null, "renderMode": "component"},
  "part1_economics:08_performance_vs_context": {"specBaseName": "08_performance_vs_context", "dataPoints": {"type": "inset_chart", "chartId": "performance_vs_context_length", "insetPosition": {"x": 1350, "y": 680}, "insetSize": {"width": 480, "height": 300}, "series": [{"id": "performance_degradation", "color": "#EF4444", "data": [{"x": "4K", "y": 1.0}, {"x": "32K", "y": 0.86}, {"x": "128K", "y": 0.5}, {"x": "1M", "y": 0.15}]}], "annotations": [{"text": "14-85% degradation", "source": "EMNLP, 2025"}, {"text": "Faster patching → faster growth → faster rot", "type": "cycle"}], "narrationSegments": ["part1_economics_017", "part1_economics_018"]}, "mediaAliases": {}, "overlayConfig": null, "renderMode": "component"},
  "part1_economics:09_two_by_two_grid": {"specBaseName": "09_two_by_two_grid", "dataPoints": {"type": "two_by_two_matrix", "chartId": "study_reconciliation_grid", "axes": {"x": {"labels": ["Greenfield", "Brownfield"]}, "y": {"labels": ["In-Distribution", "Out-of-Distribution"]}}, "quadrants": [{"position": "top-left", "color": "#5AAA6E", "label": "GitHub study: +55%", "source": "GitHub, 2022"}, {"position": "bottom-right", "color": "#EF4444", "label": "METR study: −19%", "source": "METR, 2025"}], "insightText": "Every study is correct. They just measured different quadrants.", "narrationSegments": ["part1_economics_019"]}, "mediaAliases": {}, "overlayConfig": {"fadeInFrames": 45}, "renderMode": "component"},
  "part1_economics:10_fork_codebase_size": {"specBaseName": "10_fork_codebase_size", "dataPoints": {"type": "forking_line_chart", "chartRef": "code_cost_generate_vs_patch", "forkPoint": {"x": 2020, "y": 0.48}, "forks": [{"id": "small_codebase", "label": "Small codebase", "color": "#5AAA6E", "data": [{"x": 2020, "y": 0.48}, {"x": 2022, "y": 0.3}, {"x": 2024, "y": 0.18}, {"x": 2026, "y": 0.1}]}, {"id": "large_codebase", "label": "Large codebase", "color": "#EF4444", "data": [{"x": 2020, "y": 0.48}, {"x": 2022, "y": 0.47}, {"x": 2024, "y": 0.46}, {"x": 2026, "y": 0.45}]}], "annotations": [{"text": "METR, 2025: experienced devs 19% slower on mature repos", "target": "large_codebase"}, {"text": "Developers believed AI saved 20%. It cost 19%.", "target": "large_codebase", "style": "italic"}, {"text": "Every patch adds code.", "type": "arrow", "from": "small_codebase", "to": "large_codebase"}], "narrationSegments": ["part1_economics_020", "part1_economics_021", "part1_economics_022"]}, "mediaAliases": {}, "overlayConfig": null, "renderMode": "component"},
  "part1_economics:11_patching_vs_regeneration": {"specBaseName": "11_patching_vs_regeneration", "dataPoints": {"type": "side_by_side_comparison", "chartId": "patching_vs_regeneration", "panels": {"left": {"header": "Agentic Patching", "tokenCount": 15000, "distribution": {"irrelevant": 0.8, "relevant": 0.05, "neutral": 0.15}, "label": "15,000 tokens — mostly wrong", "accentColor": "#EF4444"}, "right": {"header": "PDD Regeneration", "blocks": [{"label": "Prompt", "tokens": 300, "color": "#4A90D9"}, {"label": "Tests", "tokens": 2000, "color": "#D9944A"}, {"label": "Grounding", "tokens": 200, "color": "#5AAA6E"}], "label": "2,300 tokens — all curated", "accentColor": "#5AAA6E"}}, "narrationSegments": ["part1_economics_023", "part1_economics_024"]}, "mediaAliases": {}, "overlayConfig": null, "renderMode": "component"},
  "part1_economics:12_context_compression": {"specBaseName": "12_context_compression", "dataPoints": {"type": "context_compression_animation", "chartId": "module_compression", "modules": ["auth", "parser", "router", "validator", "logger", "cache", "queue", "mailer", "search", "analytics", "billing", "permissions", "notifications", "export", "import", "scheduler", "webhook", "api_client", "transformer", "serializer"], "codeTokensPerModule": 750, "promptTokensPerModule": 100, "contextWindowTokens": 4000, "overflowCount": 17, "compressionRatio": "5-10×", "narrationSegments": ["part1_economics_025", "part1_economics_026"]}, "mediaAliases": {}, "overlayConfig": null, "renderMode": "component"},
  "part1_economics:13_crossing_lines_moment": {"specBaseName": "13_crossing_lines_moment", "dataPoints": {"type": "crossing_moment", "chartRef": "code_cost_generate_vs_patch", "crossings": [{"id": "generate_crosses_total_cost", "year": 2025.2, "description": "Generate cost drops below total cost with debt"}, {"id": "generate_crosses_immediate", "year": 2025.6, "description": "Generate cost drops below immediate patch cost"}], "label": "We are here.", "narrationSegments": ["part1_economics_026"]}, "mediaAliases": {}, "overlayConfig": null, "renderMode": "component"},
  "part1_economics:14_split_developer_grandma": {"specBaseName": "14_split_developer_grandma", "dataPoints": {"type": "split_screen", "layout": "vertical_50_50", "divider": {"color": "#FFFFFF", "width": 2, "opacity": 0.6}, "panels": {"left": {"clips": ["developer_cursor_p1"], "label": "Developer with Cursor"}, "right": {"clips": ["grandmother_darning_p1"], "label": "Grandmother darning"}}, "narrationSegments": ["part1_economics_027", "part1_economics_028"], "durationSeconds": 17.0}, "mediaAliases": {"defaultSrc": "veo/developer_cursor_p1.mp4", "backgroundSrc": "veo/developer_cursor_p1.mp4", "outputSrc": "veo/developer_cursor_p1.mp4", "baseSrc": "veo/developer_cursor_p1.mp4"}, "overlayConfig": null, "renderMode": "component"},
  "part1_economics:18_key_insight_stillness": {"specBaseName": "18_key_insight_stillness", "dataPoints": {"type": "stillness_beat", "style": "3b1b_key_insight", "backgroundColor": "#050810", "text": "So let me put together what I just showed you.", "textColor": "#94A3B8", "textOpacity": 0.6, "purpose": "Palate cleanser before key insight synthesis"}, "mediaAliases": {}, "overlayConfig": {"fadeOutFrames": 60}, "renderMode": "component"},
  "part1_economics:19_double_meter_insight": {"specBaseName": "19_double_meter_insight", "dataPoints": {"type": "double_meter", "chartId": "context_plus_performance", "meters": [{"id": "context_window", "title": "Effective Context Window", "fillColor": "#4A90D9", "bottomValue": "1×", "topValue": "5-10×", "position": "left"}, {"id": "model_performance", "title": "Model Performance", "fillColor": "#5AAA6E", "bottomValue": "Baseline", "topValue": "+89%", "position": "right"}], "insightText": "Bigger window AND smarter model.", "insightHighlight": {"word": "AND", "color": "#F59E0B"}}, "mediaAliases": {}, "overlayConfig": null, "renderMode": "component"},
  "part1_economics:20_try_it_yourself": {"specBaseName": "20_try_it_yourself", "dataPoints": {"type": "title_card", "style": "handwritten_challenge", "mainText": "Try it yourself.", "font": "Caveat", "instructions": ["Give your favorite LLM a hard coding problem as code,", "then as natural language.", "The natural language version will win."], "backgroundColor": "#0A0F1A", "accentColor": "#4A90D9"}, "mediaAliases": {}, "overlayConfig": null, "renderMode": "component"},
  "part2_paradigm_shift:01_section_title_card": {"specBaseName": "01_section_title_card", "dataPoints": {"type": "title_card", "sectionNumber": 2, "sectionLabel": "PART 2", "titleLine1": "THE PARADIGM", "titleLine2": "SHIFT", "backgroundColor": "#0A0F1A", "ghostElements": [{"shape": "mold_silhouette", "colors": ["#4A90D9", "#D9944A"], "role": "injection_mold_preview"}], "narrationSegments": ["part2_paradigm_shift_001", "part2_paradigm_shift_002", "part2_paradigm_shift_003", "part2_paradigm_shift_004", "part2_paradigm_shift_005"]}, "mediaAliases": {}, "overlayConfig": {"fadeOutFrames": 90}, "renderMode": "component"},
  "part2_paradigm_shift:04_mold_production_counter": {"specBaseName": "04_mold_production_counter", "dataPoints": {"type": "counter_animation", "chartId": "mold_production_counter", "counter": {"start": 1, "end": 10000, "milestones": [1, 10, 100, 1000, 10000], "easing": "exponential"}, "moldCycle": {"startFramesPerCycle": 60, "endFramesPerCycle": 6}, "narrationSegments": ["part2_paradigm_shift_006"]}, "mediaAliases": {}, "overlayConfig": null, "renderMode": "component"},
  "part2_paradigm_shift:07_split_craftsman_vs_mold": {"specBaseName": "07_split_craftsman_vs_mold", "dataPoints": {"type": "split_screen", "layout": "vertical_50_50", "divider": {"color": "#FFFFFF", "width": 2, "opacity": 0.4}, "panels": {"left": {"clips": ["craftsman_carving"], "label": "Craftsman — value in the object", "aura": {"color": "#D9944A", "target": "object"}}, "right": {"clips": ["mold_plastic_flow"], "label": "Mold — value in the specification", "aura": {"color": "#4A90D9", "target": "mold"}, "partDissolve": true}}, "narrationSegments": ["part2_paradigm_shift_009", "part2_paradigm_shift_010"], "durationSeconds": 20.0}, "mediaAliases": {"defaultSrc": "veo/craftsman_carving.mp4", "backgroundSrc": "veo/craftsman_carving.mp4", "outputSrc": "veo/craftsman_carving.mp4", "baseSrc": "veo/craftsman_carving.mp4"}, "overlayConfig": null, "renderMode": "component"},
  "part2_paradigm_shift:11_schematic_density_zoom": {"specBaseName": "11_schematic_density_zoom", "dataPoints": {"type": "schematic_zoom", "chartId": "schematic_density_zoom", "counter": {"start": 20, "end": 50000, "milestones": [100, 500, 5000, 25000, 50000]}, "zoom": {"startScale": 8, "endScale": 0.1, "easing": "easeInOutCubic"}, "narrationSegments": ["part2_paradigm_shift_011"]}, "mediaAliases": {}, "overlayConfig": null, "renderMode": "component"},
  "part2_paradigm_shift:12_verilog_synthesis": {"specBaseName": "12_verilog_synthesis", "dataPoints": {"type": "synthesis_animation", "chartId": "verilog_synthesis", "codeLanguage": "verilog", "codeSample": "module counter(\\n  input clk, rst,\\n  output reg [7:0] count\\n);\\n  always @(posedge clk)\\n    if (rst) count <= 0;\\n    else count <= count + 1;\\nendmodule", "synthesisStages": ["code_input", "synthesis_process", "gate_output"], "narrationSegments": ["part2_paradigm_shift_011"]}, "mediaAliases": {}, "overlayConfig": null, "renderMode": "component"},
  "part2_paradigm_shift:13_triple_synthesis_equivalence": {"specBaseName": "13_triple_synthesis_equivalence", "dataPoints": {"type": "equivalence_demo", "chartId": "triple_synthesis_equivalence", "runs": [{"id": "run_1", "topology": "dense-left", "label": "Run 1"}, {"id": "run_2", "topology": "tree-branch", "label": "Run 2"}, {"id": "run_3", "topology": "linear-chain", "label": "Run 3"}], "equivalenceLabel": "Functionally equivalent", "equivalenceColor": "#5AAA6E", "narrationSegments": ["part2_paradigm_shift_012", "part2_paradigm_shift_013"]}, "mediaAliases": {}, "overlayConfig": {"fadeInFrames": 120}, "renderMode": "component"},
  "part2_paradigm_shift:14_synopsys_pdd_equivalence": {"specBaseName": "14_synopsys_pdd_equivalence", "dataPoints": {"type": "text_overlay", "chartId": "synopsys_pdd_equivalence", "lines": [{"accent": {"text": "Synopsys:", "color": "#4A90D9"}, "body": "specification in → verified hardware out."}, {"accent": {"text": "PDD:", "color": "#D9944A"}, "body": "prompt in → verified software out."}], "subtitle": "Same architecture.", "equivalenceMappings": [{"from": "specification", "to": "prompt"}, {"from": "hardware", "to": "software"}], "narrationSegments": ["part2_paradigm_shift_014"]}, "mediaAliases": {}, "overlayConfig": {"fadeOutFrames": 60}, "renderMode": "component"},
  "part2_paradigm_shift:15_abstraction_staircase": {"specBaseName": "15_abstraction_staircase", "dataPoints": {"type": "staircase_timeline", "chartId": "abstraction_staircase", "steps": [{"label": "Transistors", "decade": "1970s", "color": "#D9944A", "level": 1}, {"label": "Schematics", "decade": "1980s", "color": "#D9944A", "level": 2}, {"label": "RTL / Verilog", "decade": "1990s", "color": "#4A90D9", "level": 3}, {"label": "Behavioral / HLS", "decade": "2010s", "color": "#4A90D9", "level": 4}, {"label": "Natural language → Code", "decade": "2020s", "color": "#5AAA6E", "level": 5, "emphasis": true}], "transitionLabel": "Couldn't scale", "transitionColor": "#EF4444", "narrationSegments": ["part2_paradigm_shift_015"]}, "mediaAliases": {}, "overlayConfig": {"fadeOutFrames": 60}, "renderMode": "component"},
  "part2_paradigm_shift:16_billion_gate_unreviewable": {"specBaseName": "16_billion_gate_unreviewable", "dataPoints": {"type": "density_comparison", "chartId": "billion_gate_unreviewable", "chipView": {"gateCount": "2.1 billion", "zoomLevels": 3}, "diffView": {"linesChanged": 47382, "scrollSpeed": "fast"}, "narrationSegments": ["part2_paradigm_shift_016"]}, "mediaAliases": {}, "overlayConfig": null, "renderMode": "component"},
  "part2_paradigm_shift:17_review_spec_verify_output": {"specBaseName": "17_review_spec_verify_output", "dataPoints": {"type": "comparison_layout", "chartId": "review_spec_verify_output", "panels": {"left": {"type": "prompt_document", "header": "PROMPT", "accentColor": "#D9944A", "lineCount": 20}, "right": {"type": "test_suite", "header": "TEST SUITE", "accentColor": "#5AAA6E", "tests": [{"name": "test_counter_increments", "status": "pass"}, {"name": "test_reset_clears_state", "status": "pass"}, {"name": "test_overflow_wraps", "status": "pass"}, {"name": "test_edge_case_zero", "status": "pass"}, {"name": "test_concurrent_access", "status": "pass"}]}}, "label": "Review the spec. Verify the output.", "narrationSegments": ["part2_paradigm_shift_016"]}, "mediaAliases": {}, "overlayConfig": null, "renderMode": "component"},
  "part2_paradigm_shift:18_prompt_mold_finale": {"specBaseName": "18_prompt_mold_finale", "dataPoints": {"type": "metaphor_animation", "chartId": "prompt_mold_finale", "elements": {"prompt": {"label": "PROMPT", "color": "#D9944A", "role": "mold_specification"}, "code": {"color": "#E2E8F0", "role": "plastic_output", "regenerates": true}, "tests": {"color": "#5AAA6E", "role": "mold_walls", "labels": ["assert", "expect", "verify", "test"]}}, "regenerationCycles": 3, "thesis": "The prompt is your mold. The code is just plastic.", "narrationSegments": ["part2_paradigm_shift_016"]}, "mediaAliases": {}, "overlayConfig": {"fadeOutFrames": 60}, "renderMode": "component"},
  "part3_mold_parts:01_section_title_card": {"specBaseName": "01_section_title_card", "dataPoints": {"type": "title_card", "sectionNumber": 3, "sectionLabel": "PART 3", "titleLine1": "THE MOLD HAS", "titleLine2": "THREE PARTS", "backgroundColor": "#0A0F1A", "ghostElements": [{"shape": "mold_cross_section", "regions": ["walls", "nozzle", "cavity"], "role": "three_parts_preview"}], "narrationSegments": ["part3_mold_parts_001", "part3_mold_parts_002", "part3_mold_parts_003", "part3_mold_parts_004", "part3_mold_parts_005"], "durationSeconds": 44.0}, "mediaAliases": {}, "overlayConfig": {"fadeOutFrames": 60}, "renderMode": "component"},
  "part3_mold_parts:02_mold_cross_section": {"specBaseName": "02_mold_cross_section", "dataPoints": {"type": "mold_diagram", "regions": [{"id": "walls", "label": "TESTS", "color": "#4A90D9", "highlightFrame": 60}, {"id": "nozzle", "label": "PROMPT", "color": "#D9944A", "highlightFrame": 150}, {"id": "cavity", "label": "GROUNDING", "color": "#4AD9A0", "highlightFrame": 240}], "narrationSegments": ["part3_mold_parts_005"], "durationSeconds": 14.0}, "mediaAliases": {}, "overlayConfig": null, "renderMode": "component"},
  "part3_mold_parts:03_mold_walls_illuminate": {"specBaseName": "03_mold_walls_illuminate", "dataPoints": {"type": "mold_wall_labels", "walls": [{"label": "null → None", "side": "left", "frameIn": 30}, {"label": "empty string → ''", "side": "right", "frameIn": 75}, {"label": "handles unicode", "side": "left", "frameIn": 120}, {"label": "latency < 100ms", "side": "right", "frameIn": 165}], "narrationSegments": ["part3_mold_parts_006"], "durationSeconds": 10.0}, "mediaAliases": {}, "overlayConfig": null, "renderMode": "component"},
  "part3_mold_parts:04_liquid_injection": {"specBaseName": "04_liquid_injection", "dataPoints": {"type": "liquid_injection_with_annotations", "liquidGradient": ["#38BDF8", "#0D9488"], "focusWall": "null → None", "annotations": [{"text": "AI code: 1.7× more issues", "source": "CodeRabbit, 2025", "color": "#F87171", "frameIn": 330}, {"text": "AI + strong tests = amplified delivery", "source": "DORA, 2025", "color": "#4ADE80", "frameIn": 510}], "narrationSegments": ["part3_mold_parts_007", "part3_mold_parts_008"], "durationSeconds": 29.0}, "mediaAliases": {}, "overlayConfig": {"gradientOverlay": "bottom"}, "renderMode": "component"},
  "part3_mold_parts:05_bug_adds_wall": {"specBaseName": "05_bug_adds_wall", "dataPoints": {"type": "bug_to_wall", "bugLabel": "BUG", "newWall": {"label": "rejects negative IDs", "color": "#4A90D9"}, "terminalCommands": ["pdd bug user_parser", "pdd fix user_parser"], "narrationSegments": ["part3_mold_parts_009"], "durationSeconds": 16.0}, "mediaAliases": {}, "overlayConfig": {"fadeOutFrames": 30}, "renderMode": "component"},
  "part3_mold_parts:06_ratchet_timelapse": {"specBaseName": "06_ratchet_timelapse", "dataPoints": {"type": "ratchet_timelapse", "newWalls": [{"label": "handles empty array", "side": "left", "cycle": 1}, {"label": "timeout at 5s", "side": "right", "cycle": 2}, {"label": "rejects SQL injection", "side": "left", "cycle": 3}, {"label": "UTF-8 BOM stripped", "side": "right", "cycle": 4}], "wallCountRange": [5, 9], "narrationSegments": ["part3_mold_parts_010"], "durationSeconds": 9.0}, "mediaAliases": {}, "overlayConfig": null, "renderMode": "component"},
  "part3_mold_parts:07_split_traditional_vs_pdd": {"specBaseName": "07_split_traditional_vs_pdd", "dataPoints": {"type": "split_screen", "layout": "vertical_50_50", "divider": {"color": "#FFFFFF", "width": 2, "opacity": 0.3}, "panels": {"left": {"header": "TRADITIONAL", "headerColor": "#F87171", "steps": ["Bug found", "Patch code", "Similar bug elsewhere", "Patch again", "Different bug", "Patch again..."], "infinite": true}, "right": {"header": "PDD", "headerColor": "#4ADE80", "steps": ["Bug found", "Add test (pdd bug)", "Regenerate (pdd fix)", "Bug impossible forever ✓"], "infinite": false}}, "narrationSegments": ["part3_mold_parts_011"], "durationSeconds": 8.0}, "mediaAliases": {}, "overlayConfig": null, "renderMode": "component"},
  "part3_mold_parts:08_bug_fork_road": {"specBaseName": "08_bug_fork_road", "dataPoints": {"type": "fork_diagram", "root": {"label": "Bug found", "color": "#EF4444"}, "branches": [{"label": "Code bug", "action": "Add a wall", "color": "#4A90D9", "side": "left"}, {"label": "Prompt defect", "action": "Change the mold itself", "color": "#D9944A", "side": "right"}], "narrationSegments": ["part3_mold_parts_012"], "durationSeconds": 18.0}, "mediaAliases": {}, "overlayConfig": null, "renderMode": "component"},
  "part3_mold_parts:09_five_generations": {"specBaseName": "09_five_generations", "dataPoints": {"type": "multi_generation", "generationCount": 5, "results": [{"gen": 1, "status": "fail", "icon": "x", "color": "#EF4444"}, {"gen": 2, "status": "fail", "icon": "x", "color": "#EF4444"}, {"gen": 3, "status": "partial", "icon": "warning", "color": "#FBBF24"}, {"gen": 4, "status": "partial", "icon": "warning", "color": "#FBBF24"}, {"gen": 5, "status": "pass", "icon": "check", "color": "#4ADE80"}], "label": "Generate five. Pick the one that passes all tests.", "narrationSegments": ["part3_mold_parts_013"], "durationSeconds": 18.0}, "mediaAliases": {}, "overlayConfig": null, "renderMode": "component"},
  "part3_mold_parts:10_z3_formal_proof": {"specBaseName": "10_z3_formal_proof", "dataPoints": {"type": "sidebar_annotation", "topic": "Z3 formal verification", "keyTerms": ["Z3", "SMT solver", "formal equivalence checking", "mathematical proof"], "provenWalls": [1, 3], "provenColor": "#A78BFA", "logos": [{"text": "Z3", "color": "#A78BFA"}, {"text": "SF", "color": "#7C3AED"}], "narrationSegments": ["part3_mold_parts_014"], "durationSeconds": 26.0}, "mediaAliases": {}, "overlayConfig": {"fadeInFrames": 60}, "renderMode": "component"},
  "part3_mold_parts:11_module_boundary": {"specBaseName": "11_module_boundary", "dataPoints": {"type": "system_diagram", "centralModule": {"name": "user_parser", "color": "#4A90D9", "governed": true}, "surroundingModules": [{"name": "auth_service", "governed": false}, {"name": "db_layer", "governed": false}, {"name": "api_router", "governed": false}, {"name": "cache", "governed": false}, {"name": "logger", "governed": false}, {"name": "config", "governed": false}], "label": "PDD operates at the module level.", "narrationSegments": ["part3_mold_parts_015"], "durationSeconds": 22.0}, "mediaAliases": {}, "overlayConfig": {"fadeInFrames": 60}, "renderMode": "component"},
  "part3_mold_parts:12_prompt_nozzle": {"specBaseName": "12_prompt_nozzle", "dataPoints": {"type": "prompt_nozzle", "nozzleLabels": ["intent", "requirements", "constraints"], "promptText": "Parse user IDs from untrusted input. Return None on failure, never throw. Handle unicode.", "promptFile": "user_parser.prompt", "dualGeneration": true, "narrationSegments": ["part3_mold_parts_016"], "durationSeconds": 24.0}, "mediaAliases": {}, "overlayConfig": null, "renderMode": "component"},
  "part3_mold_parts:13_prompt_ratio": {"specBaseName": "13_prompt_ratio", "dataPoints": {"type": "compression_ratio", "promptLines": 15, "codeLines": 200, "ratio": "1:5 to 1:10", "contextComparison": {"left": {"tokens": 15000, "type": "raw_code", "modules": 1}, "right": {"tokens": 15000, "type": "prompts", "modules": 10}}, "narrationSegments": ["part3_mold_parts_017", "part3_mold_parts_018"], "durationSeconds": 18.0}, "mediaAliases": {}, "overlayConfig": null, "renderMode": "component"},
  "part3_mold_parts:15_grounding_styles": {"specBaseName": "15_grounding_styles", "dataPoints": {"type": "grounding_styles", "materialStreams": [{"label": "OOP", "color": "#4A90D9", "style": "angular"}, {"label": "Functional", "color": "#D9944A", "style": "smooth"}, {"label": "Your Team's Style", "color": "#4AD9A0", "style": "organic"}], "codeComparison": {"pathA": {"style": "OOP", "borderColor": "#4A90D9"}, "pathB": {"style": "Functional", "borderColor": "#D9944A"}}, "feedbackLoop": {"database": "Grounding Database", "stores": "(prompt, code) pair"}, "narrationSegments": ["part3_mold_parts_019"], "durationSeconds": 26.0}, "mediaAliases": {}, "overlayConfig": {"fadeInFrames": 60}, "renderMode": "component"},
  "part3_mold_parts:16_three_components_pullback": {"specBaseName": "16_three_components_pullback", "dataPoints": {"type": "pipeline_pullback", "stages": [{"component": "Prompt", "encodes": "Intent", "color": "#D9944A"}, {"component": "Grounding", "encodes": "Style", "color": "#4AD9A0"}, {"component": "Tests", "encodes": "Correctness", "color": "#4A90D9"}, {"component": "Code", "encodes": "Output", "color": "#38BDF8"}], "narrationSegments": ["part3_mold_parts_020"], "durationSeconds": 9.0}, "mediaAliases": {}, "overlayConfig": null, "renderMode": "component"},
  "part3_mold_parts:17_component_table": {"specBaseName": "17_component_table", "dataPoints": {"type": "component_table", "rows": [{"component": "Prompt", "encodes": "WHAT (intent)", "owner": "Developer", "color": "#D9944A"}, {"component": "Grounding", "encodes": "HOW (style)", "owner": "Automatic", "color": "#4AD9A0"}, {"component": "Tests", "encodes": "CORRECTNESS", "owner": "Accumulated", "color": "#4A90D9"}], "hierarchyRule": "When these conflict, tests win. Always.", "hierarchyOrder": ["Tests", "Prompt", "Grounding"], "narrationSegments": ["part3_mold_parts_021"], "durationSeconds": 10.0}, "mediaAliases": {}, "overlayConfig": null, "renderMode": "component"},
  "part3_mold_parts:18_code_output_finale": {"specBaseName": "18_code_output_finale", "dataPoints": {"type": "code_output_finale", "message": "The code is output. The mold is what matters.", "codeGlowFade": {"from": 0.2, "to": 0.0, "frames": [20, 40]}, "moldGlowIncrease": {"from": 0.4, "to": 0.6, "frames": [40, 60]}, "narrationSegments": ["part3_mold_parts_022"], "durationSeconds": 3.0}, "mediaAliases": {}, "overlayConfig": null, "renderMode": "component"},
  "part4_precision_tradeoff:01_section_title_card": {"specBaseName": "01_section_title_card", "dataPoints": {"type": "title_card", "sectionNumber": 4, "sectionLabel": "PART 4", "titleLine1": "THE PRECISION", "titleLine2": "TRADEOFF", "backgroundColor": "#0A0F1A", "ghostElements": [{"shape": "inverse_curve", "color": "#D9944A", "role": "precision_tradeoff_preview"}], "narrationSegments": ["part4_precision_tradeoff_001"]}, "mediaAliases": {}, "overlayConfig": {"fadeOutFrames": 60}, "renderMode": "component"},
  "part4_precision_tradeoff:02_split_printer_vs_mold": {"specBaseName": "02_split_printer_vs_mold", "dataPoints": {"type": "split_screen", "layout": "vertical_50_50", "divider": {"color": "#FFFFFF", "width": 2, "opacity": 0.4}, "panels": {"left": {"label": "3D Printer", "animation": "printer_nozzle_grid", "accentColor": "#4A90D9", "description": "Nozzle deposits material point-by-point on coordinate grid"}, "right": {"label": "Injection Mold", "animation": "liquid_flow_walls", "accentColor": "#D9944A", "description": "Liquid flows freely until walls constrain it into shape"}}, "narrationSegments": ["part4_precision_tradeoff_001"], "durationSeconds": 16.0}, "mediaAliases": {}, "overlayConfig": {"fadeOutFrames": 60}, "renderMode": "component"},
  "part4_precision_tradeoff:03_precision_tradeoff_curve": {"specBaseName": "03_precision_tradeoff_curve", "dataPoints": {"type": "line_chart", "chartId": "precision_tradeoff_curve", "xAxis": {"label": "Number of Tests", "range": [0, 50], "tickInterval": 10}, "yAxis": {"label": "Required Prompt Precision", "range": [0, 1], "tickLabels": ["Low", "High"]}, "series": [{"id": "precision_curve", "label": "Required Prompt Precision", "color": "#E2E8F0", "data": [{"x": 0, "y": 0.95}, {"x": 5, "y": 0.7}, {"x": 10, "y": 0.45}, {"x": 15, "y": 0.32}, {"x": 20, "y": 0.25}, {"x": 30, "y": 0.18}, {"x": 40, "y": 0.14}, {"x": 50, "y": 0.12}]}], "annotations": [{"type": "callout", "x": 3, "text": "50-line prompt\nEvery edge case specified", "color": "#D9944A"}, {"type": "callout", "x": 45, "text": "10-line prompt\nTests handle constraints", "color": "#4A90D9"}], "zones": [{"range": [0, 20], "color": "#D9944A", "label": "High prompt effort"}, {"range": [20, 50], "color": "#4A90D9", "label": "Test-driven precision"}], "narrationSegments": ["part4_precision_tradeoff_002"]}, "mediaAliases": {}, "overlayConfig": {"fadeInFrames": 45}, "renderMode": "component"},
  "part4_precision_tradeoff:04_detailed_prompt_file": {"specBaseName": "04_detailed_prompt_file", "dataPoints": {"type": "code_editor", "chartId": "detailed_prompt_file", "file": {"name": "parser_v1.prompt", "lineCount": 50, "sections": [{"range": [1, 3], "label": "Module description", "type": "header"}, {"range": [4, 12], "label": "Input format specification", "type": "spec"}, {"range": [13, 22], "label": "Edge case handling", "type": "edge_case", "highlight": true}, {"range": [23, 35], "label": "Error handling rules", "type": "error"}, {"range": [36, 45], "label": "Output format constraints", "type": "format"}, {"range": [46, 50], "label": "Performance requirements", "type": "perf"}]}, "accentColor": "#D9944A", "label": "Without tests: prompt must specify everything", "narrationSegments": ["part4_precision_tradeoff_003"]}, "mediaAliases": {}, "overlayConfig": null, "renderMode": "component"},
  "part4_precision_tradeoff:05_minimal_prompt_with_tests": {"specBaseName": "05_minimal_prompt_with_tests", "dataPoints": {"type": "code_editor_with_terminal", "chartId": "minimal_prompt_with_tests", "promptFile": {"name": "parser_v2.prompt", "lineCount": 10, "accentColor": "#4A90D9"}, "terminal": {"command": "pdd test parser", "testCount": 47, "allPassing": true, "accentColor": "#5AAA6E"}, "testWalls": {"count": 10, "color": "#4A90D9", "metaphor": "Tests as constraining walls around prompt"}, "narrationSegments": ["part4_precision_tradeoff_003"]}, "mediaAliases": {}, "overlayConfig": null, "renderMode": "component"},
  "part4_precision_tradeoff:06_dual_generation_comparison": {"specBaseName": "06_dual_generation_comparison", "dataPoints": {"type": "side_by_side_comparison", "chartId": "dual_generation_comparison", "panels": {"left": {"label": "High Prompt Effort", "promptLines": 50, "testCount": 0, "accentColor": "#D9944A", "result": "correct_code"}, "right": {"label": "Low Prompt + Tests", "promptLines": 10, "testCount": 47, "accentColor": "#4A90D9", "result": "correct_code"}}, "comparison": {"metric": "prompt_lines", "ratio": "5:1", "insight": "Same output, 5× less prompt effort"}, "narrationSegments": ["part4_precision_tradeoff_003"]}, "mediaAliases": {}, "overlayConfig": {"fadeOutFrames": 30}, "renderMode": "component"},
  "part4_precision_tradeoff:07_key_insight_walls": {"specBaseName": "07_key_insight_walls", "dataPoints": {"type": "key_insight", "chartId": "key_insight_walls", "primaryText": "More tests, less prompt.", "secondaryText": "The walls do the precision work.", "accentColors": {"tests": "#4A90D9", "walls": "#D9944A"}, "narrationSegments": ["part4_precision_tradeoff_003"]}, "mediaAliases": {}, "overlayConfig": {"fadeOutFrames": 20}, "renderMode": "component"},
  "part4_precision_tradeoff:08_embedded_code_document": {"specBaseName": "08_embedded_code_document", "dataPoints": {"type": "document_visualization", "chartId": "embedded_code_document", "document": {"title": "Parser Module", "sections": [{"type": "prose", "content": "Parse incoming JSON payloads according to schema...", "lines": 8}, {"type": "prose", "content": "Handle malformed input by returning structured errors...", "lines": 6}, {"type": "code_embed", "content": "comparison_function", "lines": 8, "language": "python"}, {"type": "prose", "content": "For all other formatting, follow standard conventions...", "lines": 4}]}, "annotations": [{"target": "prose", "label": "Natural language", "color": "#D9944A"}, {"target": "code_embed", "label": "Embedded code", "color": "#4A90D9"}], "label": "The boundary between prompt and code is fluid.", "narrationSegments": ["part4_precision_tradeoff_004"]}, "mediaAliases": {}, "overlayConfig": {"fadeOutFrames": 60}, "renderMode": "component"},
  "part4_precision_tradeoff:09_prompt_code_spectrum": {"specBaseName": "09_prompt_code_spectrum", "dataPoints": {"type": "spectrum_slider", "chartId": "prompt_code_spectrum", "spectrum": {"leftLabel": "Pure natural language", "leftColor": "#4A90D9", "rightLabel": "Pure code", "rightColor": "#64748B", "width": 1600}, "slider": {"position": 0.2, "label": "Typical PDD sweet spot"}, "notches": [{"position": 0.46, "label": "algorithm"}, {"position": 0.59, "label": "hash fn"}, {"position": 0.71, "label": "bit ops"}, {"position": 0.84, "label": "perf loop"}], "insight": {"primary": "Stay in prompt space as long as possible.", "secondary": "Dip into code when you must."}, "narrationSegments": ["part4_precision_tradeoff_005"]}, "mediaAliases": {}, "overlayConfig": {"fadeInFrames": 60, "fadeOutFrames": 30}, "renderMode": "component"},
  "part5_compound_returns:01_section_title_card": {"specBaseName": "01_section_title_card", "dataPoints": {"type": "title_card", "sectionNumber": 5, "sectionLabel": "PART 5", "titleLine1": "COMPOUND", "titleLine2": "RETURNS", "backgroundColor": "#0A0F1A", "ghostElements": [{"shape": "diverging_curves", "colors": ["#D9944A", "#5AAA6E"], "role": "compound_cost_preview"}], "narrationSegments": ["part5_compound_returns_001"]}, "mediaAliases": {}, "overlayConfig": {"fadeOutFrames": 62}, "renderMode": "component"},
  "part5_compound_returns:02_maintenance_pie_chart": {"specBaseName": "02_maintenance_pie_chart", "dataPoints": {"type": "pie_chart", "chartId": "maintenance_cost_split", "segments": [{"id": "maintenance", "label": "Maintenance", "percentage": "80-90%", "color": "#D9944A", "degrees": 306}, {"id": "initial_development", "label": "Initial Development", "percentage": "10-20%", "color": "#4A90D9", "degrees": 54}], "statistics": [{"source": "McKinsey", "finding": "40% more on maintenance with high technical debt"}, {"source": "Stripe", "finding": "1/3 of developer work week lost to debt"}, {"source": "CISQ", "finding": "$1.52 trillion annually in US"}], "narrationSegments": ["part5_compound_returns_001"]}, "mediaAliases": {}, "overlayConfig": {"fadeInFrames": 120}, "renderMode": "component"},
  "part5_compound_returns:03_compound_debt_curve": {"specBaseName": "03_compound_debt_curve", "dataPoints": {"type": "dual_curve_chart", "chartId": "compound_debt_vs_regeneration", "xAxis": {"label": "Time (maintenance cycles)", "range": [0, 20]}, "yAxis": {"label": "Cumulative Cost"}, "series": [{"id": "debt_exponential", "label": "Debt × (1 + Rate)^Time", "color": "#D9944A", "type": "exponential", "data": [{"x": 0, "y": 0.05}, {"x": 2, "y": 0.07}, {"x": 4, "y": 0.1}, {"x": 6, "y": 0.14}, {"x": 8, "y": 0.2}, {"x": 10, "y": 0.3}, {"x": 12, "y": 0.42}, {"x": 14, "y": 0.58}, {"x": 16, "y": 0.72}, {"x": 18, "y": 0.85}, {"x": 20, "y": 0.95}]}, {"id": "regeneration_flat", "label": "Regeneration cost (debt resets each cycle)", "color": "#5AAA6E", "type": "flat", "data": [{"x": 0, "y": 0.08}, {"x": 20, "y": 0.08}]}], "annotations": [{"type": "callout", "text": "$1.52 trillion/year", "source": "CISQ", "position": "steep_section"}], "narrationSegments": ["part5_compound_returns_002"]}, "mediaAliases": {}, "overlayConfig": null, "renderMode": "component"},
  "part5_compound_returns:04_diverging_cost_curves": {"specBaseName": "04_diverging_cost_curves", "dataPoints": {"type": "diverging_curves", "chartId": "patching_vs_pdd_compounding", "xAxis": {"label": "Time (years)", "range": [0, 10]}, "yAxis": {"label": "Cumulative Cost"}, "series": [{"id": "patching_exponential", "label": "Patching", "color": "#D9944A", "type": "exponential", "data": [{"x": 0, "y": 0.1}, {"x": 1, "y": 0.13}, {"x": 2, "y": 0.17}, {"x": 3, "y": 0.23}, {"x": 4, "y": 0.31}, {"x": 5, "y": 0.42}, {"x": 6, "y": 0.55}, {"x": 7, "y": 0.68}, {"x": 8, "y": 0.8}, {"x": 9, "y": 0.88}, {"x": 10, "y": 0.95}]}, {"id": "pdd_flat", "label": "PDD", "color": "#5AAA6E", "type": "flat_sawtooth", "baseline": 0.1, "sawtoothAmplitude": 0.03, "data": [{"x": 0, "y": 0.1}, {"x": 1, "y": 0.1}, {"x": 2, "y": 0.1}, {"x": 3, "y": 0.1}, {"x": 4, "y": 0.1}, {"x": 5, "y": 0.1}, {"x": 6, "y": 0.1}, {"x": 7, "y": 0.1}, {"x": 8, "y": 0.1}, {"x": 9, "y": 0.1}, {"x": 10, "y": 0.1}]}], "gap": {"label": "The Gap", "gradient": {"top": "#D9944A", "bottom": "#5AAA6E"}}, "thesisStatements": [{"text": "Patching accrues compound costs.", "color": "#D9944A"}, {"text": "Tests accrue compound returns.", "color": "#5AAA6E"}], "narrationSegments": ["part5_compound_returns_003"]}, "mediaAliases": {}, "overlayConfig": {"gradientOverlay": "bottom"}, "renderMode": "component"},
  "part5_compound_returns:05_investment_comparison_table": {"specBaseName": "05_investment_comparison_table", "dataPoints": {"type": "comparison_table", "chartId": "investment_patching_vs_pdd", "columns": ["Investment", "Patching", "PDD"], "columnColors": ["#E2E8F0", "#D9944A", "#5AAA6E"], "rows": [{"investment": "Fix a bug", "patching": "One place, once", "pdd": "Impossible forever"}, {"investment": "Improve code", "patching": "One version", "pdd": "All future versions"}, {"investment": "Document intent", "patching": "One snapshot", "pdd": "Living specification"}], "narrationSegments": ["part5_compound_returns_004"]}, "mediaAliases": {}, "overlayConfig": {"gradientOverlay": "bottom"}, "renderMode": "component"},
  "part5_compound_returns:08_economics_crossing_callback": {"specBaseName": "08_economics_crossing_callback", "dataPoints": {"type": "chart_callback", "chartRef": "code_cost_generate_vs_patch", "sourceSpec": "part1_economics/13_crossing_lines_moment", "crossingPoint": {"id": "generate_crosses_immediate", "year": 2025.6, "pulse": true}, "reframeText": "The economics changed.", "narrationSegments": ["part5_compound_returns_006"]}, "mediaAliases": {}, "overlayConfig": null, "renderMode": "component"},
  "part5_compound_returns:09_contrarian_quote_card": {"specBaseName": "09_contrarian_quote_card", "dataPoints": {"type": "quote_card", "quote": "This is either the way of the future or it's going to crash and burn spectacularly.", "attribution": "Research engineer, after seeing PDD for the first time.", "backgroundColor": "#0A0F1A", "accentWord": "spectacularly", "accentGlow": {"color": "#D9944A", "opacity": 0.03}, "narrationSegments": ["part5_compound_returns_007", "part5_compound_returns_008"]}, "mediaAliases": {}, "overlayConfig": null, "renderMode": "component"},
  "where_to_start:01_section_title_card": {"specBaseName": "01_section_title_card", "dataPoints": {"type": "title_card", "sectionNumber": 6, "sectionLabel": "WHERE TO START", "titleLine1": "WHERE TO", "titleLine2": "START", "backgroundColor": "#0A0F1A", "ghostElements": [{"shape": "module_grid", "rows": 4, "cols": 6, "highlightCell": [2, 3], "role": "one_module_preview"}], "narrationSegments": ["where_to_start_001"]}, "mediaAliases": {}, "overlayConfig": {"fadeOutFrames": 60}, "renderMode": "component"},
  "where_to_start:02_legacy_codebase_reveal": {"specBaseName": "02_legacy_codebase_reveal", "dataPoints": {"type": "code_editor_animation", "editorId": "legacy_codebase_reveal", "files": ["auth_handler.py", "payment_processor.py", "legacy_utils.py", "config_v2_final_FINAL.py"], "warningComments": [{"line": 15, "text": "# don't touch"}, {"line": 42, "text": "# here be dragons"}, {"line": 78, "text": "# TODO: fix this (2019)"}, {"line": 105, "text": "# nobody knows why this works"}], "narrationSegments": ["where_to_start_001"]}, "mediaAliases": {}, "overlayConfig": null, "renderMode": "component"},
  "where_to_start:03_module_highlight_terminal": {"specBaseName": "03_module_highlight_terminal", "dataPoints": {"type": "code_transformation", "transformId": "module_to_prompt", "sourceFile": "auth_handler.py", "generatedFile": "auth_handler.prompt.md", "command": "pdd update auth_handler.py", "states": [{"id": "code_highlighted", "label": "Module selected"}, {"id": "command_typed", "label": "PDD update executed"}, {"id": "prompt_extracted", "label": "Prompt materialized"}, {"id": "code_grayed", "label": "Code becomes artifact"}, {"id": "prompt_glowing", "label": "Prompt is source of truth"}], "narrationSegments": ["where_to_start_001"]}, "mediaAliases": {}, "overlayConfig": {"fadeInFrames": 30}, "renderMode": "component"},
  "where_to_start:04_source_of_truth_label": {"specBaseName": "04_source_of_truth_label", "dataPoints": {"type": "validation_sequence", "sequenceId": "regenerate_and_verify", "steps": [{"command": "pdd generate auth_handler.py", "description": "Regenerate code from prompt"}, {"command": "pdd test", "description": "Run test suite"}, {"result": "✓ All tests pass", "description": "Validation complete"}], "badge": {"text": "SOURCE OF TRUTH", "target": "auth_handler.prompt.md"}, "narrationSegments": ["where_to_start_001"]}, "mediaAliases": {}, "overlayConfig": null, "renderMode": "component"},
  "where_to_start:05_module_glow_spread": {"specBaseName": "05_module_glow_spread", "dataPoints": {"type": "module_migration_animation", "animationId": "gradual_glow_spread", "totalModules": 12, "migratedModules": [{"id": "auth_handler", "order": 1, "frameStart": 0}, {"id": "user_service", "order": 2, "frameStart": 30}, {"id": "payment_proc", "order": 3, "frameStart": 75}, {"id": "email_templates", "order": 4, "frameStart": 120}, {"id": "api_routes", "order": 5, "frameStart": 140}, {"id": "config_mgr", "order": 6, "frameStart": 165}], "unmigrated": ["db_models", "test_utils", "middleware", "validators", "cache_layer", "logging_setup"], "narrationSegments": ["where_to_start_002"]}, "mediaAliases": {}, "overlayConfig": null, "renderMode": "component"},
  "where_to_start:06_no_big_bang_callout": {"specBaseName": "06_no_big_bang_callout", "dataPoints": {"type": "key_insight_card", "insightId": "no_big_bang", "statements": [{"text": "No big bang.", "color": "#E2E8F0", "weight": 700}, {"text": "No rewrite.", "color": "#E2E8F0", "weight": 700}, {"text": "Just gradual migration.", "color": "#5AAA6E", "weight": 600}], "narrationSegments": ["where_to_start_002"]}, "mediaAliases": {}, "overlayConfig": null, "renderMode": "component"},
  "where_to_start:07_gradual_migration_insight": {"specBaseName": "07_gradual_migration_insight", "dataPoints": {"type": "value_flow_animation", "animationId": "code_to_specification", "containers": [{"id": "code", "label": "CODE", "color": "#64748B", "fillColor": "#94A3B8", "startLevel": 0.7, "endLevel": 0.4}, {"id": "specification", "label": "SPECIFICATION", "color": "#5AAA6E", "fillColor": "#5AAA6E", "startLevel": 0.3, "endLevel": 0.6}], "thesisText": "from code to specification", "narrationSegments": ["where_to_start_003"]}, "mediaAliases": {}, "overlayConfig": {"fadeInFrames": 30}, "renderMode": "component"},
  "closing:03_pdd_triangle": {"specBaseName": "03_pdd_triangle", "dataPoints": {"type": "remotion_animation", "componentId": "pdd_triangle", "durationFrames": 180, "fps": 30, "narrationSegments": ["closing_002", "closing_003"], "vertices": [{"label": "PROMPT", "position": [960, 180], "color": "#D9944A"}, {"label": "TESTS", "position": [683, 680], "color": "#4AD9A0"}, {"label": "GROUNDING", "position": [1237, 680], "color": "#4A90D9"}], "codeLines": ["def calculate_total(items):", "    return sum(i.price for i in items)", "", "def apply_discount(total, pct):", "    return total * (1 - pct)"]}, "mediaAliases": {}, "overlayConfig": null, "renderMode": "component"},
  "closing:04_dissolve_regenerate_loop": {"specBaseName": "04_dissolve_regenerate_loop", "dataPoints": {"type": "remotion_animation", "componentId": "dissolve_regenerate_loop", "durationFrames": 150, "fps": 30, "narrationSegments": ["closing_003", "closing_004"], "codeVariants": [{"version": 1, "lines": ["def calculate_total(items):", "    return sum(i.price for i in items)", "", "def apply_discount(total, pct):", "    return total * (1 - pct)"]}, {"version": 2, "lines": ["def get_total(cart_items):", "    total = 0", "    for item in cart_items:", "        total += item.price", "    return total"]}, {"version": 3, "lines": ["def compute_sum(products):", "    prices = [p.price for p in products]", "    return functools.reduce(", "        operator.add, prices, 0", "    )"]}], "terminalCommands": [{"command": "pdd test", "result": "✓ All tests passed"}]}, "mediaAliases": {}, "overlayConfig": null, "renderMode": "component"},
  "closing:06_the_beat": {"specBaseName": "06_the_beat", "dataPoints": {"type": "remotion_animation", "componentId": "the_beat", "durationFrames": 60, "fps": 30, "narrationSegments": [], "note": "Silent pause between final narration and title card"}, "mediaAliases": {}, "overlayConfig": null, "renderMode": "component"},
  "closing:07_final_title_card": {"specBaseName": "07_final_title_card", "dataPoints": {"type": "title_card", "componentId": "final_title_card", "durationFrames": 180, "fps": 30, "narrationSegments": [], "title": "Prompt-Driven Development", "commands": ["uv tool install pdd-cli", "pdd update your_module.py"], "url": "promptdrivendevelopment.com"}, "mediaAliases": {}, "overlayConfig": null, "renderMode": "component"},
};

const ColdOpen01SplitScreenDarningPreview: React.FC = () => (
  <VisualContractProvider contract={PREVIEW_VISUAL_CONTRACTS["cold_open:01_split_screen_darning"] ?? null}>
    <VisualMediaProvider media={PREVIEW_VISUAL_MEDIA["cold_open:01_split_screen_darning"] ?? null}>
      <GeneratedContractVisual />
    </VisualMediaProvider>
  </VisualContractProvider>
);
const ColdOpen07CodeCursorBlinkPreview: React.FC = () => (
  <VisualContractProvider contract={PREVIEW_VISUAL_CONTRACTS["cold_open:07_code_cursor_blink"] ?? null}>
    <VisualMediaProvider media={PREVIEW_VISUAL_MEDIA["cold_open:07_code_cursor_blink"] ?? null}>
      <ColdOpen07CodeCursorBlink />
    </VisualMediaProvider>
  </VisualContractProvider>
);
const ColdOpen08CodeRegenerationPreview: React.FC = () => (
  <VisualContractProvider contract={PREVIEW_VISUAL_CONTRACTS["cold_open:08_code_regeneration"] ?? null}>
    <VisualMediaProvider media={PREVIEW_VISUAL_MEDIA["cold_open:08_code_regeneration"] ?? null}>
      <GeneratedContractVisual />
    </VisualMediaProvider>
  </VisualContractProvider>
);
const ColdOpen09TitleCardPddPreview: React.FC = () => (
  <VisualContractProvider contract={PREVIEW_VISUAL_CONTRACTS["cold_open:09_title_card_pdd"] ?? null}>
    <VisualMediaProvider media={PREVIEW_VISUAL_MEDIA["cold_open:09_title_card_pdd"] ?? null}>
      <GeneratedContractVisual />
    </VisualMediaProvider>
  </VisualContractProvider>
);
const Part1Economics01SectionTitleCardPreview: React.FC = () => (
  <VisualContractProvider contract={PREVIEW_VISUAL_CONTRACTS["part1_economics:01_section_title_card"] ?? null}>
    <VisualMediaProvider media={PREVIEW_VISUAL_MEDIA["part1_economics:01_section_title_card"] ?? null}>
      <GeneratedContractVisual />
    </VisualMediaProvider>
  </VisualContractProvider>
);
const Part1Economics02SockPriceChartPreview: React.FC = () => (
  <VisualContractProvider contract={PREVIEW_VISUAL_CONTRACTS["part1_economics:02_sock_price_chart"] ?? null}>
    <VisualMediaProvider media={PREVIEW_VISUAL_MEDIA["part1_economics:02_sock_price_chart"] ?? null}>
      <Part1Economics02SockPriceChart />
    </VisualMediaProvider>
  </VisualContractProvider>
);
const Part1Economics03CodeCostChartPreview: React.FC = () => (
  <VisualContractProvider contract={PREVIEW_VISUAL_CONTRACTS["part1_economics:03_code_cost_chart"] ?? null}>
    <VisualMediaProvider media={PREVIEW_VISUAL_MEDIA["part1_economics:03_code_cost_chart"] ?? null}>
      <Part1Economics03CodeCostChart />
    </VisualMediaProvider>
  </VisualContractProvider>
);
const Part1Economics04ResearchAnnotationsPreview: React.FC = () => (
  <VisualContractProvider contract={PREVIEW_VISUAL_CONTRACTS["part1_economics:04_research_annotations"] ?? null}>
    <VisualMediaProvider media={PREVIEW_VISUAL_MEDIA["part1_economics:04_research_annotations"] ?? null}>
      <GeneratedContractVisual />
    </VisualMediaProvider>
  </VisualContractProvider>
);
const Part1Economics05CodeChurnAnnotationsPreview: React.FC = () => (
  <VisualContractProvider contract={PREVIEW_VISUAL_CONTRACTS["part1_economics:05_code_churn_annotations"] ?? null}>
    <VisualMediaProvider media={PREVIEW_VISUAL_MEDIA["part1_economics:05_code_churn_annotations"] ?? null}>
      <GeneratedContractVisual />
    </VisualMediaProvider>
  </VisualContractProvider>
);
const Part1Economics06DebtLayersZoomPreview: React.FC = () => (
  <VisualContractProvider contract={PREVIEW_VISUAL_CONTRACTS["part1_economics:06_debt_layers_zoom"] ?? null}>
    <VisualMediaProvider media={PREVIEW_VISUAL_MEDIA["part1_economics:06_debt_layers_zoom"] ?? null}>
      <Part1Economics06DebtLayersZoom />
    </VisualMediaProvider>
  </VisualContractProvider>
);
const Part1Economics07ContextWindowShrinkPreview: React.FC = () => (
  <VisualContractProvider contract={PREVIEW_VISUAL_CONTRACTS["part1_economics:07_context_window_shrink"] ?? null}>
    <VisualMediaProvider media={PREVIEW_VISUAL_MEDIA["part1_economics:07_context_window_shrink"] ?? null}>
      <Part1Economics07ContextWindowShrink />
    </VisualMediaProvider>
  </VisualContractProvider>
);
const Part1Economics08PerformanceVsContextPreview: React.FC = () => (
  <VisualContractProvider contract={PREVIEW_VISUAL_CONTRACTS["part1_economics:08_performance_vs_context"] ?? null}>
    <VisualMediaProvider media={PREVIEW_VISUAL_MEDIA["part1_economics:08_performance_vs_context"] ?? null}>
      <Part1Economics08PerformanceVsContext />
    </VisualMediaProvider>
  </VisualContractProvider>
);
const Part1Economics09TwoByTwoGridPreview: React.FC = () => (
  <VisualContractProvider contract={PREVIEW_VISUAL_CONTRACTS["part1_economics:09_two_by_two_grid"] ?? null}>
    <VisualMediaProvider media={PREVIEW_VISUAL_MEDIA["part1_economics:09_two_by_two_grid"] ?? null}>
      <Part1Economics09TwoByTwoGrid />
    </VisualMediaProvider>
  </VisualContractProvider>
);
const Part1Economics10ForkCodebaseSizePreview: React.FC = () => (
  <VisualContractProvider contract={PREVIEW_VISUAL_CONTRACTS["part1_economics:10_fork_codebase_size"] ?? null}>
    <VisualMediaProvider media={PREVIEW_VISUAL_MEDIA["part1_economics:10_fork_codebase_size"] ?? null}>
      <Part1Economics10ForkCodebaseSize />
    </VisualMediaProvider>
  </VisualContractProvider>
);
const Part1Economics11PatchingVsRegenerationPreview: React.FC = () => (
  <VisualContractProvider contract={PREVIEW_VISUAL_CONTRACTS["part1_economics:11_patching_vs_regeneration"] ?? null}>
    <VisualMediaProvider media={PREVIEW_VISUAL_MEDIA["part1_economics:11_patching_vs_regeneration"] ?? null}>
      <Part1Economics11PatchingVsRegeneration />
    </VisualMediaProvider>
  </VisualContractProvider>
);
const Part1Economics12ContextCompressionPreview: React.FC = () => (
  <VisualContractProvider contract={PREVIEW_VISUAL_CONTRACTS["part1_economics:12_context_compression"] ?? null}>
    <VisualMediaProvider media={PREVIEW_VISUAL_MEDIA["part1_economics:12_context_compression"] ?? null}>
      <Part1Economics12ContextCompression />
    </VisualMediaProvider>
  </VisualContractProvider>
);
const Part1Economics13CrossingLinesMomentPreview: React.FC = () => (
  <VisualContractProvider contract={PREVIEW_VISUAL_CONTRACTS["part1_economics:13_crossing_lines_moment"] ?? null}>
    <VisualMediaProvider media={PREVIEW_VISUAL_MEDIA["part1_economics:13_crossing_lines_moment"] ?? null}>
      <Part1Economics13CrossingLinesMoment />
    </VisualMediaProvider>
  </VisualContractProvider>
);
const Part1Economics14SplitDeveloperGrandmaPreview: React.FC = () => (
  <VisualContractProvider contract={PREVIEW_VISUAL_CONTRACTS["part1_economics:14_split_developer_grandma"] ?? null}>
    <VisualMediaProvider media={PREVIEW_VISUAL_MEDIA["part1_economics:14_split_developer_grandma"] ?? null}>
      <GeneratedContractVisual />
    </VisualMediaProvider>
  </VisualContractProvider>
);
const Part1Economics18KeyInsightStillnessPreview: React.FC = () => (
  <VisualContractProvider contract={PREVIEW_VISUAL_CONTRACTS["part1_economics:18_key_insight_stillness"] ?? null}>
    <VisualMediaProvider media={PREVIEW_VISUAL_MEDIA["part1_economics:18_key_insight_stillness"] ?? null}>
      <Part1Economics18KeyInsightStillness />
    </VisualMediaProvider>
  </VisualContractProvider>
);
const Part1Economics19DoubleMeterInsightPreview: React.FC = () => (
  <VisualContractProvider contract={PREVIEW_VISUAL_CONTRACTS["part1_economics:19_double_meter_insight"] ?? null}>
    <VisualMediaProvider media={PREVIEW_VISUAL_MEDIA["part1_economics:19_double_meter_insight"] ?? null}>
      <Part1Economics19DoubleMeterInsight />
    </VisualMediaProvider>
  </VisualContractProvider>
);
const Part1Economics20TryItYourselfPreview: React.FC = () => (
  <VisualContractProvider contract={PREVIEW_VISUAL_CONTRACTS["part1_economics:20_try_it_yourself"] ?? null}>
    <VisualMediaProvider media={PREVIEW_VISUAL_MEDIA["part1_economics:20_try_it_yourself"] ?? null}>
      <Part1Economics20TryItYourself />
    </VisualMediaProvider>
  </VisualContractProvider>
);
const Part2ParadigmShift01SectionTitleCardPreview: React.FC = () => (
  <VisualContractProvider contract={PREVIEW_VISUAL_CONTRACTS["part2_paradigm_shift:01_section_title_card"] ?? null}>
    <VisualMediaProvider media={PREVIEW_VISUAL_MEDIA["part2_paradigm_shift:01_section_title_card"] ?? null}>
      <GeneratedContractVisual />
    </VisualMediaProvider>
  </VisualContractProvider>
);
const Part2ParadigmShift04MoldProductionCounterPreview: React.FC = () => (
  <VisualContractProvider contract={PREVIEW_VISUAL_CONTRACTS["part2_paradigm_shift:04_mold_production_counter"] ?? null}>
    <VisualMediaProvider media={PREVIEW_VISUAL_MEDIA["part2_paradigm_shift:04_mold_production_counter"] ?? null}>
      <Part2ParadigmShift04MoldProductionCounter />
    </VisualMediaProvider>
  </VisualContractProvider>
);
const Part2ParadigmShift07SplitCraftsmanVsMoldPreview: React.FC = () => (
  <VisualContractProvider contract={PREVIEW_VISUAL_CONTRACTS["part2_paradigm_shift:07_split_craftsman_vs_mold"] ?? null}>
    <VisualMediaProvider media={PREVIEW_VISUAL_MEDIA["part2_paradigm_shift:07_split_craftsman_vs_mold"] ?? null}>
      <GeneratedContractVisual />
    </VisualMediaProvider>
  </VisualContractProvider>
);
const Part2ParadigmShift11SchematicDensityZoomPreview: React.FC = () => (
  <VisualContractProvider contract={PREVIEW_VISUAL_CONTRACTS["part2_paradigm_shift:11_schematic_density_zoom"] ?? null}>
    <VisualMediaProvider media={PREVIEW_VISUAL_MEDIA["part2_paradigm_shift:11_schematic_density_zoom"] ?? null}>
      <Part2ParadigmShift11SchematicDensityZoom />
    </VisualMediaProvider>
  </VisualContractProvider>
);
const Part2ParadigmShift12VerilogSynthesisPreview: React.FC = () => (
  <VisualContractProvider contract={PREVIEW_VISUAL_CONTRACTS["part2_paradigm_shift:12_verilog_synthesis"] ?? null}>
    <VisualMediaProvider media={PREVIEW_VISUAL_MEDIA["part2_paradigm_shift:12_verilog_synthesis"] ?? null}>
      <Part2ParadigmShift12VerilogSynthesis />
    </VisualMediaProvider>
  </VisualContractProvider>
);
const Part2ParadigmShift13TripleSynthesisEquivalencePreview: React.FC = () => (
  <VisualContractProvider contract={PREVIEW_VISUAL_CONTRACTS["part2_paradigm_shift:13_triple_synthesis_equivalence"] ?? null}>
    <VisualMediaProvider media={PREVIEW_VISUAL_MEDIA["part2_paradigm_shift:13_triple_synthesis_equivalence"] ?? null}>
      <Part2ParadigmShift13TripleSynthesisEquivalence />
    </VisualMediaProvider>
  </VisualContractProvider>
);
const Part2ParadigmShift14SynopsysPddEquivalencePreview: React.FC = () => (
  <VisualContractProvider contract={PREVIEW_VISUAL_CONTRACTS["part2_paradigm_shift:14_synopsys_pdd_equivalence"] ?? null}>
    <VisualMediaProvider media={PREVIEW_VISUAL_MEDIA["part2_paradigm_shift:14_synopsys_pdd_equivalence"] ?? null}>
      <Part2ParadigmShift14SynopsysPddEquivalence />
    </VisualMediaProvider>
  </VisualContractProvider>
);
const Part2ParadigmShift15AbstractionStaircasePreview: React.FC = () => (
  <VisualContractProvider contract={PREVIEW_VISUAL_CONTRACTS["part2_paradigm_shift:15_abstraction_staircase"] ?? null}>
    <VisualMediaProvider media={PREVIEW_VISUAL_MEDIA["part2_paradigm_shift:15_abstraction_staircase"] ?? null}>
      <Part2ParadigmShift15AbstractionStaircase />
    </VisualMediaProvider>
  </VisualContractProvider>
);
const Part2ParadigmShift16BillionGateUnreviewablePreview: React.FC = () => (
  <VisualContractProvider contract={PREVIEW_VISUAL_CONTRACTS["part2_paradigm_shift:16_billion_gate_unreviewable"] ?? null}>
    <VisualMediaProvider media={PREVIEW_VISUAL_MEDIA["part2_paradigm_shift:16_billion_gate_unreviewable"] ?? null}>
      <Part2ParadigmShift16BillionGateUnreviewable />
    </VisualMediaProvider>
  </VisualContractProvider>
);
const Part2ParadigmShift17ReviewSpecVerifyOutputPreview: React.FC = () => (
  <VisualContractProvider contract={PREVIEW_VISUAL_CONTRACTS["part2_paradigm_shift:17_review_spec_verify_output"] ?? null}>
    <VisualMediaProvider media={PREVIEW_VISUAL_MEDIA["part2_paradigm_shift:17_review_spec_verify_output"] ?? null}>
      <Part2ParadigmShift17ReviewSpecVerifyOutput />
    </VisualMediaProvider>
  </VisualContractProvider>
);
const Part2ParadigmShift18PromptMoldFinalePreview: React.FC = () => (
  <VisualContractProvider contract={PREVIEW_VISUAL_CONTRACTS["part2_paradigm_shift:18_prompt_mold_finale"] ?? null}>
    <VisualMediaProvider media={PREVIEW_VISUAL_MEDIA["part2_paradigm_shift:18_prompt_mold_finale"] ?? null}>
      <Part2ParadigmShift18PromptMoldFinale />
    </VisualMediaProvider>
  </VisualContractProvider>
);
const Part3MoldParts01SectionTitleCardPreview: React.FC = () => (
  <VisualContractProvider contract={PREVIEW_VISUAL_CONTRACTS["part3_mold_parts:01_section_title_card"] ?? null}>
    <VisualMediaProvider media={PREVIEW_VISUAL_MEDIA["part3_mold_parts:01_section_title_card"] ?? null}>
      <GeneratedContractVisual />
    </VisualMediaProvider>
  </VisualContractProvider>
);
const Part3MoldParts02MoldCrossSectionPreview: React.FC = () => (
  <VisualContractProvider contract={PREVIEW_VISUAL_CONTRACTS["part3_mold_parts:02_mold_cross_section"] ?? null}>
    <VisualMediaProvider media={PREVIEW_VISUAL_MEDIA["part3_mold_parts:02_mold_cross_section"] ?? null}>
      <Part3MoldParts02MoldCrossSection />
    </VisualMediaProvider>
  </VisualContractProvider>
);
const Part3MoldParts03MoldWallsIlluminatePreview: React.FC = () => (
  <VisualContractProvider contract={PREVIEW_VISUAL_CONTRACTS["part3_mold_parts:03_mold_walls_illuminate"] ?? null}>
    <VisualMediaProvider media={PREVIEW_VISUAL_MEDIA["part3_mold_parts:03_mold_walls_illuminate"] ?? null}>
      <Part3MoldParts03MoldWallsIlluminate />
    </VisualMediaProvider>
  </VisualContractProvider>
);
const Part3MoldParts04LiquidInjectionPreview: React.FC = () => (
  <VisualContractProvider contract={PREVIEW_VISUAL_CONTRACTS["part3_mold_parts:04_liquid_injection"] ?? null}>
    <VisualMediaProvider media={PREVIEW_VISUAL_MEDIA["part3_mold_parts:04_liquid_injection"] ?? null}>
      <Part3MoldParts04LiquidInjection />
    </VisualMediaProvider>
  </VisualContractProvider>
);
const Part3MoldParts05BugAddsWallPreview: React.FC = () => (
  <VisualContractProvider contract={PREVIEW_VISUAL_CONTRACTS["part3_mold_parts:05_bug_adds_wall"] ?? null}>
    <VisualMediaProvider media={PREVIEW_VISUAL_MEDIA["part3_mold_parts:05_bug_adds_wall"] ?? null}>
      <Part3MoldParts05BugAddsWall />
    </VisualMediaProvider>
  </VisualContractProvider>
);
const Part3MoldParts06RatchetTimelapsePreview: React.FC = () => (
  <VisualContractProvider contract={PREVIEW_VISUAL_CONTRACTS["part3_mold_parts:06_ratchet_timelapse"] ?? null}>
    <VisualMediaProvider media={PREVIEW_VISUAL_MEDIA["part3_mold_parts:06_ratchet_timelapse"] ?? null}>
      <Part3MoldParts06RatchetTimelapse />
    </VisualMediaProvider>
  </VisualContractProvider>
);
const Part3MoldParts07SplitTraditionalVsPddPreview: React.FC = () => (
  <VisualContractProvider contract={PREVIEW_VISUAL_CONTRACTS["part3_mold_parts:07_split_traditional_vs_pdd"] ?? null}>
    <VisualMediaProvider media={PREVIEW_VISUAL_MEDIA["part3_mold_parts:07_split_traditional_vs_pdd"] ?? null}>
      <GeneratedContractVisual />
    </VisualMediaProvider>
  </VisualContractProvider>
);
const Part3MoldParts08BugForkRoadPreview: React.FC = () => (
  <VisualContractProvider contract={PREVIEW_VISUAL_CONTRACTS["part3_mold_parts:08_bug_fork_road"] ?? null}>
    <VisualMediaProvider media={PREVIEW_VISUAL_MEDIA["part3_mold_parts:08_bug_fork_road"] ?? null}>
      <Part3MoldParts08BugForkRoad />
    </VisualMediaProvider>
  </VisualContractProvider>
);
const Part3MoldParts09FiveGenerationsPreview: React.FC = () => (
  <VisualContractProvider contract={PREVIEW_VISUAL_CONTRACTS["part3_mold_parts:09_five_generations"] ?? null}>
    <VisualMediaProvider media={PREVIEW_VISUAL_MEDIA["part3_mold_parts:09_five_generations"] ?? null}>
      <Part3MoldParts09FiveGenerations />
    </VisualMediaProvider>
  </VisualContractProvider>
);
const Part3MoldParts10Z3FormalProofPreview: React.FC = () => (
  <VisualContractProvider contract={PREVIEW_VISUAL_CONTRACTS["part3_mold_parts:10_z3_formal_proof"] ?? null}>
    <VisualMediaProvider media={PREVIEW_VISUAL_MEDIA["part3_mold_parts:10_z3_formal_proof"] ?? null}>
      <Part3MoldParts10Z3FormalProof />
    </VisualMediaProvider>
  </VisualContractProvider>
);
const Part3MoldParts11ModuleBoundaryPreview: React.FC = () => (
  <VisualContractProvider contract={PREVIEW_VISUAL_CONTRACTS["part3_mold_parts:11_module_boundary"] ?? null}>
    <VisualMediaProvider media={PREVIEW_VISUAL_MEDIA["part3_mold_parts:11_module_boundary"] ?? null}>
      <Part3MoldParts11ModuleBoundary />
    </VisualMediaProvider>
  </VisualContractProvider>
);
const Part3MoldParts12PromptNozzlePreview: React.FC = () => (
  <VisualContractProvider contract={PREVIEW_VISUAL_CONTRACTS["part3_mold_parts:12_prompt_nozzle"] ?? null}>
    <VisualMediaProvider media={PREVIEW_VISUAL_MEDIA["part3_mold_parts:12_prompt_nozzle"] ?? null}>
      <Part3MoldParts12PromptNozzle />
    </VisualMediaProvider>
  </VisualContractProvider>
);
const Part3MoldParts13PromptRatioPreview: React.FC = () => (
  <VisualContractProvider contract={PREVIEW_VISUAL_CONTRACTS["part3_mold_parts:13_prompt_ratio"] ?? null}>
    <VisualMediaProvider media={PREVIEW_VISUAL_MEDIA["part3_mold_parts:13_prompt_ratio"] ?? null}>
      <Part3MoldParts13PromptRatio />
    </VisualMediaProvider>
  </VisualContractProvider>
);
const Part3MoldParts15GroundingStylesPreview: React.FC = () => (
  <VisualContractProvider contract={PREVIEW_VISUAL_CONTRACTS["part3_mold_parts:15_grounding_styles"] ?? null}>
    <VisualMediaProvider media={PREVIEW_VISUAL_MEDIA["part3_mold_parts:15_grounding_styles"] ?? null}>
      <Part3MoldParts15GroundingStyles />
    </VisualMediaProvider>
  </VisualContractProvider>
);
const Part3MoldParts16ThreeComponentsPullbackPreview: React.FC = () => (
  <VisualContractProvider contract={PREVIEW_VISUAL_CONTRACTS["part3_mold_parts:16_three_components_pullback"] ?? null}>
    <VisualMediaProvider media={PREVIEW_VISUAL_MEDIA["part3_mold_parts:16_three_components_pullback"] ?? null}>
      <Part3MoldParts16ThreeComponentsPullback />
    </VisualMediaProvider>
  </VisualContractProvider>
);
const Part3MoldParts17ComponentTablePreview: React.FC = () => (
  <VisualContractProvider contract={PREVIEW_VISUAL_CONTRACTS["part3_mold_parts:17_component_table"] ?? null}>
    <VisualMediaProvider media={PREVIEW_VISUAL_MEDIA["part3_mold_parts:17_component_table"] ?? null}>
      <Part3MoldParts17ComponentTable />
    </VisualMediaProvider>
  </VisualContractProvider>
);
const Part3MoldParts18CodeOutputFinalePreview: React.FC = () => (
  <VisualContractProvider contract={PREVIEW_VISUAL_CONTRACTS["part3_mold_parts:18_code_output_finale"] ?? null}>
    <VisualMediaProvider media={PREVIEW_VISUAL_MEDIA["part3_mold_parts:18_code_output_finale"] ?? null}>
      <Part3MoldParts18CodeOutputFinale />
    </VisualMediaProvider>
  </VisualContractProvider>
);
const Part4PrecisionTradeoff01SectionTitleCardPreview: React.FC = () => (
  <VisualContractProvider contract={PREVIEW_VISUAL_CONTRACTS["part4_precision_tradeoff:01_section_title_card"] ?? null}>
    <VisualMediaProvider media={PREVIEW_VISUAL_MEDIA["part4_precision_tradeoff:01_section_title_card"] ?? null}>
      <GeneratedContractVisual />
    </VisualMediaProvider>
  </VisualContractProvider>
);
const Part4PrecisionTradeoff02SplitPrinterVsMoldPreview: React.FC = () => (
  <VisualContractProvider contract={PREVIEW_VISUAL_CONTRACTS["part4_precision_tradeoff:02_split_printer_vs_mold"] ?? null}>
    <VisualMediaProvider media={PREVIEW_VISUAL_MEDIA["part4_precision_tradeoff:02_split_printer_vs_mold"] ?? null}>
      <GeneratedContractVisual />
    </VisualMediaProvider>
  </VisualContractProvider>
);
const Part4PrecisionTradeoff03PrecisionTradeoffCurvePreview: React.FC = () => (
  <VisualContractProvider contract={PREVIEW_VISUAL_CONTRACTS["part4_precision_tradeoff:03_precision_tradeoff_curve"] ?? null}>
    <VisualMediaProvider media={PREVIEW_VISUAL_MEDIA["part4_precision_tradeoff:03_precision_tradeoff_curve"] ?? null}>
      <GeneratedContractVisual />
    </VisualMediaProvider>
  </VisualContractProvider>
);
const Part4PrecisionTradeoff04DetailedPromptFilePreview: React.FC = () => (
  <VisualContractProvider contract={PREVIEW_VISUAL_CONTRACTS["part4_precision_tradeoff:04_detailed_prompt_file"] ?? null}>
    <VisualMediaProvider media={PREVIEW_VISUAL_MEDIA["part4_precision_tradeoff:04_detailed_prompt_file"] ?? null}>
      <Part4PrecisionTradeoff04DetailedPromptFile />
    </VisualMediaProvider>
  </VisualContractProvider>
);
const Part4PrecisionTradeoff05MinimalPromptWithTestsPreview: React.FC = () => (
  <VisualContractProvider contract={PREVIEW_VISUAL_CONTRACTS["part4_precision_tradeoff:05_minimal_prompt_with_tests"] ?? null}>
    <VisualMediaProvider media={PREVIEW_VISUAL_MEDIA["part4_precision_tradeoff:05_minimal_prompt_with_tests"] ?? null}>
      <Part4PrecisionTradeoff05MinimalPromptWithTests />
    </VisualMediaProvider>
  </VisualContractProvider>
);
const Part4PrecisionTradeoff06DualGenerationComparisonPreview: React.FC = () => (
  <VisualContractProvider contract={PREVIEW_VISUAL_CONTRACTS["part4_precision_tradeoff:06_dual_generation_comparison"] ?? null}>
    <VisualMediaProvider media={PREVIEW_VISUAL_MEDIA["part4_precision_tradeoff:06_dual_generation_comparison"] ?? null}>
      <Part4PrecisionTradeoff06DualGenerationComparison />
    </VisualMediaProvider>
  </VisualContractProvider>
);
const Part4PrecisionTradeoff07KeyInsightWallsPreview: React.FC = () => (
  <VisualContractProvider contract={PREVIEW_VISUAL_CONTRACTS["part4_precision_tradeoff:07_key_insight_walls"] ?? null}>
    <VisualMediaProvider media={PREVIEW_VISUAL_MEDIA["part4_precision_tradeoff:07_key_insight_walls"] ?? null}>
      <Part4PrecisionTradeoff07KeyInsightWalls />
    </VisualMediaProvider>
  </VisualContractProvider>
);
const Part4PrecisionTradeoff08EmbeddedCodeDocumentPreview: React.FC = () => (
  <VisualContractProvider contract={PREVIEW_VISUAL_CONTRACTS["part4_precision_tradeoff:08_embedded_code_document"] ?? null}>
    <VisualMediaProvider media={PREVIEW_VISUAL_MEDIA["part4_precision_tradeoff:08_embedded_code_document"] ?? null}>
      <Part4PrecisionTradeoff08EmbeddedCodeDocument />
    </VisualMediaProvider>
  </VisualContractProvider>
);
const Part4PrecisionTradeoff09PromptCodeSpectrumPreview: React.FC = () => (
  <VisualContractProvider contract={PREVIEW_VISUAL_CONTRACTS["part4_precision_tradeoff:09_prompt_code_spectrum"] ?? null}>
    <VisualMediaProvider media={PREVIEW_VISUAL_MEDIA["part4_precision_tradeoff:09_prompt_code_spectrum"] ?? null}>
      <Part4PrecisionTradeoff09PromptCodeSpectrum />
    </VisualMediaProvider>
  </VisualContractProvider>
);
const Part5CompoundReturns01SectionTitleCardPreview: React.FC = () => (
  <VisualContractProvider contract={PREVIEW_VISUAL_CONTRACTS["part5_compound_returns:01_section_title_card"] ?? null}>
    <VisualMediaProvider media={PREVIEW_VISUAL_MEDIA["part5_compound_returns:01_section_title_card"] ?? null}>
      <GeneratedContractVisual />
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
const Part5CompoundReturns08EconomicsCrossingCallbackPreview: React.FC = () => (
  <VisualContractProvider contract={PREVIEW_VISUAL_CONTRACTS["part5_compound_returns:08_economics_crossing_callback"] ?? null}>
    <VisualMediaProvider media={PREVIEW_VISUAL_MEDIA["part5_compound_returns:08_economics_crossing_callback"] ?? null}>
      <GeneratedContractVisual />
    </VisualMediaProvider>
  </VisualContractProvider>
);
const Part5CompoundReturns09ContrarianQuoteCardPreview: React.FC = () => (
  <VisualContractProvider contract={PREVIEW_VISUAL_CONTRACTS["part5_compound_returns:09_contrarian_quote_card"] ?? null}>
    <VisualMediaProvider media={PREVIEW_VISUAL_MEDIA["part5_compound_returns:09_contrarian_quote_card"] ?? null}>
      <GeneratedContractVisual />
    </VisualMediaProvider>
  </VisualContractProvider>
);
const WhereToStart01SectionTitleCardPreview: React.FC = () => (
  <VisualContractProvider contract={PREVIEW_VISUAL_CONTRACTS["where_to_start:01_section_title_card"] ?? null}>
    <VisualMediaProvider media={PREVIEW_VISUAL_MEDIA["where_to_start:01_section_title_card"] ?? null}>
      <GeneratedContractVisual />
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
const WhereToStart04SourceOfTruthLabelPreview: React.FC = () => (
  <VisualContractProvider contract={PREVIEW_VISUAL_CONTRACTS["where_to_start:04_source_of_truth_label"] ?? null}>
    <VisualMediaProvider media={PREVIEW_VISUAL_MEDIA["where_to_start:04_source_of_truth_label"] ?? null}>
      <WhereToStart04SourceOfTruthLabel />
    </VisualMediaProvider>
  </VisualContractProvider>
);
const WhereToStart05ModuleGlowSpreadPreview: React.FC = () => (
  <VisualContractProvider contract={PREVIEW_VISUAL_CONTRACTS["where_to_start:05_module_glow_spread"] ?? null}>
    <VisualMediaProvider media={PREVIEW_VISUAL_MEDIA["where_to_start:05_module_glow_spread"] ?? null}>
      <WhereToStart05ModuleGlowSpread />
    </VisualMediaProvider>
  </VisualContractProvider>
);
const WhereToStart06NoBigBangCalloutPreview: React.FC = () => (
  <VisualContractProvider contract={PREVIEW_VISUAL_CONTRACTS["where_to_start:06_no_big_bang_callout"] ?? null}>
    <VisualMediaProvider media={PREVIEW_VISUAL_MEDIA["where_to_start:06_no_big_bang_callout"] ?? null}>
      <WhereToStart06NoBigBangCallout />
    </VisualMediaProvider>
  </VisualContractProvider>
);
const WhereToStart07GradualMigrationInsightPreview: React.FC = () => (
  <VisualContractProvider contract={PREVIEW_VISUAL_CONTRACTS["where_to_start:07_gradual_migration_insight"] ?? null}>
    <VisualMediaProvider media={PREVIEW_VISUAL_MEDIA["where_to_start:07_gradual_migration_insight"] ?? null}>
      <WhereToStart07GradualMigrationInsight />
    </VisualMediaProvider>
  </VisualContractProvider>
);
const Closing03PddTrianglePreview: React.FC = () => (
  <VisualContractProvider contract={PREVIEW_VISUAL_CONTRACTS["closing:03_pdd_triangle"] ?? null}>
    <VisualMediaProvider media={PREVIEW_VISUAL_MEDIA["closing:03_pdd_triangle"] ?? null}>
      <Closing03PddTriangle />
    </VisualMediaProvider>
  </VisualContractProvider>
);
const Closing04DissolveRegenerateLoopPreview: React.FC = () => (
  <VisualContractProvider contract={PREVIEW_VISUAL_CONTRACTS["closing:04_dissolve_regenerate_loop"] ?? null}>
    <VisualMediaProvider media={PREVIEW_VISUAL_MEDIA["closing:04_dissolve_regenerate_loop"] ?? null}>
      <Closing04DissolveRegenerateLoop />
    </VisualMediaProvider>
  </VisualContractProvider>
);
const Closing06TheBeatPreview: React.FC = () => (
  <VisualContractProvider contract={PREVIEW_VISUAL_CONTRACTS["closing:06_the_beat"] ?? null}>
    <VisualMediaProvider media={PREVIEW_VISUAL_MEDIA["closing:06_the_beat"] ?? null}>
      <Closing06TheBeat />
    </VisualMediaProvider>
  </VisualContractProvider>
);
const Closing07FinalTitleCardPreview: React.FC = () => (
  <VisualContractProvider contract={PREVIEW_VISUAL_CONTRACTS["closing:07_final_title_card"] ?? null}>
    <VisualMediaProvider media={PREVIEW_VISUAL_MEDIA["closing:07_final_title_card"] ?? null}>
      <Closing07FinalTitleCard />
    </VisualMediaProvider>
  </VisualContractProvider>
);

export const RemotionRoot: React.FC = () => {
  return (
    <>
      <Composition
        id="ColdOpenSection"
        component={ColdOpenSection}
        durationInFrames={537}
        fps={30}
        width={1920}
        height={1080}
      />
      <Composition
        id="Part1EconomicsSection"
        component={Part1EconomicsSection}
        durationInFrames={14523}
        fps={30}
        width={1920}
        height={1080}
      />
      <Composition
        id="Part2ParadigmShiftSection"
        component={Part2ParadigmShiftSection}
        durationInFrames={6845}
        fps={30}
        width={1920}
        height={1080}
      />
      <Composition
        id="Part3MoldPartsSection"
        component={Part3MoldPartsSection}
        durationInFrames={10377}
        fps={30}
        width={1920}
        height={1080}
      />
      <Composition
        id="Part4PrecisionTradeoffSection"
        component={Part4PrecisionTradeoffSection}
        durationInFrames={3249}
        fps={30}
        width={1920}
        height={1080}
      />
      <Composition
        id="Part5CompoundReturnsSection"
        component={Part5CompoundReturnsSection}
        durationInFrames={3576}
        fps={30}
        width={1920}
        height={1080}
      />
      <Composition
        id="WhereToStartSection"
        component={WhereToStartSection}
        durationInFrames={1047}
        fps={30}
        width={1920}
        height={1080}
      />
      <Composition
        id="ClosingSection"
        component={ClosingSection}
        durationInFrames={463}
        fps={30}
        width={1920}
        height={1080}
      />
      <Composition
        id="cold-open01-split-screen-darning"
        component={ColdOpen01SplitScreenDarningPreview}
        durationInFrames={270}
        fps={30}
        width={1920}
        height={1080}
      />
      <Composition
        id="cold-open07-code-cursor-blink"
        component={ColdOpen07CodeCursorBlinkPreview}
        durationInFrames={48}
        fps={30}
        width={1920}
        height={1080}
      />
      <Composition
        id="cold-open08-code-regeneration"
        component={ColdOpen08CodeRegenerationPreview}
        durationInFrames={60}
        fps={30}
        width={1920}
        height={1080}
      />
      <Composition
        id="cold-open09-title-card-pdd"
        component={ColdOpen09TitleCardPddPreview}
        durationInFrames={60}
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
        durationInFrames={720}
        fps={30}
        width={1920}
        height={1080}
      />
      <Composition
        id="part1-economics03-code-cost-chart"
        component={Part1Economics03CodeCostChartPreview}
        durationInFrames={1650}
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
        id="part1-economics05-code-churn-annotations"
        component={Part1Economics05CodeChurnAnnotationsPreview}
        durationInFrames={840}
        fps={30}
        width={1920}
        height={1080}
      />
      <Composition
        id="part1-economics06-debt-layers-zoom"
        component={Part1Economics06DebtLayersZoomPreview}
        durationInFrames={540}
        fps={30}
        width={1920}
        height={1080}
      />
      <Composition
        id="part1-economics07-context-window-shrink"
        component={Part1Economics07ContextWindowShrinkPreview}
        durationInFrames={1560}
        fps={30}
        width={1920}
        height={1080}
      />
      <Composition
        id="part1-economics08-performance-vs-context"
        component={Part1Economics08PerformanceVsContextPreview}
        durationInFrames={1470}
        fps={30}
        width={1920}
        height={1080}
      />
      <Composition
        id="part1-economics09-two-by-two-grid"
        component={Part1Economics09TwoByTwoGridPreview}
        durationInFrames={630}
        fps={30}
        width={1920}
        height={1080}
      />
      <Composition
        id="part1-economics10-fork-codebase-size"
        component={Part1Economics10ForkCodebaseSizePreview}
        durationInFrames={1380}
        fps={30}
        width={1920}
        height={1080}
      />
      <Composition
        id="part1-economics11-patching-vs-regeneration"
        component={Part1Economics11PatchingVsRegenerationPreview}
        durationInFrames={810}
        fps={30}
        width={1920}
        height={1080}
      />
      <Composition
        id="part1-economics12-context-compression"
        component={Part1Economics12ContextCompressionPreview}
        durationInFrames={1380}
        fps={30}
        width={1920}
        height={1080}
      />
      <Composition
        id="part1-economics13-crossing-lines-moment"
        component={Part1Economics13CrossingLinesMomentPreview}
        durationInFrames={360}
        fps={30}
        width={1920}
        height={1080}
      />
      <Composition
        id="part1-economics14-split-developer-grandma"
        component={Part1Economics14SplitDeveloperGrandmaPreview}
        durationInFrames={510}
        fps={30}
        width={1920}
        height={1080}
      />
      <Composition
        id="part1-economics18-key-insight-stillness"
        component={Part1Economics18KeyInsightStillnessPreview}
        durationInFrames={360}
        fps={30}
        width={1920}
        height={1080}
      />
      <Composition
        id="part1-economics19-double-meter-insight"
        component={Part1Economics19DoubleMeterInsightPreview}
        durationInFrames={360}
        fps={30}
        width={1920}
        height={1080}
      />
      <Composition
        id="part1-economics20-try-it-yourself"
        component={Part1Economics20TryItYourselfPreview}
        durationInFrames={240}
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
        id="part2-paradigm-shift04-mold-production-counter"
        component={Part2ParadigmShift04MoldProductionCounterPreview}
        durationInFrames={300}
        fps={30}
        width={1920}
        height={1080}
      />
      <Composition
        id="part2-paradigm-shift07-split-craftsman-vs-mold"
        component={Part2ParadigmShift07SplitCraftsmanVsMoldPreview}
        durationInFrames={600}
        fps={30}
        width={1920}
        height={1080}
      />
      <Composition
        id="part2-paradigm-shift11-schematic-density-zoom"
        component={Part2ParadigmShift11SchematicDensityZoomPreview}
        durationInFrames={420}
        fps={30}
        width={1920}
        height={1080}
      />
      <Composition
        id="part2-paradigm-shift12-verilog-synthesis"
        component={Part2ParadigmShift12VerilogSynthesisPreview}
        durationInFrames={360}
        fps={30}
        width={1920}
        height={1080}
      />
      <Composition
        id="part2-paradigm-shift13-triple-synthesis-equivalence"
        component={Part2ParadigmShift13TripleSynthesisEquivalencePreview}
        durationInFrames={750}
        fps={30}
        width={1920}
        height={1080}
      />
      <Composition
        id="part2-paradigm-shift14-synopsys-pdd-equivalence"
        component={Part2ParadigmShift14SynopsysPddEquivalencePreview}
        durationInFrames={390}
        fps={30}
        width={1920}
        height={1080}
      />
      <Composition
        id="part2-paradigm-shift15-abstraction-staircase"
        component={Part2ParadigmShift15AbstractionStaircasePreview}
        durationInFrames={690}
        fps={30}
        width={1920}
        height={1080}
      />
      <Composition
        id="part2-paradigm-shift16-billion-gate-unreviewable"
        component={Part2ParadigmShift16BillionGateUnreviewablePreview}
        durationInFrames={360}
        fps={30}
        width={1920}
        height={1080}
      />
      <Composition
        id="part2-paradigm-shift17-review-spec-verify-output"
        component={Part2ParadigmShift17ReviewSpecVerifyOutputPreview}
        durationInFrames={360}
        fps={30}
        width={1920}
        height={1080}
      />
      <Composition
        id="part2-paradigm-shift18-prompt-mold-finale"
        component={Part2ParadigmShift18PromptMoldFinalePreview}
        durationInFrames={360}
        fps={30}
        width={1920}
        height={1080}
      />
      <Composition
        id="part3-mold-parts01-section-title-card"
        component={Part3MoldParts01SectionTitleCardPreview}
        durationInFrames={1320}
        fps={30}
        width={1920}
        height={1080}
      />
      <Composition
        id="part3-mold-parts02-mold-cross-section"
        component={Part3MoldParts02MoldCrossSectionPreview}
        durationInFrames={420}
        fps={30}
        width={1920}
        height={1080}
      />
      <Composition
        id="part3-mold-parts03-mold-walls-illuminate"
        component={Part3MoldParts03MoldWallsIlluminatePreview}
        durationInFrames={300}
        fps={30}
        width={1920}
        height={1080}
      />
      <Composition
        id="part3-mold-parts04-liquid-injection"
        component={Part3MoldParts04LiquidInjectionPreview}
        durationInFrames={870}
        fps={30}
        width={1920}
        height={1080}
      />
      <Composition
        id="part3-mold-parts05-bug-adds-wall"
        component={Part3MoldParts05BugAddsWallPreview}
        durationInFrames={480}
        fps={30}
        width={1920}
        height={1080}
      />
      <Composition
        id="part3-mold-parts06-ratchet-timelapse"
        component={Part3MoldParts06RatchetTimelapsePreview}
        durationInFrames={270}
        fps={30}
        width={1920}
        height={1080}
      />
      <Composition
        id="part3-mold-parts07-split-traditional-vs-pdd"
        component={Part3MoldParts07SplitTraditionalVsPddPreview}
        durationInFrames={240}
        fps={30}
        width={1920}
        height={1080}
      />
      <Composition
        id="part3-mold-parts08-bug-fork-road"
        component={Part3MoldParts08BugForkRoadPreview}
        durationInFrames={540}
        fps={30}
        width={1920}
        height={1080}
      />
      <Composition
        id="part3-mold-parts09-five-generations"
        component={Part3MoldParts09FiveGenerationsPreview}
        durationInFrames={540}
        fps={30}
        width={1920}
        height={1080}
      />
      <Composition
        id="part3-mold-parts10-z3-formal-proof"
        component={Part3MoldParts10Z3FormalProofPreview}
        durationInFrames={780}
        fps={30}
        width={1920}
        height={1080}
      />
      <Composition
        id="part3-mold-parts11-module-boundary"
        component={Part3MoldParts11ModuleBoundaryPreview}
        durationInFrames={660}
        fps={30}
        width={1920}
        height={1080}
      />
      <Composition
        id="part3-mold-parts12-prompt-nozzle"
        component={Part3MoldParts12PromptNozzlePreview}
        durationInFrames={720}
        fps={30}
        width={1920}
        height={1080}
      />
      <Composition
        id="part3-mold-parts13-prompt-ratio"
        component={Part3MoldParts13PromptRatioPreview}
        durationInFrames={540}
        fps={30}
        width={1920}
        height={1080}
      />
      <Composition
        id="part3-mold-parts15-grounding-styles"
        component={Part3MoldParts15GroundingStylesPreview}
        durationInFrames={780}
        fps={30}
        width={1920}
        height={1080}
      />
      <Composition
        id="part3-mold-parts16-three-components-pullback"
        component={Part3MoldParts16ThreeComponentsPullbackPreview}
        durationInFrames={270}
        fps={30}
        width={1920}
        height={1080}
      />
      <Composition
        id="part3-mold-parts17-component-table"
        component={Part3MoldParts17ComponentTablePreview}
        durationInFrames={300}
        fps={30}
        width={1920}
        height={1080}
      />
      <Composition
        id="part3-mold-parts18-code-output-finale"
        component={Part3MoldParts18CodeOutputFinalePreview}
        durationInFrames={90}
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
        id="part4-precision-tradeoff02-split-printer-vs-mold"
        component={Part4PrecisionTradeoff02SplitPrinterVsMoldPreview}
        durationInFrames={480}
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
        id="part4-precision-tradeoff04-detailed-prompt-file"
        component={Part4PrecisionTradeoff04DetailedPromptFilePreview}
        durationInFrames={240}
        fps={30}
        width={1920}
        height={1080}
      />
      <Composition
        id="part4-precision-tradeoff05-minimal-prompt-with-tests"
        component={Part4PrecisionTradeoff05MinimalPromptWithTestsPreview}
        durationInFrames={240}
        fps={30}
        width={1920}
        height={1080}
      />
      <Composition
        id="part4-precision-tradeoff06-dual-generation-comparison"
        component={Part4PrecisionTradeoff06DualGenerationComparisonPreview}
        durationInFrames={240}
        fps={30}
        width={1920}
        height={1080}
      />
      <Composition
        id="part4-precision-tradeoff07-key-insight-walls"
        component={Part4PrecisionTradeoff07KeyInsightWallsPreview}
        durationInFrames={120}
        fps={30}
        width={1920}
        height={1080}
      />
      <Composition
        id="part4-precision-tradeoff08-embedded-code-document"
        component={Part4PrecisionTradeoff08EmbeddedCodeDocumentPreview}
        durationInFrames={840}
        fps={30}
        width={1920}
        height={1080}
      />
      <Composition
        id="part4-precision-tradeoff09-prompt-code-spectrum"
        component={Part4PrecisionTradeoff09PromptCodeSpectrumPreview}
        durationInFrames={480}
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
        component={Part5CompoundReturns08EconomicsCrossingCallbackPreview}
        durationInFrames={300}
        fps={30}
        width={1920}
        height={1080}
      />
      <Composition
        id="part5-compound-returns09-contrarian-quote-card"
        component={Part5CompoundReturns09ContrarianQuoteCardPreview}
        durationInFrames={660}
        fps={30}
        width={1920}
        height={1080}
      />
      <Composition
        id="where-to-start01-section-title-card"
        component={WhereToStart01SectionTitleCardPreview}
        durationInFrames={546}
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
        durationInFrames={270}
        fps={30}
        width={1920}
        height={1080}
      />
      <Composition
        id="where-to-start04-source-of-truth-label"
        component={WhereToStart04SourceOfTruthLabelPreview}
        durationInFrames={150}
        fps={30}
        width={1920}
        height={1080}
      />
      <Composition
        id="where-to-start05-module-glow-spread"
        component={WhereToStart05ModuleGlowSpreadPreview}
        durationInFrames={330}
        fps={30}
        width={1920}
        height={1080}
      />
      <Composition
        id="where-to-start06-no-big-bang-callout"
        component={WhereToStart06NoBigBangCalloutPreview}
        durationInFrames={150}
        fps={30}
        width={1920}
        height={1080}
      />
      <Composition
        id="where-to-start07-gradual-migration-insight"
        component={WhereToStart07GradualMigrationInsightPreview}
        durationInFrames={150}
        fps={30}
        width={1920}
        height={1080}
      />
      <Composition
        id="closing03-pdd-triangle"
        component={Closing03PddTrianglePreview}
        durationInFrames={180}
        fps={30}
        width={1920}
        height={1080}
      />
      <Composition
        id="closing04-dissolve-regenerate-loop"
        component={Closing04DissolveRegenerateLoopPreview}
        durationInFrames={150}
        fps={30}
        width={1920}
        height={1080}
      />
      <Composition
        id="closing06-the-beat"
        component={Closing06TheBeatPreview}
        durationInFrames={60}
        fps={30}
        width={1920}
        height={1080}
      />
      <Composition
        id="closing07-final-title-card"
        component={Closing07FinalTitleCardPreview}
        durationInFrames={180}
        fps={30}
        width={1920}
        height={1080}
      />
    </>
  );
};
