import React from "react";
import { Composition } from "remotion";
import { VisualMediaProvider, VisualContractProvider } from "./_shared/visual-runtime";
import { GeneratedContractVisual } from "./_shared/GeneratedContractVisual";

import { ColdOpenSection } from "./cold_open";
import { Part1EconomicsSection } from "./part1_economics";
import { Part2ParadigmShiftSection } from "./part2_paradigm_shift";
import { Part3MoldHasThreePartsSection } from "./part3_mold_has_three_parts";
import { Part4PrecisionTradeoffSection } from "./part4_precision_tradeoff";
import { Part5CompoundReturnsSection } from "./part5_compound_returns";
import { WhereToStartSection } from "./where_to_start";
import { ClosingSection } from "./closing";
import { ColdOpen07CodeRegeneration } from "./ColdOpen07CodeRegeneration";
import { ColdOpen01SplitScreenHook } from "./ColdOpen01SplitScreenHook";
import { ColdOpen07PddTitleCard } from "./ColdOpen07PddTitleCard";
import { Part1Economics04ResearchAnnotations } from "./Part1Economics04ResearchAnnotations";
import { Part1Economics05ContextWindowShrink } from "./Part1Economics05ContextWindowShrink";
import { Part1Economics09CrossingLinesMoment } from "./Part1Economics09CrossingLinesMoment";
import { Part2ParadigmShift08SynopsysPddEquivalence } from "./Part2ParadigmShift08SynopsysPddEquivalence";
import { Part2ParadigmShift09AbstractionStaircase } from "./Part2ParadigmShift09AbstractionStaircase";
import { Part4PrecisionTradeoff03PrecisionTradeoffCurve } from "./Part4PrecisionTradeoff03PrecisionTradeoffCurve";
import { Part4PrecisionTradeoff07EmbeddedCodeDocument } from "./Part4PrecisionTradeoff07EmbeddedCodeDocument";
import { Part5CompoundReturns02MaintenancePieChart } from "./Part5CompoundReturns02MaintenancePieChart";
import { Part5CompoundReturns03CompoundDebtCurve } from "./Part5CompoundReturns03CompoundDebtCurve";
import { Part5CompoundReturns04DivergingCostCurves } from "./Part5CompoundReturns04DivergingCostCurves";
import { Part5CompoundReturns05InvestmentComparisonTable } from "./Part5CompoundReturns05InvestmentComparisonTable";
import { Part5CompoundReturns07EconomicsCrossingCallback } from "./Part5CompoundReturns07EconomicsCrossingCallback";
import { WhereToStart02LegacyCodebaseReveal } from "./WhereToStart02LegacyCodebaseReveal";
import { WhereToStart07NoBigBangCallout } from "./WhereToStart07NoBigBangCallout";
import { Closing04PddTriangle } from "./Closing04PddTriangle";
import { Closing05DissolveRegenerateLoop } from "./Closing05DissolveRegenerateLoop";
import { Closing06MoldGlowFinale } from "./Closing06MoldGlowFinale";
import { Closing07TheBeat } from "./Closing07TheBeat";

const PREVIEW_VISUAL_MEDIA: Record<string, Record<string, string>> = {
  "cold_open:01_split_screen_darning": { defaultSrc: "veo/developer_cursor_edit.mp4", backgroundSrc: "veo/developer_cursor_edit.mp4", outputSrc: "veo/developer_cursor_edit.mp4", baseSrc: "veo/developer_cursor_edit.mp4" },
  "part1_economics:11_developer_darning_split": { leftSrc: "veo/developer_cursor_coding.mp4", defaultSrc: "veo/developer_cursor_coding.mp4", rightSrc: "veo/grandmother_darning_expert.mp4", backgroundSrc: "veo/developer_cursor_coding.mp4", outputSrc: "veo/developer_cursor_coding.mp4", baseSrc: "veo/developer_cursor_coding.mp4", revealSrc: "veo/grandmother_darning_expert.mp4" },
  "part2_paradigm_shift:06_split_craftsman_vs_mold": { defaultSrc: "veo/craftsman_carving.mp4", backgroundSrc: "veo/craftsman_carving.mp4", outputSrc: "veo/craftsman_carving.mp4", baseSrc: "veo/craftsman_carving.mp4" },
  "part4_precision_tradeoff:04_prompt_detail_comparison": { leftSrc: "veo/developer_prompt_shift.mp4", defaultSrc: "veo/developer_prompt_shift.mp4", rightSrc: "veo/developer_prompt_shift.mp4", backgroundSrc: "veo/developer_prompt_shift.mp4", outputSrc: "veo/developer_prompt_shift.mp4", baseSrc: "veo/developer_prompt_shift.mp4" },
};

const PREVIEW_VISUAL_CONTRACTS: Record<string, Record<string, unknown> | null> = {
  "cold_open:01_split_screen_darning": {"specBaseName": "01_split_screen_darning", "dataPoints": {"type": "split_screen", "layout": "vertical_50_50", "divider": {"color": "#FFFFFF", "width": 2, "opacity": 0.8}, "panels": {"left": {"clips": ["developer_cursor_edit", "developer_codebase_zoomout"], "crossfadeAt": 5.8}, "right": {"clips": ["grandmother_darning", "grandmother_drawer_zoomout"], "crossfadeAt": 5.8}}, "durationSeconds": 11.0}, "mediaAliases": {"defaultSrc": "veo/developer_cursor_edit.mp4", "backgroundSrc": "veo/developer_cursor_edit.mp4", "outputSrc": "veo/developer_cursor_edit.mp4", "baseSrc": "veo/developer_cursor_edit.mp4"}, "overlayConfig": null, "renderMode": "component"},
  "cold_open:07_code_cursor_blink": {"specBaseName": "07_code_cursor_blink", "dataPoints": {"type": "code_editor", "language": "typescript", "lineCount": 30, "patchIndicators": ["// HACK:", "// TODO: refactor", "// patch for #1247"], "gutterPlusLines": [3, 7, 12, 18, 22, 25], "cursorPosition": {"line": 14, "column": 4}, "theme": "vscode-dark"}, "mediaAliases": {}, "overlayConfig": null, "renderMode": "component"},
  "cold_open:08_code_regeneration": {"specBaseName": "08_code_regeneration", "dataPoints": {"type": "code_editor_animation", "phases": [{"name": "cascade_delete", "direction": "bottom-to-top", "durationFrames": 15}, {"name": "empty_beat", "durationFrames": 3}, {"name": "cascade_generate", "direction": "top-to-bottom", "durationFrames": 30}, {"name": "terminal_overlay", "text": "$ pdd generate ✓", "durationFrames": 12}], "theme": "vscode-dark", "cleanCode": true, "terminalCommand": "pdd generate"}, "mediaAliases": {}, "overlayConfig": null, "renderMode": "component"},
  "cold_open:09_title_card_pdd": {"specBaseName": "09_title_card_pdd", "dataPoints": {"type": "title_card", "title": "Prompt-Driven Development", "tagline": "Why You're Still Darning Socks", "titleFont": "Inter Bold", "titleSize": 72, "titleColor": "#FFFFFF", "glowColor": "rgba(79, 193, 255, 0.3)", "backgroundCodeOpacity": 0.2, "vignetteOpacity": 0.6}, "mediaAliases": {}, "overlayConfig": null, "renderMode": "component"},
  "cold_open:01_split_screen_hook": {"specBaseName": "01_split_screen_hook", "dataPoints": null, "mediaAliases": {}, "overlayConfig": null, "renderMode": "component"},
  "cold_open:07_pdd_title_card": {"specBaseName": "07_pdd_title_card", "dataPoints": null, "mediaAliases": {}, "overlayConfig": null, "renderMode": "component"},
  "part1_economics:01_section_title_card": {"specBaseName": "01_section_title_card", "dataPoints": {"type": "title_card", "sectionNumber": 1, "sectionLabel": "PART 1", "titleLine1": "THE ECONOMICS", "titleLine2": "OF CODE", "backgroundColor": "#0A0F1A", "ghostElements": [{"shape": "bezier_curve", "color": "#4A90D9", "role": "descending_cost"}, {"shape": "bezier_curve", "color": "#D9944A", "role": "ascending_cost"}], "narrationSegments": ["part1_economics_001", "part1_economics_002", "part1_economics_003", "part1_economics_004", "part1_economics_005"]}, "mediaAliases": {}, "overlayConfig": null, "renderMode": "component"},
  "part1_economics:04_research_annotations": {"specBaseName": "04_research_annotations", "dataPoints": {"type": "annotated_chart_overlay", "baseChart": "code_cost_chart", "annotations": [{"id": "github_individual", "text": "Individual task: −55%", "source": "GitHub, 2022", "detail": "95 developers, one greenfield task", "color": "#2DD4BF", "pointsTo": "immediate_patch_line"}, {"id": "uplevel_throughput", "text": "Overall throughput: ~0%", "source": "Uplevel, 2024", "detail": "785 developers, one year", "color": "#EF4444", "pointsTo": "total_cost_dashed_line"}, {"id": "gitclear_churn", "text": "Code churn: +44%", "source": "GitClear, 2025", "detail": "211M lines analyzed", "color": "#EF4444", "pointsTo": "debt_area"}, {"id": "refactoring_decline", "text": "Refactoring: −60%", "source": "GitClear, 2025", "color": "#EF4444", "pointsTo": "debt_area"}], "debtLayers": [{"id": "code_complexity", "label": "Code Complexity", "opacity": 0.12}, {"id": "context_rot", "label": "Context Rot", "opacity": 0.06, "texture": "noise"}], "narrationSegments": ["part1_economics_014", "part1_economics_015", "part1_economics_016", "part1_economics_017"]}, "mediaAliases": {}, "overlayConfig": null, "renderMode": "component"},
  "part1_economics:05_context_window_shrink": {"specBaseName": "05_context_window_shrink", "dataPoints": {"type": "context_window_visualization", "contextWindow": {"width": 280, "height": 200, "fixedSize": true, "borderColor": "#4A90D9"}, "gridPhases": [{"size": "4x4", "blocks": 16, "coverage": 0.8, "color": "#2DD4BF"}, {"size": "8x8", "blocks": 64, "coverage": 0.4, "color": "#F59E0B"}, {"size": "16x16", "blocks": 256, "coverage": 0.1, "color": "#EF4444"}, {"size": "32x32", "blocks": 1024, "coverage": 0.02, "color": "#EF4444"}], "highlights": {"red": {"meaning": "irrelevant_code_retrieved", "count": 4}, "green": {"meaning": "needed_code_invisible", "count": 8}}, "narrationSegments": ["part1_economics_018", "part1_economics_019", "part1_economics_020"]}, "mediaAliases": {}, "overlayConfig": null, "renderMode": "component"},
  "part1_economics:06_performance_vs_context": {"specBaseName": "06_performance_vs_context", "dataPoints": {"type": "inset_line_chart", "title": "Performance vs. Context Length", "xAxis": {"label": "Context Length (tokens)", "range": [0, 128000]}, "yAxis": {"label": "Relative Performance", "range": [0, 100], "unit": "%"}, "series": [{"id": "performance_degradation", "label": "Model Performance", "color": "#EF4444", "data": [[4000, 95], [16000, 82], [32000, 65], [64000, 40], [128000, 15]]}], "citation": "EMNLP, 2025", "keyFinding": "14-85% performance degradation as context grows", "narrationSegments": ["part1_economics_021", "part1_economics_022"]}, "mediaAliases": {}, "overlayConfig": null, "renderMode": "component"},
  "part1_economics:08_fork_codebase_size": {"specBaseName": "08_fork_codebase_size", "dataPoints": {"type": "forked_line_chart", "baseChart": "code_cost_chart", "forkPoint": {"year": 2020, "value": 2.5}, "forks": [{"id": "small_codebase", "label": "Small codebase", "color": "#22C55E", "data": [[2020, 2.5], [2022, 1.2], [2024, 0.4], [2025, 0.2]]}, {"id": "large_codebase", "label": "Large codebase", "color": "#EF4444", "data": [[2020, 2.5], [2022, 2.8], [2024, 3.0], [2025, 3.2]]}], "annotations": [{"text": "METR, 2025: experienced devs 19% slower on mature repos", "pointsTo": "large_codebase"}, {"text": "Developers believed AI saved 20%. It cost 19%.", "emphasis": true}], "growthArrow": {"from": "small_codebase", "to": "large_codebase", "label": "Every patch adds code."}, "narrationSegments": ["part1_economics_026", "part1_economics_027", "part1_economics_028"]}, "mediaAliases": {}, "overlayConfig": null, "renderMode": "component"},
  "part1_economics:09_patching_vs_regeneration_split": {"specBaseName": "09_patching_vs_regeneration_split", "dataPoints": {"type": "split_screen", "layout": "vertical_split", "splitPosition": 960, "leftPanel": {"header": "AGENTIC PATCHING", "headerColor": "#EF4444", "content": "dense_code_with_highlights", "tokenCount": 15000, "relevance": "~40%", "thematicRole": "wasteful_context"}, "rightPanel": {"header": "PDD REGENERATION", "headerColor": "#2DD4BF", "content": "prompt_test_grounding", "tokenCount": 2300, "relevance": "100%", "thematicRole": "curated_context"}, "compressionAnimation": {"codeBlocks": 20, "promptBlocks": 20, "ratio": "5-10×"}, "backgroundColor": "#0A0F1A", "narrationSegments": ["part1_economics_029", "part1_economics_030"]}, "mediaAliases": {}, "overlayConfig": null, "renderMode": "component"},
  "part1_economics:10_crossing_lines_moment": {"specBaseName": "10_crossing_lines_moment", "dataPoints": {"type": "crossing_moment", "baseChart": "code_cost_chart", "finalSegment": {"line": "generate_cost", "data": [[2024, 3], [2024.5, 2.0], [2025, 0.8], [2025.5, 0.4]]}, "crossings": [{"id": "generate_below_total_debt", "x": 2024.5, "y": 2.0, "meaning": "Regeneration cheaper than patching + debt"}, {"id": "generate_below_immediate", "x": 2025, "y": 0.6, "meaning": "Regeneration cheaper than even immediate patching"}], "label": "We are here.", "annotation": "Small modules. Clear prompts. Always fits in context.", "narrationSegments": ["part1_economics_031", "part1_economics_032"]}, "mediaAliases": {}, "overlayConfig": null, "renderMode": "component"},
  "part1_economics:11_developer_darning_split": {"specBaseName": "11_developer_darning_split", "dataPoints": {"type": "split_screen", "layout": "vertical_split", "splitPosition": 960, "leftPanel": {"content": "veo_clip_with_zoom_overlay", "clipId": "developer_cursor_coding", "zoomOut": {"startFrame": 150, "duration": 60, "from": 1.0, "to": 0.5}, "legacyComments": ["// don't touch this", "// legacy", "// temporary fix (2019)", "// TODO: refactor someday", "// no idea why this works"], "thematicRole": "developer_patching"}, "rightPanel": {"content": "veo_clip", "clipId": "grandmother_darning_expert", "thematicRole": "grandmother_darning"}, "backgroundColor": "#000000", "narrationSegments": ["part1_economics_033"]}, "mediaAliases": {"leftSrc": "veo/developer_cursor_coding.mp4", "defaultSrc": "veo/developer_cursor_coding.mp4", "rightSrc": "veo/grandmother_darning_expert.mp4", "backgroundSrc": "veo/developer_cursor_coding.mp4", "outputSrc": "veo/developer_cursor_coding.mp4", "baseSrc": "veo/developer_cursor_coding.mp4", "revealSrc": "veo/grandmother_darning_expert.mp4"}, "overlayConfig": null, "renderMode": "component"},
  "part1_economics:14_key_insight_stillness": {"specBaseName": "14_key_insight_stillness", "dataPoints": {"type": "title_card", "variant": "stillness_beat", "backgroundColor": "#0A0F1A", "elements": [{"type": "pulsing_line", "color": "#E2E8F0", "maxOpacity": 0.03, "purpose": "subliminal_presence"}, {"type": "radial_glow", "color": "#FFB347", "opacity": 0.02, "purpose": "warmth_callback"}], "narrationSegments": []}, "mediaAliases": {}, "overlayConfig": null, "renderMode": "component"},
  "part1_economics:16_try_it_yourself": {"specBaseName": "16_try_it_yourself", "dataPoints": {"type": "title_card", "variant": "handwritten_challenge", "text": "Try it yourself.", "font": "Caveat", "backgroundColor": "#0F172A", "underlineColor": "#2DD4BF", "animation": "handwritten_trace", "narrationSegments": []}, "mediaAliases": {}, "overlayConfig": null, "renderMode": "component"},
  "part2_paradigm_shift:01_section_title_card": {"specBaseName": "01_section_title_card", "dataPoints": {"type": "title_card", "sectionNumber": 2, "sectionLabel": "PART 2", "titleLine1": "THE PARADIGM", "titleLine2": "SHIFT", "backgroundColor": "#0A0F1A", "ghostElements": [{"shape": "mold_silhouette", "color": "#8B5CF6", "role": "injection_mold_preview"}], "narrationSegments": ["part2_paradigm_shift_001", "part2_paradigm_shift_002", "part2_paradigm_shift_003", "part2_paradigm_shift_004"]}, "mediaAliases": {}, "overlayConfig": {"fadeOutFrames": 60}, "renderMode": "component"},
  "part2_paradigm_shift:04_mold_production_counter": {"specBaseName": "04_mold_production_counter", "dataPoints": {"type": "animated_infographic", "elements": [{"id": "mold", "shape": "cross_section", "color": "#64748B", "role": "constant_specification"}, {"id": "parts", "shape": "rounded_rect", "color": "#D9944A", "role": "generated_output"}, {"id": "counter", "values": [1, 10, 100, 1000, 10000], "role": "scale_indicator"}, {"id": "defect", "color": "#EF4444", "role": "flaw_transition"}], "narrationSegments": ["part2_paradigm_shift_007", "part2_paradigm_shift_008"]}, "mediaAliases": {}, "overlayConfig": null, "renderMode": "component"},
  "part2_paradigm_shift:06_split_craftsman_vs_mold": {"specBaseName": "06_split_craftsman_vs_mold", "dataPoints": {"type": "split_screen", "layout": "vertical_50_50", "divider": {"color": "#FFFFFF", "width": 2, "opacity": 0.6}, "panels": {"left": {"clips": ["craftsman_carving"], "aura": {"color": "#F59E0B", "target": "chair", "appearsAt": 8.0}, "label": "Value in the object"}, "right": {"clips": ["mold_producing_parts"], "aura": {"color": "#4A90D9", "target": "mold", "appearsAt": 12.0}, "label": "Value in the specification"}}, "narrationSegments": ["part2_paradigm_shift_010", "part2_paradigm_shift_011", "part2_paradigm_shift_012"], "durationSeconds": 25.0}, "mediaAliases": {"defaultSrc": "veo/craftsman_carving.mp4", "backgroundSrc": "veo/craftsman_carving.mp4", "outputSrc": "veo/craftsman_carving.mp4", "baseSrc": "veo/craftsman_carving.mp4"}, "overlayConfig": null, "renderMode": "component"},
  "part2_paradigm_shift:11_synopsys_pdd_equivalence": {"specBaseName": "11_synopsys_pdd_equivalence", "dataPoints": {"type": "animated_infographic", "phases": [{"id": "verification_flow", "description": "Flow diagram: Verilog → Synthesis → Netlist → Formal Verification", "frames": [0, 600], "keyInsight": {"different": "The gates were different every time.", "same": "The function was the same every time."}}, {"id": "synopsys_pdd_parallel", "description": "Side-by-side comparison of Synopsys and PDD pipelines", "frames": [600, 1140], "morphs": [{"from": "Verilog", "to": "PROMPT", "colorFrom": "#C678DD", "colorTo": "#8B5CF6"}, {"from": "Gate netlist", "to": "Software code", "colorFrom": "#10B981", "colorTo": "#61AFEF"}, {"from": "Synopsys checkmark", "to": "Test suite", "colorFrom": "#10B981", "colorTo": "#10B981"}]}], "narrationSegments": ["part2_paradigm_shift_016", "part2_paradigm_shift_017"]}, "mediaAliases": {}, "overlayConfig": null, "renderMode": "component"},
  "part2_paradigm_shift:12_abstraction_staircase": {"specBaseName": "12_abstraction_staircase", "dataPoints": {"type": "animated_timeline", "layout": "ascending_staircase", "steps": [{"label": "Transistors", "decade": "1970s", "color": "#D9944A"}, {"label": "Schematics", "decade": "1980s", "color": "#E97B2C"}, {"label": "RTL / Verilog", "decade": "1990s", "color": "#4A90D9"}, {"label": "Behavioral / HLS", "decade": "2010s", "color": "#14B8A6"}, {"label": "Natural Language → Code", "decade": "2020s", "color": "#8B5CF6", "pulsing": true}], "transitionArrows": {"label": "Couldn't scale", "color": "#EF4444"}, "narrationSegments": ["part2_paradigm_shift_018"]}, "mediaAliases": {}, "overlayConfig": null, "renderMode": "component"},
  "part2_paradigm_shift:13_billion_gate_unreviewable": {"specBaseName": "13_billion_gate_unreviewable", "dataPoints": {"type": "animated_infographic", "phases": [{"id": "overwhelming_scale", "description": "Billions of gates and massive code diffs — unreviewable", "frames": [0, 210], "elements": ["gate_grid", "code_diff_scroll"]}, {"id": "prompt_and_tests", "description": "Clean prompt document + verified test suite — reviewable", "frames": [210, 390], "prompt": {"label": "PROMPT", "color": "#8B5CF6", "lineCount": 5}, "tests": {"label": "TESTS", "color": "#10B981", "items": ["test_handles_null_input", "test_validates_schema", "test_returns_correct_type", "test_edge_case_empty", "test_performance_under_load"]}, "bottomLabel": "Review the spec. Verify the output."}], "narrationSegments": ["part2_paradigm_shift_019"]}, "mediaAliases": {}, "overlayConfig": null, "renderMode": "component"},
  "part3_mold_has_three_parts:01_section_title_card": {"specBaseName": "01_section_title_card", "dataPoints": {"type": "title_card", "sectionNumber": 3, "sectionLabel": "PART 3", "titleLine1": "THE MOLD HAS", "titleLine2": "THREE PARTS", "backgroundColor": "#0A0F1A", "ghostElements": [{"shape": "mold_shell", "color": "#4A90D9", "component": "outer_shell"}, {"shape": "mold_walls", "color": "#D9944A", "component": "test_walls"}, {"shape": "mold_nozzle", "color": "#2DD4BF", "component": "prompt_nozzle"}, {"shape": "mold_material", "color": "#A78BFA", "component": "grounding_material"}], "narrationSegments": ["part3_mold_has_three_parts_001", "part3_mold_has_three_parts_002"]}, "mediaAliases": {}, "overlayConfig": null, "renderMode": "component"},
  "part3_mold_has_three_parts:02_mold_cross_section": {"specBaseName": "02_mold_cross_section", "dataPoints": {"type": "animated_diagram", "diagramId": "mold_cross_section", "regions": [{"id": "walls", "label": "Tests: The Walls", "color": "#D9944A", "role": "constraints"}, {"id": "nozzle", "label": "Prompt: The Specification", "color": "#2DD4BF", "role": "specification"}, {"id": "material", "label": "Grounding: The Material", "color": "#A78BFA", "role": "style"}], "backgroundColor": "#0A0F1A", "narrationSegments": ["part3_mold_has_three_parts_003", "part3_mold_has_three_parts_004"]}, "mediaAliases": {}, "overlayConfig": null, "renderMode": "component"},
  "part3_mold_has_three_parts:03_test_walls_illuminate": {"specBaseName": "03_test_walls_illuminate", "dataPoints": {"type": "animated_diagram", "diagramId": "test_walls_illuminate", "walls": [{"id": "wall_null", "label": "null → None"}, {"id": "wall_empty", "label": "empty string → ''"}, {"id": "wall_unicode", "label": "handles unicode"}, {"id": "wall_latency", "label": "latency < 100ms"}, {"id": "wall_no_throw", "label": "no exceptions thrown"}, {"id": "wall_idempotent", "label": "idempotent"}], "wallColor": "#D9944A", "liquidGradient": ["#4A90D9", "#A78BFA"], "backgroundColor": "#0A0F1A", "narrationSegments": ["part3_mold_has_three_parts_005", "part3_mold_has_three_parts_006"]}, "mediaAliases": {}, "overlayConfig": null, "renderMode": "component"},
  "part3_mold_has_three_parts:05_research_annotations": {"specBaseName": "05_research_annotations", "dataPoints": {"type": "annotation_overlay", "diagramId": "research_annotations", "annotations": [{"id": "coderabbit", "headline": "AI code: 1.7× more issues", "source": "CodeRabbit, 2025", "color": "#EF4444", "subStats": ["75% more logic errors", "8× more performance problems"]}, {"id": "dora", "headline": "AI + strong tests = amplified delivery", "source": "DORA, 2025", "color": "#4ADE80"}], "backgroundColor": "#0A0F1A", "narrationSegments": ["part3_mold_has_three_parts_007", "part3_mold_has_three_parts_008"]}, "mediaAliases": {}, "overlayConfig": {"fadeInFrames": 90}, "renderMode": "component"},
  "part3_mold_has_three_parts:06_bug_add_wall": {"specBaseName": "06_bug_add_wall", "dataPoints": {"type": "animated_diagram", "diagramId": "bug_add_wall", "phases": [{"id": "bug_found", "action": "highlight_bug_line", "color": "#EF4444"}, {"id": "add_wall", "action": "materialize_wall", "label": "handles_null_userid", "color": "#D9944A"}, {"id": "regenerate", "action": "dissolve_and_regenerate_code"}, {"id": "permanent", "action": "wall_glows_permanently"}], "terminalCommands": ["pdd bug user_parser", "pdd fix user_parser"], "backgroundColor": "#0A0F1A", "narrationSegments": ["part3_mold_has_three_parts_009", "part3_mold_has_three_parts_010", "part3_mold_has_three_parts_011"]}, "mediaAliases": {}, "overlayConfig": null, "renderMode": "component"},
  "part3_mold_has_three_parts:07_ratchet_timelapse": {"specBaseName": "07_ratchet_timelapse", "dataPoints": {"type": "animated_diagram", "diagramId": "ratchet_timelapse", "wallProgression": [6, 7, 8, 11, 15, 20], "wallColor": "#D9944A", "terminalCommand": "pdd test", "backgroundColor": "#0A0F1A", "narrationSegments": ["part3_mold_has_three_parts_012"]}, "mediaAliases": {}, "overlayConfig": null, "renderMode": "component"},
  "part3_mold_has_three_parts:08_traditional_vs_pdd_split": {"specBaseName": "08_traditional_vs_pdd_split", "dataPoints": {"type": "split_screen", "layout": "vertical_split", "splitPosition": 960, "leftPanel": {"header": "TRADITIONAL", "headerColor": "#EF4444", "steps": [{"text": "Bug found", "opacity": 0.8}, {"text": "→ Patch code", "opacity": 0.8}, {"text": "Similar bug elsewhere", "opacity": 0.7}, {"text": "→ Patch again", "opacity": 0.6}, {"text": "Different bug", "opacity": 0.5}, {"text": "→ Patch again...", "opacity": 0.4}, {"text": "...", "opacity": 0.2}], "thematicRole": "endless_cycle"}, "rightPanel": {"header": "PDD", "headerColor": "#4ADE80", "steps": [{"text": "Bug found"}, {"text": "→ Add test (pdd bug)"}, {"text": "→ Regenerate (pdd fix)"}, {"text": "Bug impossible forever", "icon": "lock", "glow": true}], "thematicRole": "permanent_fix"}, "backgroundColor": "#0A0F1A", "narrationSegments": ["part3_mold_has_three_parts_013"]}, "mediaAliases": {}, "overlayConfig": null, "renderMode": "component"},
  "part3_mold_has_three_parts:09_bug_fork_diagram": {"specBaseName": "09_bug_fork_diagram", "dataPoints": {"type": "animated_diagram", "diagramId": "bug_fork_diagram", "root": {"text": "Bug found", "color": "#EF4444"}, "branches": [{"id": "code_bug", "label": "Code bug", "action": "Add a wall (failing test)", "color": "#D9944A", "condition": "Code doesn't pass tests"}, {"id": "prompt_defect", "label": "Prompt defect", "action": "Change the mold itself", "color": "#2DD4BF", "condition": "Code passes tests, wrong behavior"}], "backgroundColor": "#0A0F1A", "narrationSegments": ["part3_mold_has_three_parts_014"]}, "mediaAliases": {}, "overlayConfig": {"fadeInFrames": 60}, "renderMode": "component"},
  "part3_mold_has_three_parts:10_five_generations": {"specBaseName": "10_five_generations", "dataPoints": {"type": "animated_diagram", "diagramId": "five_generations", "panels": [{"id": "gen_1", "status": "fail", "color": "#EF4444", "statusDelay": 0}, {"id": "gen_2", "status": "warn", "color": "#F59E0B", "statusDelay": 60}, {"id": "gen_3", "status": "fail", "color": "#EF4444", "statusDelay": 0}, {"id": "gen_4", "status": "warn", "color": "#F59E0B", "statusDelay": 60}, {"id": "gen_5", "status": "pass", "color": "#4ADE80", "statusDelay": 120}], "label": "Generate five. Pick the one that passes all tests.", "backgroundColor": "#0A0F1A", "narrationSegments": ["part3_mold_has_three_parts_015"]}, "mediaAliases": {}, "overlayConfig": null, "renderMode": "component"},
  "part3_mold_has_three_parts:11_z3_formal_proof": {"specBaseName": "11_z3_formal_proof", "dataPoints": {"type": "annotation_overlay", "diagramId": "z3_formal_proof", "comparison": {"left": {"label": "Synopsys Formality", "domain": "chip_verification", "color": "#4A90D9"}, "right": {"label": "PDD + Z3", "domain": "code_verification", "color": "#2DD4BF"}, "equivalence": {"symbol": "≡", "color": "#A78BFA"}}, "emphasisLine": "Not sampling. Mathematical proof.", "backgroundColor": "#0A0F1A", "narrationSegments": ["part3_mold_has_three_parts_016"]}, "mediaAliases": {}, "overlayConfig": null, "renderMode": "component"},
  "part3_mold_has_three_parts:12_module_level_aside": {"specBaseName": "12_module_level_aside", "dataPoints": {"type": "animated_diagram", "diagramId": "module_level_aside", "modules": ["auth", "api", "user_parser", "billing", "cache", "queue", "mailer"], "highlightedModule": "user_parser", "highlightColors": ["#2DD4BF", "#D9944A"], "limitation": "PDD operates at the module level", "backgroundColor": "#0A0F1A", "narrationSegments": ["part3_mold_has_three_parts_017"]}, "mediaAliases": {}, "overlayConfig": null, "renderMode": "component"},
  "part3_mold_has_three_parts:13_prompt_nozzle": {"specBaseName": "13_prompt_nozzle", "dataPoints": {"type": "animated_diagram", "diagramId": "prompt_nozzle", "nozzleLabels": ["intent", "requirements", "constraints"], "promptText": ["Parse user IDs from untrusted input.", "Return None on failure, never throw.", "Handle unicode."], "promptFile": "user_parser.prompt", "dualGeneration": true, "nozzleColor": "#2DD4BF", "backgroundColor": "#0A0F1A", "narrationSegments": ["part3_mold_has_three_parts_018", "part3_mold_has_three_parts_019", "part3_mold_has_three_parts_020"]}, "mediaAliases": {}, "overlayConfig": null, "renderMode": "component"},
  "part3_mold_has_three_parts:14_prompt_ratio": {"specBaseName": "14_prompt_ratio", "dataPoints": {"type": "animated_diagram", "diagramId": "prompt_ratio", "promptFile": {"name": "user_parser.prompt", "lines": 15, "color": "#2DD4BF"}, "codeFile": {"name": "user_parser.py", "lines": 200, "color": "#94A3B8"}, "ratio": {"from": "1:5", "to": "1:10"}, "analogy": {"prompt": "header file", "code": "OBJ file"}, "backgroundColor": "#0A0F1A", "narrationSegments": ["part3_mold_has_three_parts_021"]}, "mediaAliases": {}, "overlayConfig": null, "renderMode": "component"},
  "part3_mold_has_three_parts:15_context_window_comparison": {"specBaseName": "15_context_window_comparison", "dataPoints": {"type": "split_screen", "layout": "vertical_split", "splitPosition": 960, "leftPanel": {"header": "RAW CODE CONTEXT", "headerColor": "#94A3B8", "content": "dense_code", "tokenCount": 15000, "scope": "1 module's implementation", "thematicRole": "overwhelming_code"}, "rightPanel": {"header": "PROMPT CONTEXT", "headerColor": "#2DD4BF", "content": "prompt_blocks", "tokenCount": 15000, "scope": "10 modules' specifications", "thematicRole": "curated_prompts"}, "multiplier": "10×", "backgroundColor": "#0A0F1A", "narrationSegments": ["part3_mold_has_three_parts_022"]}, "mediaAliases": {}, "overlayConfig": null, "renderMode": "component"},
  "part3_mold_has_three_parts:17_grounding_styles_split": {"specBaseName": "17_grounding_styles_split", "dataPoints": {"type": "split_screen", "layout": "vertical_split", "splitPosition": 960, "leftPanel": {"header": "OOP GROUNDING", "headerColor": "#4A90D9", "content": "oop_code", "pathLabel": "Path A: OOP codebase grounding", "thematicRole": "object_oriented_style"}, "rightPanel": {"header": "FUNCTIONAL GROUNDING", "headerColor": "#4ADE80", "content": "functional_code", "pathLabel": "Path B: Functional codebase grounding", "thematicRole": "functional_style"}, "sharedHeader": "Same prompt. Same tests. Different grounding.", "backgroundColor": "#0A0F1A", "narrationSegments": ["part3_mold_has_three_parts_024", "part3_mold_has_three_parts_025"]}, "mediaAliases": {}, "overlayConfig": null, "renderMode": "component"},
  "part3_mold_has_three_parts:18_grounding_feedback_loop": {"specBaseName": "18_grounding_feedback_loop", "dataPoints": {"type": "animated_diagram", "diagramId": "grounding_feedback_loop", "flow": [{"id": "success", "type": "code_module", "status": "passed", "color": "#4ADE80"}, {"id": "database", "type": "grounding_database", "color": "#A78BFA"}, {"id": "future", "type": "future_generation", "color": "#A78BFA"}], "feedbackArrow": "success → database → future", "backgroundColor": "#0A0F1A", "narrationSegments": ["part3_mold_has_three_parts_025"]}, "mediaAliases": {}, "overlayConfig": null, "renderMode": "component"},
  "part3_mold_has_three_parts:19_three_components_assembly": {"specBaseName": "19_three_components_assembly", "dataPoints": {"type": "animated_diagram", "diagramId": "three_components_assembly", "pipeline": [{"stage": "prompt", "label": "intent", "color": "#2DD4BF"}, {"stage": "grounding", "label": "styled", "color": "#A78BFA"}, {"stage": "walls", "label": "constrained", "color": "#D9944A"}, {"stage": "output", "label": "code", "color": "#E2E8F0"}], "statement": "Prompt + Tests + Grounding. Intent + Constraints + Style.", "backgroundColor": "#0A0F1A", "narrationSegments": ["part3_mold_has_three_parts_026"]}, "mediaAliases": {}, "overlayConfig": null, "renderMode": "component"},
  "part3_mold_has_three_parts:20_three_components_table": {"specBaseName": "20_three_components_table", "dataPoints": {"type": "animated_diagram", "diagramId": "three_components_table", "table": {"columns": ["Component", "Encodes", "Owner"], "rows": [{"component": "Prompt", "encodes": "WHAT (intent)", "owner": "Developer", "color": "#2DD4BF"}, {"component": "Grounding", "encodes": "HOW (style)", "owner": "Automatic", "color": "#A78BFA"}, {"component": "Tests", "encodes": "CORRECTNESS", "owner": "Accumulated", "color": "#D9944A"}]}, "priorityRule": "When these conflict, tests win. Always.", "hierarchy": ["Tests", "Prompt", "Grounding"], "backgroundColor": "#0A0F1A", "narrationSegments": ["part3_mold_has_three_parts_027"]}, "mediaAliases": {}, "overlayConfig": null, "renderMode": "component"},
  "part3_mold_has_three_parts:21_code_output_finale": {"specBaseName": "21_code_output_finale", "dataPoints": {"type": "animated_diagram", "diagramId": "code_output_finale", "elements": {"code": {"role": "output", "finalOpacity": 0.15}, "mold": {"role": "source_of_truth", "colors": ["#2DD4BF", "#D9944A", "#A78BFA"], "pulsing": true}}, "statement": "The code is output. The mold is what matters.", "backgroundColor": "#0A0F1A", "narrationSegments": ["part3_mold_has_three_parts_028"]}, "mediaAliases": {}, "overlayConfig": null, "renderMode": "component"},
  "part4_precision_tradeoff:01_section_title_card": {"specBaseName": "01_section_title_card", "dataPoints": {"type": "title_card", "sectionNumber": 4, "sectionLabel": "PART 4", "titleLine1": "THE PRECISION", "titleLine2": "TRADEOFF", "backgroundColor": "#0A0F1A", "ghostElements": [{"shape": "dot_matrix_grid", "color": "#F59E0B", "role": "3d_printing_precision"}, {"shape": "mold_flow_walls", "color": "#2DD4BF", "role": "injection_molding_walls"}], "narrationSegments": ["part4_precision_tradeoff_001"]}, "mediaAliases": {}, "overlayConfig": {"fadeOutFrames": 39}, "renderMode": "component"},
  "part4_precision_tradeoff:02_printer_vs_mold_split": {"specBaseName": "02_printer_vs_mold_split", "dataPoints": {"type": "split_screen", "layout": "vertical_split", "splitPosition": 960, "leftPanel": {"header": "3D PRINTING", "headerColor": "#F59E0B", "content": "coordinate_grid_with_nozzle_path", "pointCount": 2847, "caption": "Every point must be defined.", "thematicRole": "exhaustive_specification"}, "rightPanel": {"header": "INJECTION MOLDING", "headerColor": "#2DD4BF", "content": "mold_walls_with_liquid_flow", "wallCount": 6, "liquidCurves": 10, "caption": "The walls do the precision work.", "thematicRole": "wall_based_precision"}, "backgroundColor": "#0A0F1A", "narrationSegments": ["part4_precision_tradeoff_002", "part4_precision_tradeoff_003", "part4_precision_tradeoff_004"]}, "mediaAliases": {}, "overlayConfig": null, "renderMode": "component"},
  "part4_precision_tradeoff:03_precision_tradeoff_curve": {"specBaseName": "03_precision_tradeoff_curve", "dataPoints": {"type": "animated_chart", "chartType": "inverse_curve", "axes": {"x": {"label": "Number of Tests", "range": [0, 100], "unit": "count"}, "y": {"label": "Required Prompt Precision", "range": [0, 100], "unit": "percent"}}, "curve": {"function": "y = 200 + 600 * exp(-0.04 * x)", "color": "#A78BFA", "interpretation": "inverse_relationship"}, "regions": [{"position": "above_curve", "label": "Prompt does the work", "color": "#F59E0B"}, {"position": "below_curve", "label": "Tests do the work", "color": "#2DD4BF"}], "callouts": [{"position": "left", "label": "Few tests → detailed prompt", "promptLines": 5}, {"position": "right", "label": "Many tests → minimal prompt", "promptLines": 2, "testCount": 6}], "backgroundColor": "#0A0F1A", "narrationSegments": ["part4_precision_tradeoff_005", "part4_precision_tradeoff_006"]}, "mediaAliases": {}, "overlayConfig": {"fadeInFrames": 60}, "renderMode": "component"},
  "part4_precision_tradeoff:04_prompt_detail_comparison": {"specBaseName": "04_prompt_detail_comparison", "dataPoints": {"type": "split_screen", "layout": "vertical_split", "splitPosition": 960, "leftPanel": {"header": "DETAILED PROMPT", "headerColor": "#F59E0B", "filename": "parser_v1.prompt", "lineCount": 50, "testCount": 3, "thematicRole": "verbose_specification"}, "rightPanel": {"header": "MINIMAL PROMPT", "headerColor": "#2DD4BF", "filename": "parser_v2.prompt", "lineCount": 10, "testCount": 47, "thematicRole": "test_driven_specification"}, "outcome": {"both_correct": true, "promptReduction": "5×", "summary": "Same result. 5× less prompt."}, "backgroundColor": "#0A0F1A", "narrationSegments": ["part4_precision_tradeoff_007", "part4_precision_tradeoff_008"]}, "mediaAliases": {"leftSrc": "veo/developer_prompt_shift.mp4", "defaultSrc": "veo/developer_prompt_shift.mp4", "rightSrc": "veo/developer_prompt_shift.mp4", "backgroundSrc": "veo/developer_prompt_shift.mp4", "outputSrc": "veo/developer_prompt_shift.mp4", "baseSrc": "veo/developer_prompt_shift.mp4"}, "overlayConfig": null, "renderMode": "component"},
  "part4_precision_tradeoff:05_walls_precision_callout": {"specBaseName": "05_walls_precision_callout", "dataPoints": {"type": "kinetic_typography", "primaryText": ["More tests,", "less prompt."], "secondaryText": "The walls do the precision work.", "visualElements": {"testWalls": {"count": 8, "color": "#2DD4BF"}, "promptDocument": {"initialLines": 12, "finalLines": 3, "color": "#F59E0B"}, "checkmark": {"color": "#22C55E"}}, "backgroundColor": "#0A0F1A", "narrationSegments": ["part4_precision_tradeoff_008"]}, "mediaAliases": {}, "overlayConfig": null, "renderMode": "component"},
  "part4_precision_tradeoff:06_embedded_code_document": {"specBaseName": "06_embedded_code_document", "dataPoints": {"type": "document_visualization", "document": {"width": 720, "height": 700, "sections": [{"type": "natural_language", "lines": 8, "topic": "parser_requirements"}, {"type": "natural_language", "lines": 6, "topic": "edge_cases"}, {"type": "code_block", "lines": 5, "language": "python", "topic": "token_validation"}, {"type": "natural_language", "lines": 6, "topic": "error_handling"}]}, "annotations": [{"target": "natural_language", "label": "Architecture, intent, constraints", "color": "#A78BFA"}, {"target": "code_block", "label": "Precision where it matters", "color": "#2DD4BF"}], "labels": ["The boundary between prompt and code is fluid.", "Stay in prompt space. Dip into code when you must."], "backgroundColor": "#0A0F1A", "narrationSegments": ["part4_precision_tradeoff_009"]}, "mediaAliases": {}, "overlayConfig": null, "renderMode": "component"},
  "part5_compound_returns:01_section_title_card": {"specBaseName": "01_section_title_card", "dataPoints": {"type": "title_card", "sectionLabel": "PART 5", "title": "Compound Returns", "accentStyle": "exponential_curve", "accentColor": "#D9944A", "backgroundColor": "#0A0F1A", "durationSeconds": 8, "narrationSegments": ["part5_compound_returns_001"]}, "mediaAliases": {}, "overlayConfig": {"fadeOutFrames": 30}, "renderMode": "component"},
  "part5_compound_returns:02_maintenance_pie_chart": {"specBaseName": "02_maintenance_pie_chart", "dataPoints": {"type": "animated_pie_chart", "center": [960, 460], "radius": 280, "wedges": [{"id": "initial_development", "label": "Initial Development", "value": "10-20%", "midpointPct": 15, "color": "#4A90D9", "sweepAngle": 54}, {"id": "maintenance", "label": "Maintenance", "value": "80-90%", "midpointPct": 85, "color": "#D9944A", "sweepAngle": 306}], "citations": ["McKinsey: +40% maintenance overhead from tech debt", "Stripe: 33% of dev week on debt"], "narrationSegments": ["part5_compound_returns_002"]}, "mediaAliases": {}, "overlayConfig": {"fadeInFrames": 90}, "renderMode": "component"},
  "part5_compound_returns:03_compound_debt_curve": {"specBaseName": "03_compound_debt_curve", "dataPoints": {"type": "animated_line_chart", "morphFrom": "maintenance_pie_chart", "xAxis": {"label": "Time (years)", "range": [0, 10]}, "yAxis": {"label": "Cumulative Cost", "range": [0, 100]}, "series": [{"id": "debt_curve", "label": "Debt × (1 + Rate)^Time", "color": "#D9944A", "formula": "C₀ × (1 + 0.3)^t", "data": [[0, 1], [1, 1.3], [2, 1.7], [3, 2.2], [4, 2.9], [5, 3.7], [6, 4.8], [7, 6.3], [8, 8.2], [9, 10.6], [10, 13.8]]}, {"id": "regeneration_line", "label": "Regeneration cost (resets each cycle)", "color": "#4A90D9", "style": "dashed", "data": [[0, 1], [2, 1.1], [4, 1.0], [6, 1.1], [8, 1.0], [10, 1.1]]}], "callout": {"value": "$1.52 trillion / year", "source": "US technical debt — CISQ", "anchorPoint": [8, 8.2]}, "narrationSegments": ["part5_compound_returns_003"]}, "mediaAliases": {}, "overlayConfig": null, "renderMode": "component"},
  "part5_compound_returns:04_diverging_cost_curves": {"specBaseName": "04_diverging_cost_curves", "dataPoints": {"type": "diverging_line_chart", "xAxis": {"label": "Years", "range": [0, 10]}, "yAxis": {"label": "Cumulative Cost", "range": [0, 100]}, "series": [{"id": "patching_curve", "label": "Patching", "color": "#D9944A", "style": "solid", "data": [[0, 2], [1, 3], [2, 4.5], [3, 7], [4, 11], [5, 17], [6, 26], [7, 39], [8, 55], [9, 72], [10, 90]]}, {"id": "pdd_curve", "label": "PDD", "color": "#4A90D9", "style": "solid", "data": [[0, 2], [1, 3.5], [1.5, 2.2], [3, 3.8], [3.5, 2.3], [5, 3.9], [5.5, 2.2], [7, 3.7], [7.5, 2.1], [9, 3.6], [10, 4.0]]}], "annotations": [{"text": "Each patch adds debt", "anchorYear": 6, "target": "patching_curve"}, {"text": "Each test constrains forever", "anchorYear": 6, "target": "pdd_curve"}], "impactText": "Over time, it's everything.", "narrationSegments": ["part5_compound_returns_004", "part5_compound_returns_005", "part5_compound_returns_006"]}, "mediaAliases": {}, "overlayConfig": {"fadeInFrames": 45}, "renderMode": "component"},
  "part5_compound_returns:05_investment_comparison_table": {"specBaseName": "05_investment_comparison_table", "dataPoints": {"type": "comparison_table", "columns": [{"id": "investment", "label": "Investment", "color": "#64748B"}, {"id": "patching", "label": "Patching", "color": "#D9944A"}, {"id": "pdd", "label": "PDD", "color": "#4A90D9"}], "rows": [{"investment": "Fix a bug", "patching": "One place, once", "pdd": "Impossible forever"}, {"investment": "Improve code", "patching": "One version", "pdd": "All future versions"}, {"investment": "Document intent", "patching": "One snapshot", "pdd": "Living specification"}], "narrationSegments": ["part5_compound_returns_006"]}, "mediaAliases": {}, "overlayConfig": null, "renderMode": "component"},
  "part5_compound_returns:08_economics_crossing_callback": {"specBaseName": "08_economics_crossing_callback", "dataPoints": {"type": "callback_chart", "referencesSpec": "part1_economics/02_sock_price_chart", "crossingPoint": {"x": 1962, "y": 0.85}, "pulseEffect": {"rings": 3, "maxRadius": 100, "color": "#D9944A", "cycleDuration": 90}, "newLabel": "The economics changed.", "narrationSegments": ["part5_compound_returns_009"]}, "mediaAliases": {}, "overlayConfig": null, "renderMode": "component"},
  "part5_compound_returns:09_contrarian_quote_card": {"specBaseName": "09_contrarian_quote_card", "dataPoints": {"type": "quote_card", "quote": "This is either the way of the future or it's going to crash and burn spectacularly.", "attribution": "Research engineer, after seeing PDD for the first time", "quoteFont": "Georgia", "quoteSize": 36, "accentColor": "#D9944A", "backgroundColor": "#0A0F1A", "durationSeconds": 18, "narrationSegments": ["part5_compound_returns_010"]}, "mediaAliases": {}, "overlayConfig": {"fadeOutFrames": 90}, "renderMode": "component"},
  "where_to_start:01_section_title_card": {"specBaseName": "01_section_title_card", "dataPoints": {"type": "title_card", "sectionNumber": 6, "sectionLabel": "PART 6", "titleLine1": "WHERE TO", "titleLine2": "START", "backgroundColor": "#0A0F1A", "ghostElements": [{"shape": "module_grid", "rows": 4, "cols": 6, "highlightIndex": 13, "highlightColor": "#4A90D9"}], "narrationSegments": ["where_to_start_001"]}, "mediaAliases": {}, "overlayConfig": null, "renderMode": "component"},
  "where_to_start:02_legacy_codebase_reveal": {"specBaseName": "02_legacy_codebase_reveal", "dataPoints": {"type": "code_wall", "layout": "stacked_panes", "paneCount": 3, "dangerComments": [{"pane": 1, "line": 12, "text": "// don't touch", "glowFrame": 30}, {"pane": 1, "line": 28, "text": "// here be dragons", "glowFrame": 60}, {"pane": 2, "line": 8, "text": "// TODO: refactor this someday", "glowFrame": 100}, {"pane": 2, "line": 22, "text": "// nobody knows why this works", "glowFrame": 115}, {"pane": 3, "line": 15, "text": "// legacy — do not modify", "glowFrame": 140}], "scrollRate": 0.5, "narrationSegments": ["where_to_start_001"]}, "mediaAliases": {}, "overlayConfig": null, "renderMode": "component"},
  "where_to_start:05_module_glow_spread": {"specBaseName": "05_module_glow_spread", "dataPoints": {"type": "progressive_migration", "grid": {"cols": 5, "rows": 4, "totalModules": 20}, "conversionOrder": [{"id": "auth_handler", "label": "auth_handler.py", "col": 2, "row": 1, "frame": 0, "preConverted": true}, {"id": "user_model", "label": "user_model.py", "col": 4, "row": 0, "frame": 30}, {"id": "payment_processor", "label": "payment_processor.py", "col": 1, "row": 2, "frame": 70}, {"id": "api_routes", "label": "api_routes.py", "col": 3, "row": 3, "frame": 110}, {"id": "email_service", "label": "email_service.py", "col": 0, "row": 1, "frame": 150}, {"id": "config_loader", "label": "config_loader.py", "col": 4, "row": 3, "frame": 170}, {"id": "search_index", "label": "search_index.py", "col": 2, "row": 0, "frame": 190}, {"id": "notification_hub", "label": "notification_hub.py", "col": 0, "row": 3, "frame": 210}], "unconverted": ["db_connection.py", "cache_manager.py", "logger.py", "middleware.py", "rate_limiter.py", "session_store.py", "file_upload.py", "webhook_handler.py", "scheduler.py", "analytics.py", "admin_panel.py", "test_runner.py"], "counterSteps": [1, 2, 3, 4, 5, 6, 7, 8], "narrationSegments": ["where_to_start_002"]}, "mediaAliases": {}, "overlayConfig": null, "renderMode": "component"},
  "where_to_start:06_no_big_bang_callout": {"specBaseName": "06_no_big_bang_callout", "dataPoints": {"type": "text_manifesto", "statements": [{"text": "No big bang.", "frame": 20, "style": "bold"}, {"text": "No rewrite.", "frame": 50, "style": "bold"}, {"text": "Just a gradual migration of where value lives.", "frame": 80, "highlight": "value"}], "migrationBar": {"from": "code", "to": "specification", "startSplit": 0.2, "endSplit": 0.5, "leftColor": "#475569", "rightColor": "#8B5CF6"}, "narrationSegments": ["where_to_start_002"]}, "mediaAliases": {}, "overlayConfig": null, "renderMode": "component"},
  "where_to_start:07_economics_callback": {"specBaseName": "07_economics_callback", "dataPoints": {"type": "metaphor_callback", "comparison": {"left": {"label": "patch it?", "icon": "holey_sock", "color": "#D9944A", "status": "deprecated"}, "right": {"label": "replace it.", "icon": "fresh_sock", "color": "#10B981", "status": "preferred"}}, "closingStatements": ["You don't patch socks because socks got cheap.", "The economics made patching irrational."], "narrationSegments": ["where_to_start_003"]}, "mediaAliases": {}, "overlayConfig": null, "renderMode": "component"},
  "closing:03_pdd_bug_fix_terminal": {"specBaseName": "03_pdd_bug_fix_terminal", "dataPoints": {"type": "terminal_animation", "commands": [{"cmd": "pdd bug email_validator", "output": "Test added: test_rejects_unicode_homoglyphs"}, {"cmd": "pdd fix email_validator", "output": "Regenerating... ✓ All tests pass"}], "terminalBg": "#111827", "backgroundColor": "#0A0F1A", "successColor": "#22C55E", "durationSeconds": 5, "narrationSegments": ["closing_001", "closing_002"]}, "mediaAliases": {}, "overlayConfig": null, "renderMode": "component"},
  "closing:04_pdd_triangle": {"specBaseName": "04_pdd_triangle", "dataPoints": {"type": "triangle_diagram", "vertices": [{"label": "PROMPT", "subtitle": "encode intent", "color": "#4A90D9", "position": [960, 200]}, {"label": "TESTS", "subtitle": "preserve behavior", "color": "#D9944A", "position": [520, 720]}, {"label": "GROUNDING", "subtitle": "maintain style", "color": "#5AAA6E", "position": [1400, 720]}], "edgeColor": "#334155", "centerCode": true, "backgroundColor": "#0A0F1A", "durationSeconds": 5, "narrationSegments": ["closing_002"]}, "mediaAliases": {}, "overlayConfig": null, "renderMode": "component"},
  "closing:05_dissolve_regenerate_loop": {"specBaseName": "05_dissolve_regenerate_loop", "dataPoints": {"type": "dissolve_regenerate_loop", "cycles": 2, "codeVariations": 2, "trianglePersists": true, "triangleOpacity": 0.3, "particleCount": "2-3 per character", "backgroundColor": "#0A0F1A", "successColor": "#22C55E", "durationSeconds": 5, "narrationSegments": ["closing_003"]}, "mediaAliases": {}, "overlayConfig": null, "renderMode": "component"},
  "closing:06_mold_glow_finale": {"specBaseName": "06_mold_glow_finale", "dataPoints": {"type": "mold_glow_diagram", "vertices": [{"label": "PROMPT", "color": "#4A90D9", "glowRadius": 20}, {"label": "TESTS", "color": "#D9944A", "glowRadius": 20}, {"label": "GROUNDING", "color": "#5AAA6E", "glowRadius": 20}], "codeOpacity": 0.2, "moldOverlay": true, "backgroundColor": "#0A0F1A", "durationSeconds": 4, "narrationSegments": ["closing_004"]}, "mediaAliases": {}, "overlayConfig": null, "renderMode": "component"},
  "closing:07_the_beat": {"specBaseName": "07_the_beat", "dataPoints": {"type": "dramatic_beat", "content": "empty", "backgroundFrom": "#0A0F1A", "backgroundTo": "#050810", "durationSeconds": 2, "narrationSegments": ["closing_005"]}, "mediaAliases": {}, "overlayConfig": null, "renderMode": "component"},
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
      <GeneratedContractVisual />
    </VisualMediaProvider>
  </VisualContractProvider>
);
const ColdOpen07CodeRegenerationPreview: React.FC = () => (
  <VisualContractProvider contract={PREVIEW_VISUAL_CONTRACTS["cold_open:08_code_regeneration"] ?? null}>
    <VisualMediaProvider media={PREVIEW_VISUAL_MEDIA["cold_open:08_code_regeneration"] ?? null}>
      <ColdOpen07CodeRegeneration />
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
const ColdOpen01SplitScreenHookPreview: React.FC = () => (
  <VisualContractProvider contract={PREVIEW_VISUAL_CONTRACTS["cold_open:01_split_screen_hook"] ?? null}>
    <VisualMediaProvider media={PREVIEW_VISUAL_MEDIA["cold_open:01_split_screen_hook"] ?? null}>
      <ColdOpen01SplitScreenHook />
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
const Part1Economics09CrossingLinesMomentPreview: React.FC = () => (
  <VisualContractProvider contract={PREVIEW_VISUAL_CONTRACTS["part1_economics:10_crossing_lines_moment"] ?? null}>
    <VisualMediaProvider media={PREVIEW_VISUAL_MEDIA["part1_economics:10_crossing_lines_moment"] ?? null}>
      <Part1Economics09CrossingLinesMoment />
    </VisualMediaProvider>
  </VisualContractProvider>
);
const Part1Economics11DeveloperDarningSplitPreview: React.FC = () => (
  <VisualContractProvider contract={PREVIEW_VISUAL_CONTRACTS["part1_economics:11_developer_darning_split"] ?? null}>
    <VisualMediaProvider media={PREVIEW_VISUAL_MEDIA["part1_economics:11_developer_darning_split"] ?? null}>
      <GeneratedContractVisual />
    </VisualMediaProvider>
  </VisualContractProvider>
);
const Part1Economics14KeyInsightStillnessPreview: React.FC = () => (
  <VisualContractProvider contract={PREVIEW_VISUAL_CONTRACTS["part1_economics:14_key_insight_stillness"] ?? null}>
    <VisualMediaProvider media={PREVIEW_VISUAL_MEDIA["part1_economics:14_key_insight_stillness"] ?? null}>
      <GeneratedContractVisual />
    </VisualMediaProvider>
  </VisualContractProvider>
);
const Part1Economics16TryItYourselfPreview: React.FC = () => (
  <VisualContractProvider contract={PREVIEW_VISUAL_CONTRACTS["part1_economics:16_try_it_yourself"] ?? null}>
    <VisualMediaProvider media={PREVIEW_VISUAL_MEDIA["part1_economics:16_try_it_yourself"] ?? null}>
      <GeneratedContractVisual />
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
      <GeneratedContractVisual />
    </VisualMediaProvider>
  </VisualContractProvider>
);
const Part2ParadigmShift06SplitCraftsmanVsMoldPreview: React.FC = () => (
  <VisualContractProvider contract={PREVIEW_VISUAL_CONTRACTS["part2_paradigm_shift:06_split_craftsman_vs_mold"] ?? null}>
    <VisualMediaProvider media={PREVIEW_VISUAL_MEDIA["part2_paradigm_shift:06_split_craftsman_vs_mold"] ?? null}>
      <GeneratedContractVisual />
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
const Part2ParadigmShift13BillionGateUnreviewablePreview: React.FC = () => (
  <VisualContractProvider contract={PREVIEW_VISUAL_CONTRACTS["part2_paradigm_shift:13_billion_gate_unreviewable"] ?? null}>
    <VisualMediaProvider media={PREVIEW_VISUAL_MEDIA["part2_paradigm_shift:13_billion_gate_unreviewable"] ?? null}>
      <GeneratedContractVisual />
    </VisualMediaProvider>
  </VisualContractProvider>
);
const Part3MoldHasThreeParts01SectionTitleCardPreview: React.FC = () => (
  <VisualContractProvider contract={PREVIEW_VISUAL_CONTRACTS["part3_mold_has_three_parts:01_section_title_card"] ?? null}>
    <VisualMediaProvider media={PREVIEW_VISUAL_MEDIA["part3_mold_has_three_parts:01_section_title_card"] ?? null}>
      <GeneratedContractVisual />
    </VisualMediaProvider>
  </VisualContractProvider>
);
const Part3MoldHasThreeParts02MoldCrossSectionPreview: React.FC = () => (
  <VisualContractProvider contract={PREVIEW_VISUAL_CONTRACTS["part3_mold_has_three_parts:02_mold_cross_section"] ?? null}>
    <VisualMediaProvider media={PREVIEW_VISUAL_MEDIA["part3_mold_has_three_parts:02_mold_cross_section"] ?? null}>
      <GeneratedContractVisual />
    </VisualMediaProvider>
  </VisualContractProvider>
);
const Part3MoldHasThreeParts03TestWallsIlluminatePreview: React.FC = () => (
  <VisualContractProvider contract={PREVIEW_VISUAL_CONTRACTS["part3_mold_has_three_parts:03_test_walls_illuminate"] ?? null}>
    <VisualMediaProvider media={PREVIEW_VISUAL_MEDIA["part3_mold_has_three_parts:03_test_walls_illuminate"] ?? null}>
      <GeneratedContractVisual />
    </VisualMediaProvider>
  </VisualContractProvider>
);
const Part3MoldHasThreeParts05ResearchAnnotationsPreview: React.FC = () => (
  <VisualContractProvider contract={PREVIEW_VISUAL_CONTRACTS["part3_mold_has_three_parts:05_research_annotations"] ?? null}>
    <VisualMediaProvider media={PREVIEW_VISUAL_MEDIA["part3_mold_has_three_parts:05_research_annotations"] ?? null}>
      <GeneratedContractVisual />
    </VisualMediaProvider>
  </VisualContractProvider>
);
const Part3MoldHasThreeParts06BugAddWallPreview: React.FC = () => (
  <VisualContractProvider contract={PREVIEW_VISUAL_CONTRACTS["part3_mold_has_three_parts:06_bug_add_wall"] ?? null}>
    <VisualMediaProvider media={PREVIEW_VISUAL_MEDIA["part3_mold_has_three_parts:06_bug_add_wall"] ?? null}>
      <GeneratedContractVisual />
    </VisualMediaProvider>
  </VisualContractProvider>
);
const Part3MoldHasThreeParts07RatchetTimelapsePreview: React.FC = () => (
  <VisualContractProvider contract={PREVIEW_VISUAL_CONTRACTS["part3_mold_has_three_parts:07_ratchet_timelapse"] ?? null}>
    <VisualMediaProvider media={PREVIEW_VISUAL_MEDIA["part3_mold_has_three_parts:07_ratchet_timelapse"] ?? null}>
      <GeneratedContractVisual />
    </VisualMediaProvider>
  </VisualContractProvider>
);
const Part3MoldHasThreeParts08TraditionalVsPddSplitPreview: React.FC = () => (
  <VisualContractProvider contract={PREVIEW_VISUAL_CONTRACTS["part3_mold_has_three_parts:08_traditional_vs_pdd_split"] ?? null}>
    <VisualMediaProvider media={PREVIEW_VISUAL_MEDIA["part3_mold_has_three_parts:08_traditional_vs_pdd_split"] ?? null}>
      <GeneratedContractVisual />
    </VisualMediaProvider>
  </VisualContractProvider>
);
const Part3MoldHasThreeParts09BugForkDiagramPreview: React.FC = () => (
  <VisualContractProvider contract={PREVIEW_VISUAL_CONTRACTS["part3_mold_has_three_parts:09_bug_fork_diagram"] ?? null}>
    <VisualMediaProvider media={PREVIEW_VISUAL_MEDIA["part3_mold_has_three_parts:09_bug_fork_diagram"] ?? null}>
      <GeneratedContractVisual />
    </VisualMediaProvider>
  </VisualContractProvider>
);
const Part3MoldHasThreeParts10FiveGenerationsPreview: React.FC = () => (
  <VisualContractProvider contract={PREVIEW_VISUAL_CONTRACTS["part3_mold_has_three_parts:10_five_generations"] ?? null}>
    <VisualMediaProvider media={PREVIEW_VISUAL_MEDIA["part3_mold_has_three_parts:10_five_generations"] ?? null}>
      <GeneratedContractVisual />
    </VisualMediaProvider>
  </VisualContractProvider>
);
const Part3MoldHasThreeParts11Z3FormalProofPreview: React.FC = () => (
  <VisualContractProvider contract={PREVIEW_VISUAL_CONTRACTS["part3_mold_has_three_parts:11_z3_formal_proof"] ?? null}>
    <VisualMediaProvider media={PREVIEW_VISUAL_MEDIA["part3_mold_has_three_parts:11_z3_formal_proof"] ?? null}>
      <GeneratedContractVisual />
    </VisualMediaProvider>
  </VisualContractProvider>
);
const Part3MoldHasThreeParts12ModuleLevelAsidePreview: React.FC = () => (
  <VisualContractProvider contract={PREVIEW_VISUAL_CONTRACTS["part3_mold_has_three_parts:12_module_level_aside"] ?? null}>
    <VisualMediaProvider media={PREVIEW_VISUAL_MEDIA["part3_mold_has_three_parts:12_module_level_aside"] ?? null}>
      <GeneratedContractVisual />
    </VisualMediaProvider>
  </VisualContractProvider>
);
const Part3MoldHasThreeParts13PromptNozzlePreview: React.FC = () => (
  <VisualContractProvider contract={PREVIEW_VISUAL_CONTRACTS["part3_mold_has_three_parts:13_prompt_nozzle"] ?? null}>
    <VisualMediaProvider media={PREVIEW_VISUAL_MEDIA["part3_mold_has_three_parts:13_prompt_nozzle"] ?? null}>
      <GeneratedContractVisual />
    </VisualMediaProvider>
  </VisualContractProvider>
);
const Part3MoldHasThreeParts14PromptRatioPreview: React.FC = () => (
  <VisualContractProvider contract={PREVIEW_VISUAL_CONTRACTS["part3_mold_has_three_parts:14_prompt_ratio"] ?? null}>
    <VisualMediaProvider media={PREVIEW_VISUAL_MEDIA["part3_mold_has_three_parts:14_prompt_ratio"] ?? null}>
      <GeneratedContractVisual />
    </VisualMediaProvider>
  </VisualContractProvider>
);
const Part3MoldHasThreeParts15ContextWindowComparisonPreview: React.FC = () => (
  <VisualContractProvider contract={PREVIEW_VISUAL_CONTRACTS["part3_mold_has_three_parts:15_context_window_comparison"] ?? null}>
    <VisualMediaProvider media={PREVIEW_VISUAL_MEDIA["part3_mold_has_three_parts:15_context_window_comparison"] ?? null}>
      <GeneratedContractVisual />
    </VisualMediaProvider>
  </VisualContractProvider>
);
const Part3MoldHasThreeParts17GroundingStylesSplitPreview: React.FC = () => (
  <VisualContractProvider contract={PREVIEW_VISUAL_CONTRACTS["part3_mold_has_three_parts:17_grounding_styles_split"] ?? null}>
    <VisualMediaProvider media={PREVIEW_VISUAL_MEDIA["part3_mold_has_three_parts:17_grounding_styles_split"] ?? null}>
      <GeneratedContractVisual />
    </VisualMediaProvider>
  </VisualContractProvider>
);
const Part3MoldHasThreeParts18GroundingFeedbackLoopPreview: React.FC = () => (
  <VisualContractProvider contract={PREVIEW_VISUAL_CONTRACTS["part3_mold_has_three_parts:18_grounding_feedback_loop"] ?? null}>
    <VisualMediaProvider media={PREVIEW_VISUAL_MEDIA["part3_mold_has_three_parts:18_grounding_feedback_loop"] ?? null}>
      <GeneratedContractVisual />
    </VisualMediaProvider>
  </VisualContractProvider>
);
const Part3MoldHasThreeParts19ThreeComponentsAssemblyPreview: React.FC = () => (
  <VisualContractProvider contract={PREVIEW_VISUAL_CONTRACTS["part3_mold_has_three_parts:19_three_components_assembly"] ?? null}>
    <VisualMediaProvider media={PREVIEW_VISUAL_MEDIA["part3_mold_has_three_parts:19_three_components_assembly"] ?? null}>
      <GeneratedContractVisual />
    </VisualMediaProvider>
  </VisualContractProvider>
);
const Part3MoldHasThreeParts20ThreeComponentsTablePreview: React.FC = () => (
  <VisualContractProvider contract={PREVIEW_VISUAL_CONTRACTS["part3_mold_has_three_parts:20_three_components_table"] ?? null}>
    <VisualMediaProvider media={PREVIEW_VISUAL_MEDIA["part3_mold_has_three_parts:20_three_components_table"] ?? null}>
      <GeneratedContractVisual />
    </VisualMediaProvider>
  </VisualContractProvider>
);
const Part3MoldHasThreeParts21CodeOutputFinalePreview: React.FC = () => (
  <VisualContractProvider contract={PREVIEW_VISUAL_CONTRACTS["part3_mold_has_three_parts:21_code_output_finale"] ?? null}>
    <VisualMediaProvider media={PREVIEW_VISUAL_MEDIA["part3_mold_has_three_parts:21_code_output_finale"] ?? null}>
      <GeneratedContractVisual />
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
const Part4PrecisionTradeoff02PrinterVsMoldSplitPreview: React.FC = () => (
  <VisualContractProvider contract={PREVIEW_VISUAL_CONTRACTS["part4_precision_tradeoff:02_printer_vs_mold_split"] ?? null}>
    <VisualMediaProvider media={PREVIEW_VISUAL_MEDIA["part4_precision_tradeoff:02_printer_vs_mold_split"] ?? null}>
      <GeneratedContractVisual />
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
const Part4PrecisionTradeoff04PromptDetailComparisonPreview: React.FC = () => (
  <VisualContractProvider contract={PREVIEW_VISUAL_CONTRACTS["part4_precision_tradeoff:04_prompt_detail_comparison"] ?? null}>
    <VisualMediaProvider media={PREVIEW_VISUAL_MEDIA["part4_precision_tradeoff:04_prompt_detail_comparison"] ?? null}>
      <GeneratedContractVisual />
    </VisualMediaProvider>
  </VisualContractProvider>
);
const Part4PrecisionTradeoff05WallsPrecisionCalloutPreview: React.FC = () => (
  <VisualContractProvider contract={PREVIEW_VISUAL_CONTRACTS["part4_precision_tradeoff:05_walls_precision_callout"] ?? null}>
    <VisualMediaProvider media={PREVIEW_VISUAL_MEDIA["part4_precision_tradeoff:05_walls_precision_callout"] ?? null}>
      <GeneratedContractVisual />
    </VisualMediaProvider>
  </VisualContractProvider>
);
const Part4PrecisionTradeoff07EmbeddedCodeDocumentPreview: React.FC = () => (
  <VisualContractProvider contract={PREVIEW_VISUAL_CONTRACTS["part4_precision_tradeoff:06_embedded_code_document"] ?? null}>
    <VisualMediaProvider media={PREVIEW_VISUAL_MEDIA["part4_precision_tradeoff:06_embedded_code_document"] ?? null}>
      <Part4PrecisionTradeoff07EmbeddedCodeDocument />
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
const Part5CompoundReturns07EconomicsCrossingCallbackPreview: React.FC = () => (
  <VisualContractProvider contract={PREVIEW_VISUAL_CONTRACTS["part5_compound_returns:08_economics_crossing_callback"] ?? null}>
    <VisualMediaProvider media={PREVIEW_VISUAL_MEDIA["part5_compound_returns:08_economics_crossing_callback"] ?? null}>
      <Part5CompoundReturns07EconomicsCrossingCallback />
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
const Closing03PddBugFixTerminalPreview: React.FC = () => (
  <VisualContractProvider contract={PREVIEW_VISUAL_CONTRACTS["closing:03_pdd_bug_fix_terminal"] ?? null}>
    <VisualMediaProvider media={PREVIEW_VISUAL_MEDIA["closing:03_pdd_bug_fix_terminal"] ?? null}>
      <GeneratedContractVisual />
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
        id="Part3MoldHasThreePartsSection"
        component={Part3MoldHasThreePartsSection}
        durationInFrames={1}
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
        id="cold-open01-split-screen-darning"
        component={ColdOpen01SplitScreenDarningPreview}
        durationInFrames={240}
        fps={30}
        width={1920}
        height={1080}
      />
      <Composition
        id="cold-open07-code-cursor-blink"
        component={ColdOpen07CodeCursorBlinkPreview}
        durationInFrames={150}
        fps={30}
        width={1920}
        height={1080}
      />
      <Composition
        id="cold-open08-code-regeneration"
        component={ColdOpen07CodeRegenerationPreview}
        durationInFrames={270}
        fps={30}
        width={1920}
        height={1080}
      />
      <Composition
        id="cold-open09-title-card-pdd"
        component={ColdOpen09TitleCardPddPreview}
        durationInFrames={180}
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
        durationInFrames={720}
        fps={30}
        width={1920}
        height={1080}
      />
      <Composition
        id="part1-economics08-fork-codebase-size"
        component={Part1Economics08ForkCodebaseSizePreview}
        durationInFrames={660}
        fps={30}
        width={1920}
        height={1080}
      />
      <Composition
        id="part1-economics09-patching-vs-regeneration-split"
        component={Part1Economics09PatchingVsRegenerationSplitPreview}
        durationInFrames={780}
        fps={30}
        width={1920}
        height={1080}
      />
      <Composition
        id="part1-economics10-crossing-lines-moment"
        component={Part1Economics09CrossingLinesMomentPreview}
        durationInFrames={750}
        fps={30}
        width={1920}
        height={1080}
      />
      <Composition
        id="part1-economics11-developer-darning-split"
        component={Part1Economics11DeveloperDarningSplitPreview}
        durationInFrames={240}
        fps={30}
        width={1920}
        height={1080}
      />
      <Composition
        id="part1-economics14-key-insight-stillness"
        component={Part1Economics14KeyInsightStillnessPreview}
        durationInFrames={210}
        fps={30}
        width={1920}
        height={1080}
      />
      <Composition
        id="part1-economics16-try-it-yourself"
        component={Part1Economics16TryItYourselfPreview}
        durationInFrames={150}
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
        durationInFrames={330}
        fps={30}
        width={1920}
        height={1080}
      />
      <Composition
        id="part2-paradigm-shift06-split-craftsman-vs-mold"
        component={Part2ParadigmShift06SplitCraftsmanVsMoldPreview}
        durationInFrames={750}
        fps={30}
        width={1920}
        height={1080}
      />
      <Composition
        id="part2-paradigm-shift11-synopsys-pdd-equivalence"
        component={Part2ParadigmShift08SynopsysPddEquivalencePreview}
        durationInFrames={1140}
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
        id="part2-paradigm-shift13-billion-gate-unreviewable"
        component={Part2ParadigmShift13BillionGateUnreviewablePreview}
        durationInFrames={390}
        fps={30}
        width={1920}
        height={1080}
      />
      <Composition
        id="part3-mold-has-three-parts01-section-title-card"
        component={Part3MoldHasThreeParts01SectionTitleCardPreview}
        durationInFrames={420}
        fps={30}
        width={1920}
        height={1080}
      />
      <Composition
        id="part3-mold-has-three-parts02-mold-cross-section"
        component={Part3MoldHasThreeParts02MoldCrossSectionPreview}
        durationInFrames={300}
        fps={30}
        width={1920}
        height={1080}
      />
      <Composition
        id="part3-mold-has-three-parts03-test-walls-illuminate"
        component={Part3MoldHasThreeParts03TestWallsIlluminatePreview}
        durationInFrames={300}
        fps={30}
        width={1920}
        height={1080}
      />
      <Composition
        id="part3-mold-has-three-parts05-research-annotations"
        component={Part3MoldHasThreeParts05ResearchAnnotationsPreview}
        durationInFrames={420}
        fps={30}
        width={1920}
        height={1080}
      />
      <Composition
        id="part3-mold-has-three-parts06-bug-add-wall"
        component={Part3MoldHasThreeParts06BugAddWallPreview}
        durationInFrames={540}
        fps={30}
        width={1920}
        height={1080}
      />
      <Composition
        id="part3-mold-has-three-parts07-ratchet-timelapse"
        component={Part3MoldHasThreeParts07RatchetTimelapsePreview}
        durationInFrames={420}
        fps={30}
        width={1920}
        height={1080}
      />
      <Composition
        id="part3-mold-has-three-parts08-traditional-vs-pdd-split"
        component={Part3MoldHasThreeParts08TraditionalVsPddSplitPreview}
        durationInFrames={360}
        fps={30}
        width={1920}
        height={1080}
      />
      <Composition
        id="part3-mold-has-three-parts09-bug-fork-diagram"
        component={Part3MoldHasThreeParts09BugForkDiagramPreview}
        durationInFrames={420}
        fps={30}
        width={1920}
        height={1080}
      />
      <Composition
        id="part3-mold-has-three-parts10-five-generations"
        component={Part3MoldHasThreeParts10FiveGenerationsPreview}
        durationInFrames={540}
        fps={30}
        width={1920}
        height={1080}
      />
      <Composition
        id="part3-mold-has-three-parts11-z3-formal-proof"
        component={Part3MoldHasThreeParts11Z3FormalProofPreview}
        durationInFrames={600}
        fps={30}
        width={1920}
        height={1080}
      />
      <Composition
        id="part3-mold-has-three-parts12-module-level-aside"
        component={Part3MoldHasThreeParts12ModuleLevelAsidePreview}
        durationInFrames={360}
        fps={30}
        width={1920}
        height={1080}
      />
      <Composition
        id="part3-mold-has-three-parts13-prompt-nozzle"
        component={Part3MoldHasThreeParts13PromptNozzlePreview}
        durationInFrames={540}
        fps={30}
        width={1920}
        height={1080}
      />
      <Composition
        id="part3-mold-has-three-parts14-prompt-ratio"
        component={Part3MoldHasThreeParts14PromptRatioPreview}
        durationInFrames={420}
        fps={30}
        width={1920}
        height={1080}
      />
      <Composition
        id="part3-mold-has-three-parts15-context-window-comparison"
        component={Part3MoldHasThreeParts15ContextWindowComparisonPreview}
        durationInFrames={720}
        fps={30}
        width={1920}
        height={1080}
      />
      <Composition
        id="part3-mold-has-three-parts17-grounding-styles-split"
        component={Part3MoldHasThreeParts17GroundingStylesSplitPreview}
        durationInFrames={420}
        fps={30}
        width={1920}
        height={1080}
      />
      <Composition
        id="part3-mold-has-three-parts18-grounding-feedback-loop"
        component={Part3MoldHasThreeParts18GroundingFeedbackLoopPreview}
        durationInFrames={360}
        fps={30}
        width={1920}
        height={1080}
      />
      <Composition
        id="part3-mold-has-three-parts19-three-components-assembly"
        component={Part3MoldHasThreeParts19ThreeComponentsAssemblyPreview}
        durationInFrames={420}
        fps={30}
        width={1920}
        height={1080}
      />
      <Composition
        id="part3-mold-has-three-parts20-three-components-table"
        component={Part3MoldHasThreeParts20ThreeComponentsTablePreview}
        durationInFrames={480}
        fps={30}
        width={1920}
        height={1080}
      />
      <Composition
        id="part3-mold-has-three-parts21-code-output-finale"
        component={Part3MoldHasThreeParts21CodeOutputFinalePreview}
        durationInFrames={360}
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
        id="part4-precision-tradeoff04-prompt-detail-comparison"
        component={Part4PrecisionTradeoff04PromptDetailComparisonPreview}
        durationInFrames={325}
        fps={30}
        width={1920}
        height={1080}
      />
      <Composition
        id="part4-precision-tradeoff05-walls-precision-callout"
        component={Part4PrecisionTradeoff05WallsPrecisionCalloutPreview}
        durationInFrames={186}
        fps={30}
        width={1920}
        height={1080}
      />
      <Composition
        id="part4-precision-tradeoff06-embedded-code-document"
        component={Part4PrecisionTradeoff07EmbeddedCodeDocumentPreview}
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
        component={Part5CompoundReturns07EconomicsCrossingCallbackPreview}
        durationInFrames={300}
        fps={30}
        width={1920}
        height={1080}
      />
      <Composition
        id="part5-compound-returns09-contrarian-quote-card"
        component={Part5CompoundReturns09ContrarianQuoteCardPreview}
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
        id="where-to-start05-module-glow-spread"
        component={WhereToStart05ModuleGlowSpreadPreview}
        durationInFrames={330}
        fps={30}
        width={1920}
        height={1080}
      />
      <Composition
        id="where-to-start06-no-big-bang-callout"
        component={WhereToStart07NoBigBangCalloutPreview}
        durationInFrames={180}
        fps={30}
        width={1920}
        height={1080}
      />
      <Composition
        id="where-to-start07-economics-callback"
        component={Part5CompoundReturns07EconomicsCrossingCallbackPreview}
        durationInFrames={300}
        fps={30}
        width={1920}
        height={1080}
      />
      <Composition
        id="closing03-pdd-bug-fix-terminal"
        component={Closing03PddBugFixTerminalPreview}
        durationInFrames={150}
        fps={30}
        width={1920}
        height={1080}
      />
      <Composition
        id="closing04-pdd-triangle"
        component={Closing04PddTrianglePreview}
        durationInFrames={150}
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
    </>
  );
};
