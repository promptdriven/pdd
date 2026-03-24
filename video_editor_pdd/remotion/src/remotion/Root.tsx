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
import { ColdOpen07PddTitleCard } from "./ColdOpen07PddTitleCard";
import { Part1Economics01SectionTitleCard } from "./Part1Economics01SectionTitleCard";
import { Part1Economics04ResearchAnnotations } from "./Part1Economics04ResearchAnnotations";
import { Part1Economics05ContextWindowShrink } from "./Part1Economics05ContextWindowShrink";
import { Part2ParadigmShift01SectionTitleCard } from "./Part2ParadigmShift01SectionTitleCard";
import { Part3MoldThreeParts01SectionTitleCard } from "./Part3MoldThreeParts01SectionTitleCard";
import { Part3MoldThreeParts02MoldCrossSection } from "./Part3MoldThreeParts02MoldCrossSection";
import { Part4PrecisionTradeoff01SectionTitleCard } from "./Part4PrecisionTradeoff01SectionTitleCard";
import { Part4PrecisionTradeoff02PrinterVsMoldSplit } from "./Part4PrecisionTradeoff02PrinterVsMoldSplit";
import { Part4PrecisionTradeoff03PrecisionTradeoffCurve } from "./Part4PrecisionTradeoff03PrecisionTradeoffCurve";
import { Part5CompoundReturns01SectionTitleCard } from "./Part5CompoundReturns01SectionTitleCard";
import { Part5CompoundReturns02MaintenancePieChart } from "./Part5CompoundReturns02MaintenancePieChart";
import { Part5CompoundReturns03CompoundDebtCurve } from "./Part5CompoundReturns03CompoundDebtCurve";
import { Part5CompoundReturns04DivergingCostCurves } from "./Part5CompoundReturns04DivergingCostCurves";
import { Part5CompoundReturns05InvestmentComparisonTable } from "./Part5CompoundReturns05InvestmentComparisonTable";
import { WhereToStart01SectionTitleCard } from "./WhereToStart01SectionTitleCard";
import { WhereToStart02LegacyCodebaseReveal } from "./WhereToStart02LegacyCodebaseReveal";
import { WhereToStart04SourceOfTruthShift } from "./WhereToStart04SourceOfTruthShift";
import { Closing04PddTriangle } from "./Closing04PddTriangle";
import { Closing05DissolveRegenerateLoop } from "./Closing05DissolveRegenerateLoop";
import { Closing07TheBeat } from "./Closing07TheBeat";

const PREVIEW_VISUAL_MEDIA: Record<string, Record<string, string>> = {
  "cold_open:01_split_screen_hook": { leftSrc: "veo/developer_ai_edit.mp4", defaultSrc: "veo/developer_ai_edit.mp4", rightSrc: "veo/grandmother_darning.mp4", backgroundSrc: "veo/developer_ai_edit.mp4", outputSrc: "veo/developer_ai_edit.mp4", baseSrc: "veo/developer_ai_edit.mp4", revealSrc: "veo/grandmother_darning.mp4" },
  "cold_open:07_pdd_title_card": { defaultSrc: "veo/sock_toss.mp4", backgroundSrc: "veo/sock_toss.mp4", outputSrc: "veo/sock_toss.mp4", baseSrc: "veo/sock_toss.mp4" },
  "closing:07_the_beat": { defaultSrc: "veo/mold_glow_finale.mp4", backgroundSrc: "veo/mold_glow_finale.mp4", outputSrc: "veo/mold_glow_finale.mp4", baseSrc: "veo/mold_glow_finale.mp4" },
};

const PREVIEW_VISUAL_CONTRACTS: Record<string, Record<string, unknown> | null> = {
  "cold_open:01_split_screen_hook": {"specBaseName": "01_split_screen_hook", "dataPoints": {"type": "split_screen", "layout": "vertical_split", "splitPosition": 960, "leftPanel": {"content": "veo_clip_then_zoom_out", "clipId": "developer_ai_edit", "zoomOutReveals": "massive_codebase_with_patches", "thematicRole": "modern_developer_patching"}, "rightPanel": {"content": "veo_clip_then_zoom_out", "clipId": "grandmother_darning", "zoomOutReveals": "drawer_of_mended_garments", "thematicRole": "grandmother_darning_socks"}, "backgroundColor": "#000000", "narrationSegments": ["cold_open_001", "cold_open_002", "cold_open_003"]}, "overlayConfig": null, "renderMode": "component"},
  "cold_open:07_pdd_title_card": {"specBaseName": "07_pdd_title_card", "dataPoints": {"type": "title_card", "sectionNumber": 0, "sectionLabel": "Cold Open", "title": "Prompt-Driven Development", "titleColor": "#4A90D9", "subtitle": "So why are we still patching?", "subtitleColor": "#94A3B8", "backgroundColor": "#0D1117", "codeUnderlay": true, "underlayOpacity": 0.15, "narrationSegments": ["cold_open_006"]}, "overlayConfig": null, "renderMode": "component"},
  "part1_economics:01_section_title_card": {"specBaseName": "01_section_title_card", "dataPoints": {"type": "title_card", "sectionNumber": 1, "sectionLabel": "PART 1", "titleLine1": "THE ECONOMICS", "titleLine2": "OF DARNING", "backgroundColor": "#0A0F1A", "ghostElements": [{"shape": "quadratic_curve", "color": "#D9944A", "component": "descending_cost"}, {"shape": "quadratic_curve", "color": "#4A90D9", "component": "ascending_cost"}, {"shape": "crossing_point", "color": "#E2E8F0", "component": "threshold"}], "narrationSegments": ["part1_economics_001", "part1_economics_002"]}, "overlayConfig": null, "renderMode": "component"},
  "part1_economics:04_research_annotations": {"specBaseName": "04_research_annotations", "dataPoints": {"type": "annotation_overlay", "chartId": "code_cost_triple_line", "annotations": [{"id": "github_individual", "header": "Individual task: −55%", "source": "GitHub, 2022", "finePrint": "95 developers, one greenfield task", "color": "#4ADE80", "target": "immediate_patch_line", "wave": 1}, {"id": "uplevel_overall", "header": "Overall throughput: ~0%", "source": "Uplevel, 2024", "finePrint": "785 developers, one year", "color": "#EF4444", "target": "total_cost_line", "wave": 1}, {"id": "gitclear_churn", "header": "Code churn: +44%", "source": "GitClear, 2025", "finePrint": "211M lines analyzed", "color": "#EF4444", "target": "debt_shading", "wave": 2}, {"id": "gitclear_refactoring", "header": "Refactoring: −60%", "source": "GitClear, 2025", "finePrint": "Developers aren't cleaning up. They're piling on.", "color": "#EF4444", "target": "debt_gap", "wave": 2}], "backgroundColor": "#0A0F1A", "narrationSegments": ["part1_economics_014", "part1_economics_015", "part1_economics_016"]}, "overlayConfig": null, "renderMode": "component"},
  "part1_economics:05_context_window_shrink": {"specBaseName": "05_context_window_shrink", "dataPoints": {"type": "animated_diagram", "diagramId": "context_window_shrink", "stages": [{"gridSize": 4, "blockPx": 60, "coveragePercent": 80, "color": "#4ADE80"}, {"gridSize": 8, "blockPx": 30, "coveragePercent": 40, "color": "#FBBF24"}, {"gridSize": 16, "blockPx": 15, "coveragePercent": 10, "color": "#EF4444"}, {"gridSize": 32, "blockPx": 7.5, "coveragePercent": 2, "color": "#DC2626"}], "contextWindow": {"width": 260, "height": 260, "color": "#4A90D9"}, "retrievalErrors": {"irrelevantInside": 3, "neededOutside": 5, "irrelevantColor": "#EF4444", "neededColor": "#4ADE80"}, "backgroundColor": "#0A0F1A", "narrationSegments": ["part1_economics_017", "part1_economics_018", "part1_economics_019", "part1_economics_020"]}, "overlayConfig": null, "renderMode": "component"},
  "part2_paradigm_shift:01_section_title_card": {"specBaseName": "01_section_title_card", "dataPoints": {"type": "title_card", "sectionNumber": 2, "sectionLabel": "PART 2", "titleLine1": "THE PARADIGM", "titleLine2": "SHIFT", "backgroundColor": "#0A0F1A", "ghostElements": [{"shape": "mold_nozzle", "color": "#4A90D9", "component": "injection_nozzle"}, {"shape": "mold_cavity", "color": "#4A90D9", "component": "rectangular_cavity"}, {"shape": "mold_walls", "color": "#D9944A", "component": "constraint_walls"}], "narrationSegments": ["part2_paradigm_shift_001"]}, "overlayConfig": null, "renderMode": "component"},
  "part3_mold_three_parts:01_section_title_card": {"specBaseName": "01_section_title_card", "dataPoints": {"type": "title_card", "sectionNumber": 3, "sectionLabel": "PART 3", "titleLine1": "THE MOLD HAS", "titleLine2": "THREE PARTS", "backgroundColor": "#0A0F1A", "ghostElements": [{"shape": "mold_shell", "color": "#4A90D9", "component": "outer_shell"}, {"shape": "mold_walls", "color": "#D9944A", "component": "test_walls"}, {"shape": "mold_nozzle", "color": "#2DD4BF", "component": "prompt_nozzle"}, {"shape": "mold_material", "color": "#A78BFA", "component": "grounding_material"}], "narrationSegments": ["part3_mold_three_parts_001", "part3_mold_three_parts_002", "part3_mold_three_parts_003"]}, "overlayConfig": null, "renderMode": "component"},
  "part3_mold_three_parts:02_mold_cross_section": {"specBaseName": "02_mold_cross_section", "dataPoints": {"type": "animated_diagram", "diagramId": "mold_cross_section", "regions": [{"id": "walls", "label": "Tests: The Walls", "color": "#D9944A", "role": "constraints"}, {"id": "nozzle", "label": "Prompt: The Specification", "color": "#2DD4BF", "role": "specification"}, {"id": "material", "label": "Grounding: The Material", "color": "#A78BFA", "role": "style"}], "backgroundColor": "#0A0F1A", "narrationSegments": ["part3_mold_three_parts_004", "part3_mold_three_parts_005", "part3_mold_three_parts_006"]}, "overlayConfig": null, "renderMode": "component"},
  "part4_precision_tradeoff:01_section_title_card": {"specBaseName": "01_section_title_card", "dataPoints": {"type": "title_card", "sectionNumber": 4, "sectionLabel": "PART 4", "titleLine1": "THE PRECISION", "titleLine2": "TRADEOFF", "backgroundColor": "#0A0F1A", "ghostElements": [{"shape": "printer_nozzle", "color": "#60A5FA", "side": "left"}, {"shape": "coordinate_grid", "color": "#60A5FA", "side": "left"}, {"shape": "mold_outline", "color": "#D9944A", "side": "right"}, {"shape": "flow_curves", "color": "#A78BFA", "side": "right"}], "narrationSegments": ["part4_precision_tradeoff_001"]}, "overlayConfig": null, "renderMode": "component"},
  "part4_precision_tradeoff:02_printer_vs_mold_split": {"specBaseName": "02_printer_vs_mold_split", "dataPoints": {"type": "split_screen", "layout": "vertical_split", "splitPosition": 960, "leftPanel": {"header": "3D PRINTING", "headerColor": "#60A5FA", "elements": [{"type": "coordinate_grid", "spacing": 40, "color": "#60A5FA"}, {"type": "printer_nozzle", "layers": 3, "pointsPerLayer": 8}, {"type": "coordinate_labels", "font": "JetBrains Mono", "size": 8}], "caption": "Every point must be specified", "thematicRole": "explicit_precision"}, "rightPanel": {"header": "INJECTION MOLDING", "headerColor": "#D9944A", "elements": [{"type": "mold_walls", "strokeWidth": 4, "color": "#D9944A"}, {"type": "liquid_flow", "color": "#A78BFA"}, {"type": "wall_glow_on_impact", "glowColor": "#D9944A"}], "caption": "Walls do the precision work", "thematicRole": "emergent_precision"}, "backgroundColor": "#0A0F1A", "narrationSegments": ["part4_precision_tradeoff_002", "part4_precision_tradeoff_003"]}, "overlayConfig": null, "renderMode": "component"},
  "part4_precision_tradeoff:03_precision_tradeoff_curve": {"specBaseName": "03_precision_tradeoff_curve", "dataPoints": {"type": "animated_chart", "chartId": "precision_tradeoff_curve", "axes": {"x": {"label": "Number of Tests", "range": [0, 50], "ticks": ["0", "10", "20", "30", "40", "50+"]}, "y": {"label": "Required Prompt Precision", "range": ["Low", "High"], "ticks": ["Low", "Medium", "High"]}}, "curve": {"type": "inverse_hyperbolic", "color": "#2DD4BF", "strokeWidth": 3}, "annotations": {"left": {"label": "parser_v1.prompt — 50 lines", "description": "Dense prompt, few tests", "position": "high_precision"}, "right": {"label": "parser_v2.prompt — 10 lines", "description": "Minimal prompt, 47 tests", "testCount": 47, "position": "low_precision"}}, "introText": "This maps directly to PDD.", "backgroundColor": "#0A0F1A", "narrationSegments": ["part4_precision_tradeoff_004", "part4_precision_tradeoff_005", "part4_precision_tradeoff_006"]}, "overlayConfig": null, "renderMode": "component"},
  "part5_compound_returns:01_section_title_card": {"specBaseName": "01_section_title_card", "dataPoints": {"type": "title_card", "sectionId": "part5_compound_returns", "title": "COMPOUND RETURNS", "tagline": "Why the economics compound for you.", "backgroundColor": "#0A0F1A", "narrationSegments": ["part5_compound_returns_001"]}, "overlayConfig": null, "renderMode": "component"},
  "part5_compound_returns:02_maintenance_pie_chart": {"specBaseName": "02_maintenance_pie_chart", "dataPoints": {"type": "pie_chart", "chartId": "maintenance_cost_pie", "slices": [{"label": "Maintenance", "range": "80-90%", "color": "#F59E0B", "pullOut": 8}, {"label": "Initial Development", "range": "10-20%", "color": "#4ADE80"}], "callouts": [{"text": "40% more on maintenance", "source": "McKinsey", "color": "#F59E0B"}, {"text": "⅓ of dev time on debt", "source": "Stripe", "color": "#F59E0B"}], "backgroundColor": "#0A0F1A", "narrationSegments": ["part5_compound_returns_002"]}, "overlayConfig": null, "renderMode": "component"},
  "part5_compound_returns:03_compound_debt_curve": {"specBaseName": "03_compound_debt_curve", "dataPoints": {"type": "animated_chart", "chartId": "compound_debt_curve", "morphFrom": "maintenance_cost_pie", "curves": [{"id": "debt_exponential", "formula": "base * (1 + 0.25)^x", "color": "#F59E0B", "strokeWidth": 3, "label": "Debt × (1 + Rate)^Time", "fill": true}, {"id": "regeneration_flat", "formula": "constant", "color": "#4ADE80", "strokeWidth": 2.5, "dashed": true, "label": "Regeneration cost (debt resets each cycle)"}], "stats": [{"value": "$1.52T", "label": "annually", "source": "CISQ", "color": "#F59E0B"}], "backgroundColor": "#0A0F1A", "narrationSegments": ["part5_compound_returns_003"]}, "overlayConfig": {"gradientOverlay": "bottom"}, "renderMode": "component"},
  "part5_compound_returns:04_diverging_cost_curves": {"specBaseName": "04_diverging_cost_curves", "dataPoints": {"type": "animated_chart", "chartId": "diverging_cost_curves", "curves": [{"id": "patching_exponential", "label": "Patching", "color": "#F59E0B", "type": "exponential", "direction": "up", "annotations": ["+debt", "+debt", "+debt", "+debt", "+debt"]}, {"id": "pdd_flat", "label": "PDD", "color": "#4ADE80", "type": "flat", "annotations": ["+test", "+test", "+test", "+test", "+test", "+test", "+test", "+test"]}], "xAxis": ["Now", "6 months", "1 year", "2 years", "5 years"], "pivotLabel": "Tests accrue compound returns", "backgroundColor": "#0A0F1A", "narrationSegments": ["part5_compound_returns_004", "part5_compound_returns_005"]}, "overlayConfig": null, "renderMode": "component"},
  "part5_compound_returns:05_investment_comparison_table": {"specBaseName": "05_investment_comparison_table", "dataPoints": {"type": "comparison_table", "tableId": "investment_comparison", "columns": ["Investment", "Patching", "PDD"], "columnColors": ["#E2E8F0", "#F59E0B", "#4ADE80"], "rows": [{"investment": "Fix a bug", "patching": "One place, once", "pdd": "Impossible forever"}, {"investment": "Improve code", "patching": "One version", "pdd": "All future versions"}, {"investment": "Document intent", "patching": "One snapshot", "pdd": "Living specification"}], "backgroundColor": "#0A0F1A", "narrationSegments": ["part5_compound_returns_006"]}, "overlayConfig": null, "renderMode": "component"},
  "where_to_start:01_section_title_card": {"specBaseName": "01_section_title_card", "dataPoints": {"type": "title_card", "sectionId": "where_to_start", "sectionNumber": 6, "sectionLabel": "PART 6", "title": "WHERE TO START", "backgroundColor": "#0A0F1A", "ghostElements": [{"shape": "codebase_tree", "color": "#334155", "style": "file_tree"}], "narrationSegments": ["where_to_start_001"]}, "overlayConfig": null, "renderMode": "component"},
  "where_to_start:02_legacy_codebase_reveal": {"specBaseName": "02_legacy_codebase_reveal", "dataPoints": {"type": "code_visualization", "chartId": "legacy_codebase_reveal", "panels": 5, "fileNames": ["auth_handler.py", "payment_processor.py", "user_service.py", "legacy_router.py", "config.py"], "warningComments": ["// don't touch", "// here be dragons", "// TODO: fix this someday", "// nobody knows why this works"], "lineCount": "~47,000", "backgroundColor": "#0A0F1A", "narrationSegments": ["where_to_start_001"]}, "overlayConfig": null, "renderMode": "component"},
  "where_to_start:04_source_of_truth_shift": {"specBaseName": "04_source_of_truth_shift", "dataPoints": {"type": "code_transformation", "chartId": "source_of_truth_shift", "transformedModules": [{"name": "auth_handler.py", "state": "complete"}, {"name": "payment_processor.py", "state": "animating"}], "pendingModules": ["user_service.py", "legacy_router.py", "config.py", "db_connector.py", "email_sender.py", "cache_layer.py"], "workflow": ["module", "prompt", "tests", "regenerate", "compare"], "backgroundColor": "#0A0F1A", "narrationSegments": ["where_to_start_002"]}, "overlayConfig": null, "renderMode": "component"},
  "closing:04_pdd_triangle": {"specBaseName": "04_pdd_triangle", "dataPoints": {"type": "animated_diagram", "chartId": "pdd_triangle", "vertices": [{"id": "prompt", "label": "PROMPT", "position": [960, 200], "color": "#60A5FA", "descriptor": "encode intent"}, {"id": "tests", "label": "TESTS", "position": [480, 750], "color": "#4ADE80", "descriptor": "preserve behavior"}, {"id": "grounding", "label": "GROUNDING", "position": [1440, 750], "color": "#D9944A", "descriptor": "maintain style"}], "centerElement": {"type": "generated_code", "position": [960, 520], "font": "JetBrains Mono"}, "backgroundColor": "#0A0F1A", "narrationSegments": ["closing_002"]}, "overlayConfig": null, "renderMode": "component"},
  "closing:05_dissolve_regenerate_loop": {"specBaseName": "05_dissolve_regenerate_loop", "dataPoints": {"type": "animated_diagram", "chartId": "dissolve_regenerate_loop", "cycles": 3, "cycleTints": ["#60A5FA", "#4ADE80", "#D9944A"], "triangle": {"persistent": true, "source": "pdd_triangle"}, "terminal": {"command": "pdd generate", "successIndicator": "✓"}, "backgroundColor": "#0A0F1A", "narrationSegments": ["closing_003", "closing_004"]}, "overlayConfig": null, "renderMode": "component"},
  "closing:07_the_beat": {"specBaseName": "07_the_beat", "dataPoints": {"type": "beat", "chartId": "the_beat", "ghostElements": [{"source": "pdd_triangle", "opacity": 0.02}], "backgroundColor": "#0A0F1A", "narrationSegments": []}, "overlayConfig": null, "renderMode": "component"},
};

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
      <Part1Economics01SectionTitleCard />
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
const Part2ParadigmShift01SectionTitleCardPreview: React.FC = () => (
  <VisualContractProvider contract={PREVIEW_VISUAL_CONTRACTS["part2_paradigm_shift:01_section_title_card"] ?? null}>
    <VisualMediaProvider media={PREVIEW_VISUAL_MEDIA["part2_paradigm_shift:01_section_title_card"] ?? null}>
      <Part2ParadigmShift01SectionTitleCard />
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
const WhereToStart04SourceOfTruthShiftPreview: React.FC = () => (
  <VisualContractProvider contract={PREVIEW_VISUAL_CONTRACTS["where_to_start:04_source_of_truth_shift"] ?? null}>
    <VisualMediaProvider media={PREVIEW_VISUAL_MEDIA["where_to_start:04_source_of_truth_shift"] ?? null}>
      <WhereToStart04SourceOfTruthShift />
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
        id="part2-paradigm-shift01-section-title-card"
        component={Part2ParadigmShift01SectionTitleCardPreview}
        durationInFrames={120}
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
        id="where-to-start04-source-of-truth-shift"
        component={WhereToStart04SourceOfTruthShiftPreview}
        durationInFrames={180}
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
    </>
  );
};
