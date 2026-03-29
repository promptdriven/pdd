import React from "react";
import { Sequence, useCurrentFrame, Audio, OffthreadVideo, staticFile } from "remotion";
import { VISUAL_SEQUENCE } from "./constants";
import { SlotScaledSequence, VisualMediaProvider, VisualContractProvider } from "../_shared/visual-runtime";
import { GeneratedMediaVisual } from "../_shared/GeneratedMediaVisual";
import { GeneratedContractVisual } from "../_shared/GeneratedContractVisual";
import { Part1Economics03CodeCostChart } from "../Part1Economics03CodeCostChart";
import { Part1Economics06DebtLayersZoom } from "../Part1Economics06DebtLayersZoom";
import { Part1Economics07ContextWindowShrink } from "../Part1Economics07ContextWindowShrink";
import { Part1Economics08PerformanceVsContext } from "../Part1Economics08PerformanceVsContext";
import { Part1Economics09TwoByTwoGrid } from "../Part1Economics09TwoByTwoGrid";
import { Part1Economics10ForkCodebaseSize } from "../Part1Economics10ForkCodebaseSize";
import { Part1Economics11PatchingVsRegeneration } from "../Part1Economics11PatchingVsRegeneration";
import { Part1Economics12ContextCompression } from "../Part1Economics12ContextCompression";
import { Part1Economics13CrossingLinesMoment } from "../Part1Economics13CrossingLinesMoment";
import { Part1Economics18KeyInsightStillness } from "../Part1Economics18KeyInsightStillness";
import { Part1Economics19DoubleMeterInsight } from "../Part1Economics19DoubleMeterInsight";
import { Part1Economics20TryItYourself } from "../Part1Economics20TryItYourself";

const COMPONENT_MAP: Record<string, React.ComponentType<any>> = {
  "03_code_cost_chart": Part1Economics03CodeCostChart,
  "06_debt_layers_zoom": Part1Economics06DebtLayersZoom,
  "07_context_window_shrink": Part1Economics07ContextWindowShrink,
  "08_performance_vs_context": Part1Economics08PerformanceVsContext,
  "09_two_by_two_grid": Part1Economics09TwoByTwoGrid,
  "10_fork_codebase_size": Part1Economics10ForkCodebaseSize,
  "11_patching_vs_regeneration": Part1Economics11PatchingVsRegeneration,
  "12_context_compression": Part1Economics12ContextCompression,
  "13_crossing_lines_moment": Part1Economics13CrossingLinesMoment,
  "18_key_insight_stillness": Part1Economics18KeyInsightStillness,
  "19_double_meter_insight": Part1Economics19DoubleMeterInsight,
  "20_try_it_yourself": Part1Economics20TryItYourself,
};

const VISUAL_DURATIONS: Record<string, number> = {
  "03_code_cost_chart": 1650,
  "06_debt_layers_zoom": 540,
  "07_context_window_shrink": 1560,
  "08_performance_vs_context": 1470,
  "09_two_by_two_grid": 630,
  "10_fork_codebase_size": 1380,
  "11_patching_vs_regeneration": 810,
  "12_context_compression": 1380,
  "13_crossing_lines_moment": 360,
  "18_key_insight_stillness": 360,
  "19_double_meter_insight": 360,
  "20_try_it_yourself": 240,
};

const VISUAL_MEDIA: Record<string, Record<string, string>> = {
  "14_split_developer_grandma": { leftSrc: "veo/developer_cursor_p1.mp4", defaultSrc: "veo/developer_cursor_p1.mp4", rightSrc: "veo/grandmother_darning_p1.mp4", backgroundSrc: "veo/developer_cursor_p1.mp4", outputSrc: "veo/developer_cursor_p1.mp4", baseSrc: "veo/developer_cursor_p1.mp4", revealSrc: "veo/grandmother_darning_p1.mp4" },
  "15_developer_cursor": { defaultSrc: "veo/developer_cursor_p1.mp4", backgroundSrc: "veo/developer_cursor_p1.mp4", outputSrc: "veo/developer_cursor_p1.mp4", baseSrc: "veo/developer_cursor_p1.mp4" },
  "16_grandmother_darning": { defaultSrc: "veo/grandmother_darning_p1.mp4", backgroundSrc: "veo/grandmother_darning_p1.mp4", outputSrc: "veo/grandmother_darning_p1.mp4", baseSrc: "veo/grandmother_darning_p1.mp4" },
  "17_developer_codebase_zoomout": { defaultSrc: "veo/developer_codebase_zoomout.mp4", backgroundSrc: "veo/developer_codebase_zoomout.mp4", outputSrc: "veo/developer_codebase_zoomout.mp4", baseSrc: "veo/developer_codebase_zoomout.mp4" },
};

const VISUAL_OVERLAYS: Record<string, Record<string, string | boolean | number>> = {
  "01_section_title_card": { fadeOutFrames: 60 },
  "02_sock_price_chart": { fadeInFrames: 30 },
  "09_two_by_two_grid": { fadeInFrames: 45 },
  "18_key_insight_stillness": { fadeOutFrames: 60 },
};

const VISUAL_CONTRACTS: Record<string, Record<string, unknown> | null> = {
  "01_section_title_card": {"specBaseName": "01_section_title_card", "dataPoints": {"type": "title_card", "sectionNumber": 1, "sectionLabel": "PART 1", "titleLine1": "THE ECONOMICS", "titleLine2": "OF DARNING", "backgroundColor": "#0A0F1A", "ghostElements": [{"shape": "crossing_lines", "colors": ["#D9944A", "#4A90D9"], "role": "cost_crossing_preview"}], "narrationSegments": ["part1_economics_001", "part1_economics_002", "part1_economics_003"]}, "mediaAliases": {}, "overlayConfig": {"fadeOutFrames": 60}, "renderMode": "component"},
  "02_sock_price_chart": {"specBaseName": "02_sock_price_chart", "dataPoints": {"type": "line_chart", "chartId": "sock_price_vs_labor", "xAxis": {"label": "Year", "range": [1950, 2020], "tickInterval": 10}, "yAxis": {"label": "Cost (relative to hourly wage)", "range": [0, 1]}, "series": [{"id": "labor_cost", "label": "Labor cost", "color": "#D9944A", "data": [{"x": 1950, "y": 0.2}, {"x": 1960, "y": 0.35}, {"x": 1970, "y": 0.5}, {"x": 1980, "y": 0.6}, {"x": 1990, "y": 0.7}, {"x": 2000, "y": 0.78}, {"x": 2010, "y": 0.82}, {"x": 2020, "y": 0.85}]}, {"id": "garment_cost", "label": "Garment cost (relative)", "color": "#4A90D9", "data": [{"x": 1950, "y": 0.8}, {"x": 1960, "y": 0.5}, {"x": 1965, "y": 0.35}, {"x": 1970, "y": 0.25}, {"x": 1980, "y": 0.18}, {"x": 1990, "y": 0.12}, {"x": 2000, "y": 0.1}, {"x": 2020, "y": 0.08}]}], "annotations": [{"type": "crossing_point", "x": 1962, "label": "The Threshold"}], "narrationSegments": ["part1_economics_004", "part1_economics_005"]}, "mediaAliases": {}, "overlayConfig": {"fadeInFrames": 30}, "renderMode": "component"},
  "03_code_cost_chart": {"specBaseName": "03_code_cost_chart", "dataPoints": {"type": "multi_line_chart", "chartId": "code_cost_generate_vs_patch", "xAxis": {"label": "Year", "range": [2000, 2026]}, "yAxis": {"label": "Cost (Developer Hours)"}, "series": [{"id": "generate_cost", "label": "Cost to generate", "color": "#4A90D9", "strokeStyle": "solid", "data": [{"x": 2000, "y": 0.9}, {"x": 2010, "y": 0.88}, {"x": 2020, "y": 0.85}, {"x": 2021, "y": 0.82}, {"x": 2022, "y": 0.78}, {"x": 2023, "y": 0.65}, {"x": 2024, "y": 0.35}, {"x": 2025, "y": 0.18}, {"x": 2026, "y": 0.1}]}, {"id": "immediate_patch", "label": "Immediate patch cost", "color": "#D9944A", "strokeStyle": "solid", "data": [{"x": 2000, "y": 0.55}, {"x": 2010, "y": 0.52}, {"x": 2020, "y": 0.48}, {"x": 2021, "y": 0.42}, {"x": 2022, "y": 0.35}, {"x": 2023, "y": 0.28}, {"x": 2024, "y": 0.22}, {"x": 2025, "y": 0.18}, {"x": 2026, "y": 0.15}]}, {"id": "total_cost_debt", "label": "Total cost (with debt)", "color": "#D9944A", "strokeStyle": "dashed", "data": [{"x": 2000, "y": 0.6}, {"x": 2010, "y": 0.62}, {"x": 2020, "y": 0.65}, {"x": 2021, "y": 0.66}, {"x": 2022, "y": 0.68}, {"x": 2023, "y": 0.7}, {"x": 2024, "y": 0.72}, {"x": 2025, "y": 0.73}, {"x": 2026, "y": 0.74}]}], "shadedArea": {"upper": "total_cost_debt", "lower": "immediate_patch", "color": "#D9944A", "opacity": 0.12, "label": "Technical debt"}, "dateMarkers": ["Codex (2021)", "GPT-4 (2023)", "Claude (2023)", "Gemini (2024)"], "narrationSegments": ["part1_economics_006", "part1_economics_007", "part1_economics_008", "part1_economics_009"]}, "mediaAliases": {}, "overlayConfig": null, "renderMode": "component"},
  "04_research_annotations": {"specBaseName": "04_research_annotations", "dataPoints": {"type": "annotation_overlay", "chartRef": "code_cost_generate_vs_patch", "annotations": [{"id": "github_study", "mainText": "Individual task: −55%", "source": "GitHub, 2022", "finePrint": "95 developers, one greenfield task", "targetLine": "immediate_patch", "accentColor": "#4A90D9", "direction": "positive"}, {"id": "uplevel_study", "mainText": "Overall throughput: ~0%", "source": "Uplevel, 2024", "finePrint": "785 developers, one year", "targetLine": "total_cost_debt", "accentColor": "#EF4444", "direction": "flat"}], "narrationSegments": ["part1_economics_010", "part1_economics_011"]}, "mediaAliases": {}, "overlayConfig": null, "renderMode": "component"},
  "05_code_churn_annotations": {"specBaseName": "05_code_churn_annotations", "dataPoints": {"type": "annotation_overlay", "chartRef": "code_cost_generate_vs_patch", "annotations": [{"id": "gitclear_churn", "mainText": "Code churn: +44%", "source": "GitClear, 2025", "finePrint": "211M lines analyzed", "targetArea": "debt_area", "accentColor": "#EF4444"}, {"id": "gitclear_refactoring", "mainText": "Refactoring: −60%", "source": "GitClear, 2025", "finePrint": "Code revised within 2 weeks", "targetArea": "debt_gap", "accentColor": "#F59E0B"}], "narrationSegments": ["part1_economics_012", "part1_economics_013"]}, "mediaAliases": {}, "overlayConfig": null, "renderMode": "component"},
  "06_debt_layers_zoom": {"specBaseName": "06_debt_layers_zoom", "dataPoints": {"type": "debt_layer_zoom", "chartRef": "code_cost_generate_vs_patch", "layers": [{"id": "code_complexity", "label": "Code Complexity", "color": "#D9944A", "opacity": 0.18, "position": "lower", "description": "Traditional technical debt: spaghetti code, dependency tangles"}, {"id": "context_rot", "label": "Context Rot", "color": "#F59E0B", "opacity": 0.12, "position": "upper", "noiseTexture": true, "description": "AI-specific: model performance degrades as codebase exceeds context window"}], "narrationSegments": ["part1_economics_013", "part1_economics_014"]}, "mediaAliases": {}, "overlayConfig": null, "renderMode": "component"},
  "07_context_window_shrink": {"specBaseName": "07_context_window_shrink", "dataPoints": {"type": "context_window_visualization", "chartId": "context_window_shrink", "growthStages": [{"gridSize": "4x4", "coverage": 0.8, "coverageColor": "#5AAA6E"}, {"gridSize": "8x8", "coverage": 0.4, "coverageColor": "#F59E0B"}, {"gridSize": "16x16", "coverage": 0.1, "coverageColor": "#EF4444"}, {"gridSize": "32x32", "coverage": 0.02, "coverageColor": "#DC2626"}], "contextWindow": {"width": 280, "height": 240, "borderColor": "#4A90D9", "fixed": true}, "mismatchPhase": {"irrelevantInsideCount": 4, "neededOutsideCount": 6}, "narrationSegments": ["part1_economics_014", "part1_economics_015", "part1_economics_016"]}, "mediaAliases": {}, "overlayConfig": null, "renderMode": "component"},
  "08_performance_vs_context": {"specBaseName": "08_performance_vs_context", "dataPoints": {"type": "inset_chart", "chartId": "performance_vs_context_length", "insetPosition": {"x": 1350, "y": 680}, "insetSize": {"width": 480, "height": 300}, "series": [{"id": "performance_degradation", "color": "#EF4444", "data": [{"x": "4K", "y": 1.0}, {"x": "32K", "y": 0.86}, {"x": "128K", "y": 0.5}, {"x": "1M", "y": 0.15}]}], "annotations": [{"text": "14-85% degradation", "source": "EMNLP, 2025"}, {"text": "Faster patching → faster growth → faster rot", "type": "cycle"}], "narrationSegments": ["part1_economics_017", "part1_economics_018"]}, "mediaAliases": {}, "overlayConfig": null, "renderMode": "component"},
  "09_two_by_two_grid": {"specBaseName": "09_two_by_two_grid", "dataPoints": {"type": "two_by_two_matrix", "chartId": "study_reconciliation_grid", "axes": {"x": {"labels": ["Greenfield", "Brownfield"]}, "y": {"labels": ["In-Distribution", "Out-of-Distribution"]}}, "quadrants": [{"position": "top-left", "color": "#5AAA6E", "label": "GitHub study: +55%", "source": "GitHub, 2022"}, {"position": "bottom-right", "color": "#EF4444", "label": "METR study: −19%", "source": "METR, 2025"}], "insightText": "Every study is correct. They just measured different quadrants.", "narrationSegments": ["part1_economics_019"]}, "mediaAliases": {}, "overlayConfig": {"fadeInFrames": 45}, "renderMode": "component"},
  "10_fork_codebase_size": {"specBaseName": "10_fork_codebase_size", "dataPoints": {"type": "forking_line_chart", "chartRef": "code_cost_generate_vs_patch", "forkPoint": {"x": 2020, "y": 0.48}, "forks": [{"id": "small_codebase", "label": "Small codebase", "color": "#5AAA6E", "data": [{"x": 2020, "y": 0.48}, {"x": 2022, "y": 0.3}, {"x": 2024, "y": 0.18}, {"x": 2026, "y": 0.1}]}, {"id": "large_codebase", "label": "Large codebase", "color": "#EF4444", "data": [{"x": 2020, "y": 0.48}, {"x": 2022, "y": 0.47}, {"x": 2024, "y": 0.46}, {"x": 2026, "y": 0.45}]}], "annotations": [{"text": "METR, 2025: experienced devs 19% slower on mature repos", "target": "large_codebase"}, {"text": "Developers believed AI saved 20%. It cost 19%.", "target": "large_codebase", "style": "italic"}, {"text": "Every patch adds code.", "type": "arrow", "from": "small_codebase", "to": "large_codebase"}], "narrationSegments": ["part1_economics_020", "part1_economics_021", "part1_economics_022"]}, "mediaAliases": {}, "overlayConfig": null, "renderMode": "component"},
  "11_patching_vs_regeneration": {"specBaseName": "11_patching_vs_regeneration", "dataPoints": {"type": "side_by_side_comparison", "chartId": "patching_vs_regeneration", "panels": {"left": {"header": "Agentic Patching", "tokenCount": 15000, "distribution": {"irrelevant": 0.8, "relevant": 0.05, "neutral": 0.15}, "label": "15,000 tokens — mostly wrong", "accentColor": "#EF4444"}, "right": {"header": "PDD Regeneration", "blocks": [{"label": "Prompt", "tokens": 300, "color": "#4A90D9"}, {"label": "Tests", "tokens": 2000, "color": "#D9944A"}, {"label": "Grounding", "tokens": 200, "color": "#5AAA6E"}], "label": "2,300 tokens — all curated", "accentColor": "#5AAA6E"}}, "narrationSegments": ["part1_economics_023", "part1_economics_024"]}, "mediaAliases": {}, "overlayConfig": null, "renderMode": "component"},
  "12_context_compression": {"specBaseName": "12_context_compression", "dataPoints": {"type": "context_compression_animation", "chartId": "module_compression", "modules": ["auth", "parser", "router", "validator", "logger", "cache", "queue", "mailer", "search", "analytics", "billing", "permissions", "notifications", "export", "import", "scheduler", "webhook", "api_client", "transformer", "serializer"], "codeTokensPerModule": 750, "promptTokensPerModule": 100, "contextWindowTokens": 4000, "overflowCount": 17, "compressionRatio": "5-10×", "narrationSegments": ["part1_economics_025", "part1_economics_026"]}, "mediaAliases": {}, "overlayConfig": null, "renderMode": "component"},
  "13_crossing_lines_moment": {"specBaseName": "13_crossing_lines_moment", "dataPoints": {"type": "crossing_moment", "chartRef": "code_cost_generate_vs_patch", "crossings": [{"id": "generate_crosses_total_cost", "year": 2025.2, "description": "Generate cost drops below total cost with debt"}, {"id": "generate_crosses_immediate", "year": 2025.6, "description": "Generate cost drops below immediate patch cost"}], "label": "We are here.", "narrationSegments": ["part1_economics_026"]}, "mediaAliases": {}, "overlayConfig": null, "renderMode": "component"},
  "14_split_developer_grandma": {"specBaseName": "14_split_developer_grandma", "dataPoints": {"type": "split_screen", "layout": "vertical_50_50", "divider": {"color": "#FFFFFF", "width": 2, "opacity": 0.6}, "panels": {"left": {"clips": ["developer_cursor_p1"], "label": "Developer with Cursor"}, "right": {"clips": ["grandmother_darning_p1"], "label": "Grandmother darning"}}, "narrationSegments": ["part1_economics_027", "part1_economics_028"], "durationSeconds": 17.0}, "mediaAliases": {"leftSrc": "veo/developer_cursor_p1.mp4", "defaultSrc": "veo/developer_cursor_p1.mp4", "rightSrc": "veo/grandmother_darning_p1.mp4", "backgroundSrc": "veo/developer_cursor_p1.mp4", "outputSrc": "veo/developer_cursor_p1.mp4", "baseSrc": "veo/developer_cursor_p1.mp4", "revealSrc": "veo/grandmother_darning_p1.mp4", "leftBaseSrc": "veo/developer_cursor_p1.mp4", "rightBaseSrc": "veo/grandmother_darning_p1.mp4"}, "overlayConfig": null, "renderMode": "component"},
  "15_developer_cursor": {"specBaseName": "15_developer_cursor", "dataPoints": {"type": "veo_clip", "clipId": "developer_cursor_p1", "camera": {"framing": "medium_close_up", "movement": "subtle_push_in", "dof": "moderate", "aperture": "f/4", "angle": "over_shoulder"}, "lighting": {"key": {"color": "#B0C4DE", "type": "monitor_glow"}, "fill": {"color": "#E2E8F0", "opacity": 0.2, "type": "ambient"}, "accent": {"color": "#4A90D9", "opacity": 0.1, "type": "led_backlight"}}, "characters": [{"id": "developer_protagonist", "label": "Developer", "referencePrompt": "Software developer in their 30s, modern casual attire, focused expression, typing at a workstation with monitors"}], "narrationSegments": ["part1_economics_027"]}, "mediaAliases": {"defaultSrc": "veo/developer_cursor_p1.mp4", "backgroundSrc": "veo/developer_cursor_p1.mp4", "outputSrc": "veo/developer_cursor_p1.mp4", "baseSrc": "veo/developer_cursor_p1.mp4"}, "overlayConfig": null, "renderMode": "raw-media"},
  "16_grandmother_darning": {"specBaseName": "16_grandmother_darning", "dataPoints": {"type": "veo_clip", "clipId": "grandmother_darning_p1", "camera": {"framing": "medium_close_up", "movement": "static_with_sway", "dof": "shallow", "aperture": "f/2.8", "angle": "elevated"}, "lighting": {"key": {"color": "#FFB347", "opacity": 0.7, "type": "table_lamp"}, "fill": {"color": "#D4A574", "opacity": 0.15, "type": "ambient"}}, "characters": [{"id": "grandmother", "label": "Grandmother", "referencePrompt": "Elderly woman in 1950s domestic setting, skilled hands darning wool socks by lamplight, warm amber tones"}], "narrationSegments": ["part1_economics_027"]}, "mediaAliases": {"defaultSrc": "veo/grandmother_darning_p1.mp4", "backgroundSrc": "veo/grandmother_darning_p1.mp4", "outputSrc": "veo/grandmother_darning_p1.mp4", "baseSrc": "veo/grandmother_darning_p1.mp4"}, "overlayConfig": null, "renderMode": "raw-media"},
  "17_developer_codebase_zoomout": {"specBaseName": "17_developer_codebase_zoomout", "dataPoints": {"type": "veo_clip", "clipId": "developer_codebase_zoomout", "camera": {"framing": "medium_to_wide", "movement": "dolly_back", "dof": "deepening", "angle": "eye_level"}, "lighting": {"key": {"color": "#D4E4F0", "opacity": 0.3, "type": "overhead_fluorescent"}, "fill": {"type": "multiple_monitor_glow"}}, "characters": [{"id": "developer_protagonist", "label": "Developer", "referencePrompt": "Software developer in their 30s, modern casual attire, focused expression, typing at a workstation with monitors"}], "overlays": [{"type": "floating_comment", "text": "// don't touch this", "color": "#EF4444"}, {"type": "floating_comment", "text": "// legacy", "color": "#F59E0B"}, {"type": "floating_comment", "text": "// temporary fix (2019)", "color": "#EF4444"}], "narrationSegments": ["part1_economics_028"]}, "mediaAliases": {"defaultSrc": "veo/developer_codebase_zoomout.mp4", "backgroundSrc": "veo/developer_codebase_zoomout.mp4", "outputSrc": "veo/developer_codebase_zoomout.mp4", "baseSrc": "veo/developer_codebase_zoomout.mp4"}, "overlayConfig": null, "renderMode": "raw-media"},
  "18_key_insight_stillness": {"specBaseName": "18_key_insight_stillness", "dataPoints": {"type": "stillness_beat", "style": "3b1b_key_insight", "backgroundColor": "#050810", "text": "So let me put together what I just showed you.", "textColor": "#94A3B8", "textOpacity": 0.6, "purpose": "Palate cleanser before key insight synthesis"}, "mediaAliases": {}, "overlayConfig": {"fadeOutFrames": 60}, "renderMode": "component"},
  "19_double_meter_insight": {"specBaseName": "19_double_meter_insight", "dataPoints": {"type": "double_meter", "chartId": "context_plus_performance", "meters": [{"id": "context_window", "title": "Effective Context Window", "fillColor": "#4A90D9", "bottomValue": "1×", "topValue": "5-10×", "position": "left"}, {"id": "model_performance", "title": "Model Performance", "fillColor": "#5AAA6E", "bottomValue": "Baseline", "topValue": "+89%", "position": "right"}], "insightText": "Bigger window AND smarter model.", "insightHighlight": {"word": "AND", "color": "#F59E0B"}}, "mediaAliases": {}, "overlayConfig": null, "renderMode": "component"},
  "20_try_it_yourself": {"specBaseName": "20_try_it_yourself", "dataPoints": {"type": "title_card", "style": "handwritten_challenge", "mainText": "Try it yourself.", "font": "Caveat", "instructions": ["Give your favorite LLM a hard coding problem as code,", "then as natural language.", "The natural language version will win."], "backgroundColor": "#0A0F1A", "accentColor": "#4A90D9"}, "mediaAliases": {}, "overlayConfig": null, "renderMode": "component"},
};

export const Part1EconomicsSection: React.FC = () => {
  const fps = 30;
  const durationSeconds = 484.08;
  const frame = useCurrentFrame();
  const activeVisuals = VISUAL_SEQUENCE
    .filter((visual) => frame >= visual.start && frame < visual.end)
    .slice()
    .sort((left, right) => ((left.lane ?? 0) - (right.lane ?? 0)) || (left.start - right.start));

  return (
    <Sequence from={0} durationInFrames={Math.max(1, Math.ceil(durationSeconds * fps))}>
      <Audio src={staticFile("part1_economics/narration.wav")} />
      {activeVisuals.map((visual) => {
        const VisualComponent = COMPONENT_MAP[visual.id] ?? null;
        const visualDuration = Math.max(1, visual.end - visual.start);
        const intrinsicDurationInFrames = VISUAL_DURATIONS[visual.id] ?? visualDuration;
        const visualMedia = VISUAL_MEDIA[visual.id] ?? null;
        const visualOverlayConfig = VISUAL_OVERLAYS[visual.id] ?? null;
        const visualContract = VISUAL_CONTRACTS[visual.id] ?? null;

        return (
          <Sequence key={visual.id} from={visual.start} durationInFrames={visualDuration}>
            {VisualComponent ? (
              <SlotScaledSequence intrinsicDurationInFrames={intrinsicDurationInFrames}>
                <VisualContractProvider contract={visualContract}>
                  <VisualMediaProvider media={visualContract?.renderMode === "component" ? null : visualMedia}>
                    <VisualComponent />
                  </VisualMediaProvider>
                </VisualContractProvider>
              </SlotScaledSequence>
            ) : visualContract?.renderMode === "component" ? (
              <SlotScaledSequence intrinsicDurationInFrames={intrinsicDurationInFrames}>
                <VisualContractProvider contract={visualContract}>
                  <VisualMediaProvider media={visualMedia}>
                    <GeneratedContractVisual />
                  </VisualMediaProvider>
                </VisualContractProvider>
              </SlotScaledSequence>
            ) : visualMedia?.defaultSrc ? (
              <VisualContractProvider contract={visualContract}>
                <VisualMediaProvider media={visualMedia}>
                {visualOverlayConfig || visualMedia?.leftSrc || visualMedia?.rightSrc ? (
                  <GeneratedMediaVisual config={visualOverlayConfig} />
                ) : (
                  <OffthreadVideo src={staticFile(visualMedia.defaultSrc)} style={{ width: "100%", height: "100%" }} />
                )}
                </VisualMediaProvider>
              </VisualContractProvider>
            ) : null}
          </Sequence>
        );
      })}
    </Sequence>
  );
};

export default Part1EconomicsSection;
