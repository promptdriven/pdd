import React from "react";
import { Sequence, useCurrentFrame, Audio, OffthreadVideo, staticFile } from "remotion";
import { VISUAL_SEQUENCE } from "./constants";
import { SlotScaledSequence, VisualMediaProvider, VisualContractProvider } from "../_shared/visual-runtime";
import { GeneratedMediaVisual } from "../_shared/GeneratedMediaVisual";
import { GeneratedContractVisual } from "../_shared/GeneratedContractVisual";
import { Part1Economics04ResearchAnnotations } from "../Part1Economics04ResearchAnnotations";
import { Part1Economics05ContextWindowShrink } from "../Part1Economics05ContextWindowShrink";
import { Part1Economics09CrossingLinesMoment } from "../Part1Economics09CrossingLinesMoment";

const COMPONENT_MAP: Record<string, React.ComponentType<any>> = {
  "04_research_annotations": Part1Economics04ResearchAnnotations,
  "05_context_window_shrink": Part1Economics05ContextWindowShrink,
  "10_crossing_lines_moment": Part1Economics09CrossingLinesMoment,
};

const VISUAL_DURATIONS: Record<string, number> = {
  "04_research_annotations": 900,
  "05_context_window_shrink": 900,
  "10_crossing_lines_moment": 750,
};

const VISUAL_MEDIA: Record<string, Record<string, string>> = {
  "11_developer_darning_split": { leftSrc: "veo/developer_cursor_coding.mp4", defaultSrc: "veo/developer_cursor_coding.mp4", rightSrc: "veo/grandmother_darning_expert.mp4", backgroundSrc: "veo/developer_cursor_coding.mp4", outputSrc: "veo/developer_cursor_coding.mp4", baseSrc: "veo/developer_cursor_coding.mp4", revealSrc: "veo/grandmother_darning_expert.mp4" },
  "12_developer_cursor_coding": { defaultSrc: "veo/developer_cursor_coding.mp4", backgroundSrc: "veo/developer_cursor_coding.mp4", outputSrc: "veo/developer_cursor_coding.mp4", baseSrc: "veo/developer_cursor_coding.mp4" },
  "13_grandmother_darning_expert": { defaultSrc: "veo/grandmother_darning_expert.mp4", backgroundSrc: "veo/grandmother_darning_expert.mp4", outputSrc: "veo/grandmother_darning_expert.mp4", baseSrc: "veo/grandmother_darning_expert.mp4" },
};

const VISUAL_OVERLAYS: Record<string, Record<string, string | boolean | number>> = {
  "02_sock_price_chart": { fadeInFrames: 30 },
  "03_code_cost_chart": { fadeInFrames: 30 },
  "07_two_by_two_grid": { fadeInFrames: 60 },
  "15_double_meter_insight": { fadeInFrames: 30 },
};

const VISUAL_CONTRACTS: Record<string, Record<string, unknown> | null> = {
  "01_section_title_card": {"specBaseName": "01_section_title_card", "dataPoints": {"type": "title_card", "sectionNumber": 1, "sectionLabel": "PART 1", "titleLine1": "THE ECONOMICS", "titleLine2": "OF CODE", "backgroundColor": "#0A0F1A", "ghostElements": [{"shape": "bezier_curve", "color": "#4A90D9", "role": "descending_cost"}, {"shape": "bezier_curve", "color": "#D9944A", "role": "ascending_cost"}], "narrationSegments": ["part1_economics_001", "part1_economics_002", "part1_economics_003", "part1_economics_004", "part1_economics_005"]}, "mediaAliases": {}, "overlayConfig": null, "renderMode": "component"},
  "02_sock_price_chart": {"specBaseName": "02_sock_price_chart", "dataPoints": {"type": "animated_line_chart", "xAxis": {"label": "Year", "range": [1950, 2020], "ticks": "decade"}, "yAxis": {"label": "Cost (Labor Hours)", "range": [0, 4]}, "series": [{"id": "labor_cost", "label": "Hour of labor", "color": "#4A90D9", "data": [[1950, 1.0], [1960, 1.3], [1970, 1.8], [1980, 2.2], [1990, 2.6], [2000, 3.0], [2020, 3.5]]}, {"id": "garment_cost", "label": "Pair of wool socks", "color": "#D9944A", "data": [[1950, 1.0], [1960, 0.7], [1965, 0.5], [1970, 0.35], [1980, 0.2], [2000, 0.12], [2020, 0.08]]}], "crossingPoint": {"x": 1962, "y": 0.85, "label": "The Threshold"}, "narrationSegments": ["part1_economics_006", "part1_economics_007"]}, "mediaAliases": {}, "overlayConfig": {"fadeInFrames": 30}, "renderMode": "generated-media"},
  "03_code_cost_chart": {"specBaseName": "03_code_cost_chart", "dataPoints": {"type": "animated_multi_line_chart", "xAxis": {"label": "Year", "range": [2010, 2026], "ticks": "2y"}, "yAxis": {"label": "Cost (Developer Hours)", "range": [0, 25]}, "series": [{"id": "generate_cost", "label": "Cost to generate", "color": "#4A90D9", "strokeWidth": 3, "style": "solid", "data": [[2010, 20], [2015, 19], [2020, 18], [2021, 17], [2022, 16], [2023, 8], [2024, 3], [2025, 1.5]]}, {"id": "immediate_patch", "label": "Immediate patch cost", "color": "#D9944A", "strokeWidth": 3, "style": "solid", "data": [[2010, 3], [2015, 2.8], [2020, 2.5], [2021, 2.0], [2022, 1.5], [2023, 1.2], [2024, 0.8], [2025, 0.6]]}, {"id": "total_cost_debt", "label": "Total cost (with debt)", "color": "#D9944A", "strokeWidth": 2, "style": "dashed", "data": [[2010, 18], [2015, 18.5], [2020, 19], [2021, 19], [2022, 19.5], [2023, 20], [2024, 20.5], [2025, 21]]}], "milestones": [{"label": "Codex", "year": 2021}, {"label": "GPT-4", "year": 2023}, {"label": "Claude", "year": 2023}, {"label": "Gemini", "year": 2024}], "debtArea": {"upper": "total_cost_debt", "lower": "immediate_patch", "color": "#D9944A", "opacity": 0.08}, "narrationSegments": ["part1_economics_008", "part1_economics_009", "part1_economics_010", "part1_economics_011", "part1_economics_012", "part1_economics_013"]}, "mediaAliases": {}, "overlayConfig": {"fadeInFrames": 30}, "renderMode": "generated-media"},
  "04_research_annotations": {"specBaseName": "04_research_annotations", "dataPoints": {"type": "annotated_chart_overlay", "baseChart": "code_cost_chart", "annotations": [{"id": "github_individual", "text": "Individual task: −55%", "source": "GitHub, 2022", "detail": "95 developers, one greenfield task", "color": "#2DD4BF", "pointsTo": "immediate_patch_line"}, {"id": "uplevel_throughput", "text": "Overall throughput: ~0%", "source": "Uplevel, 2024", "detail": "785 developers, one year", "color": "#EF4444", "pointsTo": "total_cost_dashed_line"}, {"id": "gitclear_churn", "text": "Code churn: +44%", "source": "GitClear, 2025", "detail": "211M lines analyzed", "color": "#EF4444", "pointsTo": "debt_area"}, {"id": "refactoring_decline", "text": "Refactoring: −60%", "source": "GitClear, 2025", "color": "#EF4444", "pointsTo": "debt_area"}], "debtLayers": [{"id": "code_complexity", "label": "Code Complexity", "opacity": 0.12}, {"id": "context_rot", "label": "Context Rot", "opacity": 0.06, "texture": "noise"}], "narrationSegments": ["part1_economics_014", "part1_economics_015", "part1_economics_016", "part1_economics_017"]}, "mediaAliases": {}, "overlayConfig": null, "renderMode": "component"},
  "05_context_window_shrink": {"specBaseName": "05_context_window_shrink", "dataPoints": {"type": "context_window_visualization", "contextWindow": {"width": 280, "height": 200, "fixedSize": true, "borderColor": "#4A90D9"}, "gridPhases": [{"size": "4x4", "blocks": 16, "coverage": 0.8, "color": "#2DD4BF"}, {"size": "8x8", "blocks": 64, "coverage": 0.4, "color": "#F59E0B"}, {"size": "16x16", "blocks": 256, "coverage": 0.1, "color": "#EF4444"}, {"size": "32x32", "blocks": 1024, "coverage": 0.02, "color": "#EF4444"}], "highlights": {"red": {"meaning": "irrelevant_code_retrieved", "count": 4}, "green": {"meaning": "needed_code_invisible", "count": 8}}, "narrationSegments": ["part1_economics_018", "part1_economics_019", "part1_economics_020"]}, "mediaAliases": {}, "overlayConfig": null, "renderMode": "component"},
  "06_performance_vs_context": {"specBaseName": "06_performance_vs_context", "dataPoints": {"type": "inset_line_chart", "title": "Performance vs. Context Length", "xAxis": {"label": "Context Length (tokens)", "range": [0, 128000]}, "yAxis": {"label": "Relative Performance", "range": [0, 100], "unit": "%"}, "series": [{"id": "performance_degradation", "label": "Model Performance", "color": "#EF4444", "data": [[4000, 95], [16000, 82], [32000, 65], [64000, 40], [128000, 15]]}], "citation": "EMNLP, 2025", "keyFinding": "14-85% performance degradation as context grows", "narrationSegments": ["part1_economics_021", "part1_economics_022"]}, "mediaAliases": {}, "overlayConfig": null, "renderMode": "component"},
  "07_two_by_two_grid": {"specBaseName": "07_two_by_two_grid", "dataPoints": {"type": "two_by_two_grid", "axes": {"x": {"left": "Greenfield", "right": "Brownfield"}, "y": {"bottom": "In-Distribution", "top": "Out-of-Distribution"}}, "quadrants": [{"position": "top-left", "label": "GitHub study", "value": "+55%", "color": "#22C55E", "interpretation": "greenfield_in_distribution"}, {"position": "bottom-right", "label": "METR study", "value": "−19%", "color": "#EF4444", "interpretation": "brownfield_out_of_distribution"}, {"position": "top-right", "color": "#F59E0B", "interpretation": "intermediate"}, {"position": "bottom-left", "color": "#F59E0B", "interpretation": "intermediate"}], "summary": "Every study is correct. They just measured different quadrants.", "narrationSegments": ["part1_economics_023", "part1_economics_024", "part1_economics_025"]}, "mediaAliases": {}, "overlayConfig": {"fadeInFrames": 60}, "renderMode": "generated-media"},
  "08_fork_codebase_size": {"specBaseName": "08_fork_codebase_size", "dataPoints": {"type": "forked_line_chart", "baseChart": "code_cost_chart", "forkPoint": {"year": 2020, "value": 2.5}, "forks": [{"id": "small_codebase", "label": "Small codebase", "color": "#22C55E", "data": [[2020, 2.5], [2022, 1.2], [2024, 0.4], [2025, 0.2]]}, {"id": "large_codebase", "label": "Large codebase", "color": "#EF4444", "data": [[2020, 2.5], [2022, 2.8], [2024, 3.0], [2025, 3.2]]}], "annotations": [{"text": "METR, 2025: experienced devs 19% slower on mature repos", "pointsTo": "large_codebase"}, {"text": "Developers believed AI saved 20%. It cost 19%.", "emphasis": true}], "growthArrow": {"from": "small_codebase", "to": "large_codebase", "label": "Every patch adds code."}, "narrationSegments": ["part1_economics_026", "part1_economics_027", "part1_economics_028"]}, "mediaAliases": {}, "overlayConfig": null, "renderMode": "component"},
  "09_patching_vs_regeneration_split": {"specBaseName": "09_patching_vs_regeneration_split", "dataPoints": {"type": "split_screen", "layout": "vertical_split", "splitPosition": 960, "leftPanel": {"header": "AGENTIC PATCHING", "headerColor": "#EF4444", "content": "dense_code_with_highlights", "tokenCount": 15000, "relevance": "~40%", "thematicRole": "wasteful_context"}, "rightPanel": {"header": "PDD REGENERATION", "headerColor": "#2DD4BF", "content": "prompt_test_grounding", "tokenCount": 2300, "relevance": "100%", "thematicRole": "curated_context"}, "compressionAnimation": {"codeBlocks": 20, "promptBlocks": 20, "ratio": "5-10×"}, "backgroundColor": "#0A0F1A", "narrationSegments": ["part1_economics_029", "part1_economics_030"]}, "mediaAliases": {}, "overlayConfig": null, "renderMode": "component"},
  "10_crossing_lines_moment": {"specBaseName": "10_crossing_lines_moment", "dataPoints": {"type": "crossing_moment", "baseChart": "code_cost_chart", "finalSegment": {"line": "generate_cost", "data": [[2024, 3], [2024.5, 2.0], [2025, 0.8], [2025.5, 0.4]]}, "crossings": [{"id": "generate_below_total_debt", "x": 2024.5, "y": 2.0, "meaning": "Regeneration cheaper than patching + debt"}, {"id": "generate_below_immediate", "x": 2025, "y": 0.6, "meaning": "Regeneration cheaper than even immediate patching"}], "label": "We are here.", "annotation": "Small modules. Clear prompts. Always fits in context.", "narrationSegments": ["part1_economics_031", "part1_economics_032"]}, "mediaAliases": {}, "overlayConfig": null, "renderMode": "component"},
  "11_developer_darning_split": {"specBaseName": "11_developer_darning_split", "dataPoints": {"type": "split_screen", "layout": "vertical_split", "splitPosition": 960, "leftPanel": {"content": "veo_clip_with_zoom_overlay", "clipId": "developer_cursor_coding", "zoomOut": {"startFrame": 150, "duration": 60, "from": 1.0, "to": 0.5}, "legacyComments": ["// don't touch this", "// legacy", "// temporary fix (2019)", "// TODO: refactor someday", "// no idea why this works"], "thematicRole": "developer_patching"}, "rightPanel": {"content": "veo_clip", "clipId": "grandmother_darning_expert", "thematicRole": "grandmother_darning"}, "backgroundColor": "#000000", "narrationSegments": ["part1_economics_033"]}, "mediaAliases": {"leftSrc": "veo/developer_cursor_coding.mp4", "defaultSrc": "veo/developer_cursor_coding.mp4", "rightSrc": "veo/grandmother_darning_expert.mp4", "backgroundSrc": "veo/developer_cursor_coding.mp4", "outputSrc": "veo/developer_cursor_coding.mp4", "baseSrc": "veo/developer_cursor_coding.mp4", "revealSrc": "veo/grandmother_darning_expert.mp4"}, "overlayConfig": null, "renderMode": "component"},
  "12_developer_cursor_coding": {"specBaseName": "12_developer_cursor_coding", "dataPoints": {"type": "veo_clip", "clipId": "developer_cursor_coding", "camera": {"framing": "medium_close_up_ots", "movement": "near_static_micro_drift", "dof": "shallow", "aperture": "f/2.8", "angle": "slightly_elevated"}, "lighting": {"key": {"color": "#E2E8F0", "type": "monitor_glow"}, "fill": {"color": "#FFB347", "opacity": 0.15, "type": "ambient_desk_lamp"}}, "characters": [{"id": "developer_protagonist", "label": "Developer", "referencePrompt": "Mid-30s software developer, focused expression, modern casual attire, working at a clean desk with dark-themed code editor"}], "narrationSegments": ["part1_economics_033"]}, "mediaAliases": {"defaultSrc": "veo/developer_cursor_coding.mp4", "backgroundSrc": "veo/developer_cursor_coding.mp4", "outputSrc": "veo/developer_cursor_coding.mp4", "baseSrc": "veo/developer_cursor_coding.mp4"}, "overlayConfig": null, "renderMode": "raw-media"},
  "13_grandmother_darning_expert": {"specBaseName": "13_grandmother_darning_expert", "dataPoints": {"type": "veo_clip", "clipId": "grandmother_darning_expert", "camera": {"framing": "close_up_hands", "movement": "near_static_micro_drift", "dof": "shallow", "aperture": "f/2.0", "angle": "slightly_above"}, "lighting": {"key": {"color": "#FFB347", "type": "warm_table_lamp"}, "fill": {"color": "#E2E8F0", "opacity": 0.05, "type": "ambient"}}, "characters": [{"id": "grandmother_darner", "label": "Grandmother", "referencePrompt": "Elderly woman in her 70s, experienced steady hands, calm focused expression, working under warm lamplight in a comfortable living room"}], "narrationSegments": ["part1_economics_033"]}, "mediaAliases": {"defaultSrc": "veo/grandmother_darning_expert.mp4", "backgroundSrc": "veo/grandmother_darning_expert.mp4", "outputSrc": "veo/grandmother_darning_expert.mp4", "baseSrc": "veo/grandmother_darning_expert.mp4"}, "overlayConfig": null, "renderMode": "raw-media"},
  "14_key_insight_stillness": {"specBaseName": "14_key_insight_stillness", "dataPoints": {"type": "title_card", "variant": "stillness_beat", "backgroundColor": "#0A0F1A", "elements": [{"type": "pulsing_line", "color": "#E2E8F0", "maxOpacity": 0.03, "purpose": "subliminal_presence"}, {"type": "radial_glow", "color": "#FFB347", "opacity": 0.02, "purpose": "warmth_callback"}], "narrationSegments": []}, "mediaAliases": {}, "overlayConfig": null, "renderMode": "component"},
  "15_double_meter_insight": {"specBaseName": "15_double_meter_insight", "dataPoints": {"type": "dual_meter_visualization", "meters": [{"id": "effective_context_window", "label": "Effective Context Window", "color": {"from": "#4A90D9", "to": "#2DD4BF"}, "scaleMarkers": ["1×", "2×", "5×", "10×"], "fillPercent": 85, "position": "left"}, {"id": "model_performance", "label": "Model Performance", "color": "#22C55E", "fillPercent": 80, "position": "right"}], "summary": "Bigger window AND smarter model.", "narrationSegments": ["part1_economics_032", "part1_economics_033"]}, "mediaAliases": {}, "overlayConfig": {"fadeInFrames": 30}, "renderMode": "generated-media"},
  "16_try_it_yourself": {"specBaseName": "16_try_it_yourself", "dataPoints": {"type": "title_card", "variant": "handwritten_challenge", "text": "Try it yourself.", "font": "Caveat", "backgroundColor": "#0F172A", "underlineColor": "#2DD4BF", "animation": "handwritten_trace", "narrationSegments": []}, "mediaAliases": {}, "overlayConfig": null, "renderMode": "component"},
};

export const Part1EconomicsSection: React.FC = () => {
  const fps = 30;
  const durationSeconds = 455.44;
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
              <VisualContractProvider contract={visualContract}>
                <VisualMediaProvider media={visualMedia}>
                  <GeneratedContractVisual />
                </VisualMediaProvider>
              </VisualContractProvider>
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
