import React from "react";
import { Sequence, useCurrentFrame, Audio, OffthreadVideo, staticFile } from "remotion";
import { VISUAL_SEQUENCE } from "./constants";
import { SlotScaledSequence, VisualMediaProvider, VisualContractProvider } from "../_shared/visual-runtime";
import { GeneratedContractVisual } from "../_shared/GeneratedContractVisual";
import { Part1Economics01SectionTitleCard } from "../Part1Economics01SectionTitleCard";
import { Part1Economics04ResearchAnnotations } from "../Part1Economics04ResearchAnnotations";
import { Part1Economics05ContextWindowShrink } from "../Part1Economics05ContextWindowShrink";
import { Part1Economics06TwoByTwoGrid } from "../Part1Economics06TwoByTwoGrid";
import { Part1Economics09CrossingLinesMoment } from "../Part1Economics09CrossingLinesMoment";
import { Part1Economics10DoubleMeterInsight } from "../Part1Economics10DoubleMeterInsight";

const COMPONENT_MAP: Record<string, React.ComponentType<any>> = {
  "01_section_title_card": Part1Economics01SectionTitleCard,
  "04_research_annotations": Part1Economics04ResearchAnnotations,
  "05_context_window_shrink": Part1Economics05ContextWindowShrink,
  "07_two_by_two_grid": Part1Economics06TwoByTwoGrid,
  "11_crossing_lines_moment": Part1Economics09CrossingLinesMoment,
  "16_double_meter_insight": Part1Economics10DoubleMeterInsight,
};

const VISUAL_DURATIONS: Record<string, number> = {
  "01_section_title_card": 120,
  "04_research_annotations": 900,
  "05_context_window_shrink": 900,
  "07_two_by_two_grid": 750,
  "11_crossing_lines_moment": 750,
  "16_double_meter_insight": 750,
};

const VISUAL_MEDIA: Record<string, Record<string, string>> = {
  "13_developer_cursor_coding": { defaultSrc: "veo/developer_cursor_edit.mp4", backgroundSrc: "veo/developer_cursor_edit.mp4", outputSrc: "veo/developer_cursor_edit.mp4", baseSrc: "veo/developer_cursor_edit.mp4" },
  "14_grandmother_darning_expert": { defaultSrc: "veo/grandmother_darning_lamplight.mp4", backgroundSrc: "veo/grandmother_darning_lamplight.mp4", outputSrc: "veo/grandmother_darning_lamplight.mp4", baseSrc: "veo/grandmother_darning_lamplight.mp4" },
};

const VISUAL_OVERLAYS: Record<string, Record<string, string | boolean>> = {
};

const VISUAL_CONTRACTS: Record<string, Record<string, unknown> | null> = {
  "01_section_title_card": {"specBaseName": "01_section_title_card", "dataPoints": {"type": "title_card", "sectionNumber": 1, "sectionLabel": "PART 1", "titleLine1": "THE ECONOMICS", "titleLine2": "OF DARNING", "backgroundColor": "#0A0F1A", "ghostElements": [{"shape": "quadratic_curve", "color": "#D9944A", "component": "descending_cost"}, {"shape": "quadratic_curve", "color": "#4A90D9", "component": "ascending_cost"}, {"shape": "crossing_point", "color": "#E2E8F0", "component": "threshold"}], "narrationSegments": ["part1_economics_001", "part1_economics_002"]}, "mediaAliases": {}, "overlayConfig": null, "renderMode": "component"},
  "02_sock_price_chart": {"specBaseName": "02_sock_price_chart", "dataPoints": {"type": "animated_chart", "chartId": "sock_economics", "chartType": "dual_line", "xAxis": {"label": "Year", "range": [1950, 2020], "majorTick": 10}, "yAxis": {"label": "Cost (Relative to Hourly Wage)", "range": [0, 100]}, "series": [{"id": "labor_cost", "label": "Labor cost (darning)", "color": "#D9944A", "dataPoints": [{"x": 1950, "y": 45}, {"x": 1960, "y": 47}, {"x": 1970, "y": 48}, {"x": 1980, "y": 48}, {"x": 1990, "y": 49}, {"x": 2000, "y": 49}, {"x": 2010, "y": 50}, {"x": 2020, "y": 50}]}, {"id": "sock_cost", "label": "Cost of new socks", "color": "#4A90D9", "dataPoints": [{"x": 1950, "y": 80}, {"x": 1955, "y": 65}, {"x": 1960, "y": 52}, {"x": 1965, "y": 40}, {"x": 1970, "y": 28}, {"x": 1980, "y": 15}, {"x": 1990, "y": 8}, {"x": 2000, "y": 4}, {"x": 2010, "y": 2}, {"x": 2020, "y": 1}]}], "threshold": {"x": 1962, "y": 47, "label": "The Threshold"}, "backgroundColor": "#0A0F1A", "narrationSegments": ["part1_economics_005", "part1_economics_006", "part1_economics_007"]}, "mediaAliases": {}, "overlayConfig": null, "renderMode": "component"},
  "03_code_cost_chart": {"specBaseName": "03_code_cost_chart", "dataPoints": {"type": "animated_chart", "chartId": "code_cost_triple_line", "chartType": "triple_line", "xAxis": {"label": "Year", "range": [2000, 2025], "majorTick": 5}, "yAxis": {"label": "Cost (Developer Hours)", "range": [0, 100]}, "series": [{"id": "generate_cost", "label": "Cost to generate", "color": "#4A90D9", "style": "solid", "dataPoints": [{"x": 2000, "y": 85}, {"x": 2005, "y": 85}, {"x": 2010, "y": 84}, {"x": 2015, "y": 83}, {"x": 2020, "y": 82}, {"x": 2021, "y": 78}, {"x": 2022, "y": 75}, {"x": 2023, "y": 50}, {"x": 2024, "y": 25}, {"x": 2025, "y": 15}]}, {"id": "immediate_patch", "label": "Immediate patch cost", "color": "#D9944A", "style": "solid", "dataPoints": [{"x": 2000, "y": 40}, {"x": 2005, "y": 39}, {"x": 2010, "y": 38}, {"x": 2015, "y": 37}, {"x": 2020, "y": 35}, {"x": 2021, "y": 32}, {"x": 2022, "y": 28}, {"x": 2023, "y": 24}, {"x": 2024, "y": 22}, {"x": 2025, "y": 20}]}, {"id": "total_cost_debt", "label": "Total cost (with debt)", "color": "#D9944A", "style": "dashed", "dataPoints": [{"x": 2000, "y": 55}, {"x": 2005, "y": 55}, {"x": 2010, "y": 56}, {"x": 2015, "y": 56}, {"x": 2020, "y": 57}, {"x": 2021, "y": 57}, {"x": 2022, "y": 58}, {"x": 2023, "y": 59}, {"x": 2024, "y": 60}, {"x": 2025, "y": 60}]}], "keyDates": [{"year": 2021, "label": "Codex"}, {"year": 2023, "label": "GPT-4"}, {"year": 2023.5, "label": "Claude"}, {"year": 2024, "label": "Gemini"}], "debtShading": {"between": ["total_cost_debt", "immediate_patch"], "color": "#D9944A"}, "backgroundColor": "#0A0F1A", "narrationSegments": ["part1_economics_008", "part1_economics_009", "part1_economics_010", "part1_economics_011", "part1_economics_012", "part1_economics_013"]}, "mediaAliases": {}, "overlayConfig": null, "renderMode": "component"},
  "04_research_annotations": {"specBaseName": "04_research_annotations", "dataPoints": {"type": "annotation_overlay", "chartId": "code_cost_triple_line", "annotations": [{"id": "github_individual", "header": "Individual task: −55%", "source": "GitHub, 2022", "finePrint": "95 developers, one greenfield task", "color": "#4ADE80", "target": "immediate_patch_line", "wave": 1}, {"id": "uplevel_overall", "header": "Overall throughput: ~0%", "source": "Uplevel, 2024", "finePrint": "785 developers, one year", "color": "#EF4444", "target": "total_cost_line", "wave": 1}, {"id": "gitclear_churn", "header": "Code churn: +44%", "source": "GitClear, 2025", "finePrint": "211M lines analyzed", "color": "#EF4444", "target": "debt_shading", "wave": 2}, {"id": "gitclear_refactoring", "header": "Refactoring: −60%", "source": "GitClear, 2025", "finePrint": "Developers aren't cleaning up. They're piling on.", "color": "#EF4444", "target": "debt_gap", "wave": 2}], "backgroundColor": "#0A0F1A", "narrationSegments": ["part1_economics_014", "part1_economics_015", "part1_economics_016"]}, "mediaAliases": {}, "overlayConfig": null, "renderMode": "component"},
  "05_context_window_shrink": {"specBaseName": "05_context_window_shrink", "dataPoints": {"type": "animated_diagram", "diagramId": "context_window_shrink", "stages": [{"gridSize": 4, "blockPx": 60, "coveragePercent": 80, "color": "#4ADE80"}, {"gridSize": 8, "blockPx": 30, "coveragePercent": 40, "color": "#FBBF24"}, {"gridSize": 16, "blockPx": 15, "coveragePercent": 10, "color": "#EF4444"}, {"gridSize": 32, "blockPx": 7.5, "coveragePercent": 2, "color": "#DC2626"}], "contextWindow": {"width": 260, "height": 260, "color": "#4A90D9"}, "retrievalErrors": {"irrelevantInside": 3, "neededOutside": 5, "irrelevantColor": "#EF4444", "neededColor": "#4ADE80"}, "backgroundColor": "#0A0F1A", "narrationSegments": ["part1_economics_017", "part1_economics_018", "part1_economics_019", "part1_economics_020"]}, "mediaAliases": {}, "overlayConfig": null, "renderMode": "component"},
  "06_performance_vs_context": {"specBaseName": "06_performance_vs_context", "dataPoints": {"type": "inset_chart", "chartId": "performance_vs_context", "chartType": "single_line_degradation", "xAxis": {"label": "Context Length"}, "yAxis": {"label": "Model Performance"}, "series": [{"id": "performance_degradation", "color": "#EF4444", "degradationRange": {"min": 14, "max": 85}, "source": "EMNLP, 2025"}], "causalChain": ["Faster patching", "faster growth", "faster rot"], "backgroundColor": "#0A0F1A", "narrationSegments": ["part1_economics_021", "part1_economics_022"]}, "mediaAliases": {}, "overlayConfig": null, "renderMode": "component"},
  "07_two_by_two_grid": {"specBaseName": "07_two_by_two_grid", "dataPoints": {"type": "two_by_two_grid", "diagramId": "productivity_quadrant", "axes": {"x": {"start": "Greenfield", "end": "Brownfield"}, "y": {"start": "In-Distribution", "end": "Out-of-Distribution"}}, "quadrants": [{"position": "top-left", "label": "GitHub study", "value": "+55%", "color": "#4ADE80", "source": "GitHub, 2022"}, {"position": "bottom-right", "label": "METR study", "value": "−19%", "color": "#EF4444", "source": "METR, 2025"}, {"position": "top-right", "label": "Mixed", "color": "#64748B"}, {"position": "bottom-left", "label": "Mixed", "color": "#64748B"}], "summary": "Every study is correct. They just measured different quadrants.", "backgroundColor": "#0A0F1A", "narrationSegments": ["part1_economics_023"]}, "mediaAliases": {}, "overlayConfig": null, "renderMode": "component"},
  "08_fork_codebase_size": {"specBaseName": "08_fork_codebase_size", "dataPoints": {"type": "forking_chart", "chartId": "codebase_size_fork", "forkYear": 2020, "forks": [{"id": "small_codebase", "label": "Small codebase", "color": "#4ADE80", "dataPoints": [{"x": 2020, "y": 35}, {"x": 2021, "y": 28}, {"x": 2022, "y": 22}, {"x": 2023, "y": 15}, {"x": 2024, "y": 12}, {"x": 2025, "y": 10}]}, {"id": "large_codebase", "label": "Large codebase", "color": "#EF4444", "dataPoints": [{"x": 2020, "y": 35}, {"x": 2021, "y": 35}, {"x": 2022, "y": 34}, {"x": 2023, "y": 34}, {"x": 2024, "y": 33}, {"x": 2025, "y": 32}]}], "annotations": [{"text": "METR, 2025: experienced devs 19% slower on mature repos", "color": "#EF4444"}, {"text": "Developers believed AI saved 20%. It cost 19%.", "color": "#EF4444", "emphasis": true}], "trapArrow": {"label": "Every patch adds code.", "color": "#D9944A"}, "backgroundColor": "#0A0F1A", "narrationSegments": ["part1_economics_024", "part1_economics_025", "part1_economics_026"]}, "mediaAliases": {}, "overlayConfig": null, "renderMode": "component"},
  "09_patching_vs_regeneration_split": {"specBaseName": "09_patching_vs_regeneration_split", "dataPoints": {"type": "split_screen", "layout": "vertical_split", "splitPosition": 960, "leftPanel": {"label": "AGENTIC PATCHING", "content": "context_window_cluttered", "tokenCount": 15000, "relevantPercent": 5, "color": "#EF4444", "background": "#0A0F1A"}, "rightPanel": {"label": "PDD REGENERATION", "content": "context_window_clean", "tokenCount": 2500, "relevantPercent": 95, "sections": [{"label": "Prompt", "tokens": 300, "color": "#4A90D9"}, {"label": "Tests", "tokens": 2000, "color": "#D9944A"}, {"label": "Grounding", "tokens": 200, "color": "#5AAA6E"}], "color": "#4ADE80", "background": "#0A0F1A"}, "backgroundColor": "#000000", "narrationSegments": ["part1_economics_027", "part1_economics_028"]}, "mediaAliases": {}, "overlayConfig": null, "renderMode": "component"},
  "10_context_compression": {"specBaseName": "10_context_compression", "dataPoints": {"type": "animated_diagram", "diagramId": "context_compression", "moduleCount": 20, "codeBlockSize": {"width": 120, "height": 80}, "promptBlockSize": {"width": 50, "height": 30}, "compressionRatio": "5-10×", "contextWindow": {"width": 600, "height": 500}, "overflowCount": 12, "resultLabel": "Same system. 5-10× more fits.", "backgroundColor": "#0A0F1A", "narrationSegments": ["part1_economics_029", "part1_economics_030"]}, "mediaAliases": {}, "overlayConfig": null, "renderMode": "component"},
  "11_crossing_lines_moment": {"specBaseName": "11_crossing_lines_moment", "dataPoints": {"type": "chart_event", "chartId": "code_cost_triple_line", "event": "crossing_moment", "crossings": [{"id": "generate_crosses_total", "year": 2024, "y": 35, "radius": 8}, {"id": "generate_crosses_immediate", "year": 2025, "y": 20, "radius": 10}], "label": "We are here.", "debtResetNote": "Debt resets with each generation.", "backgroundColor": "#0A0F1A", "narrationSegments": ["part1_economics_031"]}, "mediaAliases": {}, "overlayConfig": null, "renderMode": "component"},
  "12_developer_darning_split": {"specBaseName": "12_developer_darning_split", "dataPoints": {"type": "split_screen", "layout": "vertical_split", "splitPosition": 960, "leftPanel": {"label": "CURSOR", "content": "developer_cursor_coding", "colorGrade": {"color": "#4A90D9", "opacity": 0.03}, "codeComments": ["// don't touch this", "// legacy", "// temporary fix (2019)"], "background": "#000000"}, "rightPanel": {"label": "DARNING NEEDLE", "content": "grandmother_darning_expert", "colorGrade": {"color": "#D4A043", "opacity": 0.04}, "background": "#000000"}, "embeddedVeoClips": ["developer_cursor_coding", "grandmother_darning_expert"], "backgroundColor": "#000000", "narrationSegments": ["part1_economics_032", "part1_economics_033"]}, "mediaAliases": {}, "overlayConfig": null, "renderMode": "component"},
  "13_developer_cursor_coding": {"specBaseName": "13_developer_cursor_coding", "dataPoints": {"type": "veo_clip", "clipId": "developer_cursor_coding", "camera": {"framing": "medium_close_up", "movement": "static", "dof": "shallow", "drift": false}, "lighting": {"key": {"color": "#B8D4E8", "position": "monitor", "type": "cool_blue"}, "fill": {"color": "#E8D5B8", "position": "side", "type": "ambient"}, "grade": "cool_professional"}, "embeddedIn": "12_developer_darning_split", "panel": "left", "narrationSegments": ["part1_economics_032"], "narrationTimingSeconds": {"start": 441.12, "end": 447.88}}, "mediaAliases": {"defaultSrc": "veo/developer_cursor_edit.mp4", "backgroundSrc": "veo/developer_cursor_edit.mp4", "outputSrc": "veo/developer_cursor_edit.mp4", "baseSrc": "veo/developer_cursor_edit.mp4"}, "overlayConfig": null, "renderMode": "raw-media"},
  "14_grandmother_darning_expert": {"specBaseName": "14_grandmother_darning_expert", "dataPoints": {"type": "veo_clip", "clipId": "grandmother_darning_expert", "camera": {"framing": "close_up", "movement": "static", "dof": "moderate", "drift": false}, "lighting": {"key": {"color": "#D4A043", "position": "upper_left", "type": "table_lamp"}, "fill": "minimal", "grade": "warm_amber"}, "characters": [{"id": "grandmother_darner", "label": "Grandmother", "referencePrompt": "Elderly woman with weathered skilled hands, domestic setting, warm lamplight"}], "embeddedIn": "12_developer_darning_split", "panel": "right", "narrationSegments": ["part1_economics_032"], "narrationTimingSeconds": {"start": 441.12, "end": 447.88}}, "mediaAliases": {"defaultSrc": "veo/grandmother_darning_lamplight.mp4", "backgroundSrc": "veo/grandmother_darning_lamplight.mp4", "outputSrc": "veo/grandmother_darning_lamplight.mp4", "baseSrc": "veo/grandmother_darning_lamplight.mp4"}, "overlayConfig": null, "renderMode": "raw-media"},
  "15_key_insight_stillness": {"specBaseName": "15_key_insight_stillness", "dataPoints": {"type": "title_card", "sectionNumber": "1.key", "sectionLabel": "THE KEY INSIGHT", "style": "stillness_beat", "backgroundColor": "#0A0F1A", "breathing": true, "narrationSegments": []}, "mediaAliases": {}, "overlayConfig": null, "renderMode": "component"},
  "16_double_meter_insight": {"specBaseName": "16_double_meter_insight", "dataPoints": {"type": "dual_meter", "diagramId": "double_meter_insight", "meters": [{"id": "context_window", "label": "Effective Context Window", "color": "#4A90D9", "scale": ["1×", "5×", "10×"], "fillFrom": 0.2, "fillTo": 1.0}, {"id": "model_performance", "label": "Model Performance", "color": "#4ADE80", "scale": ["Baseline", "Optimal"], "fillFrom": 0.2, "fillTo": 1.0}], "peakText": "Bigger window AND smarter model.", "subtext": "Not one or the other. Both. That's a category shift.", "backgroundColor": "#0A0F1A", "narrationSegments": []}, "mediaAliases": {}, "overlayConfig": null, "renderMode": "component"},
  "17_try_it_yourself": {"specBaseName": "17_try_it_yourself", "dataPoints": {"type": "title_card", "sectionNumber": "1.end", "style": "handwritten_challenge", "challenge": "Try it yourself.", "supportingText": ["Take your favorite LLM.", "Give it a hard coding problem as code,", "then as natural language.", "The natural language version will win."], "font": "Caveat", "backgroundColor": "#0A0F1A", "narrationSegments": []}, "mediaAliases": {}, "overlayConfig": null, "renderMode": "component"},
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
                <OffthreadVideo src={staticFile(visualMedia.defaultSrc)} style={{ width: "100%", height: "100%" }} />
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
