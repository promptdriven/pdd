import React from "react";
import { Sequence, useCurrentFrame, Audio, staticFile } from "remotion";
import { VISUAL_SEQUENCE } from "./constants";
import { SlotScaledSequence, VisualMediaProvider, VisualContractProvider } from "../_shared/visual-runtime";
import { Part1Economics01SectionTitleCard } from "../Part1Economics01SectionTitleCard";
import { Part1Economics04ResearchAnnotations } from "../Part1Economics04ResearchAnnotations";
import { Part1Economics05ContextWindowShrink } from "../Part1Economics05ContextWindowShrink";

const COMPONENT_MAP: Record<string, React.ComponentType<any>> = {
  "01_section_title_card": Part1Economics01SectionTitleCard,
  "04_research_annotations": Part1Economics04ResearchAnnotations,
  "05_context_window_shrink": Part1Economics05ContextWindowShrink,
};

const VISUAL_DURATIONS: Record<string, number> = {
  "01_section_title_card": 120,
  "04_research_annotations": 900,
  "05_context_window_shrink": 900,
};

const VISUAL_MEDIA: Record<string, Record<string, string>> = {
};

const VISUAL_OVERLAYS: Record<string, Record<string, string | boolean>> = {
};

const VISUAL_CONTRACTS: Record<string, Record<string, unknown> | null> = {
  "01_section_title_card": {"specBaseName": "01_section_title_card", "dataPoints": {"type": "title_card", "sectionNumber": 1, "sectionLabel": "PART 1", "titleLine1": "THE ECONOMICS", "titleLine2": "OF DARNING", "backgroundColor": "#0A0F1A", "ghostElements": [{"shape": "quadratic_curve", "color": "#D9944A", "component": "descending_cost"}, {"shape": "quadratic_curve", "color": "#4A90D9", "component": "ascending_cost"}, {"shape": "crossing_point", "color": "#E2E8F0", "component": "threshold"}], "narrationSegments": ["part1_economics_001", "part1_economics_002"]}, "overlayConfig": null, "renderMode": "component"},
  "04_research_annotations": {"specBaseName": "04_research_annotations", "dataPoints": {"type": "annotation_overlay", "chartId": "code_cost_triple_line", "annotations": [{"id": "github_individual", "header": "Individual task: −55%", "source": "GitHub, 2022", "finePrint": "95 developers, one greenfield task", "color": "#4ADE80", "target": "immediate_patch_line", "wave": 1}, {"id": "uplevel_overall", "header": "Overall throughput: ~0%", "source": "Uplevel, 2024", "finePrint": "785 developers, one year", "color": "#EF4444", "target": "total_cost_line", "wave": 1}, {"id": "gitclear_churn", "header": "Code churn: +44%", "source": "GitClear, 2025", "finePrint": "211M lines analyzed", "color": "#EF4444", "target": "debt_shading", "wave": 2}, {"id": "gitclear_refactoring", "header": "Refactoring: −60%", "source": "GitClear, 2025", "finePrint": "Developers aren't cleaning up. They're piling on.", "color": "#EF4444", "target": "debt_gap", "wave": 2}], "backgroundColor": "#0A0F1A", "narrationSegments": ["part1_economics_014", "part1_economics_015", "part1_economics_016"]}, "overlayConfig": null, "renderMode": "component"},
  "05_context_window_shrink": {"specBaseName": "05_context_window_shrink", "dataPoints": {"type": "animated_diagram", "diagramId": "context_window_shrink", "stages": [{"gridSize": 4, "blockPx": 60, "coveragePercent": 80, "color": "#4ADE80"}, {"gridSize": 8, "blockPx": 30, "coveragePercent": 40, "color": "#FBBF24"}, {"gridSize": 16, "blockPx": 15, "coveragePercent": 10, "color": "#EF4444"}, {"gridSize": 32, "blockPx": 7.5, "coveragePercent": 2, "color": "#DC2626"}], "contextWindow": {"width": 260, "height": 260, "color": "#4A90D9"}, "retrievalErrors": {"irrelevantInside": 3, "neededOutside": 5, "irrelevantColor": "#EF4444", "neededColor": "#4ADE80"}, "backgroundColor": "#0A0F1A", "narrationSegments": ["part1_economics_017", "part1_economics_018", "part1_economics_019", "part1_economics_020"]}, "overlayConfig": null, "renderMode": "component"},
  "06_performance_vs_context": {"specBaseName": "06_performance_vs_context", "dataPoints": {"type": "inset_chart", "chartId": "performance_vs_context", "chartType": "single_line_degradation", "xAxis": {"label": "Context Length"}, "yAxis": {"label": "Model Performance"}, "series": [{"id": "performance_degradation", "color": "#EF4444", "degradationRange": {"min": 14, "max": 85}, "source": "EMNLP, 2025"}], "causalChain": ["Faster patching", "faster growth", "faster rot"], "backgroundColor": "#0A0F1A", "narrationSegments": ["part1_economics_021", "part1_economics_022"]}, "overlayConfig": null, "renderMode": "component"},
  "07_two_by_two_grid": {"specBaseName": "07_two_by_two_grid", "dataPoints": {"type": "two_by_two_grid", "diagramId": "productivity_quadrant", "axes": {"x": {"start": "Greenfield", "end": "Brownfield"}, "y": {"start": "In-Distribution", "end": "Out-of-Distribution"}}, "quadrants": [{"position": "top-left", "label": "GitHub study", "value": "+55%", "color": "#4ADE80", "source": "GitHub, 2022"}, {"position": "bottom-right", "label": "METR study", "value": "−19%", "color": "#EF4444", "source": "METR, 2025"}, {"position": "top-right", "label": "Mixed", "color": "#64748B"}, {"position": "bottom-left", "label": "Mixed", "color": "#64748B"}], "summary": "Every study is correct. They just measured different quadrants.", "backgroundColor": "#0A0F1A", "narrationSegments": ["part1_economics_023"]}, "overlayConfig": null, "renderMode": "component"},
  "09_patching_vs_regeneration_split": {"specBaseName": "09_patching_vs_regeneration_split", "dataPoints": {"type": "split_screen", "layout": "vertical_split", "splitPosition": 960, "leftPanel": {"label": "AGENTIC PATCHING", "content": "context_window_cluttered", "tokenCount": 15000, "relevantPercent": 5, "color": "#EF4444", "background": "#0A0F1A"}, "rightPanel": {"label": "PDD REGENERATION", "content": "context_window_clean", "tokenCount": 2500, "relevantPercent": 95, "sections": [{"label": "Prompt", "tokens": 300, "color": "#4A90D9"}, {"label": "Tests", "tokens": 2000, "color": "#D9944A"}, {"label": "Grounding", "tokens": 200, "color": "#5AAA6E"}], "color": "#4ADE80", "background": "#0A0F1A"}, "backgroundColor": "#000000", "narrationSegments": ["part1_economics_027", "part1_economics_028"]}, "overlayConfig": null, "renderMode": "component"},
  "12_developer_darning_split": {"specBaseName": "12_developer_darning_split", "dataPoints": {"type": "split_screen", "layout": "vertical_split", "splitPosition": 960, "leftPanel": {"label": "CURSOR", "content": "developer_cursor_coding", "colorGrade": {"color": "#4A90D9", "opacity": 0.03}, "codeComments": ["// don't touch this", "// legacy", "// temporary fix (2019)"], "background": "#000000"}, "rightPanel": {"label": "DARNING NEEDLE", "content": "grandmother_darning_expert", "colorGrade": {"color": "#D4A043", "opacity": 0.04}, "background": "#000000"}, "embeddedVeoClips": ["developer_cursor_coding", "grandmother_darning_expert"], "backgroundColor": "#000000", "narrationSegments": ["part1_economics_032", "part1_economics_033"]}, "overlayConfig": null, "renderMode": "component"},
  "13_developer_cursor_coding": {"specBaseName": "13_developer_cursor_coding", "dataPoints": {"type": "veo_clip", "clipId": "developer_cursor_coding", "camera": {"framing": "medium_close_up", "movement": "static", "dof": "shallow", "drift": false}, "lighting": {"key": {"color": "#B8D4E8", "position": "monitor", "type": "cool_blue"}, "fill": {"color": "#E8D5B8", "position": "side", "type": "ambient"}, "grade": "cool_professional"}, "embeddedIn": "12_developer_darning_split", "panel": "left", "narrationSegments": ["part1_economics_032"], "narrationTimingSeconds": {"start": 441.12, "end": 447.88}}, "overlayConfig": null, "renderMode": "component"},
  "14_grandmother_darning_expert": {"specBaseName": "14_grandmother_darning_expert", "dataPoints": {"type": "veo_clip", "clipId": "grandmother_darning_expert", "camera": {"framing": "close_up", "movement": "static", "dof": "moderate", "drift": false}, "lighting": {"key": {"color": "#D4A043", "position": "upper_left", "type": "table_lamp"}, "fill": "minimal", "grade": "warm_amber"}, "characters": [{"id": "grandmother_darner", "label": "Grandmother", "referencePrompt": "Elderly woman with weathered skilled hands, domestic setting, warm lamplight"}], "embeddedIn": "12_developer_darning_split", "panel": "right", "narrationSegments": ["part1_economics_032"], "narrationTimingSeconds": {"start": 441.12, "end": 447.88}}, "overlayConfig": null, "renderMode": "component"},
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
            ) : null}
          </Sequence>
        );
      })}
    </Sequence>
  );
};

export default Part1EconomicsSection;
