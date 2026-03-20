import React from "react";
import { Sequence, useCurrentFrame, Audio, OffthreadVideo, staticFile } from "remotion";
import { VISUAL_SEQUENCE } from "./constants";
import { SlotScaledSequence, VisualMediaProvider, VisualContractProvider } from "../_shared/visual-runtime";
import { GeneratedMediaVisual } from "../_shared/GeneratedMediaVisual";
import { Part1Economics01SectionTitleCard } from "../Part1Economics01SectionTitleCard";
import { Part1Economics02SockEconomicsChart } from "../Part1Economics02SockEconomicsChart";
import { Part1Economics03CodeCostTripleLine } from "../Part1Economics03CodeCostTripleLine";
import { Part1Economics04ResearchAnnotations } from "../Part1Economics04ResearchAnnotations";
import { Part1Economics05ContextWindowShrink } from "../Part1Economics05ContextWindowShrink";
import { Part1Economics06TwoByTwoGrid } from "../Part1Economics06TwoByTwoGrid";
import { Part1Economics07SplitContextComparison } from "../Part1Economics07SplitContextComparison";
import { Part1Economics09CrossingLinesMoment } from "../Part1Economics09CrossingLinesMoment";
import { Part1Economics10DoubleMeterInsight } from "../Part1Economics10DoubleMeterInsight";

const COMPONENT_MAP: Record<string, React.ComponentType<any>> = {
  "01_section_title_card": Part1Economics01SectionTitleCard,
  "02_sock_economics_chart": Part1Economics02SockEconomicsChart,
  "03_code_cost_triple_line": Part1Economics03CodeCostTripleLine,
  "04_research_annotations": Part1Economics04ResearchAnnotations,
  "05_context_window_shrink": Part1Economics05ContextWindowShrink,
  "06_two_by_two_grid": Part1Economics06TwoByTwoGrid,
  "07_split_context_comparison": Part1Economics07SplitContextComparison,
  "09_crossing_lines_moment": Part1Economics09CrossingLinesMoment,
  "10_double_meter_insight": Part1Economics10DoubleMeterInsight,
};

const VISUAL_DURATIONS: Record<string, number> = {
  "01_section_title_card": 120,
  "02_sock_economics_chart": 540,
  "03_code_cost_triple_line": 1050,
  "04_research_annotations": 900,
  "05_context_window_shrink": 900,
  "06_two_by_two_grid": 750,
  "07_split_context_comparison": 600,
  "09_crossing_lines_moment": 750,
  "10_double_meter_insight": 750,
};

const VISUAL_MEDIA: Record<string, Record<string, string>> = {
  "08_developer_patching_montage": { defaultSrc: "veo/developer_patching_montage.mp4", backgroundSrc: "veo/developer_patching_montage.mp4", outputSrc: "veo/developer_patching_montage.mp4", baseSrc: "veo/developer_patching_montage.mp4" },
  "09_crossing_lines_moment": { defaultSrc: "veo/developer_patching_montage.mp4", backgroundSrc: "veo/developer_patching_montage.mp4", outputSrc: "veo/developer_patching_montage.mp4", baseSrc: "veo/developer_patching_montage.mp4" },
  "10_double_meter_insight": { defaultSrc: "veo/developer_patching_montage.mp4", backgroundSrc: "veo/developer_patching_montage.mp4", outputSrc: "veo/developer_patching_montage.mp4", baseSrc: "veo/developer_patching_montage.mp4" },
};

const VISUAL_OVERLAYS: Record<string, Record<string, string | boolean>> = {
  "08_developer_patching_montage": { gradientOverlay: "bottom" },
};

const VISUAL_CONTRACTS: Record<string, Record<string, unknown> | null> = {
  "01_section_title_card": {"specBaseName": "01_section_title_card", "dataPoints": {"type": "title_card", "sectionNumber": 1, "sectionLabel": "Part 1", "title": "The Economics of Darning", "titleColor": "#D9944A", "subtitle": "Why patching was rational — and when it stopped.", "subtitleColor": "#94A3B8", "backgroundColor": "#0D1117", "narrationSegments": ["part1_economics_001"]}, "overlayConfig": null, "renderMode": "component"},
  "02_sock_economics_chart": {"specBaseName": "02_sock_economics_chart", "dataPoints": {"type": "animated_chart", "chartType": "dual_line_crossover", "xAxis": {"label": "Year", "range": [1950, 1975], "majorInterval": 5, "minorInterval": 1}, "yAxis": {"label": "Cost (% of hourly wage)", "range": [0, 100], "majorInterval": 25}, "series": [{"id": "labor_cost_darn", "label": "Cost to darn (time)", "color": "#D9944A", "data": [{"x": 1950, "y": 35}, {"x": 1955, "y": 34}, {"x": 1960, "y": 33}, {"x": 1965, "y": 33}, {"x": 1970, "y": 32}, {"x": 1975, "y": 32}]}, {"id": "new_sock_cost", "label": "Cost of new socks", "color": "#4A90D9", "data": [{"x": 1950, "y": 80}, {"x": 1955, "y": 55}, {"x": 1960, "y": 38}, {"x": 1962, "y": 33}, {"x": 1965, "y": 25}, {"x": 1970, "y": 18}, {"x": 1975, "y": 14}]}], "crossingPoint": {"x": 1962, "y": 33, "label": "The Threshold"}, "backgroundColor": "#0D1117", "narrationSegments": ["part1_economics_002", "part1_economics_004"]}, "overlayConfig": null, "renderMode": "component"},
  "03_code_cost_triple_line": {"specBaseName": "03_code_cost_triple_line", "dataPoints": {"type": "animated_chart", "chartType": "triple_line_debt_reveal", "xAxis": {"label": "Year", "range": [2015, 2025], "majorInterval": 2, "minorInterval": 1}, "yAxis": {"label": "Cost (Developer Hours)", "range": [0, 20], "majorInterval": 5}, "milestones": [{"x": 2021, "label": "Codex"}, {"x": 2022, "label": "Copilot"}, {"x": 2023, "label": "GPT-4 / Claude"}, {"x": 2024, "label": "Cursor / Claude Code"}], "series": [{"id": "cost_to_generate", "label": "Cost to generate", "color": "#4A90D9", "strokeWidth": 3, "style": "solid", "data": [{"x": 2015, "y": 18}, {"x": 2018, "y": 17.5}, {"x": 2020, "y": 17}, {"x": 2021, "y": 16}, {"x": 2022, "y": 14}, {"x": 2023, "y": 10}, {"x": 2024, "y": 6}, {"x": 2025, "y": 4}]}, {"id": "immediate_patch_cost", "label": "Immediate patch cost", "color": "#D9944A", "strokeWidth": 3, "style": "solid", "data": [{"x": 2015, "y": 8}, {"x": 2018, "y": 7.5}, {"x": 2020, "y": 7}, {"x": 2021, "y": 6}, {"x": 2022, "y": 5}, {"x": 2023, "y": 4}, {"x": 2024, "y": 3}, {"x": 2025, "y": 2}]}, {"id": "total_cost_with_debt", "label": "Total cost (with debt)", "color": "#D9944A", "strokeWidth": 2, "style": "dashed", "data": [{"x": 2015, "y": 14}, {"x": 2018, "y": 14}, {"x": 2020, "y": 13.5}, {"x": 2021, "y": 13.5}, {"x": 2022, "y": 13}, {"x": 2023, "y": 13}, {"x": 2024, "y": 13}, {"x": 2025, "y": 13}]}], "debtShadedArea": {"upperSeries": "total_cost_with_debt", "lowerSeries": "immediate_patch_cost", "color": "#D9944A", "opacity": 0.08}, "backgroundColor": "#0D1117", "narrationSegments": ["part1_economics_005", "part1_economics_006", "part1_economics_008", "part1_economics_009", "part1_economics_011", "part1_economics_012"]}, "overlayConfig": null, "renderMode": "component"},
  "04_research_annotations": {"specBaseName": "04_research_annotations", "dataPoints": {"type": "animated_chart_overlay", "chartType": "annotation_stack", "annotations": [{"id": "github_study", "title": "Individual task: −55%", "source": "GitHub, 2022", "detail": "95 developers, one greenfield task", "color": "#4A90D9", "targetSeries": "immediate_patch_cost", "targetX": 2022}, {"id": "uplevel_study", "title": "Overall throughput: ~0%", "source": "Uplevel, 2024", "detail": "785 developers, one year", "extra": "+41% more bugs", "color": "#D9944A", "targetSeries": "total_cost_with_debt", "targetX": 2024}, {"id": "gitclear_study", "title": ["Code churn: +44%", "Refactoring: −60%"], "source": "GitClear, 2025", "detail": "211M lines analyzed", "color": "#E74C3C", "targetArea": "debt_shaded_area"}], "debtDecomposition": {"upperLayer": {"label": "Code Complexity", "color": "#D9944A", "opacity": 0.1}, "lowerLayer": {"label": "Context Rot", "color": "#D9944A", "opacity": 0.05, "noiseTexture": true}}, "backgroundColor": "#0D1117", "narrationSegments": ["part1_economics_013", "part1_economics_014", "part1_economics_015", "part1_economics_016"]}, "overlayConfig": null, "renderMode": "component"},
  "05_context_window_shrink": {"specBaseName": "05_context_window_shrink", "dataPoints": {"type": "spatial_visualization", "chartType": "context_window_shrink", "gridStages": [{"size": 4, "coverage": 0.8, "coverageColor": "#5AAA6E"}, {"size": 8, "coverage": 0.4, "coverageColor": "#D9C44A"}, {"size": 16, "coverage": 0.1, "coverageColor": "#D9944A"}, {"size": 32, "coverage": 0.02, "coverageColor": "#E74C3C"}], "contextWindow": {"fixedSize": {"width": 480, "height": 480}, "borderColor": "#4A90D9", "glowColor": "#4A90D9"}, "highlights": {"irrelevantInsideWindow": {"count": 4, "color": "#E74C3C"}, "neededOutsideWindow": {"count": 6, "color": "#5AAA6E"}}, "insetGraph": {"title": "Performance vs. Context Length", "citation": "EMNLP, 2025", "degradationRange": "14% to 85%", "lineColor": "#E74C3C"}, "backgroundColor": "#0D1117", "narrationSegments": ["part1_economics_017", "part1_economics_018", "part1_economics_019", "part1_economics_020"]}, "overlayConfig": null, "renderMode": "component"},
  "06_two_by_two_grid": {"specBaseName": "06_two_by_two_grid", "dataPoints": {"type": "quadrant_grid", "chartType": "two_by_two_study_comparison", "axes": {"x": {"left": "Greenfield", "right": "Brownfield"}, "y": {"top": "In-Distribution", "bottom": "Out-of-Distribution"}}, "quadrants": [{"position": "top-left", "study": "GitHub, 2022", "stat": "+55%", "color": "#5AAA6E", "detail": "95 devs, greenfield"}, {"position": "bottom-right", "study": "METR, 2025", "stat": "−19%", "color": "#E74C3C", "detail": "experienced devs, mature repos"}, {"position": "top-right", "label": "Mixed results", "color": "#D9944A"}, {"position": "bottom-left", "label": "Mixed results", "color": "#D9944A"}], "enterpriseIndicator": {"quadrant": "bottom-right", "label": "Most enterprise work", "radius": 100, "color": "#E74C3C"}, "summary": "Every study is correct. They just measured different quadrants.", "backgroundColor": "#0D1117", "narrationSegments": ["part1_economics_021", "part1_economics_022"]}, "overlayConfig": null, "renderMode": "component"},
  "07_split_context_comparison": {"specBaseName": "07_split_context_comparison", "dataPoints": {"type": "split_screen", "layout": "vertical_split", "splitPosition": 960, "leftPanel": {"label": "Agentic Patching", "labelColor": "#D9944A", "content": "dense_code_context_window", "tokenCount": 15000, "irrelevantPercent": 60, "fillPercent": 100, "highlights": {"irrelevant": {"count": 5, "color": "#E74C3C"}, "relevant": {"percent": 8, "color": "#5AAA6E"}}}, "rightPanel": {"label": "PDD Regeneration", "labelColor": "#4A90D9", "content": "prompt_context_window", "tokenCount": 2300, "sections": [{"type": "prompt", "lines": 15, "color": "#4A90D9"}, {"type": "tests", "lines": 12, "color": "#5AAA6E"}, {"type": "grounding", "lines": 6, "color": "#94A3B8"}], "fillPercent": 25, "qualityNote": "100% author-curated"}, "backgroundColor": "#000000", "narrationSegments": ["part1_economics_024", "part1_economics_025"]}, "overlayConfig": null, "renderMode": "component"},
  "08_developer_patching_montage": {"specBaseName": "08_developer_patching_montage", "dataPoints": {"type": "veo_clip", "clipId": "developer_patching_montage", "camera": {"framing": "medium_shot_to_screen_rack", "movement": "rack_focus_only", "dof": "shallow", "aperture": "f/2.0", "angle": "over_the_shoulder"}, "lighting": {"key": {"color": "#4A90D9", "position": "front_monitor", "type": "screen_glow"}, "fill": {"color": "#2A1F14", "opacity": 0.15, "type": "ambient"}, "rim": "faint_edge", "grade": "cool_desaturated"}, "characters": [{"id": "developer", "label": "Developer", "referencePrompt": "Software developer, mid-30s, focused and competent expression, wearing casual professional attire. Lit by cool blue monitor glow in a dark office/home office. Modern keyboard and large monitor visible."}], "screenContent": {"ide": "dark_theme", "comments": ["// don't touch this", "// legacy", "// temporary fix (2019)"], "density": "high"}, "narrationSegments": ["part1_economics_026"], "narrationTimingSeconds": {"start": 312, "end": 320}}, "overlayConfig": {"gradientOverlay": "bottom"}, "renderMode": "generated-media"},
  "09_crossing_lines_moment": {"specBaseName": "09_crossing_lines_moment", "dataPoints": {"type": "animated_chart", "chartType": "forked_line_crossing", "forkedLine": {"forkPoint": {"x": 2020, "y": 7}, "lowerFork": {"id": "small_codebase", "label": "Small codebase", "color": "#5AAA6E", "data": [{"x": 2020, "y": 7}, {"x": 2022, "y": 4}, {"x": 2024, "y": 2}, {"x": 2025, "y": 1}]}, "upperFork": {"id": "large_codebase", "label": "Large codebase", "color": "#E74C3C", "data": [{"x": 2020, "y": 7}, {"x": 2022, "y": 10}, {"x": 2024, "y": 11}, {"x": 2025, "y": 12}]}}, "crossingLabel": "We are here.", "metrAnnotation": {"perceived": "+20%", "actual": "−19%", "perceptionGap": "39 points"}, "accumulationArrow": {"label": "Every patch adds code", "from": "lower_fork", "to": "upper_fork"}, "terminalBreadcrumb": "pdd generate", "backgroundColor": "#0D1117", "narrationSegments": ["part1_economics_025", "part1_economics_026", "part1_economics_032", "part1_economics_033"]}, "overlayConfig": null, "renderMode": "component"},
  "10_double_meter_insight": {"specBaseName": "10_double_meter_insight", "dataPoints": {"type": "double_meter", "chartType": "key_insight_dual_meter", "meters": [{"id": "effective_context_window", "label": "Effective Context Window", "color": "#4A90D9", "position": "left", "scaleMarkers": ["1×", "5×", "10×"], "maxValue": 10, "unit": "×", "citations": ["MIT CSAIL, 2024", "prompt compression ratio 5:1 to 10:1"]}, {"id": "model_performance", "label": "Model Performance", "color": "#5AAA6E", "position": "right", "scaleMarkers": ["baseline", "+50%", "+89%"], "maxValue": 89, "unit": "%", "citations": ["MIT CSAIL: NL context +59-89%", "ACL 2024: NL comments +41% HumanEval"]}], "centerText": "Bigger window AND smarter model.", "summary": "Not one or the other. Both. That's a category shift.", "challenge": "Try it yourself.", "backgroundColor": "#0D1117", "narrationSegments": ["part1_economics_032", "part1_economics_033"]}, "overlayConfig": null, "renderMode": "component"},
};

export const Part1EconomicsSection: React.FC = () => {
  const fps = 30;
  const durationSeconds = 455.44;
  const frame = useCurrentFrame();
  const activeVisuals = VISUAL_SEQUENCE.filter((visual) => frame >= visual.start && frame < visual.end);

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
                  <VisualMediaProvider media={visualMedia}>
                    <VisualComponent />
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
