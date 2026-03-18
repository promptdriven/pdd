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
  "01_section_title_card": {"specBaseName": "01_section_title_card", "dataPoints": null, "overlayConfig": null},
  "02_sock_economics_chart": {"specBaseName": "02_sock_economics_chart", "dataPoints": null, "overlayConfig": null},
  "03_code_cost_triple_line": {"specBaseName": "03_code_cost_triple_line", "dataPoints": null, "overlayConfig": null},
  "04_research_annotations": {"specBaseName": "04_research_annotations", "dataPoints": null, "overlayConfig": null},
  "05_context_window_shrink": {"specBaseName": "05_context_window_shrink", "dataPoints": null, "overlayConfig": null},
  "06_two_by_two_grid": {"specBaseName": "06_two_by_two_grid", "dataPoints": null, "overlayConfig": null},
  "07_split_context_comparison": {"specBaseName": "07_split_context_comparison", "dataPoints": null, "overlayConfig": null},
  "08_developer_patching_montage": {"specBaseName": "08_developer_patching_montage", "dataPoints": null, "overlayConfig": {"gradientOverlay": "bottom"}},
  "09_crossing_lines_moment": {"specBaseName": "09_crossing_lines_moment", "dataPoints": null, "overlayConfig": null},
  "10_double_meter_insight": {"specBaseName": "10_double_meter_insight", "dataPoints": null, "overlayConfig": null},
};

export const Part1EconomicsSection: React.FC = () => {
  const fps = 30;
  const durationSeconds = 0.426667;
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
