import React from "react";
import { Sequence, useCurrentFrame, Audio, OffthreadVideo, staticFile } from "remotion";
import { VISUAL_SEQUENCE } from "./constants";
import { SlotScaledSequence, VisualMediaProvider, VisualContractProvider } from "../_shared/visual-runtime";
import { Part3MoldThreeParts01SectionTitleCard } from "../Part3MoldThreeParts01SectionTitleCard";
import { Part3MoldThreeParts02MoldCrossSection } from "../Part3MoldThreeParts02MoldCrossSection";
import { Part3MoldThreeParts03TestWallsConstraint } from "../Part3MoldThreeParts03TestWallsConstraint";
import { Part3MoldThreeParts04ResearchAnnotationsAiQuality } from "../Part3MoldThreeParts04ResearchAnnotationsAiQuality";
import { Part3MoldThreeParts06RatchetSplitComparison } from "../Part3MoldThreeParts06RatchetSplitComparison";
import { Part3MoldThreeParts07FiveGenerationsZ3 } from "../Part3MoldThreeParts07FiveGenerationsZ3";
import { Part3MoldThreeParts08PromptCapitalSpecification } from "../Part3MoldThreeParts08PromptCapitalSpecification";
import { Part3MoldThreeParts10ThreeComponentsTable } from "../Part3MoldThreeParts10ThreeComponentsTable";

const COMPONENT_MAP: Record<string, React.ComponentType<any>> = {
  "01_section_title_card": Part3MoldThreeParts01SectionTitleCard,
  "02_mold_cross_section": Part3MoldThreeParts02MoldCrossSection,
  "03_test_walls_constraint": Part3MoldThreeParts03TestWallsConstraint,
  "04_research_annotations_ai_quality": Part3MoldThreeParts04ResearchAnnotationsAiQuality,
  "06_ratchet_split_comparison": Part3MoldThreeParts06RatchetSplitComparison,
  "07_five_generations_z3": Part3MoldThreeParts07FiveGenerationsZ3,
  "08_prompt_capital_specification": Part3MoldThreeParts08PromptCapitalSpecification,
  "10_three_components_table": Part3MoldThreeParts10ThreeComponentsTable,
};

const VISUAL_DURATIONS: Record<string, number> = {
  "01_section_title_card": 120,
  "02_mold_cross_section": 300,
  "03_test_walls_constraint": 360,
  "04_research_annotations_ai_quality": 450,
  "08_prompt_capital_specification": 600,
  "10_three_components_table": 480,
};

const VISUAL_MEDIA: Record<string, Record<string, string>> = {
  "05_bug_adds_wall": { defaultSrc: "veo/bug_adds_wall.mp4", backgroundSrc: "veo/bug_adds_wall.mp4", outputSrc: "veo/bug_adds_wall.mp4", baseSrc: "veo/bug_adds_wall.mp4" },
  "06_ratchet_split_comparison": { defaultSrc: "veo/bug_adds_wall.mp4", backgroundSrc: "veo/bug_adds_wall.mp4", outputSrc: "veo/bug_adds_wall.mp4", baseSrc: "veo/bug_adds_wall.mp4" },
  "07_five_generations_z3": { defaultSrc: "veo/bug_adds_wall.mp4", backgroundSrc: "veo/bug_adds_wall.mp4", outputSrc: "veo/bug_adds_wall.mp4", baseSrc: "veo/bug_adds_wall.mp4" },
  "08_prompt_capital_specification": { defaultSrc: "veo/bug_adds_wall.mp4", backgroundSrc: "veo/bug_adds_wall.mp4", outputSrc: "veo/bug_adds_wall.mp4", baseSrc: "veo/bug_adds_wall.mp4" },
  "09_grounding_feedback_loop": { defaultSrc: "veo/grounding_feedback_loop.mp4", backgroundSrc: "veo/grounding_feedback_loop.mp4", outputSrc: "veo/grounding_feedback_loop.mp4", baseSrc: "veo/grounding_feedback_loop.mp4" },
  "10_three_components_table": { defaultSrc: "veo/grounding_feedback_loop.mp4", backgroundSrc: "veo/grounding_feedback_loop.mp4", outputSrc: "veo/grounding_feedback_loop.mp4", baseSrc: "veo/grounding_feedback_loop.mp4" },
};

const VISUAL_OVERLAYS: Record<string, Record<string, string | boolean>> = {
};

const VISUAL_CONTRACTS: Record<string, Record<string, unknown> | null> = {
  "01_section_title_card": {"specBaseName": "01_section_title_card", "dataPoints": null, "overlayConfig": null},
  "02_mold_cross_section": {"specBaseName": "02_mold_cross_section", "dataPoints": null, "overlayConfig": null},
  "03_test_walls_constraint": {"specBaseName": "03_test_walls_constraint", "dataPoints": null, "overlayConfig": null},
  "04_research_annotations_ai_quality": {"specBaseName": "04_research_annotations_ai_quality", "dataPoints": null, "overlayConfig": null},
  "05_bug_adds_wall": {"specBaseName": "05_bug_adds_wall", "dataPoints": null, "overlayConfig": null},
  "06_ratchet_split_comparison": {"specBaseName": "06_ratchet_split_comparison", "dataPoints": null, "overlayConfig": null},
  "07_five_generations_z3": {"specBaseName": "07_five_generations_z3", "dataPoints": null, "overlayConfig": null},
  "08_prompt_capital_specification": {"specBaseName": "08_prompt_capital_specification", "dataPoints": null, "overlayConfig": null},
  "09_grounding_feedback_loop": {"specBaseName": "09_grounding_feedback_loop", "dataPoints": null, "overlayConfig": null},
  "10_three_components_table": {"specBaseName": "10_three_components_table", "dataPoints": null, "overlayConfig": null},
};

export const Part3MoldThreePartsSection: React.FC = () => {
  const fps = 30;
  const durationSeconds = 344.16;
  const frame = useCurrentFrame();
  const activeVisuals = VISUAL_SEQUENCE.filter((visual) => frame >= visual.start && frame < visual.end);

  return (
    <Sequence from={0} durationInFrames={Math.max(1, Math.ceil(durationSeconds * fps))}>
      <Audio src={staticFile("part3_mold_three_parts/narration.wav")} />
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

export default Part3MoldThreePartsSection;
