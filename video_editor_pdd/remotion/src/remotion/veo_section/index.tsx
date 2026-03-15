import React from "react";
import { Sequence, useCurrentFrame, Audio, OffthreadVideo, staticFile } from "remotion";
import { VISUAL_SEQUENCE } from "./constants";
import { SlotScaledSequence, VisualMediaProvider, VisualContractProvider } from "../_shared/visual-runtime";
import { VeoSection01TitleCard } from "../VeoSection01TitleCard";
import { VeoSection04WaveDataOverlay } from "../VeoSection04WaveDataOverlay";
import { VeoSection05SplitNatureComparison } from "../VeoSection05SplitNatureComparison";
import { VeoSection06VeoPipelineInfographic } from "../VeoSection06VeoPipelineInfographic";
import { VeoSection07NarrationOverlayIntro } from "../VeoSection07NarrationOverlayIntro";
import { VeoSection08SectionEndCard } from "../VeoSection08SectionEndCard";

const COMPONENT_MAP: Record<string, React.ComponentType<any>> = {
  "veo_section_01_title_card": VeoSection01TitleCard,
  "04_wave_data_overlay": VeoSection04WaveDataOverlay,
  "05_split_nature_comparison": VeoSection05SplitNatureComparison,
  "06_veo_pipeline_infographic": VeoSection06VeoPipelineInfographic,
  "07_narration_overlay_intro": VeoSection07NarrationOverlayIntro,
  "08_section_end_card": VeoSection08SectionEndCard,
};

const VISUAL_DURATIONS: Record<string, number> = {
  "veo_section_01_title_card": 30,
  "04_wave_data_overlay": 30,
  "06_veo_pipeline_infographic": 30,
  "07_narration_overlay_intro": 24,
  "08_section_end_card": 24,
};

const VISUAL_MEDIA: Record<string, Record<string, string>> = {
  "veo_section_01_title_card": { defaultSrc: "veo_section.mp4", backgroundSrc: "veo_section.mp4", outputSrc: "veo_section.mp4", baseSrc: "veo_section.mp4" },
  "04_wave_data_overlay": { defaultSrc: "veo_section.mp4", backgroundSrc: "veo_section.mp4", outputSrc: "veo_section.mp4", baseSrc: "veo_section.mp4" },
  "05_split_nature_comparison": { defaultSrc: "veo_section.mp4", backgroundSrc: "veo_section.mp4", outputSrc: "veo_section.mp4", baseSrc: "veo_section.mp4" },
  "06_veo_pipeline_infographic": { defaultSrc: "veo_section.mp4", backgroundSrc: "veo_section.mp4", outputSrc: "veo_section.mp4", baseSrc: "veo_section.mp4" },
  "07_narration_overlay_intro": { defaultSrc: "veo_section.mp4", backgroundSrc: "veo_section.mp4", outputSrc: "veo_section.mp4", baseSrc: "veo_section.mp4" },
  "08_section_end_card": { defaultSrc: "veo_section.mp4", backgroundSrc: "veo_section.mp4", outputSrc: "veo_section.mp4", baseSrc: "veo_section.mp4" },
};

const VISUAL_OVERLAYS: Record<string, Record<string, string | boolean>> = {
};

const VISUAL_CONTRACTS: Record<string, Record<string, unknown> | null> = {
  "veo_section_01_title_card": {"specBaseName": "01_title_card", "dataPoints": null, "overlayConfig": null},
  "04_wave_data_overlay": {"specBaseName": "04_wave_data_overlay", "dataPoints": null, "overlayConfig": null},
  "05_split_nature_comparison": {"specBaseName": "05_split_nature_comparison", "dataPoints": null, "overlayConfig": null},
  "06_veo_pipeline_infographic": {"specBaseName": "06_veo_pipeline_infographic", "dataPoints": null, "overlayConfig": null},
  "07_narration_overlay_intro": {"specBaseName": "07_narration_overlay_intro", "dataPoints": null, "overlayConfig": null},
  "08_section_end_card": {"specBaseName": "08_section_end_card", "dataPoints": null, "overlayConfig": null},
};

export const VeoSectionSection: React.FC = () => {
  const fps = 30;
  const durationSeconds = 7.829333;
  const frame = useCurrentFrame();
  const activeVisuals = VISUAL_SEQUENCE.filter((visual) => frame >= visual.start && frame < visual.end);

  return (
    <Sequence from={0} durationInFrames={Math.max(1, Math.ceil(durationSeconds * fps))}>
      <Audio src={staticFile("veo_section/narration.wav")} />
      {activeVisuals.length === 0 ? <OffthreadVideo src={staticFile("veo_section.mp4")} style={{ width: "100%", height: "100%" }} /> : null}
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

export default VeoSectionSection;
