import React from "react";
import { Sequence, useCurrentFrame, Audio, OffthreadVideo, staticFile } from "remotion";
import { VISUAL_SEQUENCE } from "./constants";
import { SlotScaledSequence, VisualMediaProvider } from "../_shared/visual-runtime";
import { VeoSection01TitleCard } from "../VeoSection01TitleCard";
import { VeoSection03WaveDataOverlay } from "../VeoSection03WaveDataOverlay";
import { VeoSection05SplitNatureComparison } from "../VeoSection05SplitNatureComparison";
import { VeoSection06VeoPipelineInfographic } from "../VeoSection06VeoPipelineInfographic";
import { VeoSection07NarrationOverlayIntro } from "../VeoSection07NarrationOverlayIntro";
import { VeoSection08SectionEndCard } from "../VeoSection08SectionEndCard";

const COMPONENT_MAP: Record<string, React.ComponentType<any>> = {
  "veo_section_01_title_card": VeoSection01TitleCard,
  "03_wave_data_overlay": VeoSection03WaveDataOverlay,
  "05_split_nature_comparison": VeoSection05SplitNatureComparison,
  "06_veo_pipeline_infographic": VeoSection06VeoPipelineInfographic,
  "07_narration_overlay_intro": VeoSection07NarrationOverlayIntro,
  "08_section_end_card": VeoSection08SectionEndCard,
};

const VISUAL_DURATIONS: Record<string, number> = {
  "veo_section_01_title_card": 90,
  "03_wave_data_overlay": 120,
  "05_split_nature_comparison": 120,
  "06_veo_pipeline_infographic": 150,
  "07_narration_overlay_intro": 120,
  "08_section_end_card": 90,
};

const VISUAL_MEDIA: Record<string, Record<string, string>> = {
  "veo_section_01_title_card": { defaultSrc: "veo/veo_section.mp4", backgroundSrc: "veo/veo_section.mp4", outputSrc: "veo/veo_section.mp4", baseSrc: "veo/veo_section.mp4" },
  "02_ocean_wave_broll": { defaultSrc: "veo/veo_section.mp4", backgroundSrc: "veo/veo_section.mp4", outputSrc: "veo/veo_section.mp4", baseSrc: "veo/veo_section.mp4" },
  "03_wave_data_overlay": { defaultSrc: "veo/veo_section.mp4", backgroundSrc: "veo/veo_section.mp4", outputSrc: "veo/veo_section.mp4", baseSrc: "veo/veo_section.mp4" },
  "04_aerial_forest_broll": { defaultSrc: "veo/veo_section.mp4", backgroundSrc: "veo/veo_section.mp4", outputSrc: "veo/veo_section.mp4", baseSrc: "veo/veo_section.mp4" },
  "05_split_nature_comparison": { defaultSrc: "veo/veo_section.mp4", backgroundSrc: "veo/veo_section.mp4", outputSrc: "veo/veo_section.mp4", baseSrc: "veo/veo_section.mp4" },
  "06_veo_pipeline_infographic": { defaultSrc: "veo/veo_section.mp4", backgroundSrc: "veo/veo_section.mp4", outputSrc: "veo/veo_section.mp4", baseSrc: "veo/veo_section.mp4" },
  "07_narration_overlay_intro": { defaultSrc: "veo/veo_section.mp4", backgroundSrc: "veo/veo_section.mp4", outputSrc: "veo/veo_section.mp4", baseSrc: "veo/veo_section.mp4" },
  "08_section_end_card": { defaultSrc: "veo/veo_section.mp4", backgroundSrc: "veo/veo_section.mp4", outputSrc: "veo/veo_section.mp4", baseSrc: "veo/veo_section.mp4" },
};

export const VeoSectionSection: React.FC = () => {
  const fps = 30;
  const durationSeconds = 7.424;
  const frame = useCurrentFrame();
  let activeVisual = VISUAL_SEQUENCE.length > 0 ? VISUAL_SEQUENCE[0] : null;
  for (let i = VISUAL_SEQUENCE.length - 1; i >= 0; i--) {
    if (frame >= VISUAL_SEQUENCE[i].start) {
      activeVisual = VISUAL_SEQUENCE[i];
      break;
    }
  }
  const ActiveComponent = activeVisual ? COMPONENT_MAP[activeVisual.id] ?? null : null;
  const activeVisualDuration = activeVisual ? Math.max(1, activeVisual.end - activeVisual.start) : 1;
  const intrinsicDurationInFrames = activeVisual ? VISUAL_DURATIONS[activeVisual.id] ?? activeVisualDuration : activeVisualDuration;
  const activeVisualMedia = activeVisual ? VISUAL_MEDIA[activeVisual.id] ?? null : null;

  return (
    <Sequence from={0} durationInFrames={Math.max(1, Math.ceil(durationSeconds * fps))}>
      <Audio src={staticFile("veo_section/narration.wav")} />
      {activeVisualMedia?.defaultSrc && !ActiveComponent ? (
        <OffthreadVideo src={staticFile(activeVisualMedia.defaultSrc)} style={{ width: "100%", height: "100%" }} />
      ) : (
        !ActiveComponent ? <OffthreadVideo src={staticFile("veo/veo_section.mp4")} style={{ width: "100%", height: "100%" }} /> : null
      )}
      {ActiveComponent && activeVisual ? (
        <Sequence
          from={activeVisual.start}
          durationInFrames={Math.max(1, activeVisual.end - activeVisual.start)}
        >
          <SlotScaledSequence intrinsicDurationInFrames={intrinsicDurationInFrames}>
            <VisualMediaProvider media={activeVisualMedia}>
              <ActiveComponent />
            </VisualMediaProvider>
          </SlotScaledSequence>
        </Sequence>
      ) : null}
    </Sequence>
  );
};

export default VeoSectionSection;
