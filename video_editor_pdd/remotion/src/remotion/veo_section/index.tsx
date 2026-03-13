import React from "react";
import { Sequence, useCurrentFrame, Audio, OffthreadVideo, staticFile } from "remotion";
import { VISUAL_SEQUENCE } from "./constants";
import { SlotScaledSequence, VisualMediaProvider } from "../_shared/visual-runtime";
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
  "veo_section_01_title_card": 90,
  "04_wave_data_overlay": 38,
  "07_narration_overlay_intro": 38,
  "08_section_end_card": 37,
};

const VISUAL_MEDIA: Record<string, Record<string, string>> = {
  "veo_section_01_title_card": { defaultSrc: "veo_section.mp4", backgroundSrc: "veo_section.mp4", outputSrc: "veo_section.mp4", baseSrc: "veo_section.mp4" },
  "02_veo_ocean_broll": { defaultSrc: "veo/04_veo_broll.mp4", backgroundSrc: "veo/04_veo_broll.mp4", outputSrc: "veo/04_veo_broll.mp4", baseSrc: "veo/04_veo_broll.mp4" },
  "03_veo_forest_cutaway": { defaultSrc: "veo/05_veo_cutaway.mp4", backgroundSrc: "veo/05_veo_cutaway.mp4", outputSrc: "veo/05_veo_cutaway.mp4", baseSrc: "veo/05_veo_cutaway.mp4" },
  "04_wave_data_overlay": { defaultSrc: "veo/04_veo_broll.mp4", backgroundSrc: "veo/04_veo_broll.mp4", outputSrc: "veo/04_veo_broll.mp4", baseSrc: "veo/04_veo_broll.mp4" },
  "05_split_nature_comparison": { defaultSrc: "veo/04_veo_broll.mp4", backgroundSrc: "veo/04_veo_broll.mp4", outputSrc: "veo/04_veo_broll.mp4", baseSrc: "veo/04_veo_broll.mp4", leftSrc: "veo/04_veo_broll.mp4", rightSrc: "veo/05_veo_cutaway.mp4", revealSrc: "veo/05_veo_cutaway.mp4" },
  "06_veo_pipeline_infographic": { defaultSrc: "veo/04_veo_broll.mp4", backgroundSrc: "veo/04_veo_broll.mp4", outputSrc: "veo/04_veo_broll.mp4", baseSrc: "veo/04_veo_broll.mp4" },
  "07_narration_overlay_intro": { defaultSrc: "veo/04_veo_broll.mp4", backgroundSrc: "veo/04_veo_broll.mp4", outputSrc: "veo/04_veo_broll.mp4", baseSrc: "veo/04_veo_broll.mp4" },
  "08_section_end_card": { defaultSrc: "veo/04_veo_broll.mp4", backgroundSrc: "veo/04_veo_broll.mp4", outputSrc: "veo/04_veo_broll.mp4", baseSrc: "veo/04_veo_broll.mp4" },
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
        !ActiveComponent ? <OffthreadVideo src={staticFile("veo_section.mp4")} style={{ width: "100%", height: "100%" }} /> : null
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
