import React from "react";
import { Sequence, useCurrentFrame, Audio, OffthreadVideo, staticFile } from "remotion";
import { VISUAL_SEQUENCE } from "./constants";
import { SlotScaledSequence, VisualMediaProvider } from "../_shared/visual-runtime";
import { GeneratedMediaVisual } from "../_shared/GeneratedMediaVisual";
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
  "veo_section_01_title_card": 38,
  "04_wave_data_overlay": 38,
  "07_narration_overlay_intro": 38,
  "08_section_end_card": 37,
};

const VISUAL_MEDIA: Record<string, Record<string, string>> = {
  "veo_section_01_title_card": { defaultSrc: "veo_section.mp4", backgroundSrc: "veo_section.mp4", outputSrc: "veo_section.mp4", baseSrc: "veo_section.mp4" },
  "02_veo_ocean_broll": { defaultSrc: "veo/02_veo_ocean_broll.mp4", backgroundSrc: "veo/02_veo_ocean_broll.mp4", outputSrc: "veo/02_veo_ocean_broll.mp4", baseSrc: "veo/02_veo_ocean_broll.mp4" },
  "03_veo_forest_cutaway": { defaultSrc: "veo/03_veo_forest_cutaway.mp4", backgroundSrc: "veo/03_veo_forest_cutaway.mp4", outputSrc: "veo/03_veo_forest_cutaway.mp4", baseSrc: "veo/03_veo_forest_cutaway.mp4" },
  "04_wave_data_overlay": { defaultSrc: "veo/02_veo_ocean_broll.mp4", backgroundSrc: "veo/02_veo_ocean_broll.mp4", outputSrc: "veo/02_veo_ocean_broll.mp4", baseSrc: "veo/02_veo_ocean_broll.mp4" },
  "05_split_nature_comparison": { defaultSrc: "veo/02_veo_ocean_broll.mp4", backgroundSrc: "veo/02_veo_ocean_broll.mp4", outputSrc: "veo/02_veo_ocean_broll.mp4", baseSrc: "veo/02_veo_ocean_broll.mp4", leftSrc: "veo/02_veo_ocean_broll.mp4", rightSrc: "veo/03_veo_forest_cutaway.mp4", revealSrc: "veo/03_veo_forest_cutaway.mp4" },
  "06_veo_pipeline_infographic": { defaultSrc: "veo/02_veo_ocean_broll.mp4", backgroundSrc: "veo/02_veo_ocean_broll.mp4", outputSrc: "veo/02_veo_ocean_broll.mp4", baseSrc: "veo/02_veo_ocean_broll.mp4" },
  "07_narration_overlay_intro": { defaultSrc: "veo/02_veo_ocean_broll.mp4", backgroundSrc: "veo/02_veo_ocean_broll.mp4", outputSrc: "veo/02_veo_ocean_broll.mp4", baseSrc: "veo/02_veo_ocean_broll.mp4" },
  "08_section_end_card": { defaultSrc: "veo/02_veo_ocean_broll.mp4", backgroundSrc: "veo/02_veo_ocean_broll.mp4", outputSrc: "veo/02_veo_ocean_broll.mp4", baseSrc: "veo/02_veo_ocean_broll.mp4" },
};

const VISUAL_OVERLAYS: Record<string, Record<string, string | boolean>> = {
  "veo_section_01_title_card": { gradientOverlay: "bottom" },
  "02_veo_ocean_broll": { gradientOverlay: "bottom", lowerThirdText: "This is the second section of the integration test video." },
  "03_veo_forest_cutaway": { lightBloom: true, lowerThirdText: "It uses Veo-generated clips with narration overlay." },
  "08_section_end_card": { gradientOverlay: "bottom" },
};

export const VeoSectionSection: React.FC = () => {
  const fps = 30;
  const durationSeconds = 7.616;
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

        return (
          <Sequence key={visual.id} from={visual.start} durationInFrames={visualDuration}>
            {VisualComponent ? (
              <SlotScaledSequence intrinsicDurationInFrames={intrinsicDurationInFrames}>
                <VisualMediaProvider media={visualMedia}>
                  <VisualComponent />
                </VisualMediaProvider>
              </SlotScaledSequence>
            ) : visualMedia?.defaultSrc ? (
              <VisualMediaProvider media={visualMedia}>
                {visualOverlayConfig ? (
                  <GeneratedMediaVisual config={visualOverlayConfig} />
                ) : (
                  <OffthreadVideo src={staticFile(visualMedia.defaultSrc)} style={{ width: "100%", height: "100%" }} />
                )}
              </VisualMediaProvider>
            ) : null}
          </Sequence>
        );
      })}
    </Sequence>
  );
};

export default VeoSectionSection;
