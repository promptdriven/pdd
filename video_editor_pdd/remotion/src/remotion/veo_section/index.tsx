import React from "react";
import { Sequence, useCurrentFrame, Audio, OffthreadVideo, staticFile } from "remotion";
import { VISUAL_SEQUENCE } from "./constants";
import { SlotScaledSequence, VisualMediaProvider, VisualContractProvider } from "../_shared/visual-runtime";
import { GeneratedMediaVisual } from "../_shared/GeneratedMediaVisual";
import { VeoSection01TitleCard } from "../VeoSection01TitleCard";
import { VeoSection03WaveDataOverlay } from "../VeoSection03WaveDataOverlay";
import { VeoSection07NarrationOverlayIntro } from "../VeoSection07NarrationOverlayIntro";
import { VeoSection08SectionEndCard } from "../VeoSection08SectionEndCard";

const COMPONENT_MAP: Record<string, React.ComponentType<any>> = {
  "veo_section_01_title_card": VeoSection01TitleCard,
  "03_wave_data_overlay": VeoSection03WaveDataOverlay,
  "07_narration_overlay_intro": VeoSection07NarrationOverlayIntro,
  "08_section_end_card": VeoSection08SectionEndCard,
};

const VISUAL_DURATIONS: Record<string, number> = {
  "veo_section_01_title_card": 30,
  "03_wave_data_overlay": 120,
  "07_narration_overlay_intro": 24,
  "08_section_end_card": 24,
};

const VISUAL_MEDIA: Record<string, Record<string, string>> = {
  "veo_section_01_title_card": { defaultSrc: "veo_section.mp4", backgroundSrc: "veo_section.mp4", outputSrc: "veo_section.mp4", baseSrc: "veo_section.mp4" },
  "02_ocean_wave_sunset": { defaultSrc: "veo/02_ocean_wave_sunset.mp4", backgroundSrc: "veo/02_ocean_wave_sunset.mp4", outputSrc: "veo/02_ocean_wave_sunset.mp4", baseSrc: "veo/02_ocean_wave_sunset.mp4" },
  "03_wave_data_overlay": { defaultSrc: "veo/02_ocean_wave_sunset.mp4", backgroundSrc: "veo/02_ocean_wave_sunset.mp4", outputSrc: "veo/02_ocean_wave_sunset.mp4", baseSrc: "veo/02_ocean_wave_sunset.mp4" },
  "04_split_nature_comparison": { leftSrc: "veo/02_ocean_wave_sunset.mp4", defaultSrc: "veo/02_ocean_wave_sunset.mp4", rightSrc: "veo/05_veo_cutaway.mp4", backgroundSrc: "veo/02_ocean_wave_sunset.mp4", outputSrc: "veo/02_ocean_wave_sunset.mp4", baseSrc: "veo/02_ocean_wave_sunset.mp4", revealSrc: "veo/05_veo_cutaway.mp4" },
  "06_aerial_forest_canopy": { defaultSrc: "veo/05_veo_cutaway.mp4", backgroundSrc: "veo/05_veo_cutaway.mp4", outputSrc: "veo/05_veo_cutaway.mp4", baseSrc: "veo/05_veo_cutaway.mp4" },
  "07_narration_overlay_intro": { defaultSrc: "veo/05_veo_cutaway.mp4", backgroundSrc: "veo/05_veo_cutaway.mp4", outputSrc: "veo/05_veo_cutaway.mp4", baseSrc: "veo/05_veo_cutaway.mp4" },
  "08_section_end_card": { defaultSrc: "veo/05_veo_cutaway.mp4", backgroundSrc: "veo/05_veo_cutaway.mp4", outputSrc: "veo/05_veo_cutaway.mp4", baseSrc: "veo/05_veo_cutaway.mp4" },
};

const VISUAL_OVERLAYS: Record<string, Record<string, string | boolean>> = {
  "03_wave_data_overlay": { gradientOverlay: "bottom" },
  "07_narration_overlay_intro": { lowerThirdText: "It uses Veo-generated clips with narration overlay." },
};

const VISUAL_CONTRACTS: Record<string, Record<string, unknown> | null> = {
  "veo_section_01_title_card": {"specBaseName": "01_title_card", "dataPoints": {"title": "Veo Section", "subtitle": "AI-Generated Cinematic Footage", "background": "#0B1120", "accent": "#C9A84C"}, "overlayConfig": null},
  "02_ocean_wave_sunset": {"specBaseName": "02_ocean_wave_sunset", "dataPoints": {"veo_prompt": "A calm ocean wave rolling onto a sandy beach at sunset, cinematic, slow motion", "source_file": "veo/04_veo_broll.mp4", "scene": "beach at golden hour", "mood": "serene, cinematic", "camera": "low-angle, near waterline"}, "overlayConfig": null},
  "03_wave_data_overlay": {"specBaseName": "03_wave_data_overlay", "dataPoints": {"wave_height_m": 0.8, "wave_period_s": 6.2, "water_temp_c": 22, "waveform": {"amplitude": 0.8, "frequency": 1.2, "samples": 120}}, "overlayConfig": {"gradientOverlay": "bottom"}},
  "04_split_nature_comparison": {"specBaseName": "04_split_nature_comparison", "dataPoints": {"left": {"label": "Ocean · Sunset", "source": "veo/04_veo_broll.mp4", "scene": "beach at golden hour"}, "right": {"label": "Forest · Canopy", "source": "veo/05_veo_cutaway.mp4", "scene": "aerial forest with dappled light"}}, "overlayConfig": null},
  "06_aerial_forest_canopy": {"specBaseName": "06_aerial_forest_canopy", "dataPoints": {"veo_prompt": "An aerial drone shot of a green forest canopy with sunlight filtering through the leaves", "source_file": "veo/05_veo_cutaway.mp4", "scene": "aerial forest with dappled light", "mood": "lush, tranquil", "camera": "top-down aerial, slow forward drift"}, "overlayConfig": null},
  "07_narration_overlay_intro": {"specBaseName": "07_narration_overlay_intro", "dataPoints": {"caption": "It uses Veo-generated clips with narration overlay.", "words": ["It", "uses", "Veo-generated", "clips", "with", "narration", "overlay."], "word_timing_frames": [10, 17, 24, 31, 38, 45, 52], "waveform_bars": 5, "panel_height": 200}, "overlayConfig": {"lowerThirdText": "It uses Veo-generated clips with narration overlay."}},
  "08_section_end_card": {"specBaseName": "08_section_end_card", "dataPoints": {"title": "Veo Section Complete", "icon": "checkmark", "background": "#0B1120", "accent": "#C9A84C"}, "overlayConfig": null},
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

export default VeoSectionSection;
