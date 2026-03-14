import React from "react";
import { Sequence, useCurrentFrame, Audio, OffthreadVideo, staticFile } from "remotion";
import { VISUAL_SEQUENCE } from "./constants";
import { SlotScaledSequence, VisualMediaProvider, VisualContractProvider } from "../_shared/visual-runtime";
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
  "veo_section_01_title_card": 30,
  "04_wave_data_overlay": 30,
  "06_veo_pipeline_infographic": 30,
  "07_narration_overlay_intro": 24,
  "08_section_end_card": 24,
};

const VISUAL_MEDIA: Record<string, Record<string, string>> = {
  "veo_section_01_title_card": { defaultSrc: "veo_section.mp4", backgroundSrc: "veo_section.mp4", outputSrc: "veo_section.mp4", baseSrc: "veo_section.mp4" },
  "02_ocean_wave_sunset": { defaultSrc: "veo/02_ocean_wave_sunset.mp4", backgroundSrc: "veo/02_ocean_wave_sunset.mp4", outputSrc: "veo/02_ocean_wave_sunset.mp4", baseSrc: "veo/02_ocean_wave_sunset.mp4" },
  "03_aerial_forest_canopy": { defaultSrc: "veo/03_aerial_forest_canopy.mp4", backgroundSrc: "veo/03_aerial_forest_canopy.mp4", outputSrc: "veo/03_aerial_forest_canopy.mp4", baseSrc: "veo/03_aerial_forest_canopy.mp4" },
  "04_wave_data_overlay": { defaultSrc: "veo/03_aerial_forest_canopy.mp4", backgroundSrc: "veo/03_aerial_forest_canopy.mp4", outputSrc: "veo/03_aerial_forest_canopy.mp4", baseSrc: "veo/03_aerial_forest_canopy.mp4" },
  "05_split_nature_comparison": { leftSrc: "veo/02_ocean_wave_sunset.mp4", defaultSrc: "veo/02_ocean_wave_sunset.mp4", rightSrc: "veo/03_aerial_forest_canopy.mp4", backgroundSrc: "veo/02_ocean_wave_sunset.mp4", outputSrc: "veo/02_ocean_wave_sunset.mp4", baseSrc: "veo/02_ocean_wave_sunset.mp4", revealSrc: "veo/03_aerial_forest_canopy.mp4" },
  "06_veo_pipeline_infographic": { defaultSrc: "veo/02_ocean_wave_sunset.mp4", backgroundSrc: "veo/02_ocean_wave_sunset.mp4", outputSrc: "veo/02_ocean_wave_sunset.mp4", baseSrc: "veo/02_ocean_wave_sunset.mp4" },
  "07_narration_overlay_intro": { defaultSrc: "veo/02_ocean_wave_sunset.mp4", backgroundSrc: "veo/02_ocean_wave_sunset.mp4", outputSrc: "veo/02_ocean_wave_sunset.mp4", baseSrc: "veo/02_ocean_wave_sunset.mp4" },
  "08_section_end_card": { defaultSrc: "veo/02_ocean_wave_sunset.mp4", backgroundSrc: "veo/02_ocean_wave_sunset.mp4", outputSrc: "veo/02_ocean_wave_sunset.mp4", baseSrc: "veo/02_ocean_wave_sunset.mp4" },
};

const VISUAL_OVERLAYS: Record<string, Record<string, string | boolean>> = {
  "04_wave_data_overlay": { gradientOverlay: "bottom" },
};

const VISUAL_CONTRACTS: Record<string, Record<string, unknown> | null> = {
  "veo_section_01_title_card": {"specBaseName": "01_title_card", "dataPoints": {"title": "Veo Section", "subtitle": "AI-Generated Cinematic Footage", "background": "#0B1120", "accent": "#C9A84C"}, "overlayConfig": null},
  "02_ocean_wave_sunset": {"specBaseName": "02_ocean_wave_sunset", "dataPoints": {"veo_prompt": "A calm ocean wave rolling onto a sandy beach at sunset, cinematic, slow motion", "source_file": "ocean_wave_sunset.mp4", "aspect_ratio": "16:9", "style": "cinematic slow motion", "color_temperature": "warm golden hour"}, "overlayConfig": null},
  "03_aerial_forest_canopy": {"specBaseName": "03_aerial_forest_canopy", "dataPoints": {"veo_prompt": "An aerial drone shot of a green forest canopy with sunlight filtering through the leaves", "source_file": "aerial_forest_canopy.mp4", "aspect_ratio": "16:9", "style": "cinematic aerial drone", "color_temperature": "natural green with warm highlights"}, "overlayConfig": null},
  "04_wave_data_overlay": {"specBaseName": "04_wave_data_overlay", "dataPoints": {"wave_height_m": 0.8, "wave_period_s": 6.2, "water_temp_c": 22, "waveform": {"amplitude": 0.8, "frequency": 1.2, "samples": 120}}, "overlayConfig": {"gradientOverlay": "bottom"}},
  "05_split_nature_comparison": {"specBaseName": "05_split_nature_comparison", "dataPoints": {"left": {"label": "Ocean · Sunset", "source": "ocean_wave_sunset_still.jpg", "scene": "beach at golden hour"}, "right": {"label": "Forest · Canopy", "source": "aerial_forest_canopy_still.jpg", "scene": "aerial forest with dappled light"}}, "overlayConfig": null},
  "06_veo_pipeline_infographic": {"specBaseName": "06_veo_pipeline_infographic", "dataPoints": {"pipeline_steps": [{"id": "prompt", "label": "Text Prompt", "color": "#6366F1", "icon": "text-cursor"}, {"id": "model", "label": "Veo Model", "color": "#8B5CF6", "icon": "brain"}, {"id": "output", "label": "Video Output", "color": "#10B981", "icon": "play"}], "arrows": [{"from": "prompt", "to": "model"}, {"from": "model", "to": "output"}]}, "overlayConfig": null},
  "07_narration_overlay_intro": {"specBaseName": "07_narration_overlay_intro", "dataPoints": {"narration_text": "Veo-generated clips with narration overlay", "word_count": 6, "waveform_bars": 40, "accent_color": "#C9A84C", "background_source": "ocean_wave_sunset_still.jpg"}, "overlayConfig": null},
  "08_section_end_card": {"specBaseName": "08_section_end_card", "dataPoints": {"title": "Veo Section Complete", "subtitle": "2 Veo clips · 3 Remotion overlays", "stats": {"veo_clips": 2, "remotion_overlays": 3}, "background": "#0B1120", "accent": "#C9A84C", "checkmark_color": "#10B981"}, "overlayConfig": null},
};

export const VeoSectionSection: React.FC = () => {
  const fps = 30;
  const durationSeconds = 7.744;
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
                {visualOverlayConfig ? (
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
