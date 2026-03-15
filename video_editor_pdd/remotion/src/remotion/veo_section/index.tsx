import React from "react";
import { Sequence, useCurrentFrame, Audio, OffthreadVideo, staticFile } from "remotion";
import { VISUAL_SEQUENCE } from "./constants";
import { SlotScaledSequence, VisualMediaProvider, VisualContractProvider } from "../_shared/visual-runtime";
import { GeneratedMediaVisual } from "../_shared/GeneratedMediaVisual";
import { VeoSection01TitleCard } from "../VeoSection01TitleCard";
import { VeoSection03WaveDataOverlay } from "../VeoSection03WaveDataOverlay";
import { VeoSection04SplitNatureComparison } from "../VeoSection04SplitNatureComparison";
import { VeoSection05VeoPipelineInfographic } from "../VeoSection05VeoPipelineInfographic";
import { VeoSection07NarrationOverlayIntro } from "../VeoSection07NarrationOverlayIntro";
import { VeoSection08SectionEndCard } from "../VeoSection08SectionEndCard";

const COMPONENT_MAP: Record<string, React.ComponentType<any>> = {
  "veo_section_01_title_card": VeoSection01TitleCard,
  "03_wave_data_overlay": VeoSection03WaveDataOverlay,
  "04_split_nature_comparison": VeoSection04SplitNatureComparison,
  "05_veo_pipeline_infographic": VeoSection05VeoPipelineInfographic,
  "07_narration_overlay_intro": VeoSection07NarrationOverlayIntro,
  "08_section_end_card": VeoSection08SectionEndCard,
};

const VISUAL_DURATIONS: Record<string, number> = {
  "veo_section_01_title_card": 51,
  "03_wave_data_overlay": 52,
  "05_veo_pipeline_infographic": 30,
  "07_narration_overlay_intro": 51,
};

const VISUAL_MEDIA: Record<string, Record<string, string>> = {
  "veo_section_01_title_card": { defaultSrc: "veo/veo_section.mp4", backgroundSrc: "veo/veo_section.mp4", outputSrc: "veo/veo_section.mp4", baseSrc: "veo/veo_section.mp4" },
  "02_ocean_wave_sunset": { defaultSrc: "veo/02_ocean_wave_sunset.mp4", backgroundSrc: "veo/02_ocean_wave_sunset.mp4", outputSrc: "veo/02_ocean_wave_sunset.mp4", baseSrc: "veo/02_ocean_wave_sunset.mp4" },
  "03_wave_data_overlay": { defaultSrc: "veo/02_ocean_wave_sunset.mp4", backgroundSrc: "veo/02_ocean_wave_sunset.mp4", outputSrc: "veo/02_ocean_wave_sunset.mp4", baseSrc: "veo/02_ocean_wave_sunset.mp4" },
  "04_split_nature_comparison": { defaultSrc: "veo/02_ocean_wave_sunset.mp4", backgroundSrc: "veo/02_ocean_wave_sunset.mp4", outputSrc: "veo/02_ocean_wave_sunset.mp4", baseSrc: "veo/02_ocean_wave_sunset.mp4", leftSrc: "veo/02_ocean_wave_sunset.mp4", rightSrc: "veo/06_aerial_forest_canopy.mp4", revealSrc: "veo/06_aerial_forest_canopy.mp4" },
  "05_veo_pipeline_infographic": { defaultSrc: "veo/02_ocean_wave_sunset.mp4", backgroundSrc: "veo/02_ocean_wave_sunset.mp4", outputSrc: "veo/02_ocean_wave_sunset.mp4", baseSrc: "veo/02_ocean_wave_sunset.mp4" },
  "06_aerial_forest_canopy": { defaultSrc: "veo/06_aerial_forest_canopy.mp4", backgroundSrc: "veo/06_aerial_forest_canopy.mp4", outputSrc: "veo/06_aerial_forest_canopy.mp4", baseSrc: "veo/06_aerial_forest_canopy.mp4" },
  "07_narration_overlay_intro": { defaultSrc: "veo/06_aerial_forest_canopy.mp4", backgroundSrc: "veo/06_aerial_forest_canopy.mp4", outputSrc: "veo/06_aerial_forest_canopy.mp4", baseSrc: "veo/06_aerial_forest_canopy.mp4" },
  "08_section_end_card": { defaultSrc: "veo/06_aerial_forest_canopy.mp4", backgroundSrc: "veo/06_aerial_forest_canopy.mp4", outputSrc: "veo/06_aerial_forest_canopy.mp4", baseSrc: "veo/06_aerial_forest_canopy.mp4" },
};

const VISUAL_OVERLAYS: Record<string, Record<string, string | boolean>> = {
  "03_wave_data_overlay": { gradientOverlay: "bottom" },
  "05_veo_pipeline_infographic": { gradientOverlay: "bottom" },
  "07_narration_overlay_intro": { lowerThirdText: "It uses Veo-generated clips with narration overlay." },
};

const VISUAL_CONTRACTS: Record<string, Record<string, unknown> | null> = {
  "veo_section_01_title_card": {"specBaseName": "01_title_card", "dataPoints": {"title": "Veo Section", "subtitle": "AI-Generated Cinematic Footage", "background": "#0B1120", "accent": "#C9A84C"}, "overlayConfig": null},
  "02_ocean_wave_sunset": {"specBaseName": "02_ocean_wave_sunset", "dataPoints": {"source": "veo/04_veo_broll.mp4", "veo_prompt": "A calm ocean wave rolling onto a sandy beach at sunset, cinematic, slow motion", "duration_seconds": 4.0, "veo_model": "veo-3.1-generate-001"}, "overlayConfig": null},
  "03_wave_data_overlay": {"specBaseName": "03_wave_data_overlay", "dataPoints": {"waveform": {"amplitude": 0.8, "frequency": 1.2, "samples": 120}, "stats": [{"label": "Wave Height", "value": "0.8m", "icon": "wave"}, {"label": "Wave Period", "value": "6.2s", "icon": "clock"}, {"label": "Water Temp", "value": "22°C", "icon": "thermometer"}]}, "overlayConfig": {"gradientOverlay": "bottom"}},
  "04_split_nature_comparison": {"specBaseName": "04_split_nature_comparison", "dataPoints": {"panels": [{"side": "left", "label": "Ocean · Sunset", "source": "veo/04_veo_broll.mp4"}, {"side": "right", "label": "Forest · Canopy", "source": "veo/05_veo_cutaway.mp4"}], "divider_color": "#C9A84C"}, "overlayConfig": null},
  "05_veo_pipeline_infographic": {"specBaseName": "05_veo_pipeline_infographic", "dataPoints": {"pipeline_steps": [{"label": "Prompt", "icon": "text", "x": 330}, {"label": "Veo AI", "icon": "sparkle", "x": 870}, {"label": "Clip", "icon": "film", "x": 1410}], "arrow_style": {"stroke": "#C9A84C", "dash_pattern": "8 4", "particle_count": 2}}, "overlayConfig": {"gradientOverlay": "bottom"}},
  "06_aerial_forest_canopy": {"specBaseName": "06_aerial_forest_canopy", "dataPoints": {"source": "veo/05_veo_cutaway.mp4", "veo_prompt": "An aerial drone shot of a green forest canopy with sunlight filtering through the leaves", "duration_seconds": 4.0, "veo_model": "veo-3.1-generate-001"}, "overlayConfig": null},
  "07_narration_overlay_intro": {"specBaseName": "07_narration_overlay_intro", "dataPoints": {"caption": "It uses Veo-generated clips with narration overlay.", "words": ["It", "uses", "Veo-generated", "clips", "with", "narration", "overlay."], "word_timings_frames": [10, 17, 24, 31, 38, 45, 52], "waveform_bars": 5, "panel_height": 200, "active_color": "#C9A84C", "inactive_color": "rgba(255,255,255,0.5)"}, "overlayConfig": {"lowerThirdText": "It uses Veo-generated clips with narration overlay."}},
  "08_section_end_card": {"specBaseName": "08_section_end_card", "dataPoints": {"title": "Veo Section Complete", "icon": "checkmark", "background": "#0B1120", "accent": "#C9A84C", "checkmark_size": 80, "rule_width": 200}, "overlayConfig": null},
};

export const VeoSectionSection: React.FC = () => {
  const fps = 30;
  const durationSeconds = 8.021333;
  const frame = useCurrentFrame();
  const activeVisuals = VISUAL_SEQUENCE.filter((visual) => frame >= visual.start && frame < visual.end);

  return (
    <Sequence from={0} durationInFrames={Math.max(1, Math.ceil(durationSeconds * fps))}>
      <Audio src={staticFile("veo_section/narration.wav")} />
      {activeVisuals.length === 0 ? <OffthreadVideo src={staticFile("veo/veo_section.mp4")} style={{ width: "100%", height: "100%" }} /> : null}
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
