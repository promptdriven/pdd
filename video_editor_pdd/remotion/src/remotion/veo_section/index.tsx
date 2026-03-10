import React from "react";
import { Sequence, useCurrentFrame, Audio, OffthreadVideo, staticFile } from "remotion";
import { VISUAL_SEQUENCE } from "./constants";
import { SlotScaledSequence, VisualMediaProvider } from "../_shared/visual-runtime";
import { VeoSection01TitleCard } from "../VeoSection01TitleCard";
import { VeoSection03NarrationOverlayIntro } from "../VeoSection03NarrationOverlayIntro";
import { VeoSection05NarrationOverlayForest } from "../VeoSection05NarrationOverlayForest";
import { VeoSection06VeoBadgeCallout } from "../VeoSection06VeoBadgeCallout";
import { VeoSection07SplitOceanForest } from "../VeoSection07SplitOceanForest";
import { VeoSection08VeoTechnologyCallout } from "../VeoSection08VeoTechnologyCallout";
import { VeoSection09WaveformVisualizer } from "../VeoSection09WaveformVisualizer";
import { VeoSection10SplitComparison } from "../VeoSection10SplitComparison";
import { VeoSection11VeoBadgeReprise } from "../VeoSection11VeoBadgeReprise";
import { VeoSection12SplitOceanForestReprise } from "../VeoSection12SplitOceanForestReprise";
import { VeoSection13VeoTechnologyReprise } from "../VeoSection13VeoTechnologyReprise";
import { VeoSection14SectionOutro } from "../VeoSection14SectionOutro";

const COMPONENT_MAP: Record<string, React.ComponentType<any>> = {
  "veo_section_01_title_card": VeoSection01TitleCard,
  "03_narration_overlay_intro": VeoSection03NarrationOverlayIntro,
  "05_narration_overlay_forest": VeoSection05NarrationOverlayForest,
  "06_veo_badge_callout": VeoSection06VeoBadgeCallout,
  "07_split_ocean_forest": VeoSection07SplitOceanForest,
  "08_veo_technology_callout": VeoSection08VeoTechnologyCallout,
  "09_waveform_visualizer": VeoSection09WaveformVisualizer,
  "10_split_comparison": VeoSection10SplitComparison,
  "11_veo_badge_reprise": VeoSection11VeoBadgeReprise,
  "12_split_ocean_forest_reprise": VeoSection12SplitOceanForestReprise,
  "13_veo_technology_reprise": VeoSection13VeoTechnologyReprise,
  "14_section_outro": VeoSection14SectionOutro,
};

const VISUAL_DURATIONS: Record<string, number> = {
  "veo_section_01_title_card": 90,
  "03_narration_overlay_intro": 90,
  "05_narration_overlay_forest": 90,
  "06_veo_badge_callout": 90,
  "07_split_ocean_forest": 90,
  "08_veo_technology_callout": 90,
  "09_waveform_visualizer": 90,
  "10_split_comparison": 90,
  "11_veo_badge_reprise": 90,
  "12_split_ocean_forest_reprise": 90,
  "13_veo_technology_reprise": 90,
  "14_section_outro": 90,
};

const VISUAL_MEDIA: Record<string, Record<string, string>> = {
  "veo_section_01_title_card": { defaultSrc: "veo/veo_section.mp4", backgroundSrc: "veo/veo_section.mp4", outputSrc: "veo/veo_section.mp4", baseSrc: "veo/veo_section.mp4" },
  "02_ocean_wave_sunset": { defaultSrc: "veo/ocean_wave_sunset.mp4", backgroundSrc: "veo/ocean_wave_sunset.mp4", outputSrc: "veo/ocean_wave_sunset.mp4", baseSrc: "veo/ocean_wave_sunset.mp4" },
  "03_narration_overlay_intro": { defaultSrc: "veo/ocean_wave_sunset.mp4", backgroundSrc: "veo/ocean_wave_sunset.mp4", outputSrc: "veo/ocean_wave_sunset.mp4", baseSrc: "veo/ocean_wave_sunset.mp4" },
  "04_forest_canopy_aerial": { defaultSrc: "veo/forest_canopy_aerial.mp4", backgroundSrc: "veo/forest_canopy_aerial.mp4", outputSrc: "veo/forest_canopy_aerial.mp4", baseSrc: "veo/forest_canopy_aerial.mp4" },
  "05_narration_overlay_forest": { defaultSrc: "veo/forest_canopy_aerial.mp4", backgroundSrc: "veo/forest_canopy_aerial.mp4", outputSrc: "veo/forest_canopy_aerial.mp4", baseSrc: "veo/forest_canopy_aerial.mp4" },
  "06_veo_badge_callout": { defaultSrc: "veo/forest_canopy_aerial.mp4", backgroundSrc: "veo/forest_canopy_aerial.mp4", outputSrc: "veo/forest_canopy_aerial.mp4", baseSrc: "veo/forest_canopy_aerial.mp4" },
  "07_split_ocean_forest": { leftSrc: "veo/ocean_wave_sunset.mp4", rightSrc: "veo/forest_canopy_aerial.mp4", defaultSrc: "veo/ocean_wave_sunset.mp4", backgroundSrc: "veo/ocean_wave_sunset.mp4", outputSrc: "veo/ocean_wave_sunset.mp4", baseSrc: "veo/ocean_wave_sunset.mp4", revealSrc: "veo/forest_canopy_aerial.mp4" },
  "08_veo_technology_callout": { defaultSrc: "veo/ocean_wave_sunset.mp4", backgroundSrc: "veo/ocean_wave_sunset.mp4", outputSrc: "veo/ocean_wave_sunset.mp4", baseSrc: "veo/ocean_wave_sunset.mp4" },
  "09_waveform_visualizer": { defaultSrc: "veo/ocean_wave_sunset.mp4", backgroundSrc: "veo/ocean_wave_sunset.mp4", outputSrc: "veo/ocean_wave_sunset.mp4", baseSrc: "veo/ocean_wave_sunset.mp4" },
  "10_split_comparison": { defaultSrc: "veo/ocean_wave_sunset.mp4", backgroundSrc: "veo/ocean_wave_sunset.mp4", outputSrc: "veo/ocean_wave_sunset.mp4", baseSrc: "veo/ocean_wave_sunset.mp4" },
  "11_veo_badge_reprise": { defaultSrc: "veo/forest_canopy_aerial.mp4", backgroundSrc: "veo/forest_canopy_aerial.mp4", outputSrc: "veo/forest_canopy_aerial.mp4", baseSrc: "veo/forest_canopy_aerial.mp4" },
  "12_split_ocean_forest_reprise": { baseSrc: "veo/ocean_wave_sunset.mp4", revealSrc: "veo/forest_canopy_aerial.mp4", defaultSrc: "veo/ocean_wave_sunset.mp4", backgroundSrc: "veo/ocean_wave_sunset.mp4", outputSrc: "veo/ocean_wave_sunset.mp4", leftSrc: "veo/ocean_wave_sunset.mp4", rightSrc: "veo/forest_canopy_aerial.mp4" },
  "13_veo_technology_reprise": { defaultSrc: "veo/ocean_wave_sunset.mp4", backgroundSrc: "veo/ocean_wave_sunset.mp4", outputSrc: "veo/ocean_wave_sunset.mp4", baseSrc: "veo/ocean_wave_sunset.mp4" },
  "14_section_outro": { defaultSrc: "veo/ocean_wave_sunset.mp4", backgroundSrc: "veo/ocean_wave_sunset.mp4", outputSrc: "veo/ocean_wave_sunset.mp4", baseSrc: "veo/ocean_wave_sunset.mp4" },
};

export const VeoSectionSection: React.FC = () => {
  const fps = 30;
  const durationSeconds = 11.797333;
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
    <Sequence from={0} durationInFrames={Math.ceil(durationSeconds * fps)}>
      <Audio src={staticFile("veo_section/narration.wav")} />
      {activeVisualMedia?.defaultSrc ? (
        <OffthreadVideo src={staticFile(activeVisualMedia.defaultSrc)} style={{ width: "100%", height: "100%" }} />
      ) : (
        <OffthreadVideo src={staticFile("veo/veo_section.mp4")} style={{ width: "100%", height: "100%" }} />
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
