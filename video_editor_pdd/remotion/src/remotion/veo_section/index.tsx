import React from "react";
import { Sequence, useCurrentFrame, Audio, OffthreadVideo, staticFile } from "remotion";
import { VISUAL_SEQUENCE } from "./constants";
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

export const VeoSectionSection: React.FC = () => {
  const fps = 30;
  const durationSeconds = 11.52;
  const frame = useCurrentFrame();
  let activeVisual = VISUAL_SEQUENCE.length > 0 ? VISUAL_SEQUENCE[0] : null;
  for (let i = VISUAL_SEQUENCE.length - 1; i >= 0; i--) {
    if (frame >= VISUAL_SEQUENCE[i].start) {
      activeVisual = VISUAL_SEQUENCE[i];
      break;
    }
  }
  const ActiveComponent = activeVisual ? COMPONENT_MAP[activeVisual.id] ?? null : null;

  return (
    <Sequence from={0} durationInFrames={Math.ceil(durationSeconds * fps)}>
      <Audio src={staticFile("veo_section/narration.wav")} />
      <OffthreadVideo src={staticFile("veo/veo_section.mp4")} style={{ width: "100%", height: "100%" }} />
      {ActiveComponent && activeVisual ? (
        <Sequence
          from={activeVisual.start}
          durationInFrames={Math.max(1, activeVisual.end - activeVisual.start)}
        >
          <ActiveComponent />
        </Sequence>
      ) : null}
    </Sequence>
  );
};

export default VeoSectionSection;
