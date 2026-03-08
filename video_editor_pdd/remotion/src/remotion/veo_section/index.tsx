import React from "react";
import { Sequence, useCurrentFrame, Audio, OffthreadVideo, staticFile } from "remotion";
import { VISUAL_SEQUENCE } from "./constants";
import { VeoSection01TitleCard } from "../VeoSection01TitleCard";
import { VeoSection03NarrationOverlayIntro } from "../VeoSection03NarrationOverlayIntro";
import { VeoSection05NarrationOverlayForest } from "../VeoSection05NarrationOverlayForest";
import { VeoSection05VeoBadgeCallout } from "../VeoSection05VeoBadgeCallout";
import { VeoSection06SplitOceanForest } from "../VeoSection06SplitOceanForest";
import { VeoSection06VeoBadgeCallout } from "../VeoSection06VeoBadgeCallout";
import { VeoSection06VeoTechnologyCallout } from "../VeoSection06VeoTechnologyCallout";
import { VeoSection07SplitComparison } from "../VeoSection07SplitComparison";
import { VeoSection07VeoBadgeCallout } from "../VeoSection07VeoBadgeCallout";
import { VeoSection07WaveformVisualizer } from "../VeoSection07WaveformVisualizer";
import { VeoSection08SectionEndCard } from "../VeoSection08SectionEndCard";
import { VeoSection08SplitOceanForest } from "../VeoSection08SplitOceanForest";
import { VeoSection08VeoTechnologyCallout } from "../VeoSection08VeoTechnologyCallout";
import { VeoSection09SectionOutro } from "../VeoSection09SectionOutro";

const COMPONENT_MAP: Record<string, React.ComponentType<any>> = {
  "veo_section_01_title_card": VeoSection01TitleCard,
  "03_narration_overlay_intro": VeoSection03NarrationOverlayIntro,
  "05_narration_overlay_forest": VeoSection05NarrationOverlayForest,
  "05_veo_badge_callout": VeoSection05VeoBadgeCallout,
  "06_split_ocean_forest": VeoSection06SplitOceanForest,
  "06_veo_badge_callout": VeoSection06VeoBadgeCallout,
  "06_veo_technology_callout": VeoSection06VeoTechnologyCallout,
  "07_split_comparison": VeoSection07SplitComparison,
  "07_veo_badge_callout": VeoSection07VeoBadgeCallout,
  "07_waveform_visualizer": VeoSection07WaveformVisualizer,
  "08_section_end_card": VeoSection08SectionEndCard,
  "08_split_ocean_forest": VeoSection08SplitOceanForest,
  "08_veo_technology_callout": VeoSection08VeoTechnologyCallout,
  "09_section_outro": VeoSection09SectionOutro,
};

export const VeoSectionSection: React.FC = () => {
  const fps = 30;
  const durationSeconds = 11.392;
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
