import React from "react";
import { Sequence, useCurrentFrame, Audio, staticFile } from "remotion";
import { VISUAL_SEQUENCE } from "./constants";
import { SlotScaledSequence, VisualMediaProvider, VisualContractProvider } from "../_shared/visual-runtime";
import { AnimationSection01TitleCard } from "../AnimationSection01TitleCard";
import { AnimationSection02BlueCirclePulse } from "../AnimationSection02BlueCirclePulse";
import { AnimationSection03CircleToSquareMorph } from "../AnimationSection03CircleToSquareMorph";
import { AnimationSection04SquareSlideRight } from "../AnimationSection04SquareSlideRight";
import { AnimationSection05SplitComparison } from "../AnimationSection05SplitComparison";
import { AnimationSection06ParticleBurst } from "../AnimationSection06ParticleBurst";
import { AnimationSection07SectionOutro } from "../AnimationSection07SectionOutro";
import { AnimationSection08KeyVisual } from "../AnimationSection08KeyVisual";
import { AnimationSection09SplitSummary } from "../AnimationSection09SplitSummary";

const COMPONENT_MAP: Record<string, React.ComponentType<any>> = {
  "animation_section_01_title_card": AnimationSection01TitleCard,
  "02_blue_circle_pulse": AnimationSection02BlueCirclePulse,
  "03_circle_to_square_morph": AnimationSection03CircleToSquareMorph,
  "04_square_slide_right": AnimationSection04SquareSlideRight,
  "05_split_comparison": AnimationSection05SplitComparison,
  "06_particle_burst": AnimationSection06ParticleBurst,
  "07_section_outro": AnimationSection07SectionOutro,
  "08_key_visual": AnimationSection08KeyVisual,
  "09_split_summary": AnimationSection09SplitSummary,
};

const VISUAL_DURATIONS: Record<string, number> = {
  "animation_section_01_title_card": 45,
  "02_blue_circle_pulse": 30,
  "07_section_outro": 21,
};

const VISUAL_MEDIA: Record<string, Record<string, string>> = {
};

const VISUAL_OVERLAYS: Record<string, Record<string, string | boolean>> = {
};

const VISUAL_CONTRACTS: Record<string, Record<string, unknown> | null> = {
  "animation_section_01_title_card": {"specBaseName": "01_title_card", "dataPoints": null, "overlayConfig": null},
  "02_blue_circle_pulse": {"specBaseName": "02_blue_circle_pulse", "dataPoints": null, "overlayConfig": null},
  "03_circle_to_square_morph": {"specBaseName": "03_circle_to_square_morph", "dataPoints": null, "overlayConfig": null},
  "04_square_slide_right": {"specBaseName": "04_square_slide_right", "dataPoints": null, "overlayConfig": null},
  "05_split_comparison": {"specBaseName": "05_split_comparison", "dataPoints": null, "overlayConfig": null},
  "06_particle_burst": {"specBaseName": "06_particle_burst", "dataPoints": null, "overlayConfig": null},
  "07_section_outro": {"specBaseName": "07_section_outro", "dataPoints": null, "overlayConfig": null},
  "08_key_visual": {"specBaseName": "08_key_visual", "dataPoints": null, "overlayConfig": null},
  "09_split_summary": {"specBaseName": "09_split_summary", "dataPoints": null, "overlayConfig": null},
};

export const AnimationSectionSection: React.FC = () => {
  const fps = 30;
  const durationSeconds = 7.786667;
  const frame = useCurrentFrame();
  const activeVisuals = VISUAL_SEQUENCE.filter((visual) => frame >= visual.start && frame < visual.end);

  return (
    <Sequence from={0} durationInFrames={Math.max(1, Math.ceil(durationSeconds * fps))}>
      <Audio src={staticFile("animation_section/narration.wav")} />
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
            ) : null}
          </Sequence>
        );
      })}
    </Sequence>
  );
};

export default AnimationSectionSection;
