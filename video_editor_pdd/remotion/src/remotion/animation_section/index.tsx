import React from "react";
import { Sequence, useCurrentFrame, Audio, staticFile } from "remotion";
import { VISUAL_SEQUENCE } from "./constants";
import { SlotScaledSequence, VisualMediaProvider } from "../_shared/visual-runtime";
import { AnimationSection01TitleCard } from "../AnimationSection01TitleCard";
import { AnimationSection02BlueCirclePulse } from "../AnimationSection02BlueCirclePulse";
import { AnimationSection03CircleToSquareMorph } from "../AnimationSection03CircleToSquareMorph";
import { AnimationSection04SquareSlideRight } from "../AnimationSection04SquareSlideRight";
import { AnimationSection05SplitComparison } from "../AnimationSection05SplitComparison";
import { AnimationSection06ParticleBurst } from "../AnimationSection06ParticleBurst";
import { AnimationSection07SectionOutro } from "../AnimationSection07SectionOutro";

const COMPONENT_MAP: Record<string, React.ComponentType<any>> = {
  "animation_section_01_title_card": AnimationSection01TitleCard,
  "02_blue_circle_pulse": AnimationSection02BlueCirclePulse,
  "03_circle_to_square_morph": AnimationSection03CircleToSquareMorph,
  "04_square_slide_right": AnimationSection04SquareSlideRight,
  "05_split_comparison": AnimationSection05SplitComparison,
  "06_particle_burst": AnimationSection06ParticleBurst,
  "07_section_outro": AnimationSection07SectionOutro,
};

const VISUAL_DURATIONS: Record<string, number> = {
  "animation_section_01_title_card": 33,
  "02_blue_circle_pulse": 45,
  "03_circle_to_square_morph": 33,
  "04_square_slide_right": 33,
  "05_split_comparison": 33,
  "07_section_outro": 22,
};

const VISUAL_MEDIA: Record<string, Record<string, string>> = {
};

export const AnimationSectionSection: React.FC = () => {
  const fps = 30;
  const durationSeconds = 7.658667;
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
      <Audio src={staticFile("animation_section/narration.wav")} />
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

export default AnimationSectionSection;
