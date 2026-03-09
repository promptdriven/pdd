import React from "react";
import { Sequence, useCurrentFrame, Audio, staticFile } from "remotion";
import { VISUAL_SEQUENCE } from "./constants";
import { SlotScaledSequence, VisualMediaProvider } from "../_shared/visual-runtime";
import { AnimationSection01TitleCard } from "../AnimationSection01TitleCard";
import { AnimationSection02BlueCirclePulse } from "../AnimationSection02BlueCirclePulse";
import { AnimationSection03CircleToSquareTransform } from "../AnimationSection03CircleToSquareTransform";
import { AnimationSection04ShapeShowcase } from "../AnimationSection04ShapeShowcase";
import { AnimationSection05AnimationTimeline } from "../AnimationSection05AnimationTimeline";
import { AnimationSection06SplitBeforeAfter } from "../AnimationSection06SplitBeforeAfter";
import { AnimationSection07SectionClosingCard } from "../AnimationSection07SectionClosingCard";

const COMPONENT_MAP: Record<string, React.ComponentType<any>> = {
  "animation_section_01_title_card": AnimationSection01TitleCard,
  "02_blue_circle_pulse": AnimationSection02BlueCirclePulse,
  "03_circle_to_square_transform": AnimationSection03CircleToSquareTransform,
  "04_shape_showcase": AnimationSection04ShapeShowcase,
  "05_animation_timeline": AnimationSection05AnimationTimeline,
  "06_split_before_after": AnimationSection06SplitBeforeAfter,
  "07_section_closing_card": AnimationSection07SectionClosingCard,
};

const VISUAL_DURATIONS: Record<string, number> = {
  "animation_section_01_title_card": 90,
  "02_blue_circle_pulse": 150,
  "03_circle_to_square_transform": 150,
  "04_shape_showcase": 150,
  "05_animation_timeline": 150,
  "06_split_before_after": 120,
  "07_section_closing_card": 90,
};

const VISUAL_MEDIA: Record<string, Record<string, string>> = {
};

export const AnimationSectionSection: React.FC = () => {
  const fps = 30;
  const durationSeconds = 10.88;
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
