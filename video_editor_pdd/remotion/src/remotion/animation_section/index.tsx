import React from "react";
import { Sequence, useCurrentFrame, Audio, staticFile } from "remotion";
import { VISUAL_SEQUENCE } from "./constants";
import { SlotScaledSequence, VisualMediaProvider } from "../_shared/visual-runtime";
import { AnimationSection01TitleCard } from "../AnimationSection01TitleCard";
import { AnimationSection02KeyVisual } from "../animation_section_02_key_visual";
import { AnimationSection03SplitSummary } from "../animation_section_03_split_summary";

const COMPONENT_MAP: Record<string, React.ComponentType<any>> = {
  "animation_section_01_title_card": AnimationSection01TitleCard,
  "animation_section_02_key_visual": AnimationSection02KeyVisual,
  "animation_section_03_split_summary": AnimationSection03SplitSummary,
};

const VISUAL_DURATIONS: Record<string, number> = {
  "animation_section_01_title_card": 90,
};

const VISUAL_MEDIA: Record<string, Record<string, string>> = {
};

export const AnimationSectionSection: React.FC = () => {
  const fps = 30;
  const durationSeconds = 7.381333;
  const frame = useCurrentFrame();
  let activeVisual = VISUAL_SEQUENCE.length > 0 ? VISUAL_SEQUENCE[0] : null;
  let activeVisualIndex = VISUAL_SEQUENCE.length > 0 ? 0 : -1;
  for (let i = VISUAL_SEQUENCE.length - 1; i >= 0; i--) {
    if (frame >= VISUAL_SEQUENCE[i].start) {
      activeVisual = VISUAL_SEQUENCE[i];
      activeVisualIndex = i;
      break;
    }
  }
  let renderVisual = activeVisual;
  for (let i = activeVisualIndex; i >= 0; i--) {
    const candidate = VISUAL_SEQUENCE[i];
    const candidateComponent = COMPONENT_MAP[candidate.id] ?? null;
    const candidateMedia = VISUAL_MEDIA[candidate.id] ?? null;
    if (candidateComponent || candidateMedia?.defaultSrc) {
      renderVisual = candidate;
      break;
    }
  }
  const ActiveComponent = renderVisual ? COMPONENT_MAP[renderVisual.id] ?? null : null;
  const activeVisualDuration = activeVisual ? Math.max(1, activeVisual.end - activeVisual.start) : 1;
  const intrinsicDurationInFrames = renderVisual ? VISUAL_DURATIONS[renderVisual.id] ?? activeVisualDuration : activeVisualDuration;
  const activeVisualMedia = renderVisual ? VISUAL_MEDIA[renderVisual.id] ?? null : null;

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
