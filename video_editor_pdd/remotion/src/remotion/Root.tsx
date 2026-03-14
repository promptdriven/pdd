import React from "react";
import { Composition } from "remotion";
import { VisualMediaProvider } from "./_shared/visual-runtime";
import "./_shared/load-inter-font";

import { AnimationSectionSection } from "./animation_section";
import { VeoSectionSection } from "./veo_section";
import { AnimationSection01TitleCard } from "./AnimationSection01TitleCard";
import { AnimationSection02KeyVisual } from "./animation_section_02_key_visual";
import { AnimationSection03SplitSummary } from "./animation_section_03_split_summary";
import { VeoSection01TitleCard } from "./VeoSection01TitleCard";
import { VeoSection02KeyVisual } from "./veo_section_02_key_visual";
import { VeoSection03SplitSummary } from "./veo_section_03_split_summary";

const PREVIEW_VISUAL_MEDIA: Record<string, Record<string, string>> = {
  "veo_section:veo_section_01_title_card": { defaultSrc: "veo_section.mp4", backgroundSrc: "veo_section.mp4", outputSrc: "veo_section.mp4", baseSrc: "veo_section.mp4" },
  "veo_section:veo_section_02_key_visual": { defaultSrc: "veo_section.mp4", backgroundSrc: "veo_section.mp4", outputSrc: "veo_section.mp4", baseSrc: "veo_section.mp4" },
  "veo_section:veo_section_03_split_summary": { defaultSrc: "veo_section.mp4", backgroundSrc: "veo_section.mp4", outputSrc: "veo_section.mp4", baseSrc: "veo_section.mp4" },
};

const VeoSection01TitleCardPreview: React.FC = () => (
  <VisualMediaProvider media={PREVIEW_VISUAL_MEDIA["veo_section:veo_section_01_title_card"] ?? null}>
    <VeoSection01TitleCard />
  </VisualMediaProvider>
);
const VeoSection02KeyVisualPreview: React.FC = () => (
  <VisualMediaProvider media={PREVIEW_VISUAL_MEDIA["veo_section:veo_section_02_key_visual"] ?? null}>
    <VeoSection02KeyVisual />
  </VisualMediaProvider>
);
const VeoSection03SplitSummaryPreview: React.FC = () => (
  <VisualMediaProvider media={PREVIEW_VISUAL_MEDIA["veo_section:veo_section_03_split_summary"] ?? null}>
    <VeoSection03SplitSummary />
  </VisualMediaProvider>
);

const PREVIEW_DURATION = 150; // 5s at 30fps

export const RemotionRoot: React.FC = () => {
  return (
    <>
      <Composition
        id="AnimationSection"
        component={AnimationSectionSection}
        durationInFrames={220}
        fps={30}
        width={1280}
        height={720}
      />
      <Composition
        id="VeoSection"
        component={VeoSectionSection}
        durationInFrames={221}
        fps={30}
        width={1280}
        height={720}
      />
      <Composition
        id="animation-section01-title-card"
        component={AnimationSection01TitleCard}
        durationInFrames={PREVIEW_DURATION}
        fps={30}
        width={1280}
        height={720}
      />
      <Composition
        id="animation-section02-key-visual"
        component={AnimationSection02KeyVisual}
        durationInFrames={PREVIEW_DURATION}
        fps={30}
        width={1280}
        height={720}
      />
      <Composition
        id="animation-section03-split-summary"
        component={AnimationSection03SplitSummary}
        durationInFrames={PREVIEW_DURATION}
        fps={30}
        width={1280}
        height={720}
      />
      <Composition
        id="veo-section01-title-card"
        component={VeoSection01TitleCardPreview}
        durationInFrames={PREVIEW_DURATION}
        fps={30}
        width={1280}
        height={720}
      />
      <Composition
        id="veo-section02-key-visual"
        component={VeoSection02KeyVisualPreview}
        durationInFrames={PREVIEW_DURATION}
        fps={30}
        width={1280}
        height={720}
      />
      <Composition
        id="veo-section03-split-summary"
        component={VeoSection03SplitSummaryPreview}
        durationInFrames={PREVIEW_DURATION}
        fps={30}
        width={1280}
        height={720}
      />
    </>
  );
};
