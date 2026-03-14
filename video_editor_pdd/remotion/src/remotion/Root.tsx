import React from "react";
import { Composition } from "remotion";
import { VisualMediaProvider } from "./_shared/visual-runtime";
import "./_shared/load-inter-font";

import { AnimationSectionSection } from "./animation_section";
import { VeoSectionSection } from "./veo_section";
import { AnimationSection01TitleCard } from "./AnimationSection01TitleCard";
import { AnimationSection02BlueCirclePulse } from "./AnimationSection02BlueCirclePulse";
import { AnimationSection03CircleToSquareMorph } from "./AnimationSection03CircleToSquareMorph";
import { AnimationSection04SquareSlideRight } from "./AnimationSection04SquareSlideRight";
import { AnimationSection05SplitComparison } from "./AnimationSection05SplitComparison";
import { AnimationSection06ParticleBurst } from "./AnimationSection06ParticleBurst";
import { AnimationSection07SectionOutro } from "./AnimationSection07SectionOutro";
import { VeoSection01TitleCard } from "./VeoSection01TitleCard";
import { VeoSection04WaveDataOverlay } from "./VeoSection04WaveDataOverlay";
import { VeoSection05SplitNatureComparison } from "./VeoSection05SplitNatureComparison";
import { VeoSection06VeoPipelineInfographic } from "./VeoSection06VeoPipelineInfographic";
import { VeoSection07NarrationOverlayIntro } from "./VeoSection07NarrationOverlayIntro";
import { VeoSection08SectionEndCard } from "./VeoSection08SectionEndCard";

const PREVIEW_VISUAL_MEDIA: Record<string, Record<string, string>> = {
  "veo_section:veo_section_01_title_card": { defaultSrc: "veo_section.mp4", backgroundSrc: "veo_section.mp4", outputSrc: "veo_section.mp4", baseSrc: "veo_section.mp4" },
  "veo_section:04_wave_data_overlay": { defaultSrc: "veo/02_veo_ocean_broll.mp4", backgroundSrc: "veo/02_veo_ocean_broll.mp4", outputSrc: "veo/02_veo_ocean_broll.mp4", baseSrc: "veo/02_veo_ocean_broll.mp4" },
  "veo_section:05_split_nature_comparison": { defaultSrc: "veo/02_veo_ocean_broll.mp4", backgroundSrc: "veo/02_veo_ocean_broll.mp4", outputSrc: "veo/02_veo_ocean_broll.mp4", baseSrc: "veo/02_veo_ocean_broll.mp4", leftSrc: "veo/02_veo_ocean_broll.mp4", rightSrc: "veo/03_veo_forest_cutaway.mp4", revealSrc: "veo/03_veo_forest_cutaway.mp4" },
  "veo_section:06_veo_pipeline_infographic": { defaultSrc: "veo/02_veo_ocean_broll.mp4", backgroundSrc: "veo/02_veo_ocean_broll.mp4", outputSrc: "veo/02_veo_ocean_broll.mp4", baseSrc: "veo/02_veo_ocean_broll.mp4" },
  "veo_section:07_narration_overlay_intro": { defaultSrc: "veo/02_veo_ocean_broll.mp4", backgroundSrc: "veo/02_veo_ocean_broll.mp4", outputSrc: "veo/02_veo_ocean_broll.mp4", baseSrc: "veo/02_veo_ocean_broll.mp4" },
  "veo_section:08_section_end_card": { defaultSrc: "veo/02_veo_ocean_broll.mp4", backgroundSrc: "veo/02_veo_ocean_broll.mp4", outputSrc: "veo/02_veo_ocean_broll.mp4", baseSrc: "veo/02_veo_ocean_broll.mp4" },
};

const VeoSection01TitleCardPreview: React.FC = () => (
  <VisualMediaProvider media={PREVIEW_VISUAL_MEDIA["veo_section:veo_section_01_title_card"] ?? null}>
    <VeoSection01TitleCard />
  </VisualMediaProvider>
);
const VeoSection04WaveDataOverlayPreview: React.FC = () => (
  <VisualMediaProvider media={PREVIEW_VISUAL_MEDIA["veo_section:04_wave_data_overlay"] ?? null}>
    <VeoSection04WaveDataOverlay />
  </VisualMediaProvider>
);
const VeoSection05SplitNatureComparisonPreview: React.FC = () => (
  <VisualMediaProvider media={PREVIEW_VISUAL_MEDIA["veo_section:05_split_nature_comparison"] ?? null}>
    <VeoSection05SplitNatureComparison />
  </VisualMediaProvider>
);
const VeoSection06VeoPipelineInfographicPreview: React.FC = () => (
  <VisualMediaProvider media={PREVIEW_VISUAL_MEDIA["veo_section:06_veo_pipeline_infographic"] ?? null}>
    <VeoSection06VeoPipelineInfographic />
  </VisualMediaProvider>
);
const VeoSection07NarrationOverlayIntroPreview: React.FC = () => (
  <VisualMediaProvider media={PREVIEW_VISUAL_MEDIA["veo_section:07_narration_overlay_intro"] ?? null}>
    <VeoSection07NarrationOverlayIntro />
  </VisualMediaProvider>
);
const VeoSection08SectionEndCardPreview: React.FC = () => (
  <VisualMediaProvider media={PREVIEW_VISUAL_MEDIA["veo_section:08_section_end_card"] ?? null}>
    <VeoSection08SectionEndCard />
  </VisualMediaProvider>
);

const PREVIEW_DURATION = 150; // 5s at 30fps

export const RemotionRoot: React.FC = () => {
  return (
    <>
      <Composition
        id="AnimationSection"
        component={AnimationSectionSection}
        durationInFrames={230}
        fps={30}
        width={1920}
        height={1080}
      />
      <Composition
        id="VeoSection"
        component={VeoSectionSection}
        durationInFrames={231}
        fps={30}
        width={1920}
        height={1080}
      />
      <Composition
        id="animation-section01-title-card"
        component={AnimationSection01TitleCard}
        durationInFrames={PREVIEW_DURATION}
        fps={30}
        width={1920}
        height={1080}
      />
      <Composition
        id="animation-section02-blue-circle-pulse"
        component={AnimationSection02BlueCirclePulse}
        durationInFrames={PREVIEW_DURATION}
        fps={30}
        width={1920}
        height={1080}
      />
      <Composition
        id="animation-section03-circle-to-square-morph"
        component={AnimationSection03CircleToSquareMorph}
        durationInFrames={PREVIEW_DURATION}
        fps={30}
        width={1920}
        height={1080}
      />
      <Composition
        id="animation-section04-square-slide-right"
        component={AnimationSection04SquareSlideRight}
        durationInFrames={PREVIEW_DURATION}
        fps={30}
        width={1920}
        height={1080}
      />
      <Composition
        id="animation-section05-split-comparison"
        component={AnimationSection05SplitComparison}
        durationInFrames={PREVIEW_DURATION}
        fps={30}
        width={1920}
        height={1080}
      />
      <Composition
        id="animation-section06-particle-burst"
        component={AnimationSection06ParticleBurst}
        durationInFrames={PREVIEW_DURATION}
        fps={30}
        width={1920}
        height={1080}
      />
      <Composition
        id="animation-section07-section-outro"
        component={AnimationSection07SectionOutro}
        durationInFrames={PREVIEW_DURATION}
        fps={30}
        width={1920}
        height={1080}
      />
      <Composition
        id="veo-section01-title-card"
        component={VeoSection01TitleCardPreview}
        durationInFrames={PREVIEW_DURATION}
        fps={30}
        width={1920}
        height={1080}
      />
      <Composition
        id="veo-section04-wave-data-overlay"
        component={VeoSection04WaveDataOverlayPreview}
        durationInFrames={PREVIEW_DURATION}
        fps={30}
        width={1920}
        height={1080}
      />
      <Composition
        id="veo-section05-split-nature-comparison"
        component={VeoSection05SplitNatureComparisonPreview}
        durationInFrames={PREVIEW_DURATION}
        fps={30}
        width={1920}
        height={1080}
      />
      <Composition
        id="veo-section06-veo-pipeline-infographic"
        component={VeoSection06VeoPipelineInfographicPreview}
        durationInFrames={PREVIEW_DURATION}
        fps={30}
        width={1920}
        height={1080}
      />
      <Composition
        id="veo-section07-narration-overlay-intro"
        component={VeoSection07NarrationOverlayIntroPreview}
        durationInFrames={PREVIEW_DURATION}
        fps={30}
        width={1920}
        height={1080}
      />
      <Composition
        id="veo-section08-section-end-card"
        component={VeoSection08SectionEndCardPreview}
        durationInFrames={PREVIEW_DURATION}
        fps={30}
        width={1920}
        height={1080}
      />
    </>
  );
};
