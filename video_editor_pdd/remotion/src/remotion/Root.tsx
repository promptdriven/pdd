import React from "react";
import { Composition } from "remotion";
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
import { VeoSection03WaveDataOverlay } from "./VeoSection03WaveDataOverlay";
import { VeoSection05SplitNatureComparison } from "./VeoSection05SplitNatureComparison";
import { VeoSection06VeoPipelineInfographic } from "./VeoSection06VeoPipelineInfographic";

const PREVIEW_DURATION = 150; // 5s at 30fps

export const RemotionRoot: React.FC = () => {
  return (
    <>
      <Composition
        id="AnimationSection"
        component={AnimationSectionSection}
        durationInFrames={220}
        fps={30}
        width={1920}
        height={1080}
      />
      <Composition
        id="VeoSection"
        component={VeoSectionSection}
        durationInFrames={221}
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
        component={VeoSection01TitleCard}
        durationInFrames={PREVIEW_DURATION}
        fps={30}
        width={1920}
        height={1080}
      />
      <Composition
        id="veo-section03-wave-data-overlay"
        component={VeoSection03WaveDataOverlay}
        durationInFrames={PREVIEW_DURATION}
        fps={30}
        width={1920}
        height={1080}
      />
      <Composition
        id="veo-section05-split-nature-comparison"
        component={VeoSection05SplitNatureComparison}
        durationInFrames={PREVIEW_DURATION}
        fps={30}
        width={1920}
        height={1080}
      />
      <Composition
        id="veo-section06-veo-pipeline-infographic"
        component={VeoSection06VeoPipelineInfographic}
        durationInFrames={PREVIEW_DURATION}
        fps={30}
        width={1920}
        height={1080}
      />
    </>
  );
};
