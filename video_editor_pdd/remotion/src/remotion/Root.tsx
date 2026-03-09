import React from "react";
import { Composition } from "remotion";

import { AnimationSectionSection } from "./animation_section";
import { VeoSectionSection } from "./veo_section";
import { AnimationSection01TitleCard } from "./AnimationSection01TitleCard";
import { AnimationSection02BlueCirclePulse } from "./AnimationSection02BlueCirclePulse";
import { AnimationSection03CircleToSquareTransform } from "./AnimationSection03CircleToSquareTransform";
import { AnimationSection04ShapeShowcase } from "./AnimationSection04ShapeShowcase";
import { AnimationSection05AnimationTimeline } from "./AnimationSection05AnimationTimeline";
import { AnimationSection06SplitBeforeAfter } from "./AnimationSection06SplitBeforeAfter";
import { AnimationSection07SectionClosingCard } from "./AnimationSection07SectionClosingCard";
import { VeoSection01TitleCard } from "./VeoSection01TitleCard";
import { VeoSection03NarrationOverlayIntro } from "./VeoSection03NarrationOverlayIntro";
import { VeoSection05NarrationOverlayForest } from "./VeoSection05NarrationOverlayForest";
import { VeoSection06VeoBadgeCallout } from "./VeoSection06VeoBadgeCallout";
import { VeoSection07SplitOceanForest } from "./VeoSection07SplitOceanForest";
import { VeoSection08VeoTechnologyCallout } from "./VeoSection08VeoTechnologyCallout";
import { VeoSection09WaveformVisualizer } from "./VeoSection09WaveformVisualizer";
import { VeoSection10SplitComparison } from "./VeoSection10SplitComparison";
import { VeoSection11VeoBadgeReprise } from "./VeoSection11VeoBadgeReprise";
import { VeoSection12SplitOceanForestReprise } from "./VeoSection12SplitOceanForestReprise";
import { VeoSection13VeoTechnologyReprise } from "./VeoSection13VeoTechnologyReprise";
import { VeoSection14SectionOutro } from "./VeoSection14SectionOutro";

const PREVIEW_DURATION = 150; // 5s at 30fps

export const RemotionRoot: React.FC = () => {
  return (
    <>
      <Composition
        id="AnimationSection"
        component={AnimationSectionSection}
        durationInFrames={323}
        fps={30}
        width={1920}
        height={1080}
      />
      <Composition
        id="VeoSection"
        component={VeoSectionSection}
        durationInFrames={348}
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
        id="animation-section03-circle-to-square-transform"
        component={AnimationSection03CircleToSquareTransform}
        durationInFrames={PREVIEW_DURATION}
        fps={30}
        width={1920}
        height={1080}
      />
      <Composition
        id="animation-section04-shape-showcase"
        component={AnimationSection04ShapeShowcase}
        durationInFrames={PREVIEW_DURATION}
        fps={30}
        width={1920}
        height={1080}
      />
      <Composition
        id="animation-section05-animation-timeline"
        component={AnimationSection05AnimationTimeline}
        durationInFrames={PREVIEW_DURATION}
        fps={30}
        width={1920}
        height={1080}
      />
      <Composition
        id="animation-section06-split-before-after"
        component={AnimationSection06SplitBeforeAfter}
        durationInFrames={PREVIEW_DURATION}
        fps={30}
        width={1920}
        height={1080}
      />
      <Composition
        id="animation-section07-section-closing-card"
        component={AnimationSection07SectionClosingCard}
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
        id="veo-section03-narration-overlay-intro"
        component={VeoSection03NarrationOverlayIntro}
        durationInFrames={PREVIEW_DURATION}
        fps={30}
        width={1920}
        height={1080}
      />
      <Composition
        id="veo-section05-narration-overlay-forest"
        component={VeoSection05NarrationOverlayForest}
        durationInFrames={PREVIEW_DURATION}
        fps={30}
        width={1920}
        height={1080}
      />
      <Composition
        id="veo-section06-veo-badge-callout"
        component={VeoSection06VeoBadgeCallout}
        durationInFrames={PREVIEW_DURATION}
        fps={30}
        width={1920}
        height={1080}
      />
      <Composition
        id="veo-section07-split-ocean-forest"
        component={VeoSection07SplitOceanForest}
        durationInFrames={PREVIEW_DURATION}
        fps={30}
        width={1920}
        height={1080}
      />
      <Composition
        id="veo-section08-veo-technology-callout"
        component={VeoSection08VeoTechnologyCallout}
        durationInFrames={PREVIEW_DURATION}
        fps={30}
        width={1920}
        height={1080}
      />
      <Composition
        id="veo-section09-waveform-visualizer"
        component={VeoSection09WaveformVisualizer}
        durationInFrames={PREVIEW_DURATION}
        fps={30}
        width={1920}
        height={1080}
      />
      <Composition
        id="veo-section10-split-comparison"
        component={VeoSection10SplitComparison}
        durationInFrames={PREVIEW_DURATION}
        fps={30}
        width={1920}
        height={1080}
      />
      <Composition
        id="veo-section11-veo-badge-reprise"
        component={VeoSection11VeoBadgeReprise}
        durationInFrames={PREVIEW_DURATION}
        fps={30}
        width={1920}
        height={1080}
      />
      <Composition
        id="veo-section12-split-ocean-forest-reprise"
        component={VeoSection12SplitOceanForestReprise}
        durationInFrames={PREVIEW_DURATION}
        fps={30}
        width={1920}
        height={1080}
      />
      <Composition
        id="veo-section13-veo-technology-reprise"
        component={VeoSection13VeoTechnologyReprise}
        durationInFrames={PREVIEW_DURATION}
        fps={30}
        width={1920}
        height={1080}
      />
      <Composition
        id="veo-section14-section-outro"
        component={VeoSection14SectionOutro}
        durationInFrames={PREVIEW_DURATION}
        fps={30}
        width={1920}
        height={1080}
      />
    </>
  );
};
