import React from "react";
import { Composition } from "remotion";

import { AnimationSectionSection } from "./animation_section";
import { VeoSectionSection } from "./veo_section";
import { AnimationSection01TitleCard } from "./AnimationSection01TitleCard";
import { AnimationSection02BarChartKeyVisual } from "./AnimationSection02BarChartKeyVisual";
import { AnimationSection02IntroDataPulse } from "./AnimationSection02IntroDataPulse";
import { AnimationSection03BlueCirclePulse } from "./AnimationSection03BlueCirclePulse";
import { AnimationSection03KeyVisualBarChart } from "./AnimationSection03KeyVisualBarChart";
import { AnimationSection03ParticleTransition } from "./AnimationSection03ParticleTransition";
import { AnimationSection04CircleToSquareTransform } from "./AnimationSection04CircleToSquareTransform";
import { AnimationSection04RemotionLogoReveal } from "./AnimationSection04RemotionLogoReveal";
import { AnimationSection05AnimationEngineDiagram } from "./AnimationSection05AnimationEngineDiagram";
import { AnimationSection05AnimationShowcase } from "./AnimationSection05AnimationShowcase";
import { AnimationSection05BarChartKeyVisual } from "./AnimationSection05BarChartKeyVisual";
import { AnimationSection06FrameworkComparison } from "./AnimationSection06FrameworkComparison";
import { AnimationSection06SplitBeforeAfter } from "./AnimationSection06SplitBeforeAfter";
import { AnimationSection06SplitSummary } from "./AnimationSection06SplitSummary";
import { AnimationSection07BeforeAfterSplitSummary } from "./AnimationSection07BeforeAfterSplitSummary";
import { AnimationSection08ClosingBadge } from "./AnimationSection08ClosingBadge";
import { AnimationSection08SectionClosingCard } from "./AnimationSection08SectionClosingCard";
import { VeoSection01TitleCard } from "./VeoSection01TitleCard";
import { VeoSection03NarrationOverlayIntro } from "./VeoSection03NarrationOverlayIntro";
import { VeoSection05NarrationOverlayForest } from "./VeoSection05NarrationOverlayForest";
import { VeoSection05VeoBadgeCallout } from "./VeoSection05VeoBadgeCallout";
import { VeoSection06SplitOceanForest } from "./VeoSection06SplitOceanForest";
import { VeoSection06VeoBadgeCallout } from "./VeoSection06VeoBadgeCallout";
import { VeoSection06VeoTechnologyCallout } from "./VeoSection06VeoTechnologyCallout";
import { VeoSection07SplitComparison } from "./VeoSection07SplitComparison";
import { VeoSection07VeoBadgeCallout } from "./VeoSection07VeoBadgeCallout";
import { VeoSection07WaveformVisualizer } from "./VeoSection07WaveformVisualizer";
import { VeoSection08SectionEndCard } from "./VeoSection08SectionEndCard";
import { VeoSection08SplitOceanForest } from "./VeoSection08SplitOceanForest";
import { VeoSection08VeoTechnologyCallout } from "./VeoSection08VeoTechnologyCallout";
import { VeoSection09SectionOutro } from "./VeoSection09SectionOutro";

const PREVIEW_DURATION = 150; // 5s at 30fps

export const RemotionRoot: React.FC = () => {
  return (
    <>
      <Composition
        id="AnimationSection"
        component={AnimationSectionSection}
        durationInFrames={317}
        fps={30}
        width={1920}
        height={1080}
      />
      <Composition
        id="VeoSection"
        component={VeoSectionSection}
        durationInFrames={342}
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
        id="animation-section02-bar-chart-key-visual"
        component={AnimationSection02BarChartKeyVisual}
        durationInFrames={PREVIEW_DURATION}
        fps={30}
        width={1920}
        height={1080}
      />
      <Composition
        id="animation-section02-intro-data-pulse"
        component={AnimationSection02IntroDataPulse}
        durationInFrames={PREVIEW_DURATION}
        fps={30}
        width={1920}
        height={1080}
      />
      <Composition
        id="animation-section03-blue-circle-pulse"
        component={AnimationSection03BlueCirclePulse}
        durationInFrames={PREVIEW_DURATION}
        fps={30}
        width={1920}
        height={1080}
      />
      <Composition
        id="animation-section03-key-visual-bar-chart"
        component={AnimationSection03KeyVisualBarChart}
        durationInFrames={PREVIEW_DURATION}
        fps={30}
        width={1920}
        height={1080}
      />
      <Composition
        id="animation-section03-particle-transition"
        component={AnimationSection03ParticleTransition}
        durationInFrames={PREVIEW_DURATION}
        fps={30}
        width={1920}
        height={1080}
      />
      <Composition
        id="animation-section04-circle-to-square-transform"
        component={AnimationSection04CircleToSquareTransform}
        durationInFrames={PREVIEW_DURATION}
        fps={30}
        width={1920}
        height={1080}
      />
      <Composition
        id="animation-section04-remotion-logo-reveal"
        component={AnimationSection04RemotionLogoReveal}
        durationInFrames={PREVIEW_DURATION}
        fps={30}
        width={1920}
        height={1080}
      />
      <Composition
        id="animation-section05-animation-engine-diagram"
        component={AnimationSection05AnimationEngineDiagram}
        durationInFrames={PREVIEW_DURATION}
        fps={30}
        width={1920}
        height={1080}
      />
      <Composition
        id="animation-section05-animation-showcase"
        component={AnimationSection05AnimationShowcase}
        durationInFrames={PREVIEW_DURATION}
        fps={30}
        width={1920}
        height={1080}
      />
      <Composition
        id="animation-section05-bar-chart-key-visual"
        component={AnimationSection05BarChartKeyVisual}
        durationInFrames={PREVIEW_DURATION}
        fps={30}
        width={1920}
        height={1080}
      />
      <Composition
        id="animation-section06-framework-comparison"
        component={AnimationSection06FrameworkComparison}
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
        id="animation-section06-split-summary"
        component={AnimationSection06SplitSummary}
        durationInFrames={PREVIEW_DURATION}
        fps={30}
        width={1920}
        height={1080}
      />
      <Composition
        id="animation-section07-before-after-split-summary"
        component={AnimationSection07BeforeAfterSplitSummary}
        durationInFrames={PREVIEW_DURATION}
        fps={30}
        width={1920}
        height={1080}
      />
      <Composition
        id="animation-section08-closing-badge"
        component={AnimationSection08ClosingBadge}
        durationInFrames={PREVIEW_DURATION}
        fps={30}
        width={1920}
        height={1080}
      />
      <Composition
        id="animation-section08-section-closing-card"
        component={AnimationSection08SectionClosingCard}
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
        id="veo-section05-veo-badge-callout"
        component={VeoSection05VeoBadgeCallout}
        durationInFrames={PREVIEW_DURATION}
        fps={30}
        width={1920}
        height={1080}
      />
      <Composition
        id="veo-section06-split-ocean-forest"
        component={VeoSection06SplitOceanForest}
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
        id="veo-section06-veo-technology-callout"
        component={VeoSection06VeoTechnologyCallout}
        durationInFrames={PREVIEW_DURATION}
        fps={30}
        width={1920}
        height={1080}
      />
      <Composition
        id="veo-section07-split-comparison"
        component={VeoSection07SplitComparison}
        durationInFrames={PREVIEW_DURATION}
        fps={30}
        width={1920}
        height={1080}
      />
      <Composition
        id="veo-section07-veo-badge-callout"
        component={VeoSection07VeoBadgeCallout}
        durationInFrames={PREVIEW_DURATION}
        fps={30}
        width={1920}
        height={1080}
      />
      <Composition
        id="veo-section07-waveform-visualizer"
        component={VeoSection07WaveformVisualizer}
        durationInFrames={PREVIEW_DURATION}
        fps={30}
        width={1920}
        height={1080}
      />
      <Composition
        id="veo-section08-section-end-card"
        component={VeoSection08SectionEndCard}
        durationInFrames={PREVIEW_DURATION}
        fps={30}
        width={1920}
        height={1080}
      />
      <Composition
        id="veo-section08-split-ocean-forest"
        component={VeoSection08SplitOceanForest}
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
        id="veo-section09-section-outro"
        component={VeoSection09SectionOutro}
        durationInFrames={PREVIEW_DURATION}
        fps={30}
        width={1920}
        height={1080}
      />
    </>
  );
};
