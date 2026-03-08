import React from "react";
import { Sequence, useCurrentFrame, Audio, OffthreadVideo, staticFile } from "remotion";
import { VISUAL_SEQUENCE } from "./constants";
import { AnimationSection01TitleCard } from "../AnimationSection01TitleCard";
import { AnimationSection02BarChartKeyVisual } from "../AnimationSection02BarChartKeyVisual";
import { AnimationSection02IntroDataPulse } from "../AnimationSection02IntroDataPulse";
import { AnimationSection03BlueCirclePulse } from "../AnimationSection03BlueCirclePulse";
import { AnimationSection03KeyVisualBarChart } from "../AnimationSection03KeyVisualBarChart";
import { AnimationSection03ParticleTransition } from "../AnimationSection03ParticleTransition";
import { AnimationSection04CircleToSquareTransform } from "../AnimationSection04CircleToSquareTransform";
import { AnimationSection04RemotionLogoReveal } from "../AnimationSection04RemotionLogoReveal";
import { AnimationSection05AnimationEngineDiagram } from "../AnimationSection05AnimationEngineDiagram";
import { AnimationSection05AnimationShowcase } from "../AnimationSection05AnimationShowcase";
import { AnimationSection05BarChartKeyVisual } from "../AnimationSection05BarChartKeyVisual";
import { AnimationSection06FrameworkComparison } from "../AnimationSection06FrameworkComparison";
import { AnimationSection06SplitBeforeAfter } from "../AnimationSection06SplitBeforeAfter";
import { AnimationSection06SplitSummary } from "../AnimationSection06SplitSummary";
import { AnimationSection07BeforeAfterSplitSummary } from "../AnimationSection07BeforeAfterSplitSummary";
import { AnimationSection08ClosingBadge } from "../AnimationSection08ClosingBadge";
import { AnimationSection08SectionClosingCard } from "../AnimationSection08SectionClosingCard";

const COMPONENT_MAP: Record<string, React.ComponentType<any>> = {
  "animation_section_01_title_card": AnimationSection01TitleCard,
  "02_bar_chart_key_visual": AnimationSection02BarChartKeyVisual,
  "02_intro_data_pulse": AnimationSection02IntroDataPulse,
  "03_blue_circle_pulse": AnimationSection03BlueCirclePulse,
  "03_key_visual_bar_chart": AnimationSection03KeyVisualBarChart,
  "03_particle_transition": AnimationSection03ParticleTransition,
  "04_circle_to_square_transform": AnimationSection04CircleToSquareTransform,
  "04_remotion_logo_reveal": AnimationSection04RemotionLogoReveal,
  "05_animation_engine_diagram": AnimationSection05AnimationEngineDiagram,
  "05_animation_showcase": AnimationSection05AnimationShowcase,
  "05_bar_chart_key_visual": AnimationSection05BarChartKeyVisual,
  "06_framework_comparison": AnimationSection06FrameworkComparison,
  "06_split_before_after": AnimationSection06SplitBeforeAfter,
  "06_split_summary": AnimationSection06SplitSummary,
  "07_before_after_split_summary": AnimationSection07BeforeAfterSplitSummary,
  "08_closing_badge": AnimationSection08ClosingBadge,
  "08_section_closing_card": AnimationSection08SectionClosingCard,
};

export const AnimationSectionSection: React.FC = () => {
  const fps = 30;
  const durationSeconds = 10.56;
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
      <Audio src={staticFile("animation_section/narration.wav")} />
      <OffthreadVideo src={staticFile("veo/animation_section.mp4")} style={{ width: "100%", height: "100%" }} />
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

export default AnimationSectionSection;
