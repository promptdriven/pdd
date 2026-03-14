import React from "react";
import { Sequence } from "remotion";

import { AnimationSection01TitleCard } from "../animation_section_01_title_card";
import { AnimationSection02BlueCirclePulse } from "../02_blue_circle_pulse";
import { AnimationSection03CircleToSquareMorph } from "../03_circle_to_square_morph";
import { AnimationSection04SquareSlideRight } from "../04_square_slide_right";
import { AnimationSection05SplitComparison } from "../05_split_comparison";
import { AnimationSection06ParticleBurst } from "../06_particle_burst";
import { AnimationSection07SectionOutro } from "../07_section_outro";
import { AnimationSection08KeyVisual } from "../08_key_visual";
import { AnimationSection09SplitSummary } from "../09_split_summary";

export const AnimationSectionSection: React.FC = () => {
  const fps = 30;
  const offsetSeconds = 0;
  const durationSeconds = 7.722667;

  return (
    <Sequence from={0} durationInFrames={Math.max(1, Math.ceil(durationSeconds * fps))}>
      <AnimationSection01TitleCard />
      <AnimationSection02BlueCirclePulse />
      <AnimationSection03CircleToSquareMorph />
      <AnimationSection04SquareSlideRight />
      <AnimationSection05SplitComparison />
      <AnimationSection06ParticleBurst />
      <AnimationSection07SectionOutro />
      <AnimationSection08KeyVisual />
      <AnimationSection09SplitSummary />
    </Sequence>
  );
};

export default AnimationSectionSection;
