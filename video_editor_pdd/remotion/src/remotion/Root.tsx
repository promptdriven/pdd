import React from "react";
import { Composition } from "remotion";
import "./_shared/load-inter-font";
import { AnimationSectionSection } from "./animation_section";
import { VeoSectionSection } from "./veo_section";

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
    </>
  );
};
