import React from "react";
import { Composition } from "remotion";
import { AnimationSectionSection } from "./animation_section";
import { VeoSectionSection } from "./veo_section";

export const RemotionRoot: React.FC = () => {
  return (
    <>      <Composition
        id="AnimationSection"
        component={AnimationSectionSection}
        durationInFrames={211}
        fps={30}
        width={1920}
        height={1080}
      />
      <Composition
        id="VeoSection"
        component={VeoSectionSection}
        durationInFrames={223}
        fps={30}
        width={1920}
        height={1080}
      />

    </>
  );
};
