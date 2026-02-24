import React from "react";
import { Composition } from "remotion";

import { ColdOpenSection } from "./ColdOpenSection";
import { Part1Economics } from "./Part1Economics";

const FPS = 30;

export const RemotionRoot: React.FC = () => {
  return (
    <>
      <Composition
        id="ColdOpenSection"
        component={ColdOpenSection}
        durationInFrames={Math.ceil(15.288 * FPS)}
        fps={FPS}
        width={1920}
        height={1080}
      />
      <Composition
        id="Part1Economics"
        component={Part1Economics}
        durationInFrames={Math.ceil(382.176 * FPS)}
        fps={FPS}
        width={1920}
        height={1080}
      />
    </>
  );
};
