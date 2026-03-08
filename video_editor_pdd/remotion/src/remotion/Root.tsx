import React from "react";
import { Composition } from "remotion";
import { ColdOpenSection } from "./cold_open";

export const RemotionRoot: React.FC = () => {
  return (
    <>
      <Composition
        id="ColdOpenSection"
        component={ColdOpenSection}
        durationInFrames={473}
        fps={30}
        width={1920}
        height={1080}
      />
    </>
  );
};
