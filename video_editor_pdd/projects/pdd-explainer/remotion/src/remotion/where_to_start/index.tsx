import React from "react";
import { Sequence } from "remotion";

export const WhereToStartSection: React.FC = () => {
  const fps = 30;
  const offsetSeconds = 799.9428330000001;
  const durationSeconds = 32.569083;

  return (
    <Sequence from={0} durationInFrames={Math.max(1, Math.ceil(durationSeconds * fps))}>
      {/* Sub-compositions will be added here */}
    </Sequence>
  );
};

export default WhereToStartSection;
