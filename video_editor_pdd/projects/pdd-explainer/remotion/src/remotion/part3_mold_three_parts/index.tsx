import React from "react";
import { Sequence } from "remotion";

export const Part3MoldThreePartsSection: React.FC = () => {
  const fps = 30;
  const offsetSeconds = 228.223958;
  const durationSeconds = 344.396583;

  return (
    <Sequence from={0} durationInFrames={Math.max(1, Math.ceil(durationSeconds * fps))}>
      {/* Sub-compositions will be added here */}
    </Sequence>
  );
};

export default Part3MoldThreePartsSection;
