import React from "react";
import { Sequence } from "remotion";

export const ClosingSection: React.FC = () => {
  const fps = 30;
  const offsetSeconds = 832.511916;
  const durationSeconds = 20.903208;

  return (
    <Sequence from={0} durationInFrames={Math.max(1, Math.ceil(durationSeconds * fps))}>
      {/* Sub-compositions will be added here */}
    </Sequence>
  );
};

export default ClosingSection;
