import React from "react";
import { AbsoluteFill } from "remotion";
import { BACKGROUND_COLOR } from "./constants";
import { GrayCodeFile } from "./GrayCodeFile";
import { PromptFile } from "./PromptFile";
import { CompactTerminal } from "./CompactTerminal";
import { SourceOfTruthBadge } from "./SourceOfTruthBadge";

export const defaultWhereToStart04SourceOfTruthLabelProps = {};

export const WhereToStart04SourceOfTruthLabel: React.FC = () => {
  return (
    <AbsoluteFill
      style={{
        backgroundColor: BACKGROUND_COLOR,
        overflow: "hidden",
      }}
    >
      {/* Gray code file — background, receding */}
      <GrayCodeFile />

      {/* Prompt file — dominant, center-right */}
      <PromptFile />

      {/* Compact terminal — below prompt file */}
      <CompactTerminal />

      {/* SOURCE OF TRUTH badge — overlapping top-right of prompt file */}
      <SourceOfTruthBadge />
    </AbsoluteFill>
  );
};

export default WhereToStart04SourceOfTruthLabel;
