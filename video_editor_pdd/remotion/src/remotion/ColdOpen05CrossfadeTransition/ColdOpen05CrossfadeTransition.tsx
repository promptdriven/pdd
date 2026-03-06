import React from "react";
import { AbsoluteFill } from "remotion";
import { CrossfadeLayer } from "./CrossfadeLayer";
import {
  BG_COLOR,
  LAYER_A_SRC,
  LAYER_B_SRC,
  LAYER_A_START_FROM,
  LAYER_B_START_FROM,
  CROSSFADE_START,
  CROSSFADE_END,
} from "./constants";

export const defaultColdOpen05CrossfadeTransitionProps = {};

export const ColdOpen05CrossfadeTransition: React.FC = () => {
  return (
    <AbsoluteFill style={{ backgroundColor: BG_COLOR }}>
      {/* Layer A — outgoing wide desk shot */}
      <CrossfadeLayer
        src={LAYER_A_SRC}
        startFrom={LAYER_A_START_FROM}
        direction="out"
        crossfadeStart={CROSSFADE_START}
        crossfadeEnd={CROSSFADE_END}
      />

      {/* Layer B — incoming close-up shot */}
      <CrossfadeLayer
        src={LAYER_B_SRC}
        startFrom={LAYER_B_START_FROM}
        direction="in"
        crossfadeStart={CROSSFADE_START}
        crossfadeEnd={CROSSFADE_END}
      />
    </AbsoluteFill>
  );
};

export default ColdOpen05CrossfadeTransition;
