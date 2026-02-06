import React from "react";
import {
  AbsoluteFill,
  Audio,
  Sequence,
  OffthreadVideo,
  staticFile,
  useCurrentFrame,
} from "remotion";
import { BEATS, VISUAL_SEQUENCE, Part1EconomicsPropsType } from "./constants";
import { CodeCostChart, defaultCodeCostChartProps } from "../05-CodeCostChart";
import { ContextRot, defaultContextRotProps } from "../07-ContextRot";
import { CrossingPoint, defaultCrossingPointProps } from "../08-CrossingPoint";
import { DeveloperEditZoomout, defaultDeveloperEditZoomoutProps } from "../09-DeveloperEditZoomout";
import { PieChart, defaultPieChartProps } from "../12-PieChart";
import { PieToCurve, defaultPieToCurveProps } from "../13-PieToCurve";
import { SockPriceChart, defaultSockPriceChartProps } from "../02-SockPriceChart";

export const Part1Economics: React.FC<Part1EconomicsPropsType> = () => {
  const frame = useCurrentFrame();

  // Determine which visual is active based on frame position
  let activeVisual = 0;
  for (let i = VISUAL_SEQUENCE.length - 1; i >= 0; i--) {
    if (frame >= VISUAL_SEQUENCE[i].start) {
      activeVisual = i;
      break;
    }
  }

  return (
    <AbsoluteFill style={{ backgroundColor: "#0a0a1a" }}>
      {/* Narration audio */}
      <Audio src={staticFile("part1_economics_narration.wav")} />

      {/* Visual compositions sequenced by BEATS */}
      
      {/* Visual 0: SockPriceChart - Sock economics: cost, labor, darning, flipped, irr */}
      {activeVisual === 0 && (
        <Sequence from={BEATS.VISUAL_00_START} durationInFrames={BEATS.VISUAL_00_END - BEATS.VISUAL_00_START}>
          <SockPriceChart {...defaultSockPriceChartProps} />
        </Sequence>
      )}

      {/* Visual 1: CodeCostChart - Code cost: expensive, scratch, patched, rational */}
      {activeVisual === 1 && (
        <Sequence from={BEATS.VISUAL_01_START} durationInFrames={BEATS.VISUAL_01_END - BEATS.VISUAL_01_START}>
          <CodeCostChart {...defaultCodeCostChartProps} />
        </Sequence>
      )}

      {/* Visual 2: CodeCostChart - AI enters: patching faster, tools, feel it */}
      {activeVisual === 2 && (
        <Sequence from={BEATS.VISUAL_02_START} durationInFrames={BEATS.VISUAL_02_END - BEATS.VISUAL_02_START}>
          <CodeCostChart {...defaultCodeCostChartProps} />
        </Sequence>
      )}

      {/* Visual 3: CrossingPoint - Dashed line, debt accumulates, 60% speedup */}
      {activeVisual === 3 && (
        <Sequence from={BEATS.VISUAL_03_START} durationInFrames={BEATS.VISUAL_03_END - BEATS.VISUAL_03_START}>
          <CrossingPoint {...defaultCrossingPointProps} />
        </Sequence>
      )}

      {/* Visual 4: ContextRot - Context rot: AI debt, keyhole, guesses wrong */}
      {activeVisual === 4 && (
        <Sequence from={BEATS.VISUAL_04_START} durationInFrames={BEATS.VISUAL_04_END - BEATS.VISUAL_04_START}>
          <ContextRot {...defaultContextRotProps} />
        </Sequence>
      )}

      {/* Visual 5: DeveloperEditZoomout - Regeneration: no debt, no rot, crossed lines */}
      {activeVisual === 5 && (
        <Sequence from={BEATS.VISUAL_05_START} durationInFrames={BEATS.VISUAL_05_END - BEATS.VISUAL_05_START}>
          <DeveloperEditZoomout {...defaultDeveloperEditZoomoutProps} />
        </Sequence>
      )}

      {/* Visual 6: Veo clip - Best darning needles, still accumulation */}
      {activeVisual === 6 && (
        <AbsoluteFill>
          <OffthreadVideo
            src={staticFile("07_split_screen_sepia.mp4")}
            style={{ width: "100%", height: "100%" }}
          />
        </AbsoluteFill>
      )}

      {/* Visual 7: PieChart - 80-90% maintenance costs */}
      {activeVisual === 7 && (
        <Sequence from={BEATS.VISUAL_07_START} durationInFrames={BEATS.VISUAL_07_END - BEATS.VISUAL_07_START}>
          <PieChart {...defaultPieChartProps} />
        </Sequence>
      )}

      {/* Visual 8: PieToCurve - Costs compound, regenerate resets to zero */}
      {activeVisual === 8 && (
        <Sequence from={BEATS.VISUAL_08_START} durationInFrames={BEATS.VISUAL_08_END - BEATS.VISUAL_08_START}>
          <PieToCurve {...defaultPieToCurveProps} />
        </Sequence>
      )}
    </AbsoluteFill>
  );
};
