import React from "react";
import {
  AbsoluteFill,
  OffthreadVideo,
  staticFile,
  useCurrentFrame,
  interpolate,
  spring,
} from "remotion";
import { MoldShape } from "./MoldShape";
import { ConveyorBelt } from "./ConveyorBelt";
import { PartStream, getDefectPartX } from "./PartStream";
import { PartCounter } from "./PartCounter";
import { DefectTraceback } from "./DefectTraceback";
import {
  BG_COLOR,
  PANEL_X,
  PANEL_Y,
  PANEL_W,
  PANEL_H,
  PANEL_BORDER_RADIUS,
  PANEL_BG,
  PANEL_BLUR,
  PANEL_FADE_START,
  PANEL_FADE_END,
  DEFECT_APPEAR,
  DEFECT_DISSOLVE_END,
  WRENCH_APPEAR,
  FADEOUT_START,
  FADEOUT_END,
  FPS,
} from "./constants";

export const defaultPart2ParadigmShift03MoldProductionInfographicProps = {};

export const Part2ParadigmShift03MoldProductionInfographic: React.FC = () => {
  const frame = useCurrentFrame();

  // Backing panel opacity: fades in 0-30, holds, fades out 570-600
  const panelOpacity = interpolate(
    frame,
    [PANEL_FADE_START, PANEL_FADE_END, FADEOUT_START, FADEOUT_END],
    [0, 0.75, 0.75, 0],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
  );

  // Wrench spring animation at frame 330
  const showWrench = frame >= WRENCH_APPEAR;
  const wrenchScale = showWrench
    ? spring({
        frame: frame - WRENCH_APPEAR,
        fps: FPS,
        config: { damping: 10, stiffness: 180 },
      })
    : 0;

  // Defect part X position (fixed once defect appears)
  const defectX = getDefectPartX();

  return (
    <AbsoluteFill style={{ backgroundColor: BG_COLOR }}>
      {/* Veo background video */}
      <AbsoluteFill>
        <OffthreadVideo
          src={staticFile("veo/part2_paradigm_shift.mp4")}
          style={{ width: "100%", height: "100%", objectFit: "cover" }}
          muted
        />
      </AbsoluteFill>

      {/* Backing panel with blur */}
      <div
        style={{
          position: "absolute",
          left: PANEL_X,
          top: PANEL_Y,
          width: PANEL_W,
          height: PANEL_H,
          borderRadius: PANEL_BORDER_RADIUS,
          backgroundColor: PANEL_BG,
          backdropFilter: `blur(${PANEL_BLUR}px)`,
          WebkitBackdropFilter: `blur(${PANEL_BLUR}px)`,
          opacity: panelOpacity,
        }}
      />

      {/* Mold shape with glow and wrench icon */}
      <MoldShape showWrench={showWrench} wrenchScale={wrenchScale} />

      {/* Conveyor belt */}
      <ConveyorBelt />

      {/* Streaming parts */}
      <PartStream />

      {/* Part counter */}
      <PartCounter />

      {/* Defect "✗" mark + trace-back line — hidden after dissolve completes */}
      {frame >= DEFECT_APPEAR && frame <= DEFECT_DISSOLVE_END && (
        <DefectTraceback defectX={defectX} />
      )}
    </AbsoluteFill>
  );
};

export default Part2ParadigmShift03MoldProductionInfographic;
