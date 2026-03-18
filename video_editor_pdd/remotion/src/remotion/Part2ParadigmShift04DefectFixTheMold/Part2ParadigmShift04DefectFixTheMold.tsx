import React from "react";
import {
  AbsoluteFill,
  useCurrentFrame,
  Sequence,
  Video,
  interpolate,
} from "remotion";
import { useVisualMediaAssetSrc } from "../_shared/visual-runtime";
import {
  BG_COLOR,
  TOTAL_FRAMES,
  MOLD_CENTER_X,
  PART_W,
  PART_H,
} from "./constants";
import { DraftGrid } from "./DraftGrid";
import { MoldDiagram } from "./MoldDiagram";
import { EjectedPart } from "./EjectedPart";
import { DefectHighlight } from "./DefectHighlight";
import { RejectedPatch } from "./RejectedPatch";
import { WallAdjustment } from "./WallAdjustment";
import { FixedParts } from "./FixedParts";

export const defaultPart2ParadigmShift04DefectFixTheMoldProps = {};

/**
 * Section 2.4 — Defect → Fix the Mold, Not the Part
 *
 * An animated diagram showing:
 * 1. A mold ejects a defective part
 * 2. The "patch the part" approach is rejected
 * 3. The mold itself is fixed
 * 4. All future parts come out perfect
 *
 * Duration: 420 frames @ 30fps (~14s)
 */
export const Part2ParadigmShift04DefectFixTheMold: React.FC = () => {
  const frame = useCurrentFrame();
  const backgroundSrc = useVisualMediaAssetSrc("backgroundSrc");

  // Positions for the defective ejected part
  const partFromY = 650;
  const partToY = 780;
  const defectEdgeX = MOLD_CENTER_X + PART_W / 2 - 12; // right edge where defect is
  const defectEdgeY = partToY;

  // Background video opacity — subtle, underlays the diagram
  const bgOpacity = interpolate(frame, [0, 30], [0, 0.15], {
    extrapolateLeft: "clamp",
    extrapolateRight: "clamp",
  });

  return (
    <AbsoluteFill
      style={{
        backgroundColor: BG_COLOR,
        overflow: "hidden",
      }}
    >
      {/* Optional Veo background video */}
      {backgroundSrc && (
        <AbsoluteFill style={{ opacity: bgOpacity }}>
          <Video
            src={backgroundSrc}
            style={{
              width: "100%",
              height: "100%",
              objectFit: "cover",
            }}
            startFrom={0}
            muted
          />
        </AbsoluteFill>
      )}

      {/* Drafting grid */}
      <DraftGrid />

      {/* Mold diagram — draws from frame 0 */}
      <Sequence from={0} durationInFrames={TOTAL_FRAMES}>
        <MoldDiagram />
      </Sequence>

      {/* Defective part ejection — from frame 30 */}
      <Sequence from={0} durationInFrames={TOTAL_FRAMES}>
        <EjectedPart fromY={partFromY} toY={partToY} showDefect />
      </Sequence>

      {/* Defect highlight — callout, magnifier, label */}
      <Sequence from={0} durationInFrames={TOTAL_FRAMES}>
        <DefectHighlight partX={defectEdgeX} partY={defectEdgeY} />
      </Sequence>

      {/* Rejected "patch the part" approach */}
      <Sequence from={0} durationInFrames={TOTAL_FRAMES}>
        <RejectedPatch partX={MOLD_CENTER_X} partY={partToY + PART_H / 2} />
      </Sequence>

      {/* Fix the mold — wrench icon + label */}
      <Sequence from={0} durationInFrames={TOTAL_FRAMES}>
        <WallAdjustment />
      </Sequence>

      {/* Fixed parts with green checkmarks */}
      <Sequence from={0} durationInFrames={TOTAL_FRAMES}>
        <FixedParts />
      </Sequence>
    </AbsoluteFill>
  );
};

export default Part2ParadigmShift04DefectFixTheMold;
