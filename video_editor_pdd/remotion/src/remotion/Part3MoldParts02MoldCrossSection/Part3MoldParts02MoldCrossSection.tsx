import React from "react";
import { AbsoluteFill } from "remotion";
import "../_shared/load-inter-font";
import { BG_COLOR, REGIONS } from "./constants";
import { BlueprintGrid } from "./BlueprintGrid";
import { MoldDiagram } from "./MoldDiagram";
import { ConnectorLabel } from "./ConnectorLabel";

export const defaultPart3MoldParts02MoldCrossSectionProps = {};

/**
 * Section 3.2 – Mold Cross-Section: Three Regions
 *
 * A technical cross-section diagram of an injection mold with three
 * regions (Walls/Tests, Nozzle/Prompt, Cavity/Grounding) that
 * illuminate in sequence over 420 frames (14s @ 30fps).
 */
export const Part3MoldParts02MoldCrossSection: React.FC = () => {
  return (
    <AbsoluteFill
      style={{
        backgroundColor: BG_COLOR,
        width: 1920,
        height: 1080,
        overflow: "hidden",
      }}
    >
      {/* Blueprint grid background – visible from frame 0 */}
      <BlueprintGrid />

      {/* Mold outline + region glows (SVG layer) */}
      <MoldDiagram />

      {/* Connector labels for each region */}
      {REGIONS.map((region) => (
        <ConnectorLabel key={region.id} region={region} />
      ))}
    </AbsoluteFill>
  );
};

export default Part3MoldParts02MoldCrossSection;
