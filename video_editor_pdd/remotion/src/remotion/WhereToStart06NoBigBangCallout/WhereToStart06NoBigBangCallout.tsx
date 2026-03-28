import React from "react";
import { AbsoluteFill } from "remotion";
import "../_shared/load-inter-font";
import {
  BG_COLOR,
  TEXT_CONTAINER_WIDTH,
  LINE1_START,
  LINE2_START,
  LINE3_START,
  STATEMENTS,
} from "./constants";
import { ModuleGrid } from "./ModuleGrid";
import { StatementLine } from "./StatementLine";

export const defaultWhereToStart06NoBigBangCalloutProps = {};

const LINE_START_FRAMES = [LINE1_START, LINE2_START, LINE3_START] as const;

export const WhereToStart06NoBigBangCallout: React.FC = () => {
  return (
    <AbsoluteFill style={{ backgroundColor: BG_COLOR }}>
      {/* Dimmed module grid background */}
      <ModuleGrid />

      {/* Statement stack */}
      <AbsoluteFill
        style={{
          justifyContent: "center",
          alignItems: "center",
        }}
      >
        <div
          style={{
            width: TEXT_CONTAINER_WIDTH,
            display: "flex",
            flexDirection: "column",
          }}
        >
          {STATEMENTS.map((stmt, i) => (
            <StatementLine
              key={stmt.text}
              text={stmt.text}
              color={stmt.color}
              weight={stmt.weight}
              startFrame={LINE_START_FRAMES[i]}
            />
          ))}
        </div>
      </AbsoluteFill>
    </AbsoluteFill>
  );
};

export default WhereToStart06NoBigBangCallout;
