import React from "react";
import { AbsoluteFill } from "remotion";
import { TableHeader } from "./TableHeader";
import { TableRowItem } from "./TableRow";
import { HierarchyText } from "./HierarchyText";

const BG_COLOR = "#0A0F1A";

const TABLE_ROWS_DATA = [
  {
    component: "Prompt",
    encodes: "WHAT",
    parenthetical: "(intent)",
    owner: "Developer",
    accentColor: "#D9944A",
  },
  {
    component: "Grounding",
    encodes: "HOW",
    parenthetical: "(style)",
    owner: "Automatic",
    accentColor: "#4AD9A0",
  },
  {
    component: "Tests",
    encodes: "CORRECTNESS",
    parenthetical: "",
    owner: "Accumulated",
    accentColor: "#4A90D9",
  },
];

// Header is 48px tall, starts at y=280
// Each row is 60px tall, starting below header at y=328
const HEADER_BOTTOM = 280 + 48; // 328

export const defaultPart3MoldParts17ComponentTableProps = {};

export const Part3MoldParts17ComponentTable: React.FC = () => {
  return (
    <AbsoluteFill
      style={{
        backgroundColor: BG_COLOR,
        fontFamily: "Inter, sans-serif",
      }}
    >
      {/* Table header — fades in frame 0–15 */}
      <TableHeader />

      {/* Table rows — slide in starting at frames 30, 60, 90 */}
      {TABLE_ROWS_DATA.map((row, i) => (
        <TableRowItem
          key={row.component}
          component={row.component}
          encodes={row.encodes}
          parenthetical={row.parenthetical}
          owner={row.owner}
          accentColor={row.accentColor}
          startFrame={30 + i * 30}
          topY={HEADER_BOTTOM + i * 60}
        />
      ))}

      {/* Hierarchy text + subtext — appear at frames 180 and 240 */}
      <HierarchyText />
    </AbsoluteFill>
  );
};

export default Part3MoldParts17ComponentTable;
