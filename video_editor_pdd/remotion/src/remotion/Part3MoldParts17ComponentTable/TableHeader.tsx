import React from "react";
import { interpolate, useCurrentFrame, Easing } from "remotion";

const HEADERS = ["COMPONENT", "ENCODES", "OWNER"];
const COL_WIDTHS = [200, 300, 200];
const TABLE_W = 800;
const HEADER_BG = "#1E1E2E";
const HEADER_BORDER = "#334155";
const HEADER_TEXT = "#64748B";

export const TableHeader: React.FC = () => {
  const frame = useCurrentFrame();

  const opacity = interpolate(frame, [0, 15], [0, 1], {
    extrapolateLeft: "clamp",
    extrapolateRight: "clamp",
    easing: Easing.out(Easing.quad),
  });

  return (
    <div
      style={{
        position: "absolute",
        top: 280,
        left: (1920 - TABLE_W) / 2,
        width: TABLE_W,
        height: 48,
        backgroundColor: HEADER_BG,
        borderBottom: `2px solid ${HEADER_BORDER}`,
        display: "flex",
        flexDirection: "row",
        alignItems: "center",
        opacity,
      }}
    >
      {HEADERS.map((header, i) => (
        <div
          key={header}
          style={{
            width: COL_WIDTHS[i],
            paddingLeft: 24,
            paddingRight: 24,
            fontFamily: "Inter, sans-serif",
            fontSize: 14,
            fontWeight: 600,
            color: HEADER_TEXT,
            textTransform: "uppercase",
            letterSpacing: 2,
          }}
        >
          {header}
        </div>
      ))}
    </div>
  );
};

export default TableHeader;
