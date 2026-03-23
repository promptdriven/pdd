import React from "react";
import { useCurrentFrame, interpolate, Easing } from "remotion";
import {
  FILE_TREE,
  SIDEBAR_BG,
  SIDEBAR_BORDER,
  TEXT_SECONDARY,
  TEXT_DIM,
  LAYER2_START,
} from "./constants";

const FOLDER_ICON = "📁";
const FILE_ICON = "📄";

interface FileExplorerTreeProps {
  width?: number;
}

const FileExplorerTree: React.FC<FileExplorerTreeProps> = ({
  width = 220,
}) => {
  const frame = useCurrentFrame();

  // Slide in from left
  const slideX = interpolate(
    frame,
    [LAYER2_START, LAYER2_START + 20],
    [-width, 0],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.out(Easing.quad),
    }
  );

  const opacity = interpolate(
    frame,
    [LAYER2_START, LAYER2_START + 15],
    [0, 1],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
    }
  );

  return (
    <div
      style={{
        position: "absolute",
        left: 0,
        top: 0,
        width,
        height: "100%",
        backgroundColor: SIDEBAR_BG,
        borderRight: `1px solid ${SIDEBAR_BORDER}`,
        transform: `translateX(${slideX}px)`,
        opacity,
        padding: "8px 0",
        overflow: "hidden",
        zIndex: 10,
      }}
    >
      {/* Explorer header */}
      <div
        style={{
          padding: "4px 12px 8px",
          fontFamily: "Inter, sans-serif",
          fontSize: 10,
          color: TEXT_SECONDARY,
          opacity: 0.6,
          textTransform: "uppercase",
          letterSpacing: 1,
        }}
      >
        Explorer
      </div>

      {/* File tree */}
      {FILE_TREE.map((node, i) => {
        // Stagger each item's appearance
        const itemDelay = LAYER2_START + 5 + i * 0.4;
        const itemOpacity = interpolate(
          frame,
          [itemDelay, itemDelay + 8],
          [0, 1],
          {
            extrapolateLeft: "clamp",
            extrapolateRight: "clamp",
          }
        );

        return (
          <div
            key={i}
            style={{
              display: "flex",
              alignItems: "center",
              height: 18,
              paddingLeft: 12 + node.indent * 14,
              opacity: itemOpacity * 0.4,
              cursor: "default",
            }}
          >
            <span style={{ fontSize: 9, marginRight: 4, width: 14 }}>
              {node.isDir
                ? node.isExpanded
                  ? "▾"
                  : "▸"
                : ""}
            </span>
            <span
              style={{
                fontFamily: "Inter, sans-serif",
                fontSize: 10,
                color: node.isDir ? TEXT_SECONDARY : TEXT_DIM,
                whiteSpace: "nowrap",
              }}
            >
              {node.name}
            </span>
          </div>
        );
      })}
    </div>
  );
};

export default FileExplorerTree;
