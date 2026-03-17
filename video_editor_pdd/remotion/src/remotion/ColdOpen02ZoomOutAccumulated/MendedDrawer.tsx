import React from "react";
import { useCurrentFrame, interpolate } from "remotion";
import {
  DRAWER_BG,
  DRAWER_BORDER,
  GARMENT_STAGGER_FRAMES,
  STITCH_COLOR,
  STITCH_OPACITY,
  GARMENT_COLORS,
  ZOOM_START_FRAME,
} from "./constants";

// Deterministic pseudo-random
const pseudoRandom = (seed: number): number => {
  const x = Math.sin(seed * 127.1 + 311.7) * 43758.5453;
  return x - Math.floor(x);
};

interface GarmentItem {
  x: number;
  y: number;
  width: number;
  height: number;
  color: string;
  type: "sock" | "shirt" | "trouser";
  rotation: number;
}

// Generate 47 mended garment items in a drawer layout
const generateGarments = (): GarmentItem[] => {
  const items: GarmentItem[] = [];
  const drawerWidth = 800;
  const drawerHeight = 700;
  const offsetX = (958 - drawerWidth) / 2;
  const offsetY = (1080 - drawerHeight) / 2 + 40;

  for (let i = 0; i < 47; i++) {
    const row = Math.floor(i / 7);
    const col = i % 7;
    const types: Array<"sock" | "shirt" | "trouser"> = ["sock", "shirt", "trouser"];
    const type = types[Math.floor(pseudoRandom(i + 50) * 3)];

    let w: number, h: number;
    if (type === "sock") {
      w = 50 + pseudoRandom(i + 10) * 20;
      h = 70 + pseudoRandom(i + 20) * 20;
    } else if (type === "shirt") {
      w = 80 + pseudoRandom(i + 30) * 20;
      h = 60 + pseudoRandom(i + 40) * 20;
    } else {
      w = 55 + pseudoRandom(i + 60) * 15;
      h = 90 + pseudoRandom(i + 70) * 20;
    }

    const colorIndex = Math.floor(pseudoRandom(i + 80) * GARMENT_COLORS.length);
    const jitterX = (pseudoRandom(i + 90) - 0.5) * 16;
    const jitterY = (pseudoRandom(i + 100) - 0.5) * 12;
    const rotation = (pseudoRandom(i + 110) - 0.5) * 12;

    items.push({
      x: offsetX + col * (drawerWidth / 7) + (drawerWidth / 7 - w) / 2 + jitterX,
      y: offsetY + row * (drawerHeight / 7) + (drawerHeight / 7 - h) / 2 + jitterY,
      width: w,
      height: h,
      color: GARMENT_COLORS[colorIndex],
      type,
      rotation,
    });
  }

  return items;
};

const garments = generateGarments();

const StitchMarks: React.FC<{ width: number; height: number }> = ({
  width,
  height,
}) => {
  // Draw crosshatch stitch lines
  const lines: React.ReactNode[] = [];
  const spacing = 10;
  for (let i = 0; i < Math.floor(width / spacing); i++) {
    const x = i * spacing + 4;
    lines.push(
      <line
        key={`v${i}`}
        x1={x}
        y1={2}
        x2={x + 4}
        y2={height - 2}
        stroke={STITCH_COLOR}
        strokeWidth={0.8}
        opacity={STITCH_OPACITY}
      />
    );
  }
  for (let i = 0; i < Math.floor(height / spacing); i++) {
    const y = i * spacing + 4;
    lines.push(
      <line
        key={`h${i}`}
        x1={2}
        y1={y}
        x2={width - 2}
        y2={y + 4}
        stroke={STITCH_COLOR}
        strokeWidth={0.8}
        opacity={STITCH_OPACITY}
      />
    );
  }
  return (
    <svg
      width={width}
      height={height}
      style={{ position: "absolute", top: 0, left: 0 }}
    >
      {lines}
    </svg>
  );
};

const GarmentTile: React.FC<{
  item: GarmentItem;
  index: number;
  revealProgress: number;
}> = ({ item, index, revealProgress }) => {
  const frame = useCurrentFrame();
  const staggerDelay = index * GARMENT_STAGGER_FRAMES;
  const itemProgress = interpolate(
    revealProgress,
    [staggerDelay / 200, Math.min(1, (staggerDelay + 40) / 200)],
    [0, 1],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
  );

  return (
    <div
      style={{
        position: "absolute",
        left: item.x,
        top: item.y,
        width: item.width,
        height: item.height,
        backgroundColor: item.color,
        borderRadius: item.type === "sock" ? "40% 40% 20% 20%" : 4,
        opacity: itemProgress,
        transform: `rotate(${item.rotation}deg) scale(${interpolate(itemProgress, [0, 1], [0.7, 1])})`,
        boxShadow: "0 1px 3px rgba(0,0,0,0.3)",
        overflow: "hidden",
      }}
    >
      {/* Visible stitch marks on each garment */}
      <StitchMarks width={item.width} height={item.height} />
    </div>
  );
};

export const MendedDrawer: React.FC<{ revealProgress: number }> = ({
  revealProgress,
}) => {
  const drawerWidth = 840;
  const drawerHeight = 740;
  const offsetX = (958 - drawerWidth) / 2;
  const offsetY = (1080 - drawerHeight) / 2 + 20;

  return (
    <>
      {/* Wooden drawer background */}
      <div
        style={{
          position: "absolute",
          left: offsetX,
          top: offsetY,
          width: drawerWidth,
          height: drawerHeight,
          backgroundColor: DRAWER_BG,
          border: `3px solid ${DRAWER_BORDER}`,
          borderRadius: 8,
          opacity: interpolate(revealProgress, [0, 0.15], [0, 1], {
            extrapolateRight: "clamp",
          }),
          boxShadow: "inset 0 4px 20px rgba(0,0,0,0.4)",
        }}
      />

      {/* Garment items */}
      {garments.map((item, i) => (
        <GarmentTile
          key={i}
          item={item}
          index={i}
          revealProgress={revealProgress}
        />
      ))}
    </>
  );
};
