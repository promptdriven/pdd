import React from "react";
import { interpolate, Easing, useCurrentFrame } from "remotion";
import {
  STITCH_AMBER,
  DRAWER_BG,
  GARMENT_SOCK,
  GARMENT_SHIRT,
  GARMENT_TROUSER,
} from "./constants";

function seededRandom(seed: number): number {
  const x = Math.sin(seed * 9301 + 49297) * 49297;
  return x - Math.floor(x);
}

interface GarmentItem {
  x: number;
  y: number;
  width: number;
  height: number;
  type: "sock" | "shirt" | "trouser";
  rotation: number;
  seed: number;
}

function generateGarments(): GarmentItem[] {
  const items: GarmentItem[] = [];
  const types: Array<"sock" | "shirt" | "trouser"> = [
    "sock",
    "shirt",
    "trouser",
  ];

  // Place 47 garments in a roughly grid-like but organic layout
  const cols = 7;
  const rows = 7;
  const cellW = 120;
  const cellH = 100;
  let count = 0;

  for (let r = 0; r < rows && count < 47; r++) {
    for (let c = 0; c < cols && count < 47; c++) {
      const seed = count * 31 + 11;
      const rand = seededRandom(seed);
      const type = types[count % 3];

      // Slight random offset within the cell for organic look
      const offsetX = (seededRandom(seed + 1) - 0.5) * 20;
      const offsetY = (seededRandom(seed + 2) - 0.5) * 16;

      const baseW =
        type === "sock" ? 50 : type === "shirt" ? 80 : 65;
      const baseH =
        type === "sock" ? 30 : type === "shirt" ? 60 : 70;

      items.push({
        x: c * cellW + 20 + offsetX,
        y: r * cellH + 15 + offsetY,
        width: baseW + seededRandom(seed + 3) * 15,
        height: baseH + seededRandom(seed + 4) * 10,
        type,
        rotation: (seededRandom(seed + 5) - 0.5) * 12,
        seed,
      });
      count++;
    }
  }
  return items;
}

const GARMENTS = generateGarments();

const garmentColor = (type: "sock" | "shirt" | "trouser") => {
  switch (type) {
    case "sock":
      return GARMENT_SOCK;
    case "shirt":
      return GARMENT_SHIRT;
    case "trouser":
      return GARMENT_TROUSER;
  }
};

interface StitchPatternProps {
  width: number;
  height: number;
}

const StitchPattern: React.FC<StitchPatternProps> = ({ width, height }) => {
  // Cross-hatch stitch marks
  const lines: React.ReactNode[] = [];
  const step = 8;
  for (let i = 0; i < Math.max(width, height); i += step) {
    // Diagonal one way
    lines.push(
      <line
        key={`a${i}`}
        x1={i}
        y1={0}
        x2={i + 12}
        y2={12}
        stroke={STITCH_AMBER}
        strokeWidth={0.8}
        opacity={0.3}
      />
    );
    // Diagonal other way
    lines.push(
      <line
        key={`b${i}`}
        x1={i + 12}
        y1={0}
        x2={i}
        y2={12}
        stroke={STITCH_AMBER}
        strokeWidth={0.8}
        opacity={0.3}
      />
    );
  }
  return (
    <svg
      width={width}
      height={height}
      style={{ position: "absolute", top: 0, left: 0 }}
      viewBox={`0 0 ${width} ${height}`}
    >
      {lines}
    </svg>
  );
};

interface MendedGarmentProps {
  item: GarmentItem;
  revealFrame: number;
}

const MendedGarment: React.FC<MendedGarmentProps> = ({
  item,
  revealFrame,
}) => {
  const frame = useCurrentFrame();

  const opacity = interpolate(frame, [revealFrame, revealFrame + 15], [0, 1], {
    extrapolateLeft: "clamp",
    extrapolateRight: "clamp",
    easing: Easing.out(Easing.quad),
  });

  const scale = interpolate(
    frame,
    [revealFrame, revealFrame + 15],
    [0.5, 1],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.out(Easing.quad),
    }
  );

  const color = garmentColor(item.type);

  // Different shapes per garment type
  const shape =
    item.type === "sock" ? (
      // Sock: rounded rectangle
      <div
        style={{
          width: item.width,
          height: item.height,
          backgroundColor: color,
          borderRadius: "12px 12px 20px 20px",
          position: "relative",
          overflow: "hidden",
        }}
      >
        <StitchPattern width={item.width} height={item.height} />
        {/* Darning patch circle */}
        <div
          style={{
            position: "absolute",
            bottom: 4,
            left: "50%",
            transform: "translateX(-50%)",
            width: item.width * 0.4,
            height: item.height * 0.5,
            borderRadius: "50%",
            border: `1.5px solid ${STITCH_AMBER}`,
            opacity: 0.5,
          }}
        />
      </div>
    ) : item.type === "shirt" ? (
      // Shirt: wider rectangle with button dots
      <div
        style={{
          width: item.width,
          height: item.height,
          backgroundColor: color,
          borderRadius: 4,
          position: "relative",
          overflow: "hidden",
        }}
      >
        <StitchPattern width={item.width} height={item.height} />
        {/* Button line */}
        {[0.2, 0.4, 0.6, 0.8].map((pct, i) => (
          <div
            key={i}
            style={{
              position: "absolute",
              left: "50%",
              top: `${pct * 100}%`,
              width: 4,
              height: 4,
              borderRadius: "50%",
              backgroundColor: STITCH_AMBER,
              opacity: 0.5,
              transform: "translateX(-50%)",
            }}
          />
        ))}
      </div>
    ) : (
      // Trousers: tall rectangle
      <div
        style={{
          width: item.width,
          height: item.height,
          backgroundColor: color,
          borderRadius: "4px 4px 2px 2px",
          position: "relative",
          overflow: "hidden",
        }}
      >
        <StitchPattern width={item.width} height={item.height} />
        {/* Knee reinforcement */}
        <div
          style={{
            position: "absolute",
            top: item.height * 0.55,
            left: 4,
            right: 4,
            height: item.height * 0.2,
            border: `1px solid ${STITCH_AMBER}`,
            borderRadius: 3,
            opacity: 0.4,
          }}
        />
      </div>
    );

  return (
    <div
      style={{
        position: "absolute",
        left: item.x,
        top: item.y,
        opacity,
        transform: `scale(${scale}) rotate(${item.rotation}deg)`,
        transformOrigin: "center center",
      }}
    >
      {shape}
    </div>
  );
};

interface MendedDrawerProps {
  revealStartFrame: number;
}

export const MendedDrawer: React.FC<MendedDrawerProps> = ({
  revealStartFrame,
}) => {
  const drawerWidth = 860;
  const drawerHeight = 720;

  return (
    <div
      style={{
        position: "absolute",
        width: drawerWidth,
        height: drawerHeight,
        left: "50%",
        top: "50%",
        transform: "translate(-50%, -50%)",
      }}
    >
      {/* Drawer background */}
      <div
        style={{
          position: "absolute",
          inset: 0,
          backgroundColor: DRAWER_BG,
          borderRadius: 8,
          border: "2px solid #5C4333",
          boxShadow: "inset 0 4px 20px rgba(0,0,0,0.5)",
        }}
      />

      {/* Garment items */}
      {GARMENTS.map((item, idx) => (
        <MendedGarment
          key={idx}
          item={item}
          revealFrame={revealStartFrame + idx * 1.5}
        />
      ))}
    </div>
  );
};
