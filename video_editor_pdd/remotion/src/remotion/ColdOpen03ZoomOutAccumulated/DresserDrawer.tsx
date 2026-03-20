import React from "react";
import { useCurrentFrame, interpolate, Easing } from "remotion";
import {
  PANEL_WIDTH,
  CANVAS_HEIGHT,
  DRAWER_WOOD_COLOR,
  STITCH_COLOR,
  GARMENT_COLORS,
  ZOOM_START,
  ZOOM_END,
  ZOOM_FROM,
  ZOOM_TO,
  PULSE_START,
  PULSE_DURATION,
  seededRandom,
} from "./constants";

// Pre-generate garment layout: a top-down dresser drawer with folded garments
const DRAWER_MARGIN = 60;
const DRAWER_WIDTH = PANEL_WIDTH - 2 * DRAWER_MARGIN;
const DRAWER_HEIGHT = CANVAS_HEIGHT - 2 * DRAWER_MARGIN;
const DRAWER_LEFT = DRAWER_MARGIN;
const DRAWER_TOP = DRAWER_MARGIN;

interface Garment {
  x: number;
  y: number;
  width: number;
  height: number;
  color: string;
  stitchAngle: number;
  distFromCenter: number;
}

const CENTER_X = PANEL_WIDTH / 2;
const CENTER_Y = CANVAS_HEIGHT / 2;

const GARMENT_COUNT = 47;
const COLS = 7;
const ROWS = Math.ceil(GARMENT_COUNT / COLS);
const GARMENT_W = (DRAWER_WIDTH - 20) / COLS;
const GARMENT_H = (DRAWER_HEIGHT - 20) / ROWS;

const garments: Garment[] = Array.from({ length: GARMENT_COUNT }, (_, i) => {
  const col = i % COLS;
  const row = Math.floor(i / COLS);
  const jitterX = (seededRandom(i * 5 + 50) - 0.5) * 8;
  const jitterY = (seededRandom(i * 5 + 51) - 0.5) * 6;
  const x = DRAWER_LEFT + 10 + col * GARMENT_W + jitterX;
  const y = DRAWER_TOP + 10 + row * GARMENT_H + jitterY;
  const color = GARMENT_COLORS[i % GARMENT_COLORS.length];
  const stitchAngle = seededRandom(i * 13 + 77) * 360;
  const dx = x + GARMENT_W / 2 - CENTER_X;
  const dy = y + GARMENT_H / 2 - CENTER_Y;
  const distFromCenter = Math.sqrt(dx * dx + dy * dy);
  return {
    x,
    y,
    width: GARMENT_W - 6,
    height: GARMENT_H - 6,
    color,
    stitchAngle,
    distFromCenter,
  };
});

const maxDist = Math.max(...garments.map((g) => g.distFromCenter));

export const DresserDrawer: React.FC = () => {
  const frame = useCurrentFrame();

  // Zoom
  const scale = interpolate(frame, [ZOOM_START, ZOOM_END], [ZOOM_FROM, ZOOM_TO], {
    extrapolateLeft: "clamp",
    extrapolateRight: "clamp",
    easing: Easing.inOut(Easing.cubic),
  });

  // Brightness pulse
  const pulseProgress = interpolate(
    frame,
    [PULSE_START, PULSE_START + PULSE_DURATION],
    [0, Math.PI * 2],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
  );
  const brightnessOffset = frame >= PULSE_START ? Math.sin(pulseProgress) * 0.02 : 0;
  const brightness = 1 + brightnessOffset;

  // Stitch draw-in progress (frames 90-140)
  const stitchProgress = interpolate(frame, [90, 140], [0, 1], {
    extrapolateLeft: "clamp",
    extrapolateRight: "clamp",
    easing: Easing.out(Easing.quad),
  });

  return (
    <div
      style={{
        width: PANEL_WIDTH,
        height: CANVAS_HEIGHT,
        position: "relative",
        overflow: "hidden",
        filter: `brightness(${brightness})`,
      }}
    >
      {/* Zoomed content */}
      <div
        style={{
          position: "absolute",
          left: "50%",
          top: "50%",
          width: PANEL_WIDTH,
          height: CANVAS_HEIGHT,
          transform: `translate(-50%, -50%) scale(${scale})`,
          transformOrigin: "center center",
        }}
      >
        {/* Drawer base */}
        <div
          style={{
            position: "absolute",
            left: DRAWER_LEFT,
            top: DRAWER_TOP,
            width: DRAWER_WIDTH,
            height: DRAWER_HEIGHT,
            backgroundColor: DRAWER_WOOD_COLOR,
            borderRadius: 8,
            border: "3px solid #6B5538",
            boxShadow: "inset 0 4px 16px rgba(0,0,0,0.3)",
          }}
        />

        {/* Inner drawer shadow/lining */}
        <div
          style={{
            position: "absolute",
            left: DRAWER_LEFT + 6,
            top: DRAWER_TOP + 6,
            width: DRAWER_WIDTH - 12,
            height: DRAWER_HEIGHT - 12,
            backgroundColor: "#5A4633",
            borderRadius: 4,
          }}
        />

        {/* Garments */}
        {garments.map((garment, i) => {
          const normalizedDist = garment.distFromCenter / maxDist;
          const garmentFadeStart = ZOOM_START + normalizedDist * 60;
          const garmentOpacity = interpolate(
            frame,
            [garmentFadeStart, garmentFadeStart + 20],
            [0, 1],
            {
              extrapolateLeft: "clamp",
              extrapolateRight: "clamp",
              easing: Easing.out(Easing.quad),
            }
          );

          // Stitch line length for this garment
          const stitchLen = stitchProgress * garment.width * 0.6;

          return (
            <div
              key={i}
              style={{
                position: "absolute",
                left: garment.x,
                top: garment.y,
                width: garment.width,
                height: garment.height,
                opacity: garmentOpacity,
              }}
            >
              {/* Fabric */}
              <div
                style={{
                  width: "100%",
                  height: "100%",
                  backgroundColor: garment.color,
                  borderRadius: 3,
                  border: "1px solid rgba(0,0,0,0.15)",
                  position: "relative",
                  overflow: "hidden",
                }}
              >
                {/* Cross-stitch repair mark */}
                <svg
                  width={garment.width}
                  height={garment.height}
                  style={{ position: "absolute", left: 0, top: 0 }}
                  viewBox={`0 0 ${garment.width} ${garment.height}`}
                >
                  {/* Diagonal stitch line 1 */}
                  <line
                    x1={garment.width * 0.2}
                    y1={garment.height * 0.3}
                    x2={garment.width * 0.2 + stitchLen * 0.7}
                    y2={garment.height * 0.3 + stitchLen * 0.4}
                    stroke={STITCH_COLOR}
                    strokeWidth={1.5}
                    strokeLinecap="round"
                    strokeDasharray="3 3"
                  />
                  {/* Diagonal stitch line 2 (cross) */}
                  <line
                    x1={garment.width * 0.2 + stitchLen * 0.7}
                    y1={garment.height * 0.3}
                    x2={garment.width * 0.2}
                    y2={garment.height * 0.3 + stitchLen * 0.4}
                    stroke={STITCH_COLOR}
                    strokeWidth={1.5}
                    strokeLinecap="round"
                    strokeDasharray="3 3"
                  />
                </svg>
              </div>
            </div>
          );
        })}
      </div>
    </div>
  );
};

export default DresserDrawer;
