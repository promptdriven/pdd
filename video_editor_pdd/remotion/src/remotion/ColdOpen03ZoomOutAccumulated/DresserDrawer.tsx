import React from 'react';
import { useCurrentFrame, interpolate, Easing } from 'remotion';
import {
  DRAWER_WOOD_COLOR,
  STITCH_COLOR,
  GARMENT_FILLS,
  ZOOM_START,
  seededRandom,
} from './constants';

interface Garment {
  x: number;
  y: number;
  width: number;
  height: number;
  fill: string;
  rotation: number;
  distFromCenter: number;
  seed: number;
}

function generateGarments(): Garment[] {
  const garments: Garment[] = [];
  const cols = 6;
  const rows = 7;
  const gapX = 10;
  const gapY = 8;
  const baseW = 50;
  const baseH = 36;
  const totalW = cols * (baseW + gapX);
  const totalH = rows * (baseH + gapY);
  const offsetX = -totalW / 2;
  const offsetY = -totalH / 2;
  const centerCol = cols / 2;
  const centerRow = rows / 2;
  let count = 0;

  for (let row = 0; row < rows; row++) {
    for (let col = 0; col < cols; col++) {
      if (count >= 47) break;
      const idx = count;
      const rand = seededRandom(idx + 200);
      const w = baseW + Math.floor(seededRandom(idx + 300) * 16) - 8;
      const h = baseH + Math.floor(seededRandom(idx + 400) * 12) - 6;
      const rot = (seededRandom(idx + 500) - 0.5) * 12;
      const dist = Math.sqrt(
        Math.pow(col - centerCol, 2) + Math.pow(row - centerRow, 2)
      );

      garments.push({
        x: offsetX + col * (baseW + gapX) + (seededRandom(idx + 600) - 0.5) * 6,
        y: offsetY + row * (baseH + gapY) + (seededRandom(idx + 700) - 0.5) * 6,
        width: w,
        height: h,
        fill: GARMENT_FILLS[Math.floor(rand * GARMENT_FILLS.length)],
        rotation: rot,
        distFromCenter: dist,
        seed: idx,
      });
      count++;
    }
  }
  return garments;
}

const garments = generateGarments();
const maxDist = Math.max(...garments.map((g) => g.distFromCenter));

export const DresserDrawer: React.FC = () => {
  const frame = useCurrentFrame();

  return (
    <div
      style={{
        position: 'absolute',
        left: '50%',
        top: '50%',
        transform: 'translate(-50%, -50%)',
      }}
    >
      {/* Drawer base (top-down view) */}
      <div
        style={{
          position: 'absolute',
          left: -200,
          top: -160,
          width: 400,
          height: 320,
          backgroundColor: DRAWER_WOOD_COLOR,
          borderRadius: 6,
          opacity: 0.4,
          border: `3px solid rgba(139, 109, 75, 0.6)`,
        }}
      />

      {/* Inner drawer */}
      <div
        style={{
          position: 'absolute',
          left: -185,
          top: -145,
          width: 370,
          height: 290,
          backgroundColor: '#2A1F14',
          borderRadius: 3,
          opacity: 0.6,
        }}
      />

      {/* Garments */}
      {garments.map((garment, i) => {
        const delayFrames = (garment.distFromCenter / maxDist) * 40;
        const fadeStart = ZOOM_START + delayFrames;
        const opacity = interpolate(
          frame,
          [fadeStart, fadeStart + 30],
          [0, 0.85],
          {
            extrapolateLeft: 'clamp',
            extrapolateRight: 'clamp',
            easing: Easing.out(Easing.quad),
          }
        );

        // Stitch lines draw in from frame 90
        const stitchProgress = interpolate(
          frame,
          [90 + i * 0.5, 130 + i * 0.5],
          [0, 1],
          {
            extrapolateLeft: 'clamp',
            extrapolateRight: 'clamp',
            easing: Easing.out(Easing.quad),
          }
        );

        return (
          <div
            key={i}
            style={{
              position: 'absolute',
              left: garment.x,
              top: garment.y,
              width: garment.width,
              height: garment.height,
              backgroundColor: garment.fill,
              opacity,
              borderRadius: 3,
              transform: `rotate(${garment.rotation}deg)`,
              overflow: 'hidden',
            }}
          >
            {/* Cross-stitch repair marks */}
            <svg
              width={garment.width}
              height={garment.height}
              style={{ position: 'absolute', left: 0, top: 0 }}
            >
              {/* Diagonal stitch line 1 */}
              <line
                x1={garment.width * 0.2}
                y1={garment.height * 0.3}
                x2={garment.width * 0.8}
                y2={garment.height * 0.7}
                stroke={STITCH_COLOR}
                strokeWidth={1.5}
                strokeDasharray={`${garment.width * stitchProgress} ${garment.width}`}
                opacity={0.8}
              />
              {/* Diagonal stitch line 2 (cross) */}
              <line
                x1={garment.width * 0.8}
                y1={garment.height * 0.3}
                x2={garment.width * 0.2}
                y2={garment.height * 0.7}
                stroke={STITCH_COLOR}
                strokeWidth={1.5}
                strokeDasharray={`${garment.width * stitchProgress} ${garment.width}`}
                opacity={0.8}
              />
              {/* Small stitch marks */}
              {[0.3, 0.45, 0.6, 0.75].map((t, si) => (
                <line
                  key={si}
                  x1={garment.width * t - 2}
                  y1={garment.height * 0.5 - 3}
                  x2={garment.width * t + 2}
                  y2={garment.height * 0.5 + 3}
                  stroke={STITCH_COLOR}
                  strokeWidth={1}
                  opacity={0.6 * stitchProgress}
                />
              ))}
            </svg>
          </div>
        );
      })}
    </div>
  );
};

export default DresserDrawer;
