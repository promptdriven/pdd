import React from 'react';
import { useCurrentFrame, interpolate, Easing } from 'remotion';
import {
  MOLD_CENTER_X,
  MOLD_CENTER_Y,
  MOLD_WIDTH,
  MOLD_HEIGHT,
  MOLD_BASE_COLOR,
  WALL_COLOR,
  WALL_LABEL_COLOR,
  LIQUID_COLOR,
  FLASH_COLOR,
  BASE_WALLS,
  WALL_CYCLES,
  NEW_WALL_POSITIONS,
  CYCLE_FRAMES,
  FLASH_DURATION,
  WALL_SLIDE_DURATION,
  RECONFORM_START,
  TOTAL_FRAMES,
} from './constants';

// ── Outer mold shell ────────────────────────────────────────────
const MoldShell: React.FC = () => {
  const left = MOLD_CENTER_X - MOLD_WIDTH / 2;
  const top = MOLD_CENTER_Y - MOLD_HEIGHT / 2;

  return (
    <>
      {/* Outer mold body */}
      <div
        style={{
          position: 'absolute',
          left,
          top,
          width: MOLD_WIDTH,
          height: MOLD_HEIGHT,
          border: `3px solid ${MOLD_BASE_COLOR}`,
          borderRadius: 8,
          background: 'rgba(15, 23, 42, 0.6)',
        }}
      />
      {/* Mold label */}
      <div
        style={{
          position: 'absolute',
          left: left + 10,
          top: top - 28,
          fontFamily: 'JetBrains Mono, monospace',
          fontSize: 13,
          color: MOLD_BASE_COLOR,
          fontWeight: 600,
          opacity: 0.8,
        }}
      >
        MOLD CROSS-SECTION
      </div>
    </>
  );
};

// ── Single wall segment ─────────────────────────────────────────
interface WallSegmentProps {
  x: number;
  y: number;
  width: number;
  height: number;
  label: string;
  opacity: number;
  glowIntensity?: number;
}

const WallSegment: React.FC<WallSegmentProps> = ({
  x,
  y,
  width,
  height,
  label,
  opacity,
  glowIntensity = 0,
}) => {
  const isVertical = height > width;
  const labelX = isVertical ? x + 18 : x;
  const labelY = isVertical ? y + height / 2 - 6 : y - 16;

  return (
    <>
      <div
        style={{
          position: 'absolute',
          left: x,
          top: y,
          width,
          height,
          backgroundColor: WALL_COLOR,
          opacity,
          borderRadius: 2,
          boxShadow: glowIntensity > 0
            ? `0 0 ${8 + glowIntensity * 12}px rgba(74,144,217,${0.3 + glowIntensity * 0.4})`
            : 'none',
        }}
      />
      <div
        style={{
          position: 'absolute',
          left: labelX,
          top: labelY,
          fontFamily: 'JetBrains Mono, monospace',
          fontSize: 11,
          color: WALL_LABEL_COLOR,
          opacity: opacity * 0.85,
          whiteSpace: 'nowrap',
        }}
      >
        {label}
      </div>
    </>
  );
};

// ── Liquid fill ─────────────────────────────────────────────────
const LiquidFill: React.FC<{ reconformProgress: number }> = ({ reconformProgress }) => {
  const left = MOLD_CENTER_X - MOLD_WIDTH / 2 + 20;
  const top = MOLD_CENTER_Y - MOLD_HEIGHT / 2 + 20;
  const w = MOLD_WIDTH - 40;
  const h = MOLD_HEIGHT - 40;

  // Liquid slightly wobbles during reconform
  const wobble = Math.sin(reconformProgress * Math.PI * 2) * 3;

  return (
    <div
      style={{
        position: 'absolute',
        left: left + wobble,
        top: top + Math.abs(wobble) * 0.5,
        width: w - Math.abs(wobble) * 2,
        height: h - Math.abs(wobble),
        background: `radial-gradient(ellipse at center, ${LIQUID_COLOR}33, ${LIQUID_COLOR}11)`,
        borderRadius: 6,
        border: `1px solid ${LIQUID_COLOR}44`,
      }}
    />
  );
};

// ── Red flash overlay ───────────────────────────────────────────
const BugFlash: React.FC<{ progress: number }> = ({ progress }) => {
  const opacity = interpolate(progress, [0, 1], [0.5, 0], { extrapolateRight: 'clamp' });
  return (
    <div
      style={{
        position: 'absolute',
        left: MOLD_CENTER_X - MOLD_WIDTH / 2 - 20,
        top: MOLD_CENTER_Y - MOLD_HEIGHT / 2 - 20,
        width: MOLD_WIDTH + 40,
        height: MOLD_HEIGHT + 40,
        background: `radial-gradient(ellipse at center, ${FLASH_COLOR}66, transparent 70%)`,
        opacity,
        pointerEvents: 'none',
      }}
    />
  );
};

// ── Composed mold with animated walls ───────────────────────────
export const MoldCrossSection: React.FC = () => {
  const frame = useCurrentFrame();

  // Determine which cycles have completed
  const activeCycleCount = Math.min(
    WALL_CYCLES.length,
    Math.floor(frame / CYCLE_FRAMES) + 1
  );

  // Hold phase glow (frames 216-270)
  const holdGlow =
    frame >= 216
      ? Math.sin(((frame - 216) / 54) * Math.PI * 2) * 0.3 + 0.3
      : 0;

  // Reconform wobble accumulator
  let reconformProgress = 0;
  for (let i = 0; i < activeCycleCount; i++) {
    const cycleStart = i * CYCLE_FRAMES;
    const reconformFrame = frame - (cycleStart + RECONFORM_START);
    if (reconformFrame > 0 && reconformFrame < 20) {
      reconformProgress = interpolate(reconformFrame, [0, 20], [0, 1], {
        extrapolateRight: 'clamp',
      });
    }
  }

  return (
    <>
      <MoldShell />
      <LiquidFill reconformProgress={reconformProgress} />

      {/* Pre-existing base walls — visible from frame 0 */}
      {BASE_WALLS.map((wall, i) => (
        <WallSegment
          key={`base-${i}`}
          x={wall.x}
          y={wall.y}
          width={wall.width}
          height={wall.height}
          label={wall.label}
          opacity={0.7}
          glowIntensity={holdGlow}
        />
      ))}

      {/* New walls sliding in per cycle */}
      {WALL_CYCLES.map((cycle, i) => {
        const cycleStart = i * CYCLE_FRAMES;
        const pos = NEW_WALL_POSITIONS[i];

        // Red flash (0–8 frames into cycle)
        const flashLocalFrame = frame - cycleStart;
        const showFlash = flashLocalFrame >= 0 && flashLocalFrame < FLASH_DURATION;
        const flashProgress = showFlash
          ? interpolate(flashLocalFrame, [0, FLASH_DURATION], [0, 1], {
              extrapolateRight: 'clamp',
              easing: Easing.out(Easing.exp),
            })
          : 1;

        // Wall slide-in (starts 8 frames into cycle, 20 frames long)
        const slideStart = cycleStart + FLASH_DURATION;
        const slideLocalFrame = frame - slideStart;
        const slideProgress =
          slideLocalFrame >= 0
            ? interpolate(
                Math.min(slideLocalFrame, WALL_SLIDE_DURATION),
                [0, WALL_SLIDE_DURATION],
                [0, 1],
                {
                  extrapolateRight: 'clamp',
                  easing: Easing.out(Easing.back(1.4)),
                }
              )
            : 0;

        if (frame < cycleStart) return null;

        const slideOffset = cycle.side === 'left' ? -150 : 150;
        const currentOffset = slideOffset * (1 - slideProgress);

        return (
          <React.Fragment key={`cycle-${i}`}>
            {showFlash && <BugFlash progress={flashProgress} />}
            {slideLocalFrame >= 0 && (
              <WallSegment
                x={pos.x + currentOffset}
                y={pos.y}
                width={pos.width}
                height={pos.height}
                label={cycle.label}
                opacity={slideProgress}
                glowIntensity={holdGlow}
              />
            )}
          </React.Fragment>
        );
      })}
    </>
  );
};
