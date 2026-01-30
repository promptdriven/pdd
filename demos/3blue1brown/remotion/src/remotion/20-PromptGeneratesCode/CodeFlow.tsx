import React from "react";
import { useCurrentFrame, interpolate, Easing } from "remotion";
import {
  COLORS,
  PROMPT_DOC,
  CODE_CONTAINER,
  BEATS,
} from "./constants";

/**
 * Particle definition for code flow animation.
 */
interface Particle {
  x: number;
  y: number;
  width: number;
  height: number;
  opacity: number;
}

/**
 * Returns a seeded pseudo-random number (0-1) from an integer seed.
 */
function seededRandom(seed: number): number {
  const x = Math.sin(seed * 127.1 + 311.7) * 43758.5453;
  return x - Math.floor(x);
}

/**
 * Renders the code flow: a stream of gray particles flowing from the prompt
 * toward the container area, and the code fill that settles inside the walls.
 *
 * Frame 60-150:  Free-form particle stream from prompt.
 * Frame 150-270: Particles begin converging on the container.
 * Frame 270-360: Code fill grows inside the container.
 * Frame 360+:    Static filled code area (no glow).
 */
export const CodeFlow: React.FC = () => {
  const frame = useCurrentFrame();

  // --- Particle stream (frame 60 - 360) ---
  const particles: Particle[] = [];
  const streamActive = frame >= BEATS.CODE_FLOW_START && frame < BEATS.FINAL_START;

  if (streamActive) {
    const numParticles = 30;
    const sourceX = PROMPT_DOC.x + PROMPT_DOC.width;
    const sourceY = PROMPT_DOC.y + PROMPT_DOC.height / 2;
    const targetX = CODE_CONTAINER.x + CODE_CONTAINER.width / 2;
    const targetY = CODE_CONTAINER.y + CODE_CONTAINER.height / 2;

    for (let i = 0; i < numParticles; i++) {
      const seed = i;
      const r1 = seededRandom(seed);
      const r2 = seededRandom(seed + 100);
      const r3 = seededRandom(seed + 200);

      // Each particle has its own cycle period and phase offset
      const period = 40 + r1 * 50;
      const phase = ((frame - BEATS.CODE_FLOW_START + r2 * period) % period) / period;

      // Particle travels along a curved path from source to target
      const t = phase;

      // How much the flow is constrained (increases as walls appear)
      const constrainFactor = interpolate(
        frame,
        [BEATS.WALLS_START, BEATS.WALLS_END],
        [0, 1],
        {
          extrapolateLeft: "clamp",
          extrapolateRight: "clamp",
        },
      );

      // Free-form spread when unconstrained
      const spreadX = (r2 - 0.5) * 200 * (1 - constrainFactor);
      const spreadY = (r3 - 0.5) * 300 * (1 - constrainFactor);

      // Constrained target jitter (inside container)
      const containerJitterX =
        (r2 - 0.5) * CODE_CONTAINER.width * 0.8 * constrainFactor;
      const containerJitterY =
        (r3 - 0.5) * CODE_CONTAINER.height * 0.8 * constrainFactor;

      // Bezier-like curve through midpoint
      const midX = (sourceX + targetX) / 2 + spreadX;
      const midY = (sourceY + targetY) / 2 + spreadY - 60;

      // Quadratic bezier interpolation
      const oneMinusT = 1 - t;
      const finalTargetX = targetX + containerJitterX;
      const finalTargetY = targetY + containerJitterY;

      const px =
        oneMinusT * oneMinusT * sourceX +
        2 * oneMinusT * t * midX +
        t * t * finalTargetX;
      const py =
        oneMinusT * oneMinusT * sourceY +
        2 * oneMinusT * t * midY +
        t * t * finalTargetY;

      // Fade in at start, fade out near end of travel
      const pOpacity = interpolate(t, [0, 0.1, 0.8, 1], [0, 0.8, 0.5, 0], {
        extrapolateLeft: "clamp",
        extrapolateRight: "clamp",
      });

      // Overall stream intensity
      const streamIntensity = interpolate(
        frame,
        [
          BEATS.CODE_FLOW_START,
          BEATS.CODE_FLOW_START + 30,
          BEATS.CODE_FILL_END,
          BEATS.FINAL_START,
        ],
        [0, 1, 0.6, 0],
        {
          extrapolateLeft: "clamp",
          extrapolateRight: "clamp",
        },
      );

      const pWidth = 4 + r1 * 16;
      const pHeight = 2 + r3 * 4;

      particles.push({
        x: px,
        y: py,
        width: pWidth,
        height: pHeight,
        opacity: pOpacity * streamIntensity,
      });
    }
  }

  // --- Code fill (frame 270-450) ---
  const fillProgress = interpolate(
    frame,
    [BEATS.CODE_FILL_START, BEATS.CODE_FILL_END],
    [0, 1],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.out(Easing.cubic),
    },
  );

  const fillOpacity = interpolate(
    frame,
    [BEATS.CODE_FILL_START, BEATS.CODE_FILL_START + 30],
    [0, 0.55],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
    },
  );

  // Generate static "code" lines inside the fill area
  const codeLines: { y: number; segments: { x: number; width: number }[] }[] =
    [];
  if (fillProgress > 0) {
    const lineCount = 16;
    const lineSpacing = CODE_CONTAINER.height / (lineCount + 1);
    const visibleLines = Math.floor(fillProgress * lineCount);

    for (let i = 0; i < visibleLines; i++) {
      const lineY = CODE_CONTAINER.y + lineSpacing * (i + 1);
      const segments: { x: number; width: number }[] = [];
      const segCount = 2 + Math.floor(seededRandom(i + 500) * 4);
      let segX = CODE_CONTAINER.x + 20;

      for (let s = 0; s < segCount; s++) {
        const segW = 30 + seededRandom(i * 10 + s) * 100;
        if (segX + segW > CODE_CONTAINER.x + CODE_CONTAINER.width - 20) break;
        segments.push({ x: segX, width: segW });
        segX += segW + 10 + seededRandom(i * 10 + s + 50) * 20;
      }

      codeLines.push({ y: lineY, segments });
    }
  }

  return (
    <svg
      width="1920"
      height="1080"
      viewBox="0 0 1920 1080"
      style={{ position: "absolute", top: 0, left: 0, pointerEvents: "none" }}
    >
      {/* Particle stream */}
      {particles.map((p, i) => (
        <rect
          key={`particle-${i}`}
          x={p.x - p.width / 2}
          y={p.y - p.height / 2}
          width={p.width}
          height={p.height}
          rx={1}
          fill={COLORS.CODE_GRAY}
          opacity={p.opacity}
        />
      ))}

      {/* Code fill: rendered as horizontal line segments (no glow) */}
      {codeLines.map((line, li) => (
        <g key={`line-${li}`}>
          {line.segments.map((seg, si) => (
            <rect
              key={`seg-${li}-${si}`}
              x={seg.x}
              y={line.y}
              width={seg.width}
              height={3}
              rx={1.5}
              fill={COLORS.CODE_GRAY}
              opacity={fillOpacity}
            />
          ))}
        </g>
      ))}
    </svg>
  );
};
