import React from "react";
import { useCurrentFrame, interpolate, Easing, spring, useVideoConfig } from "remotion";
import { BEATS, COLORS, CHECKMARK_CONFIG, TEST_LINES } from "./constants";

/**
 * Renders Synopsys verification checkmark that morphs into a test suite.
 * LEFT side (setup): Single green checkmark from chip design verification.
 * Morph: Checkmark splits into multiple test checkmarks, moves to RIGHT side.
 * RIGHT side (final): Test suite with amber glow and green checkmarks.
 */

export const SynopsysCheckmark: React.FC = () => {
  const frame = useCurrentFrame();
  const { fps } = useVideoConfig();

  // Morph progress
  const morphProgress = interpolate(
    frame,
    [BEATS.MORPH_START, BEATS.MORPH_END],
    [0, 1],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.inOut(Easing.cubic),
    }
  );

  // Position interpolation (LEFT → RIGHT)
  const x = interpolate(
    morphProgress,
    [0, 1],
    [CHECKMARK_CONFIG.initialX, CHECKMARK_CONFIG.finalX]
  );
  const y = interpolate(
    morphProgress,
    [0, 1],
    [CHECKMARK_CONFIG.initialY, CHECKMARK_CONFIG.finalY]
  );

  // Single checkmark visibility (fades out during morph)
  const singleCheckOpacity = interpolate(
    morphProgress,
    [0, 0.5],
    [1, 0],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
    }
  );

  // Multiple test checkmarks visibility (fade in during morph)
  const multiCheckOpacity = interpolate(
    morphProgress,
    [0.5, 1],
    [0, 1],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
    }
  );

  // Test labels visibility (labels phase)
  const labelsOpacity = interpolate(
    frame,
    [BEATS.LABELS_START, BEATS.LABELS_START + 60],
    [0, 1],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.out(Easing.cubic),
    }
  );

  // Amber glow for test suite (labels phase)
  const glowOpacity = interpolate(
    frame,
    [BEATS.LABELS_START, BEATS.LABELS_END],
    [0, 1],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.out(Easing.quad),
    }
  );

  // Scale animation for initial checkmark (setup phase)
  const setupScale = frame < BEATS.MORPH_START
    ? spring({
        frame: frame - 30,
        fps,
        config: {
          damping: 12,
          stiffness: 200,
          mass: 0.5,
        },
      })
    : 1;

  return (
    <>
      <defs>
        <filter id="testGlow" x="-50%" y="-50%" width="200%" height="200%">
          <feGaussianBlur stdDeviation="8" result="blur" />
          <feMerge>
            <feMergeNode in="blur" />
            <feMergeNode in="SourceGraphic" />
          </feMerge>
        </filter>
      </defs>

      {/* Amber glow around test suite (final state) */}
      {glowOpacity > 0 && multiCheckOpacity > 0 && (
        <rect
          x={x - 10}
          y={y - 10}
          width={240}
          height={TEST_LINES.length * 32 + 20}
          rx={8}
          fill="none"
          stroke={COLORS.TEST_AMBER}
          strokeWidth={3}
          opacity={glowOpacity * 0.5}
          filter="url(#testGlow)"
        />
      )}

      {/* Single Synopsys checkmark (LEFT side, setup) */}
      {singleCheckOpacity > 0 && (
        <g
          transform={`translate(${x + 24}, ${y}) scale(${setupScale})`}
          opacity={singleCheckOpacity}
        >
          <circle
            cx={0}
            cy={0}
            r={24}
            fill="none"
            stroke={COLORS.CHECK_GREEN}
            strokeWidth={2.5}
          />
          <path
            d="M-10 0 L-3 7 L10 -6"
            fill="none"
            stroke={COLORS.CHECK_GREEN}
            strokeWidth={3.5}
            strokeLinecap="round"
            strokeLinejoin="round"
          />
        </g>
      )}

      {/* Multiple test checkmarks (RIGHT side, final) */}
      {multiCheckOpacity > 0 && (
        <g opacity={multiCheckOpacity}>
          {TEST_LINES.map((testName, i) => {
            // Stagger checkmark appearance
            const checkDelay = i * 10;
            const checkOpacity = interpolate(
              frame,
              [BEATS.LABELS_START + checkDelay, BEATS.LABELS_START + 30 + checkDelay],
              [0, 1],
              {
                extrapolateLeft: "clamp",
                extrapolateRight: "clamp",
              }
            );

            const checkY = y + i * 32 + 16;

            return (
              <g key={`test-${i}`}>
                {/* Checkmark icon */}
                <g opacity={checkOpacity}>
                  <circle
                    cx={x + 12}
                    cy={checkY}
                    r={10}
                    fill="none"
                    stroke={COLORS.TEST_CHECK_GREEN}
                    strokeWidth={2}
                  />
                  <path
                    d={`M${x + 6} ${checkY} L${x + 10} ${checkY + 4} L${x + 18} ${checkY - 4}`}
                    fill="none"
                    stroke={COLORS.TEST_CHECK_GREEN}
                    strokeWidth={2.5}
                    strokeLinecap="round"
                    strokeLinejoin="round"
                  />
                </g>

                {/* Test name label */}
                {labelsOpacity > 0 && (
                  <text
                    x={x + 32}
                    y={checkY + 5}
                    fontSize={14}
                    fontFamily="'JetBrains Mono', 'Fira Code', monospace"
                    fontWeight={400}
                    fill={COLORS.CODE_GRAY}
                    opacity={labelsOpacity * checkOpacity}
                  >
                    {testName}
                  </text>
                )}
              </g>
            );
          })}
        </g>
      )}
    </>
  );
};
