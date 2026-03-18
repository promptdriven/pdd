import React from 'react';
import { useCurrentFrame, interpolate, Easing } from 'remotion';
import { CHECKMARK_COLOR, COL_1_X, COL_2_X, COL_3_X } from './constants';

interface EquivalenceOverlayProps {
  startFrame: number;
}

/**
 * Green checkmarks over each netlist + "Functionally equivalent" label + dashed connecting line.
 */
export const EquivalenceOverlay: React.FC<EquivalenceOverlayProps> = ({ startFrame }) => {
  const frame = useCurrentFrame();
  const localFrame = frame - startFrame;

  if (localFrame < 0) return null;

  const columns = [COL_1_X, COL_2_X, COL_3_X];
  const checkmarkY = 410;

  // Dashed line draw
  const lineProgress = interpolate(localFrame, [30, 50], [0, 1], {
    extrapolateLeft: 'clamp',
    extrapolateRight: 'clamp',
    easing: Easing.out(Easing.quad),
  });

  // Label fade in
  const labelOpacity = interpolate(localFrame, [20, 35], [0, 0.6], {
    extrapolateLeft: 'clamp',
    extrapolateRight: 'clamp',
    easing: Easing.out(Easing.quad),
  });

  return (
    <>
      {/* Checkmarks */}
      {columns.map((cx, i) => {
        const delay = i * 8;
        // easeOut(back(1.5)) — simulate with overshoot
        const scaleRaw = interpolate(localFrame, [delay, delay + 12], [0, 1], {
          extrapolateLeft: 'clamp',
          extrapolateRight: 'clamp',
          easing: Easing.out(Easing.back(1.5)),
        });
        const checkOpacity = interpolate(localFrame, [delay, delay + 6], [0, 1], {
          extrapolateLeft: 'clamp',
          extrapolateRight: 'clamp',
        });

        return (
          <div
            key={i}
            style={{
              position: 'absolute',
              left: cx - 15,
              top: checkmarkY - 15,
              width: 30,
              height: 30,
              transform: `scale(${scaleRaw})`,
              opacity: checkOpacity,
            }}
          >
            <svg width={30} height={30}>
              <circle cx={15} cy={15} r={14} fill="none" stroke={CHECKMARK_COLOR} strokeWidth={2} />
              <polyline
                points="8,15 13,21 22,10"
                fill="none"
                stroke={CHECKMARK_COLOR}
                strokeWidth={2.5}
                strokeLinecap="round"
                strokeLinejoin="round"
              />
            </svg>
          </div>
        );
      })}

      {/* Dashed connecting line between checkmarks */}
      <svg
        style={{
          position: 'absolute',
          top: 0,
          left: 0,
          width: 1920,
          height: 1080,
          pointerEvents: 'none',
        }}
      >
        <line
          x1={COL_1_X}
          y1={checkmarkY}
          x2={COL_1_X + (COL_3_X - COL_1_X) * lineProgress}
          y2={checkmarkY}
          stroke={CHECKMARK_COLOR}
          strokeWidth={1}
          strokeDasharray="6,4"
          opacity={0.2}
        />
      </svg>

      {/* "Functionally equivalent" label */}
      <div
        style={{
          position: 'absolute',
          left: 0,
          top: checkmarkY + 20,
          width: 1920,
          textAlign: 'center',
          fontFamily: "'Inter', sans-serif",
          fontSize: 12,
          color: CHECKMARK_COLOR,
          opacity: labelOpacity,
          letterSpacing: 0.5,
        }}
      >
        Functionally equivalent
      </div>
    </>
  );
};
