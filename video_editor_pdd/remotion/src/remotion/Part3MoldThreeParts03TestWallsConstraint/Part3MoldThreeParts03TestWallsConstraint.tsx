import React, { useMemo } from 'react';
import {
  AbsoluteFill,
  Sequence,
  useCurrentFrame,
  interpolate,
  Easing,
} from 'remotion';
import {
  BG_COLOR,
  TOTAL_FRAMES,
  MOLD_CENTER_X,
  MOLD_CENTER_Y,
  MOLD_LEFT,
  MOLD_TOP,
} from './constants';
import MoldStructure from './MoldStructure';
import LiquidFlow from './LiquidFlow';
import WallCollision, { getWallFlashes } from './WallCollision';
import TerminalOverlay from './TerminalOverlay';

export const defaultPart3MoldThreeParts03TestWallsConstraintProps = {};

export const Part3MoldThreeParts03TestWallsConstraint: React.FC = () => {
  const frame = useCurrentFrame();

  // ── Camera zoom logic ──
  // Frame 90-120: zoom in to "null → None" wall on the left
  // Frame 150-180: zoom back out
  const zoomIn = interpolate(frame, [90, 120], [0, 1], {
    extrapolateLeft: 'clamp',
    extrapolateRight: 'clamp',
    easing: Easing.inOut(Easing.cubic),
  });

  const zoomOut = interpolate(frame, [150, 180], [0, 1], {
    extrapolateLeft: 'clamp',
    extrapolateRight: 'clamp',
    easing: Easing.inOut(Easing.cubic),
  });

  // Combined zoom: 1.0 → 1.2 → 1.0
  const zoomScale = interpolate(
    zoomIn - zoomOut,
    [0, 1],
    [1, 1.2],
    { extrapolateLeft: 'clamp', extrapolateRight: 'clamp' }
  );

  // Camera target: center → left-wall focus → center
  const focusX = MOLD_LEFT + 100; // Focus near "null → None" wall
  const focusY = MOLD_TOP + 200;
  const camTargetX = interpolate(
    zoomIn - zoomOut,
    [0, 1],
    [MOLD_CENTER_X, focusX],
    { extrapolateLeft: 'clamp', extrapolateRight: 'clamp' }
  );
  const camTargetY = interpolate(
    zoomIn - zoomOut,
    [0, 1],
    [MOLD_CENTER_Y, focusY],
    { extrapolateLeft: 'clamp', extrapolateRight: 'clamp' }
  );

  // Transform origin for zoom
  const translateX = -(camTargetX - 960) * (zoomScale - 1);
  const translateY = -(camTargetY - 540) * (zoomScale - 1);

  // ── Screen shake on "null → None" wall impact (frame 110) ──
  const shakeElapsed = frame - 110;
  let shakeX = 0;
  let shakeY = 0;
  if (shakeElapsed >= 0 && shakeElapsed < 8) {
    const shakeDecay = interpolate(shakeElapsed, [0, 8], [1, 0], {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.out(Easing.quad),
    });
    shakeX = Math.sin(shakeElapsed * 4.5) * 2 * shakeDecay;
    shakeY = Math.cos(shakeElapsed * 6.2) * 1.5 * shakeDecay;
  }

  // ── Wall flash intensities ──
  const wallFlashes = useMemo(() => getWallFlashes(frame), [frame]);

  // Focus on "null → None" wall: flash at the special collision
  // The focus collision for "null → None" happens around frame 100-115
  const nullWallFocusCollisionFlash = interpolate(
    frame,
    [100, 106],
    [1, 0],
    { extrapolateLeft: 'clamp', extrapolateRight: 'clamp', easing: Easing.out(Easing.exp) }
  );
  const focusFlashes = { ...wallFlashes };
  if (frame >= 100 && frame <= 115) {
    focusFlashes['left-top'] = Math.max(focusFlashes['left-top'] || 0, nullWallFocusCollisionFlash);
  }

  // Focus progress for label brightening
  const focusProgress = interpolate(frame, [90, 120], [0, 1], {
    extrapolateLeft: 'clamp',
    extrapolateRight: 'clamp',
    easing: Easing.out(Easing.cubic),
  });
  const focusRevert = interpolate(frame, [150, 180], [0, 1], {
    extrapolateLeft: 'clamp',
    extrapolateRight: 'clamp',
    easing: Easing.out(Easing.cubic),
  });
  const netFocusProgress = focusProgress * (1 - focusRevert);

  return (
    <AbsoluteFill style={{ backgroundColor: BG_COLOR }}>
      {/* Camera transform layer */}
      <div
        style={{
          position: 'absolute',
          width: 1920,
          height: 1080,
          transform: `translate(${translateX + shakeX}px, ${translateY + shakeY}px) scale(${zoomScale})`,
          transformOrigin: `${camTargetX}px ${camTargetY}px`,
          willChange: 'transform',
        }}
      >
        {/* Mold structure with walls */}
        <MoldStructure
          focusWallId={frame >= 90 && frame < 180 ? 'left-top' : undefined}
          focusProgress={netFocusProgress}
          wallFlashes={focusFlashes}
        />

        {/* Liquid particle flow */}
        <LiquidFlow />

        {/* Wall collision ripple effects */}
        <WallCollision />

        {/* Additional focus collision ripple for "null → None" */}
        {frame >= 100 && frame < 120 && (
          <svg
            width={1920}
            height={1080}
            viewBox="0 0 1920 1080"
            style={{ position: 'absolute', top: 0, left: 0, pointerEvents: 'none' }}
          >
            {(() => {
              const elapsed = frame - 100;
              const progress = interpolate(elapsed, [0, 18], [0, 1], {
                extrapolateLeft: 'clamp',
                extrapolateRight: 'clamp',
                easing: Easing.out(Easing.cubic),
              });
              const opacity = interpolate(elapsed, [0, 18], [0.5, 0], {
                extrapolateLeft: 'clamp',
                extrapolateRight: 'clamp',
              });
              const cx = MOLD_LEFT + 5;
              const cy = MOLD_TOP + 150;
              return (
                <>
                  {[0, 0.15, 0.3].map((delay, i) => {
                    const dp = Math.max(0, progress - delay);
                    const r = 12 + dp * 80;
                    const op = opacity * (1 - delay) * (dp > 0 ? 1 : 0);
                    if (op < 0.01) return null;
                    return (
                      <ellipse
                        key={i}
                        cx={cx + 10}
                        cy={cy}
                        rx={r * 0.35}
                        ry={r}
                        fill="none"
                        stroke="#D9944A"
                        strokeWidth={2}
                        opacity={op}
                      />
                    );
                  })}
                </>
              );
            })()}
          </svg>
        )}
      </div>

      {/* Terminal overlay (outside camera transform so it stays fixed) */}
      <Sequence from={150} durationInFrames={TOTAL_FRAMES - 150}>
        <TerminalOverlay />
      </Sequence>

      {/* Subtle vignette overlay */}
      <div
        style={{
          position: 'absolute',
          top: 0,
          left: 0,
          width: 1920,
          height: 1080,
          background:
            'radial-gradient(ellipse at center, transparent 50%, rgba(0,0,0,0.4) 100%)',
          pointerEvents: 'none',
        }}
      />
    </AbsoluteFill>
  );
};

export default Part3MoldThreeParts03TestWallsConstraint;
