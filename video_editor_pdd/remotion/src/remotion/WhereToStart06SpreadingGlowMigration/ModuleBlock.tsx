import React from 'react';
import { useCurrentFrame, Easing, interpolate } from 'remotion';
import {
  MODULE_W,
  MODULE_H,
  UNCONVERTED,
  CONVERTING,
  CONVERTED,
  FLASH_IN_FRAMES,
  FLASH_HOLD_FRAMES,
  FLASH_SETTLE_FRAMES,
  PULSE_START_FRAME,
  PULSE_PERIOD,
  PULSE_AMPLITUDE,
} from './constants';

interface ModuleBlockProps {
  id: number;
  name: string;
  x: number;
  y: number;
  conversionFrame: number | null; // null = never converts
  staggerOffset: number;          // additional delay within a wave
  isPreConverted: boolean;        // already converted at frame 0
}

export const ModuleBlock: React.FC<ModuleBlockProps> = ({
  name,
  x,
  y,
  conversionFrame,
  staggerOffset,
  isPreConverted,
}) => {
  const frame = useCurrentFrame();

  // Determine module state
  const effectiveConversionStart =
    conversionFrame !== null ? conversionFrame + staggerOffset : Infinity;
  const isConverting = !isPreConverted && frame >= effectiveConversionStart;
  const flashEnd =
    effectiveConversionStart + FLASH_IN_FRAMES + FLASH_HOLD_FRAMES + FLASH_SETTLE_FRAMES;
  const isFullyConverted = isPreConverted || frame >= flashEnd;
  const isInFlash = isConverting && !isFullyConverted;

  // Compute visual properties
  let fill = UNCONVERTED.fill;
  let borderColor = UNCONVERTED.border;
  let borderOpacity = UNCONVERTED.borderOpacity;
  let borderWidth = UNCONVERTED.borderWidth;
  let glowOpacity = 0;
  let glowBlur = 0;
  let glowColor = CONVERTING.glowColor;
  let showLabel = false;

  if (isPreConverted || isFullyConverted) {
    fill = CONVERTED.fill;
    borderColor = CONVERTED.border;
    borderOpacity = CONVERTED.borderOpacity;
    borderWidth = CONVERTED.borderWidth;
    glowOpacity = CONVERTED.glowOpacity;
    glowBlur = CONVERTED.glowBlur;
    glowColor = CONVERTED.glowColor;

    // Pulse effect after frame 170
    if (frame >= PULSE_START_FRAME) {
      const pulsePhase = ((frame - PULSE_START_FRAME) / PULSE_PERIOD) * Math.PI * 2;
      const pulseDelta = Math.sin(pulsePhase) * PULSE_AMPLITUDE;
      glowOpacity = CONVERTED.glowOpacity + pulseDelta;
    }
  } else if (isInFlash) {
    const localFrame = frame - effectiveConversionStart;
    fill = UNCONVERTED.fill; // stays same during flash
    borderColor = CONVERTING.border;
    borderWidth = CONVERTING.borderWidth;
    showLabel = true;

    if (localFrame < FLASH_IN_FRAMES) {
      // Flash in: easeOut cubic, opacity 0 → 0.6
      const t = interpolate(localFrame, [0, FLASH_IN_FRAMES - 1], [0, 1], {
        easing: Easing.out(Easing.cubic),
        extrapolateLeft: 'clamp',
        extrapolateRight: 'clamp',
      });
      borderOpacity = t * CONVERTING.borderOpacity;
      glowOpacity = t * CONVERTING.glowOpacity;
      glowBlur = CONVERTING.glowBlur;
    } else if (localFrame < FLASH_IN_FRAMES + FLASH_HOLD_FRAMES) {
      // Hold at peak
      borderOpacity = CONVERTING.borderOpacity;
      glowOpacity = CONVERTING.glowOpacity;
      glowBlur = CONVERTING.glowBlur;
    } else {
      // Settle: easeOut quad, opacity 0.6 → 0.3
      const settleLocal = localFrame - FLASH_IN_FRAMES - FLASH_HOLD_FRAMES;
      const t = interpolate(settleLocal, [0, FLASH_SETTLE_FRAMES - 1], [0, 1], {
        easing: Easing.out(Easing.quad),
        extrapolateLeft: 'clamp',
        extrapolateRight: 'clamp',
      });
      borderOpacity = CONVERTING.borderOpacity - t * (CONVERTING.borderOpacity - CONVERTED.borderOpacity);
      glowOpacity = CONVERTING.glowOpacity - t * (CONVERTING.glowOpacity - CONVERTED.glowOpacity);
      glowBlur = CONVERTING.glowBlur - t * (CONVERTING.glowBlur - CONVERTED.glowBlur);
    }
  }

  return (
    <div
      style={{
        position: 'absolute',
        left: x - MODULE_W / 2,
        top: y - MODULE_H / 2,
        width: MODULE_W,
        height: MODULE_H,
        backgroundColor: fill,
        border: `${borderWidth}px solid ${borderColor}`,
        borderRadius: 4,
        opacity: 1,
        boxShadow:
          glowOpacity > 0
            ? `0 0 ${glowBlur}px rgba(74, 144, 217, ${glowOpacity})`
            : 'none',
        transition: 'none',
      }}
    >
      {/* Module label — visible during flash or when converted */}
      {(showLabel || isFullyConverted || isPreConverted) && (
        <div
          style={{
            position: 'absolute',
            top: '50%',
            left: '50%',
            transform: 'translate(-50%, -50%)',
            fontFamily: 'JetBrains Mono, monospace',
            fontSize: 6,
            color: '#E2E8F0',
            opacity: showLabel ? 0.5 : 0.2,
            whiteSpace: 'nowrap',
            overflow: 'hidden',
            textOverflow: 'ellipsis',
            maxWidth: MODULE_W - 8,
            textAlign: 'center',
            lineHeight: 1,
          }}
        >
          {name}
        </div>
      )}
    </div>
  );
};
