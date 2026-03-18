import React from 'react';
import {
  BLOCK_W,
  BLOCK_H,
  UNCONVERTED,
  CONVERTING,
  CONVERTED,
  BLUE_ACCENT,
  LABEL_COLOR,
} from './constants';

export type ModuleState = 'unconverted' | 'converting' | 'converted';

interface ModuleBlockProps {
  x: number;
  y: number;
  name: string;
  state: ModuleState;
  /** 0-1 flash intensity, used during converting state */
  flashIntensity: number;
  /** extra ambient glow multiplier for pulse effect */
  pulseOffset: number;
}

const ModuleBlock: React.FC<ModuleBlockProps> = ({
  x,
  y,
  name,
  state,
  flashIntensity,
  pulseOffset,
}) => {
  let fill: string;
  let borderColor: string;
  let borderOpacity: number;
  let borderWidth: number;
  let boxShadow = 'none';
  let showLabel = false;

  if (state === 'unconverted') {
    fill = UNCONVERTED.fill;
    borderColor = UNCONVERTED.border;
    borderOpacity = UNCONVERTED.borderOpacity;
    borderWidth = UNCONVERTED.borderWidth;
  } else if (state === 'converting') {
    fill = UNCONVERTED.fill;
    borderColor = CONVERTING.border;
    const intensity = flashIntensity;
    borderOpacity = UNCONVERTED.borderOpacity + (CONVERTING.borderOpacity - UNCONVERTED.borderOpacity) * intensity;
    borderWidth = UNCONVERTED.borderWidth + (CONVERTING.borderWidth - UNCONVERTED.borderWidth) * intensity;
    const glowOpacity = CONVERTING.glowOpacity * intensity;
    boxShadow = `0 0 ${CONVERTING.glowBlur}px rgba(74, 144, 217, ${glowOpacity})`;
    showLabel = intensity > 0.3;
  } else {
    // converted
    fill = CONVERTED.fill;
    borderColor = CONVERTED.border;
    borderOpacity = CONVERTED.borderOpacity;
    borderWidth = CONVERTED.borderWidth;
    const glowOp = CONVERTED.glowOpacity + pulseOffset;
    boxShadow = `0 0 ${CONVERTED.glowBlur}px rgba(74, 144, 217, ${glowOp})`;
  }

  return (
    <div
      style={{
        position: 'absolute',
        left: x - BLOCK_W / 2,
        top: y - BLOCK_H / 2,
        width: BLOCK_W,
        height: BLOCK_H,
        backgroundColor: fill,
        border: `${borderWidth}px solid`,
        borderColor: `rgba(${hexToRgb(borderColor)}, ${borderOpacity})`,
        borderRadius: 4,
        boxShadow,
        display: 'flex',
        alignItems: 'center',
        justifyContent: 'center',
        overflow: 'hidden',
      }}
    >
      {showLabel && (
        <span
          style={{
            fontFamily: 'JetBrains Mono, monospace',
            fontSize: 8,
            color: LABEL_COLOR,
            opacity: 0.3 * flashIntensity,
            whiteSpace: 'nowrap',
          }}
        >
          {name}
        </span>
      )}
    </div>
  );
};

function hexToRgb(hex: string): string {
  const r = parseInt(hex.slice(1, 3), 16);
  const g = parseInt(hex.slice(3, 5), 16);
  const b = parseInt(hex.slice(5, 7), 16);
  return `${r}, ${g}, ${b}`;
}

export default ModuleBlock;
