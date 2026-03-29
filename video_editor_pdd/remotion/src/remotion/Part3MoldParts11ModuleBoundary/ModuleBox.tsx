import React from 'react';

interface ModuleBoxProps {
  label: string;
  x: number;
  y: number;
  width: number;
  height: number;
  fillColor: string;
  borderColor: string;
  borderWidth: number;
  borderRadius: number;
  labelColor: string;
  labelSize: number;
  labelWeight: number;
  opacity: number;
  glowColor?: string;
  glowBlur?: number;
  glowOpacity?: number;
}

export const ModuleBox: React.FC<ModuleBoxProps> = ({
  label,
  x,
  y,
  width,
  height,
  fillColor,
  borderColor,
  borderWidth,
  borderRadius,
  labelColor,
  labelSize,
  labelWeight,
  opacity,
  glowColor,
  glowBlur,
  glowOpacity,
}) => {
  const left = x - width / 2;
  const top = y - height / 2;

  return (
    <div
      style={{
        position: 'absolute',
        left,
        top,
        width,
        height,
        opacity,
      }}
    >
      <div
        style={{
          width: '100%',
          height: '100%',
          backgroundColor: fillColor,
          border: `${borderWidth}px solid ${borderColor}`,
          borderRadius,
          display: 'flex',
          alignItems: 'center',
          justifyContent: 'center',
          boxShadow:
            glowColor && glowBlur && glowOpacity
              ? `0 0 ${glowBlur}px ${glowColor}${Math.round(glowOpacity * 255)
                  .toString(16)
                  .padStart(2, '0')}`
              : 'none',
        }}
      >
        <span
          style={{
            fontFamily: 'JetBrains Mono, monospace',
            fontSize: labelSize,
            fontWeight: labelWeight,
            color: labelColor,
            userSelect: 'none',
          }}
        >
          {label}
        </span>
      </div>
    </div>
  );
};
