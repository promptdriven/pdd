import React from 'react';
import { DIMENSIONS, TYPOGRAPHY } from './constants';
import { MockupUI } from './MockupUI';

interface PanelProps {
  side: 'left' | 'right';
  label: string;
  labelColor: string;
  backgroundColor: string;
  labelBgColor: string;
  glowIntensity?: number;
}

export const Panel: React.FC<PanelProps> = ({
  side,
  label,
  labelColor,
  backgroundColor,
  labelBgColor,
  glowIntensity = 0,
}) => {
  const panelX = side === 'left' ? DIMENSIONS.panelMargin : DIMENSIONS.splitPosition + DIMENSIONS.panelMargin;
  const labelX = side === 'left' ? 480 : 1440;

  return (
    <div
      style={{
        position: 'absolute',
        top: 0,
        left: side === 'left' ? 0 : DIMENSIONS.splitPosition,
        width: DIMENSIONS.splitPosition,
        height: DIMENSIONS.canvasHeight,
        backgroundColor,
        boxShadow: glowIntensity > 0
          ? `inset 0 0 ${60 * glowIntensity}px rgba(59, 130, 246, ${glowIntensity})`
          : 'none',
      }}
    >
      {/* Label Badge */}
      <div
        style={{
          position: 'absolute',
          left: labelX - DIMENSIONS.labelWidth / 2,
          top: DIMENSIONS.labelY,
          width: DIMENSIONS.labelWidth,
          height: DIMENSIONS.labelHeight,
          backgroundColor: labelBgColor,
          borderRadius: 8,
          display: 'flex',
          alignItems: 'center',
          justifyContent: 'center',
          opacity: 0.9,
        }}
      >
        <span
          style={{
            fontFamily: TYPOGRAPHY.labelFont,
            fontSize: TYPOGRAPHY.labelSize,
            fontWeight: TYPOGRAPHY.labelWeight,
            color: labelColor,
          }}
        >
          {label}
        </span>
      </div>

      {/* Content Area with Mockup */}
      <div
        style={{
          position: 'absolute',
          left: DIMENSIONS.panelMargin,
          top: DIMENSIONS.labelY + DIMENSIONS.labelHeight + 40,
          width: DIMENSIONS.panelWidth,
          height: DIMENSIONS.panelHeight - 100,
        }}
      >
        <MockupUI side={side} />
      </div>
    </div>
  );
};
