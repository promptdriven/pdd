import React from 'react';
import { useCurrentFrame, interpolate, Easing } from 'remotion';
import { PANEL_DRAW_START, PANEL_DRAW_END } from './constants';

interface ContextWindowPanelProps {
  x: number;
  y: number;
  width: number;
  height: number;
  header: string;
  headerColor: string;
  borderColor: string;
  borderStyle: 'solid' | 'dashed';
  children?: React.ReactNode;
}

const ContextWindowPanel: React.FC<ContextWindowPanelProps> = ({
  x,
  y,
  width,
  height,
  header,
  headerColor,
  borderColor,
  borderStyle,
  children,
}) => {
  const frame = useCurrentFrame();

  // Panel outline draws from 0-60 frames
  const drawProgress = interpolate(
    frame,
    [PANEL_DRAW_START, PANEL_DRAW_END],
    [0, 1],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.out(Easing.quad),
    }
  );

  // Header types in over same period
  const headerChars = Math.round(header.length * drawProgress);
  const displayedHeader = header.slice(0, headerChars);

  // Border opacity matches draw progress
  const borderOpacity = drawProgress;

  return (
    <div
      style={{
        position: 'absolute',
        left: x,
        top: y - 40, // Room for header above panel
        width,
      }}
    >
      {/* Header */}
      <div
        style={{
          fontFamily: 'Inter, sans-serif',
          fontSize: 20,
          fontWeight: 700,
          color: headerColor,
          marginBottom: 12,
          opacity: drawProgress,
          height: 28,
        }}
      >
        {displayedHeader}
      </div>

      {/* Panel outline + content area */}
      <div
        style={{
          position: 'relative',
          width,
          height,
          border: `2px ${borderStyle} ${borderColor}`,
          borderRadius: 8,
          opacity: borderOpacity,
          overflow: 'hidden',
        }}
      >
        {children}
      </div>
    </div>
  );
};

export default ContextWindowPanel;
