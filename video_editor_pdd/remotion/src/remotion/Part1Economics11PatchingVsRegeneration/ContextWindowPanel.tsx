import React from 'react';
import { useCurrentFrame, interpolate, Easing } from 'remotion';
import {
  PANEL_DRAW_START,
  PANEL_DRAW_DURATION,
  FONT_FAMILY,
  HEADER_FONT_SIZE,
} from './constants';

interface ContextWindowPanelProps {
  x: number;
  y: number;
  width: number;
  height: number;
  header: string;
  headerColor: string;
  borderColor: string;
  borderStyle: 'solid' | 'dashed';
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
}) => {
  const frame = useCurrentFrame();

  // Panel outline draws in over PANEL_DRAW_DURATION frames
  const drawProgress = interpolate(
    frame,
    [PANEL_DRAW_START, PANEL_DRAW_START + PANEL_DRAW_DURATION],
    [0, 1],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.out(Easing.quad),
    }
  );

  // Header types in character by character
  const headerChars = Math.round(
    interpolate(
      frame,
      [PANEL_DRAW_START, PANEL_DRAW_START + PANEL_DRAW_DURATION],
      [0, header.length],
      {
        extrapolateLeft: 'clamp',
        extrapolateRight: 'clamp',
        easing: Easing.out(Easing.quad),
      }
    )
  );

  const displayHeader = header.substring(0, headerChars);

  // Perimeter for clip-path stroke animation
  const perimeter = 2 * (width + height);
  const dashLength = perimeter * drawProgress;

  return (
    <>
      {/* Panel header */}
      <div
        style={{
          position: 'absolute',
          left: x,
          top: y - 36,
          fontFamily: FONT_FAMILY,
          fontSize: HEADER_FONT_SIZE,
          fontWeight: 700,
          color: headerColor,
          opacity: 0.95,
          whiteSpace: 'nowrap',
        }}
      >
        {displayHeader}
      </div>

      {/* Panel outline using SVG for animated dashed/solid border */}
      <svg
        style={{
          position: 'absolute',
          left: x,
          top: y,
          width,
          height,
          overflow: 'visible',
        }}
      >
        <rect
          x={1}
          y={1}
          width={width - 2}
          height={height - 2}
          fill="none"
          stroke={borderColor}
          strokeWidth={2}
          strokeDasharray={
            borderStyle === 'dashed'
              ? `8 4`
              : `${perimeter}`
          }
          strokeDashoffset={
            borderStyle === 'dashed'
              ? perimeter - dashLength
              : perimeter - dashLength
          }
          rx={4}
          ry={4}
          opacity={drawProgress}
        />
      </svg>
    </>
  );
};

export default ContextWindowPanel;
