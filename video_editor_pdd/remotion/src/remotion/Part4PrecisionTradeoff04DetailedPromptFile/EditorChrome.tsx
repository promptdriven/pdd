import React from 'react';
import { interpolate, useCurrentFrame, Easing } from 'remotion';
import {
  EDITOR_WIDTH,
  EDITOR_HEIGHT,
  EDITOR_X,
  EDITOR_Y,
  EDITOR_BORDER_RADIUS,
  EDITOR_FRAME_COLOR,
  TITLE_BAR_COLOR,
  TITLE_BAR_HEIGHT,
  FILENAME_COLOR,
  ACCENT_AMBER,
  TRAFFIC_RED,
  TRAFFIC_YELLOW,
  TRAFFIC_GREEN,
  WINDOW_FADE_IN_END,
  BADGE_SCALE_START,
  BADGE_SCALE_DURATION,
  TOTAL_LINES,
} from './constants';

interface EditorChromeProps {
  children: React.ReactNode;
}

export const EditorChrome: React.FC<EditorChromeProps> = ({ children }) => {
  const frame = useCurrentFrame();

  // Window fade-in
  const windowOpacity = interpolate(frame, [0, WINDOW_FADE_IN_END], [0, 1], {
    extrapolateLeft: 'clamp',
    extrapolateRight: 'clamp',
    easing: Easing.out(Easing.quad),
  });

  // Badge scale-in (0.8 → 1.0 with back easing)
  const badgeProgress = interpolate(
    frame,
    [BADGE_SCALE_START, BADGE_SCALE_START + BADGE_SCALE_DURATION],
    [0, 1],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.out(Easing.back(1.7)),
    }
  );
  const badgeScale = interpolate(badgeProgress, [0, 1], [0.8, 1]);
  const badgeOpacity = interpolate(
    frame,
    [BADGE_SCALE_START, BADGE_SCALE_START + 8],
    [0, 1],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
    }
  );

  return (
    <div
      style={{
        position: 'absolute',
        left: EDITOR_X,
        top: EDITOR_Y,
        width: EDITOR_WIDTH,
        height: EDITOR_HEIGHT,
        borderRadius: EDITOR_BORDER_RADIUS,
        border: `1px solid ${EDITOR_FRAME_COLOR}`,
        overflow: 'hidden',
        opacity: windowOpacity,
        // Amber glow
        boxShadow: `0 0 12px rgba(217, 148, 74, 0.08), 0 4px 24px rgba(0, 0, 0, 0.3)`,
      }}
    >
      {/* Title bar */}
      <div
        style={{
          height: TITLE_BAR_HEIGHT,
          backgroundColor: TITLE_BAR_COLOR,
          display: 'flex',
          alignItems: 'center',
          paddingLeft: 14,
          paddingRight: 14,
          gap: 8,
          borderBottom: `1px solid ${EDITOR_FRAME_COLOR}`,
        }}
      >
        {/* Traffic light dots */}
        <div style={{ display: 'flex', gap: 6, marginRight: 10 }}>
          <div
            style={{
              width: 10,
              height: 10,
              borderRadius: '50%',
              backgroundColor: TRAFFIC_RED,
            }}
          />
          <div
            style={{
              width: 10,
              height: 10,
              borderRadius: '50%',
              backgroundColor: TRAFFIC_YELLOW,
            }}
          />
          <div
            style={{
              width: 10,
              height: 10,
              borderRadius: '50%',
              backgroundColor: TRAFFIC_GREEN,
            }}
          />
        </div>

        {/* Filename */}
        <span
          style={{
            fontFamily: 'JetBrains Mono, monospace',
            fontSize: 13,
            fontWeight: 400,
            color: FILENAME_COLOR,
          }}
        >
          parser_v1.prompt
        </span>

        {/* Line count badge */}
        <div
          style={{
            marginLeft: 'auto',
            transform: `scale(${badgeScale})`,
            opacity: badgeOpacity,
          }}
        >
          <span
            style={{
              fontFamily: 'Inter, sans-serif',
              fontSize: 11,
              fontWeight: 600,
              color: ACCENT_AMBER,
              backgroundColor: `rgba(217, 148, 74, 0.15)`,
              padding: '2px 8px',
              borderRadius: 9999,
            }}
          >
            {TOTAL_LINES} lines
          </span>
        </div>
      </div>

      {/* Editor body */}
      <div
        style={{
          backgroundColor: '#0D1320',
          flex: 1,
          height: EDITOR_HEIGHT - TITLE_BAR_HEIGHT,
          overflow: 'hidden',
          position: 'relative',
        }}
      >
        {children}
      </div>
    </div>
  );
};

export default EditorChrome;
