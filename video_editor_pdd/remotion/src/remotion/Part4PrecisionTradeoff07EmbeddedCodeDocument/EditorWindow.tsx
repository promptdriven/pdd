import React from 'react';
import { interpolate, useCurrentFrame, Easing } from 'remotion';
import { COLORS, EDITOR, FONTS } from './constants';

interface EditorWindowProps {
  children: React.ReactNode;
}

export const EditorWindow: React.FC<EditorWindowProps> = ({ children }) => {
  const frame = useCurrentFrame();

  // Editor window appears with easeOut(cubic) over 20 frames
  // Start at 0.15 opacity so content is visible from frame 0
  const windowOpacity = interpolate(frame, [0, 20], [0.15, 1], {
    easing: Easing.out(Easing.cubic),
    extrapolateRight: 'clamp',
  });

  const windowScale = interpolate(frame, [0, 20], [0.97, 1], {
    easing: Easing.out(Easing.cubic),
    extrapolateRight: 'clamp',
  });

  return (
    <div
      style={{
        position: 'absolute',
        left: EDITOR.x,
        top: EDITOR.y,
        width: EDITOR.width,
        height: EDITOR.height,
        opacity: windowOpacity,
        transform: `scale(${windowScale})`,
        borderRadius: EDITOR.borderRadius,
        overflow: 'hidden',
        boxShadow: '0 20px 60px rgba(0, 0, 0, 0.5)',
      }}
    >
      {/* Title bar */}
      <div
        style={{
          width: '100%',
          height: EDITOR.titleBarHeight,
          backgroundColor: COLORS.titleBar,
          display: 'flex',
          alignItems: 'center',
          paddingLeft: 16,
          gap: 8,
          borderTopLeftRadius: EDITOR.borderRadius,
          borderTopRightRadius: EDITOR.borderRadius,
        }}
      >
        {/* Window dots */}
        <div
          style={{
            width: 10,
            height: 10,
            borderRadius: '50%',
            backgroundColor: '#EF4444',
            opacity: 0.7,
          }}
        />
        <div
          style={{
            width: 10,
            height: 10,
            borderRadius: '50%',
            backgroundColor: '#F59E0B',
            opacity: 0.7,
          }}
        />
        <div
          style={{
            width: 10,
            height: 10,
            borderRadius: '50%',
            backgroundColor: '#22C55E',
            opacity: 0.7,
          }}
        />
        {/* Filename */}
        <span
          style={{
            fontFamily: FONTS.mono,
            fontSize: 11,
            color: COLORS.titleText,
            opacity: 0.7,
            marginLeft: 12,
          }}
        >
          ad_latency_optimizer.prompt
        </span>
      </div>

      {/* Editor body */}
      <div
        style={{
          width: '100%',
          height: EDITOR.height - EDITOR.titleBarHeight,
          backgroundColor: COLORS.editorBg,
          position: 'relative',
          overflow: 'hidden',
        }}
      >
        {children}
      </div>
    </div>
  );
};
