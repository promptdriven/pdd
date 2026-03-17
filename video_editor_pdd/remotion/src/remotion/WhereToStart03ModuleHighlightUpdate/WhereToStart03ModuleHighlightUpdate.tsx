import React from 'react';
import {
  AbsoluteFill,
  useCurrentFrame,
  interpolate,
  Easing,
} from 'remotion';
import { BG, MODULE_POS, MODULE_SIZE, TEXT_LIGHT } from './constants';
import { CodebaseBackground } from './CodebaseBackground';
import { ParticleStream } from './ParticleStream';
import { PromptDocument } from './PromptDocument';
import { TerminalPanel } from './TerminalPanel';

/**
 * Section 6.3 — Module Highlight & Update: Extracting a Prompt from Existing Code
 *
 * 240 frames @ 30fps = 8 seconds
 *
 * Animation sequence:
 *   0-20    Codebase dims, selected module pulses blue
 *   20-40   auth_handler.py label + terminal fade in
 *   40-70   Terminal types command
 *   70-80   "Analyzing module..." appears
 *   80-160  Particle stream flows, prompt document materializes
 *   160-180 Terminal shows success, document fully visible
 *   180-240 Hold — code block + prompt document side by side
 */

export const defaultWhereToStart03ModuleHighlightUpdateProps = {};

export const WhereToStart03ModuleHighlightUpdate: React.FC = () => {
  const frame = useCurrentFrame();

  // ── Module label: fades in at frame 20 over 15 frames ──
  const labelOpacity = interpolate(frame, [20, 35], [0, 0.7], {
    extrapolateLeft: 'clamp',
    extrapolateRight: 'clamp',
    easing: Easing.out(Easing.quad),
  });

  // ── Connection line between code block and prompt doc (appears with particles) ──
  const connectionOpacity = interpolate(frame, [100, 140], [0, 0.12], {
    extrapolateLeft: 'clamp',
    extrapolateRight: 'clamp',
    easing: Easing.out(Easing.quad),
  });

  return (
    <AbsoluteFill style={{ backgroundColor: BG }}>
      {/* Dimmed codebase graph */}
      <CodebaseBackground />

      {/* Module label: auth_handler.py */}
      <div
        style={{
          position: 'absolute',
          left: MODULE_POS.x + MODULE_SIZE.w / 2,
          top: MODULE_POS.y + MODULE_SIZE.h + 8,
          transform: 'translateX(-50%)',
          fontFamily: 'JetBrains Mono, monospace',
          fontSize: 11,
          color: TEXT_LIGHT,
          opacity: labelOpacity,
          whiteSpace: 'nowrap',
        }}
      >
        auth_handler.py
      </div>

      {/* Subtle connection line between code block and prompt */}
      <svg
        width={1920}
        height={1080}
        style={{ position: 'absolute', top: 0, left: 0, pointerEvents: 'none' }}
      >
        <path
          d={`M ${MODULE_POS.x + MODULE_SIZE.w} ${MODULE_POS.y + MODULE_SIZE.h / 2} Q ${900} ${320} ${1100} ${380 + 100}`}
          fill="none"
          stroke="#4A90D9"
          strokeWidth={1}
          strokeDasharray="4 4"
          opacity={connectionOpacity}
        />
      </svg>

      {/* Particle stream: starts at frame 80 */}
      <ParticleStream startFrame={80} />

      {/* Prompt document: materializes starting at frame 100 */}
      <PromptDocument startFrame={100} />

      {/* Terminal panel: starts at frame 20 */}
      <TerminalPanel startFrame={20} />
    </AbsoluteFill>
  );
};

export default WhereToStart03ModuleHighlightUpdate;
