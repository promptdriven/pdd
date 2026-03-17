import React from 'react';
import { AbsoluteFill, useCurrentFrame, interpolate, Easing } from 'remotion';
import {
  BG_COLOR,
  TEXT_COLOR,
  ACCENT_BLUE,
  TITLE_FADE_START,
  TITLE_FADE_DURATION,
  URL_FADE_START,
  URL_FADE_DURATION,
} from './constants';
import { GhostTriangle } from './GhostTriangle';
import { CommandBlock } from './CommandBlock';

export const defaultClosing09FinalTitleCardProps = {};

export const Closing09FinalTitleCard: React.FC = () => {
  const frame = useCurrentFrame();

  // Title fade-in: frames 30-55
  const titleOpacity = interpolate(
    frame,
    [TITLE_FADE_START, TITLE_FADE_START + TITLE_FADE_DURATION],
    [0, 0.85],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.out(Easing.quad),
    }
  );

  // URL fade-in: frames 120-138
  const urlOpacity = interpolate(
    frame,
    [URL_FADE_START, URL_FADE_START + URL_FADE_DURATION],
    [0, 0.6],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.out(Easing.quad),
    }
  );

  // Underline opacity relative to URL text (parent div already applies urlOpacity)
  const underlineRelativeOpacity = urlOpacity > 0 ? 0.1 / 0.6 : 0;

  return (
    <AbsoluteFill
      style={{
        backgroundColor: BG_COLOR,
        fontFamily: 'Inter, system-ui, -apple-system, sans-serif',
      }}
    >
      {/* Ghost triangle watermark — behind everything */}
      <GhostTriangle />

      {/* Title: "Prompt-Driven Development" */}
      <div
        style={{
          position: 'absolute',
          top: 380 - 24, // center text vertically around y=380
          left: 0,
          width: 1920,
          textAlign: 'center',
          opacity: titleOpacity,
        }}
      >
        <span
          style={{
            fontFamily: 'Inter, system-ui, -apple-system, sans-serif',
            fontSize: 48,
            fontWeight: 700,
            color: TEXT_COLOR,
            letterSpacing: 1,
          }}
        >
          Prompt-Driven Development
        </span>
      </div>

      {/* Command block */}
      <CommandBlock />

      {/* URL: "pdd.dev" */}
      <div
        style={{
          position: 'absolute',
          top: 660 - 10,
          left: 0,
          width: 1920,
          textAlign: 'center',
          opacity: urlOpacity,
        }}
      >
        <span
          style={{
            fontFamily: 'Inter, system-ui, -apple-system, sans-serif',
            fontSize: 20,
            fontWeight: 600,
            color: ACCENT_BLUE,
            position: 'relative',
            display: 'inline-block',
          }}
        >
          pdd.dev
          {/* Subtle underline */}
          <span
            style={{
              position: 'absolute',
              bottom: -4,
              left: 0,
              right: 0,
              height: 1,
              backgroundColor: ACCENT_BLUE,
              opacity: underlineRelativeOpacity,
            }}
          />
        </span>
      </div>
    </AbsoluteFill>
  );
};

export default Closing09FinalTitleCard;
