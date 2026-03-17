import React from 'react';
import { useCurrentFrame, interpolate, Easing } from 'remotion';
import {
  ACCENT_BLUE,
  TEXT_COLOR,
  PROMPT_GRAY,
  CMD_BLOCK_START,
  CMD_BG_FADE_DURATION,
  CMD_LINE1,
  CMD_LINE2,
} from './constants';

/**
 * Renders a single terminal line with character-by-character typing.
 * Colorizes $ prompt, pdd keyword, and rest of text differently.
 */
const TerminalLine: React.FC<{
  text: string;
  visibleChars: number;
}> = ({ text, visibleChars }) => {
  const visible = text.slice(0, visibleChars);

  // Parse the visible text into colored spans
  const segments: { text: string; color: string; opacity: number }[] = [];

  if (visible.startsWith('$')) {
    // Dollar prompt
    const dollarEnd = visible.indexOf(' ') >= 0 ? visible.indexOf(' ') + 1 : visible.length;
    segments.push({
      text: visible.slice(0, dollarEnd),
      color: PROMPT_GRAY,
      opacity: 0.4,
    });

    const rest = visible.slice(dollarEnd);

    // Check if this line has "pdd" as a keyword (standalone or start of command)
    if (text.includes('$ pdd ')) {
      // "pdd" is the command itself
      const pddLen = Math.min(3, rest.length);
      if (pddLen > 0) {
        segments.push({
          text: rest.slice(0, pddLen),
          color: ACCENT_BLUE,
          opacity: 0.8,
        });
        if (rest.length > 3) {
          segments.push({
            text: rest.slice(3),
            color: TEXT_COLOR,
            opacity: 0.7,
          });
        }
      }
    } else if (text.includes('pdd-cli')) {
      // "pdd-cli" is highlighted at end
      const pddIdx = rest.indexOf('pdd-cli');
      if (pddIdx >= 0) {
        segments.push({
          text: rest.slice(0, pddIdx),
          color: TEXT_COLOR,
          opacity: 0.7,
        });
        segments.push({
          text: rest.slice(pddIdx),
          color: ACCENT_BLUE,
          opacity: 0.8,
        });
      } else {
        segments.push({
          text: rest,
          color: TEXT_COLOR,
          opacity: 0.7,
        });
      }
    } else {
      segments.push({
        text: rest,
        color: TEXT_COLOR,
        opacity: 0.7,
      });
    }
  } else {
    segments.push({
      text: visible,
      color: TEXT_COLOR,
      opacity: 0.7,
    });
  }

  return (
    <div
      style={{
        fontFamily: '"JetBrains Mono", "Fira Code", "Courier New", monospace',
        fontSize: 15,
        lineHeight: '28px',
        whiteSpace: 'pre',
        height: 28,
      }}
    >
      {segments.map((seg, i) => (
        <span key={i} style={{ color: seg.color, opacity: seg.opacity }}>
          {seg.text}
        </span>
      ))}
      {/* Blinking cursor during typing */}
      {visibleChars < text.length && visibleChars > 0 && (
        <span style={{ color: TEXT_COLOR, opacity: 0.6 }}>▌</span>
      )}
    </div>
  );
};

/**
 * Command block card with two terminal lines that type in sequentially.
 */
export const CommandBlock: React.FC = () => {
  const frame = useCurrentFrame();

  // Background card fades in
  const bgOpacity = interpolate(
    frame,
    [CMD_BLOCK_START, CMD_BLOCK_START + CMD_BG_FADE_DURATION],
    [0, 0.4],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.out(Easing.quad),
    }
  );

  // Border fades in with bg
  const borderOpacity = interpolate(
    frame,
    [CMD_BLOCK_START, CMD_BLOCK_START + CMD_BG_FADE_DURATION],
    [0, 0.15],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.out(Easing.quad),
    }
  );

  // Line 1 starts typing after bg fades (CMD_BLOCK_START + 15)
  const line1Start = CMD_BLOCK_START + 15;
  const line1Chars = Math.floor(
    interpolate(frame, [line1Start, line1Start + CMD_LINE1.length * 2], [0, CMD_LINE1.length], {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
    })
  );

  // Line 2 starts 20 frames after line 1 finishes
  const line2Start = line1Start + CMD_LINE1.length * 2 + 20;
  const line2Chars = Math.floor(
    interpolate(frame, [line2Start, line2Start + CMD_LINE2.length * 2], [0, CMD_LINE2.length], {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
    })
  );

  return (
    <div
      style={{
        position: 'absolute',
        left: (1920 - 480) / 2,
        top: 520 - 52, // center vertically around y=520
        width: 480,
        padding: '24px 32px',
        backgroundColor: `rgba(15, 23, 42, ${bgOpacity})`,
        borderRadius: 8,
        borderLeft: `2px solid rgba(74, 144, 217, ${borderOpacity})`,
        boxSizing: 'border-box',
      }}
    >
      {line1Chars > 0 && <TerminalLine text={CMD_LINE1} visibleChars={line1Chars} />}
      {line2Chars > 0 && <TerminalLine text={CMD_LINE2} visibleChars={line2Chars} />}
    </div>
  );
};

export default CommandBlock;
