import React from 'react';

interface TypeWriterProps {
  text: string;
  /** Number of characters revealed so far (can be fractional — floors internally) */
  charsRevealed: number;
  style?: React.CSSProperties;
}

/**
 * Renders text with a typewriter reveal effect.
 * Characters beyond `charsRevealed` are transparent.
 */
export const TypeWriter: React.FC<TypeWriterProps> = ({
  text,
  charsRevealed,
  style,
}) => {
  const count = Math.floor(Math.max(0, Math.min(charsRevealed, text.length)));

  return (
    <span style={style}>
      {text.split('').map((char, i) => (
        <span
          key={i}
          style={{
            opacity: i < count ? 1 : 0,
            transition: 'none',
          }}
        >
          {char}
        </span>
      ))}
    </span>
  );
};
