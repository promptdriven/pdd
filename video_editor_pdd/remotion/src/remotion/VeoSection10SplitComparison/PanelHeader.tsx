import React from 'react';
import { COLORS, TYPOGRAPHY } from './constants';

interface PanelHeaderProps {
  text: string;
  align: 'left' | 'right';
}

export const PanelHeader: React.FC<PanelHeaderProps> = ({ text, align }) => {
  return (
    <div
      style={{
        position: 'absolute',
        left: align === 'left' ? 60 : undefined,
        right: align === 'right' ? 60 : undefined,
        top: 40,
        fontSize: TYPOGRAPHY.header.fontSize,
        fontFamily: TYPOGRAPHY.header.fontFamily,
        fontWeight: TYPOGRAPHY.header.fontWeight,
        letterSpacing: TYPOGRAPHY.header.letterSpacing,
        color: COLORS.headerText,
        textTransform: 'uppercase' as const,
        zIndex: 2,
      }}
    >
      {text}
    </div>
  );
};
