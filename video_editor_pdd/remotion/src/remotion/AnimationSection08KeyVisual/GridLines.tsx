import React from 'react';
import { COLORS, DIMENSIONS } from './constants';

export const GridLines: React.FC = () => {
  const marks = [0.25, 0.5, 0.75];
  const chartTop = DIMENSIONS.containerBottomY - DIMENSIONS.maxHeight;

  return (
    <>
      {marks.map((pct) => {
        const y = chartTop + DIMENSIONS.maxHeight * (1 - pct);
        return (
          <div
            key={pct}
            style={{
              position: 'absolute',
              left: 0,
              right: 0,
              top: y,
              height: 1,
              backgroundColor: COLORS.gridLine,
            }}
          />
        );
      })}
    </>
  );
};
