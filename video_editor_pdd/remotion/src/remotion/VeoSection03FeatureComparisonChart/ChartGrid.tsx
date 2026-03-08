import React from 'react';
import { CANVAS, GRID } from './constants';

export const ChartGrid: React.FC = () => {
  return (
    <>
      {GRID.POSITIONS.map((position, index) => {
        const xPosition = CANVAS.WIDTH * position;
        return (
          <div
            key={`grid-line-${index}`}
            style={{
              position: 'absolute',
              left: xPosition,
              top: 0,
              width: 1,
              height: CANVAS.HEIGHT,
              backgroundColor: GRID.COLOR,
              opacity: GRID.OPACITY,
            }}
          />
        );
      })}
    </>
  );
};
