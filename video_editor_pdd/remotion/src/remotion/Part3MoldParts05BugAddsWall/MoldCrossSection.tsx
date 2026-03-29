import React from 'react';
import {
  MOLD_X,
  MOLD_Y,
  MOLD_WIDTH,
  MOLD_HEIGHT,
  MOLD_WALL_THICKNESS,
  MOLD_OUTER_COLOR,
  MOLD_CAVITY_COLOR,
  CAVITY_X,
  CAVITY_Y,
  CAVITY_WIDTH,
  CAVITY_HEIGHT,
  NOZZLE_X,
  NOZZLE_Y,
  NOZZLE_WIDTH,
  NOZZLE_HEIGHT,
  NOZZLE_COLOR,
  EXISTING_WALLS,
  WALL_EXISTING_COLOR,
} from './constants';

interface MoldCrossSectionProps {
  wallsOpacity?: number;
}

export const MoldCrossSection: React.FC<MoldCrossSectionProps> = ({
  wallsOpacity = 0.4,
}) => {
  return (
    <>
      {/* Outer mold body */}
      <div
        style={{
          position: 'absolute',
          left: MOLD_X,
          top: MOLD_Y,
          width: MOLD_WIDTH,
          height: MOLD_HEIGHT,
          backgroundColor: MOLD_OUTER_COLOR,
          borderRadius: 8,
          opacity: 0.9,
        }}
      />

      {/* Cavity (cut-out interior) */}
      <div
        style={{
          position: 'absolute',
          left: CAVITY_X,
          top: CAVITY_Y,
          width: CAVITY_WIDTH,
          height: CAVITY_HEIGHT,
          backgroundColor: MOLD_CAVITY_COLOR,
          borderRadius: 4,
        }}
      />

      {/* Nozzle at the top */}
      <div
        style={{
          position: 'absolute',
          left: NOZZLE_X,
          top: NOZZLE_Y,
          width: NOZZLE_WIDTH,
          height: NOZZLE_HEIGHT,
          backgroundColor: NOZZLE_COLOR,
          borderRadius: '4px 4px 0 0',
          opacity: 0.8,
        }}
      />
      {/* Nozzle opening */}
      <div
        style={{
          position: 'absolute',
          left: NOZZLE_X + 15,
          top: NOZZLE_Y + NOZZLE_HEIGHT - 10,
          width: NOZZLE_WIDTH - 30,
          height: 10 + MOLD_WALL_THICKNESS,
          backgroundColor: MOLD_CAVITY_COLOR,
          borderRadius: 2,
        }}
      />

      {/* Existing internal walls */}
      {EXISTING_WALLS.map((wall, i) => (
        <div
          key={i}
          style={{
            position: 'absolute',
            left: wall.x,
            top: wall.y,
            width: wall.width,
            height: wall.height,
            backgroundColor: WALL_EXISTING_COLOR,
            opacity: wallsOpacity,
            borderRadius: 3,
            boxShadow: `0 0 8px ${WALL_EXISTING_COLOR}40`,
          }}
        />
      ))}

      {/* Wall labels for existing walls */}
      {EXISTING_WALLS.map((wall, i) => (
        <div
          key={`label-${i}`}
          style={{
            position: 'absolute',
            left: wall.x - 40,
            top: wall.y + wall.height + 8,
            width: wall.width + 80,
            textAlign: 'center',
            fontFamily: '"JetBrains Mono", monospace',
            fontSize: 11,
            color: '#94A3B8',
            opacity: wallsOpacity * 0.8,
            whiteSpace: 'nowrap',
          }}
        >
          {wall.label}
        </div>
      ))}
    </>
  );
};
