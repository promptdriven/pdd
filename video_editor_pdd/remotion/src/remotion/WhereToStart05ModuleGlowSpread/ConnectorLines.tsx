import React from 'react';
import { interpolate, useCurrentFrame, Easing } from 'remotion';
import {
  MODULES,
  MIGRATION_SEQUENCE,
  MIGRATED_GLOW_COLOR,
  CONNECTORS_START_FRAME,
  CONNECTOR_DRAW_DURATION,
  CANVAS_WIDTH,
  CANVAS_HEIGHT,
  getModuleCenter,
} from './constants';

// Build pairs of connections between migrated modules in sequence order
function getMigratedConnections(): Array<{
  fromId: string;
  toId: string;
  delay: number;
}> {
  const migratedIds = MIGRATION_SEQUENCE.map((s) => s.id);
  const connections: Array<{ fromId: string; toId: string; delay: number }> = [];
  for (let i = 1; i < migratedIds.length; i++) {
    connections.push({
      fromId: migratedIds[i - 1],
      toId: migratedIds[i],
      delay: i * 4, // stagger each line by 4 frames
    });
  }
  return connections;
}

const ConnectorLines: React.FC = () => {
  const frame = useCurrentFrame();
  const connections = getMigratedConnections();

  const moduleMap = new Map(
    MODULES.map((m) => [m.id, { row: m.row, col: m.col }])
  );

  return (
    <svg
      width={CANVAS_WIDTH}
      height={CANVAS_HEIGHT}
      style={{ position: 'absolute', top: 0, left: 0, pointerEvents: 'none' }}
    >
      {connections.map(({ fromId, toId, delay }, idx) => {
        const fromMod = moduleMap.get(fromId);
        const toMod = moduleMap.get(toId);
        if (!fromMod || !toMod) return null;

        const from = getModuleCenter(fromMod.row, fromMod.col);
        const to = getModuleCenter(toMod.row, toMod.col);

        const lineStart = CONNECTORS_START_FRAME + delay;
        const drawProgress = interpolate(
          frame,
          [lineStart, lineStart + CONNECTOR_DRAW_DURATION],
          [0, 1],
          {
            extrapolateLeft: 'clamp',
            extrapolateRight: 'clamp',
            easing: Easing.inOut(Easing.quad),
          }
        );

        if (drawProgress <= 0) return null;

        // Calculate the endpoint based on draw progress
        const currentX = from.x + (to.x - from.x) * drawProgress;
        const currentY = from.y + (to.y - from.y) * drawProgress;

        return (
          <line
            key={idx}
            x1={from.x}
            y1={from.y}
            x2={currentX}
            y2={currentY}
            stroke={MIGRATED_GLOW_COLOR}
            strokeOpacity={0.08}
            strokeWidth={1.5}
            strokeDasharray="4 4"
          />
        );
      })}
    </svg>
  );
};

export default ConnectorLines;
