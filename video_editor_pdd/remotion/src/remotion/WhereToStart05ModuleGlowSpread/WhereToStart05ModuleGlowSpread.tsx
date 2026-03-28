import React from 'react';
import { AbsoluteFill } from 'remotion';
import {
  BG_COLOR,
  MODULES,
  MIGRATION_SEQUENCE,
} from './constants';
import ModuleCell from './ModuleCell';
import MigrationCounter from './MigrationCounter';
import ConnectorLines from './ConnectorLines';

export const defaultWhereToStart05ModuleGlowSpreadProps = {};

export const WhereToStart05ModuleGlowSpread: React.FC = () => {
  // Build a lookup: moduleId → frameStart (null if never migrated)
  const migrationMap = new Map<string, number>();
  for (const step of MIGRATION_SEQUENCE) {
    migrationMap.set(step.id, step.frameStart);
  }

  return (
    <AbsoluteFill
      style={{
        backgroundColor: BG_COLOR,
        fontFamily: 'Inter, sans-serif',
      }}
    >
      {/* Module grid */}
      {MODULES.map((mod) => (
        <ModuleCell
          key={mod.id}
          id={mod.id}
          label={mod.label}
          row={mod.row}
          col={mod.col}
          migrateStartFrame={migrationMap.get(mod.id) ?? null}
        />
      ))}

      {/* Connector lines between migrated modules */}
      <ConnectorLines />

      {/* Migration counter */}
      <MigrationCounter />
    </AbsoluteFill>
  );
};

export default WhereToStart05ModuleGlowSpread;
