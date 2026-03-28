import React from 'react';
import { interpolate, useCurrentFrame, Easing } from 'remotion';
import {
  CELL_WIDTH,
  CELL_HEIGHT,
  MODULE_FILL,
  MODULE_BORDER,
  MODULE_LABEL_COLOR,
  MIGRATED_GLOW_COLOR,
  MODULE_FONT_SIZE,
  PROMPT_ICON_WIDTH,
  PROMPT_ICON_HEIGHT,
  MIGRATE_DURATION,
  ICON_SCALE_DURATION,
  getModulePosition,
} from './constants';

interface ModuleCellProps {
  id: string;
  label: string;
  row: number;
  col: number;
  migrateStartFrame: number | null; // null = never migrates
}

const ModuleCell: React.FC<ModuleCellProps> = ({
  label,
  row,
  col,
  migrateStartFrame,
}) => {
  const frame = useCurrentFrame();
  const pos = getModulePosition(row, col);

  // Determine migration progress (0 = unmigrated, 1 = fully migrated)
  const migrationProgress =
    migrateStartFrame !== null
      ? interpolate(frame, [migrateStartFrame, migrateStartFrame + MIGRATE_DURATION], [0, 1], {
          extrapolateLeft: 'clamp',
          extrapolateRight: 'clamp',
          easing: Easing.out(Easing.quad),
        })
      : 0;

  const isMigrated = migrationProgress > 0;

  // Prompt icon scale (appears with back-like bounce after migration starts)
  const iconScale =
    migrateStartFrame !== null
      ? interpolate(
          frame,
          [
            migrateStartFrame + MIGRATE_DURATION * 0.5,
            migrateStartFrame + MIGRATE_DURATION * 0.5 + ICON_SCALE_DURATION,
          ],
          [0, 1],
          {
            extrapolateLeft: 'clamp',
            extrapolateRight: 'clamp',
            easing: Easing.out(Easing.poly(3)),
          }
        )
      : 0;

  // Border color and width
  const borderColor = isMigrated ? MIGRATED_GLOW_COLOR : MODULE_BORDER;
  const borderWidth = isMigrated ? 2 : 1;

  // Glow intensity
  const glowBlur = interpolate(migrationProgress, [0, 1], [0, 10]);
  const glowOpacity = interpolate(migrationProgress, [0, 1], [0, 0.15]);

  // Label color and opacity
  const labelOpacity = isMigrated
    ? interpolate(migrationProgress, [0, 1], [0.3, 0.7])
    : 0.5; // spec: 0.5 unmigrated, 0.7 migrated (adjusted from 0.3 default)
  const labelColor = isMigrated ? MIGRATED_GLOW_COLOR : MODULE_LABEL_COLOR;

  // Internal "code lines" gray out
  const codeLineOpacity = interpolate(migrationProgress, [0, 1], [0.25, 0.08]);

  // Counter pulse for hold phase (subtle)
  const pulseScale =
    migrateStartFrame !== null && frame > (migrateStartFrame + MIGRATE_DURATION)
      ? 1 + Math.sin(frame * 0.05) * 0.005
      : 1;

  return (
    <div
      style={{
        position: 'absolute',
        left: pos.x,
        top: pos.y,
        width: CELL_WIDTH,
        height: CELL_HEIGHT,
        backgroundColor: MODULE_FILL,
        border: `${borderWidth}px solid ${borderColor}`,
        borderRadius: 4,
        boxShadow: isMigrated
          ? `0 0 ${glowBlur}px rgba(90, 170, 110, ${glowOpacity}), inset 0 0 ${glowBlur * 0.5}px rgba(90, 170, 110, ${glowOpacity * 0.5})`
          : 'none',
        overflow: 'hidden',
        transform: `scale(${pulseScale})`,
      }}
    >
      {/* Fake code lines inside the module */}
      <div style={{ padding: '8px 10px', paddingTop: 6 }}>
        {[0.7, 0.5, 0.85, 0.4, 0.6].map((widthFraction, i) => (
          <div
            key={i}
            style={{
              width: `${widthFraction * 100}%`,
              height: 3,
              backgroundColor: '#94A3B8',
              opacity: codeLineOpacity,
              borderRadius: 1,
              marginBottom: 4,
            }}
          />
        ))}
      </div>

      {/* Module label */}
      <div
        style={{
          position: 'absolute',
          bottom: 6,
          left: 0,
          right: 0,
          textAlign: 'center',
          fontFamily: 'Inter, sans-serif',
          fontSize: MODULE_FONT_SIZE,
          color: labelColor,
          opacity: labelOpacity,
          fontWeight: 400,
          lineHeight: 1,
          letterSpacing: -0.2,
        }}
      >
        {label}
      </div>

      {/* Prompt file icon (top-right corner) */}
      {isMigrated && (
        <div
          style={{
            position: 'absolute',
            top: 4,
            right: 4,
            width: PROMPT_ICON_WIDTH,
            height: PROMPT_ICON_HEIGHT,
            transform: `scale(${iconScale})`,
            transformOrigin: 'center center',
          }}
        >
          {/* Simple file/prompt icon */}
          <svg
            width={PROMPT_ICON_WIDTH}
            height={PROMPT_ICON_HEIGHT}
            viewBox="0 0 12 16"
            fill="none"
          >
            {/* File body */}
            <path
              d="M1 2C1 1.44772 1.44772 1 2 1H7L11 5V14C11 14.5523 10.5523 15 10 15H2C1.44772 15 1 14.5523 1 14V2Z"
              fill={MIGRATED_GLOW_COLOR}
              fillOpacity={0.3}
              stroke={MIGRATED_GLOW_COLOR}
              strokeWidth={1}
            />
            {/* Folded corner */}
            <path
              d="M7 1V5H11"
              stroke={MIGRATED_GLOW_COLOR}
              strokeWidth={1}
              fill="none"
            />
            {/* Prompt chevron */}
            <path
              d="M3.5 9L5.5 11L3.5 13"
              stroke={MIGRATED_GLOW_COLOR}
              strokeWidth={1.2}
              strokeLinecap="round"
              strokeLinejoin="round"
              fill="none"
            />
          </svg>
        </div>
      )}
    </div>
  );
};

export default ModuleCell;
