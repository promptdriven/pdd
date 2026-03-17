import React, { useMemo } from 'react';
import { AbsoluteFill, useCurrentFrame } from 'remotion';
import {
  BG_COLOR,
  MODULES,
  CONVERSION_WAVES,
  FLASH_IN_FRAMES,
  FLASH_HOLD_FRAMES,
  FLASH_SETTLE_FRAMES,
  STAGGER_FRAMES,
} from './constants';
import { ModuleBlock } from './ModuleBlock';
import { DependencyEdges } from './DependencyEdges';
import { ModuleCounter } from './ModuleCounter';

export const defaultWhereToStart06SpreadingGlowMigrationProps = {};

export const WhereToStart06SpreadingGlowMigration: React.FC = () => {
  const frame = useCurrentFrame();

  // Build a map: moduleId → { conversionFrame, staggerOffset, isPreConverted }
  const moduleConversionInfo = useMemo(() => {
    const info = new Map<
      number,
      { conversionFrame: number | null; staggerOffset: number; isPreConverted: boolean }
    >();

    // Initialize all modules as unconverted
    for (const mod of MODULES) {
      info.set(mod.id, {
        conversionFrame: null,
        staggerOffset: 0,
        isPreConverted: false,
      });
    }

    // Apply conversion waves
    for (const wave of CONVERSION_WAVES) {
      wave.moduleIds.forEach((moduleId, index) => {
        if (wave.startFrame === 0) {
          // Pre-converted (frame 0)
          info.set(moduleId, {
            conversionFrame: 0,
            staggerOffset: 0,
            isPreConverted: true,
          });
        } else {
          info.set(moduleId, {
            conversionFrame: wave.startFrame,
            staggerOffset: index * STAGGER_FRAMES,
            isPreConverted: false,
          });
        }
      });
    }

    return info;
  }, []);

  // Compute which modules are currently converted (for edge rendering)
  const { convertedModuleIds, conversionCompletionFrames } = useMemo(() => {
    const converted = new Set<number>();
    const completionFrames = new Map<number, number>();

    for (const [moduleId, info] of moduleConversionInfo.entries()) {
      if (info.isPreConverted) {
        converted.add(moduleId);
        completionFrames.set(moduleId, 0);
      } else if (info.conversionFrame !== null) {
        const completionFrame =
          info.conversionFrame +
          info.staggerOffset +
          FLASH_IN_FRAMES +
          FLASH_HOLD_FRAMES +
          FLASH_SETTLE_FRAMES;
        if (frame >= completionFrame) {
          converted.add(moduleId);
        }
        completionFrames.set(moduleId, completionFrame);
      }
    }

    return { convertedModuleIds: converted, conversionCompletionFrames: completionFrames };
  }, [frame, moduleConversionInfo]);

  return (
    <AbsoluteFill
      style={{
        backgroundColor: BG_COLOR,
        overflow: 'hidden',
      }}
    >
      {/* Dependency edges (rendered behind modules) */}
      <DependencyEdges
        convertedModuleIds={convertedModuleIds}
        conversionCompletionFrames={conversionCompletionFrames}
      />

      {/* Module blocks */}
      {MODULES.map((mod) => {
        const info = moduleConversionInfo.get(mod.id)!;
        return (
          <ModuleBlock
            key={mod.id}
            id={mod.id}
            name={mod.name}
            x={mod.x}
            y={mod.y}
            conversionFrame={info.conversionFrame}
            staggerOffset={info.staggerOffset}
            isPreConverted={info.isPreConverted}
          />
        );
      })}

      {/* Module counter */}
      <ModuleCounter />
    </AbsoluteFill>
  );
};

export default WhereToStart06SpreadingGlowMigration;
