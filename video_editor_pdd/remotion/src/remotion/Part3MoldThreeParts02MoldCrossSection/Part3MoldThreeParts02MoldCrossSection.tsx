import React from 'react';
import {
  AbsoluteFill,
  useCurrentFrame,
  interpolate,
  Easing,
  Sequence,
} from 'remotion';
import { EngineeringGrid } from './EngineeringGrid';
import { MoldShape } from './MoldShape';
import { WallLabels, NozzleLabels, CavityLabels } from './RegionLabels';
import {
  BG_COLOR,
  GRID_COLOR,
  GRID_OPACITY,
  GRID_SPACING,
  LABEL_SLATE,
  DRAW_START,
  DRAW_END,
  TITLE_START,
  TITLE_END,
  WALLS_START,
  WALLS_END,
  NOZZLE_START,
  NOZZLE_END,
  CAVITY_START,
  CAVITY_END,
  FINALE_START,
  TOTAL_FRAMES,
} from './constants';

export const defaultPart3MoldThreeParts02MoldCrossSectionProps = {};

export const Part3MoldThreeParts02MoldCrossSection: React.FC = () => {
  const frame = useCurrentFrame();

  // ── Phase 1: Mold draw-in (0-40) ─────────────────
  const drawProgress = interpolate(frame, [DRAW_START, DRAW_END], [0, 1], {
    easing: Easing.inOut(Easing.cubic),
    extrapolateLeft: 'clamp',
    extrapolateRight: 'clamp',
  });

  // ── Phase 2: Title fade-in (40-60) ────────────────
  const titleOpacity = interpolate(
    frame,
    [TITLE_START, TITLE_END],
    [0, 0.4],
    {
      easing: Easing.out(Easing.quad),
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
    }
  );

  // ── Phase 3: Walls illuminate (60-120) ────────────
  const wallIlluminate = interpolate(
    frame,
    [WALLS_START, WALLS_START + 20],
    [0, 1],
    {
      easing: Easing.out(Easing.quad),
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
    }
  );

  // Wall labels appear staggered (frame 75-120)
  const wallLabelProgresses = [0, 1, 2, 3].map((i) => {
    const labelStart = WALLS_START + 15 + i * 12;
    return interpolate(frame, [labelStart, labelStart + 15], [0, 1], {
      easing: Easing.out(Easing.quad),
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
    });
  });

  const wallArrowProgress = interpolate(
    frame,
    [WALLS_START + 15, WALLS_START + 27],
    [0, 1],
    {
      easing: Easing.out(Easing.cubic),
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
    }
  );

  // ── Phase 4: Nozzle illuminates (120-180) ─────────
  const nozzleIlluminate = interpolate(
    frame,
    [NOZZLE_START, NOZZLE_START + 20],
    [0, 1],
    {
      easing: Easing.out(Easing.quad),
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
    }
  );

  // Nozzle labels staggered
  const nozzleLabelProgresses = [0, 1, 2].map((i) => {
    const labelStart = NOZZLE_START + 15 + i * 12;
    return interpolate(frame, [labelStart, labelStart + 15], [0, 1], {
      easing: Easing.out(Easing.quad),
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
    });
  });

  // Walls dim when nozzle activates
  const wallDimFactor = interpolate(
    frame,
    [NOZZLE_START, NOZZLE_START + 15],
    [1, 0.3],
    {
      easing: Easing.out(Easing.quad),
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
    }
  );

  // ── Phase 5: Cavity fills (180-240) ───────────────
  const cavityFillProgress = interpolate(
    frame,
    [CAVITY_START, CAVITY_START + 40],
    [0, 1],
    {
      easing: Easing.out(Easing.cubic),
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
    }
  );

  // Cavity labels staggered
  const cavityLabelProgresses = [0, 1, 2].map((i) => {
    const labelStart = CAVITY_START + 20 + i * 12;
    return interpolate(frame, [labelStart, labelStart + 15], [0, 1], {
      easing: Easing.out(Easing.quad),
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
    });
  });

  // Nozzle dims when cavity activates
  const nozzleDimFactor = interpolate(
    frame,
    [CAVITY_START, CAVITY_START + 15],
    [1, 0.3],
    {
      easing: Easing.out(Easing.quad),
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
    }
  );

  // ── Phase 6: All re-illuminate (240-300) ──────────
  const finaleBoost = interpolate(
    frame,
    [FINALE_START, FINALE_START + 20],
    [0, 1],
    {
      easing: Easing.out(Easing.quad),
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
    }
  );

  // ── Compute final opacities ───────────────────────
  // Walls: illuminate → dim on nozzle → re-illuminate on finale
  let wallOpacity = wallIlluminate;
  if (frame >= NOZZLE_START) {
    wallOpacity = wallIlluminate * wallDimFactor;
  }
  if (frame >= FINALE_START) {
    wallOpacity = interpolate(
      finaleBoost,
      [0, 1],
      [wallIlluminate * wallDimFactor, wallIlluminate]
    );
  }

  // Nozzle: illuminate → dim on cavity → re-illuminate on finale
  let nozzleOpacity = nozzleIlluminate;
  if (frame >= CAVITY_START) {
    nozzleOpacity = nozzleIlluminate * nozzleDimFactor;
  }
  if (frame >= FINALE_START) {
    nozzleOpacity = interpolate(
      finaleBoost,
      [0, 1],
      [nozzleIlluminate * nozzleDimFactor, nozzleIlluminate]
    );
  }

  // Cavity fill stays once filled, re-brightens on finale
  const cavityFillOpacity =
    frame >= FINALE_START
      ? interpolate(finaleBoost, [0, 1], [0.12, 0.15])
      : interpolate(cavityFillProgress, [0, 1], [0.08, 0.15]);

  // Wall labels: visible from walls phase, dim with walls, re-brighten
  let wallLabelsOverall = wallOpacity;
  if (frame >= FINALE_START) {
    wallLabelsOverall = interpolate(
      finaleBoost,
      [0, 1],
      [wallLabelsOverall, 1]
    );
  }

  // Nozzle labels: visible from nozzle phase, dim with nozzle, re-brighten
  let nozzleLabelsOverall = nozzleOpacity;
  if (frame >= FINALE_START) {
    nozzleLabelsOverall = interpolate(
      finaleBoost,
      [0, 1],
      [nozzleLabelsOverall, 1]
    );
  }

  // Cavity labels
  let cavityLabelsOverall = frame >= CAVITY_START ? 1 : 0;
  if (frame >= CAVITY_START && frame < FINALE_START) {
    cavityLabelsOverall = cavityFillProgress;
  }
  if (frame >= FINALE_START) {
    cavityLabelsOverall = interpolate(
      finaleBoost,
      [0, 1],
      [cavityLabelsOverall, 1]
    );
  }

  return (
    <AbsoluteFill style={{ backgroundColor: BG_COLOR }}>
      {/* Engineering grid */}
      <EngineeringGrid
        spacing={GRID_SPACING}
        color={GRID_COLOR}
        opacity={GRID_OPACITY}
        width={1920}
        height={1080}
      />

      {/* Section title */}
      <div
        style={{
          position: 'absolute',
          top: 120,
          left: 0,
          right: 0,
          textAlign: 'center',
          opacity: titleOpacity,
          fontFamily: 'Inter, sans-serif',
          fontSize: 12,
          fontWeight: 600,
          color: LABEL_SLATE,
          letterSpacing: 3,
        }}
      >
        THREE TYPES OF CAPITAL
      </div>

      {/* Mold cross-section shape */}
      <MoldShape
        drawProgress={drawProgress}
        wallOpacity={wallOpacity}
        nozzleOpacity={nozzleOpacity}
        cavityFillProgress={frame >= CAVITY_START ? cavityFillProgress : 0}
        cavityFillOpacity={frame >= CAVITY_START ? cavityFillOpacity : 0}
      />

      {/* Wall labels with callout arrows */}
      <WallLabels
        opacity={wallLabelsOverall}
        arrowProgress={wallArrowProgress}
        labelProgresses={wallLabelProgresses}
      />

      {/* Nozzle labels */}
      <NozzleLabels
        opacity={nozzleLabelsOverall}
        labelProgresses={nozzleLabelProgresses}
      />

      {/* Cavity labels */}
      <CavityLabels
        opacity={cavityLabelsOverall}
        labelProgresses={cavityLabelProgresses}
      />
    </AbsoluteFill>
  );
};

export default Part3MoldThreeParts02MoldCrossSection;
