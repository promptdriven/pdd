// Component-level constants for VeoSection12SplitOceanForestReprise
// Wipe transition: ocean wave sunset → forest canopy aerial

export const CANVAS = {
  width: 1920,
  height: 1080,
};

export const COLORS = {
  background: '#000000',
  wipeEdge: '#FFFFFF',
  wipeGlow: 'rgba(245, 158, 11, 0.15)',
  wipeGlowSolid: '#F59E0B',
  progressStart: '#F59E0B',
  progressEnd: '#34D399',
};

export const WIPE = {
  edgeWidth: 8,
  glowWidth: 40,
};

export const PROGRESS_BAR = {
  y: 1076,
  height: 4,
};

export const ANIMATION = {
  // Frame 0-30: Wipe moves from X=0 to X=960 (center)
  wipeInStart: 0,
  wipeInEnd: 30,

  // Frame 30-60: Wipe holds at center (split visible)
  holdStart: 30,
  holdEnd: 60,

  // Frame 60-85: Wipe continues from X=960 to X=1920
  wipeOutStart: 60,
  wipeOutEnd: 85,

  // Frame 85-90: Hold on full forest, glow fades
  glowFadeStart: 85,
  glowFadeEnd: 90,

  totalDuration: 90,
};
