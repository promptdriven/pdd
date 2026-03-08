/**
 * Constants for AnimationSection06IconGridAnimation
 */

export const COLORS = {
  backgroundStart: '#f8fafc', // slate-50
  backgroundEnd: '#e2e8f0', // slate-200
  iconBackground: '#ffffff',
  labelText: '#475569', // slate-600

  // Icon colors
  chartBar: '#3b82f6', // blue-500
  lightning: '#f59e0b', // amber-500
  shield: '#10b981', // emerald-500
  code: '#8b5cf6', // violet-500
  sparkles: '#ec4899', // pink-500
  rocket: '#06b6d4', // cyan-500
  layers: '#6366f1', // indigo-500
  zap: '#f97316', // orange-500
  heart: '#ef4444', // red-500
} as const;

export const GRID_CONFIG = {
  columns: 3,
  rows: 3,
  cellSize: 200,
  gapHorizontal: 100,
  gapVertical: 100,
} as const;

export const ICON_CONFIG = {
  containerSize: 80,
  borderWidth: 2,
  iconSize: 40,
  shadow: '0 8px 24px rgba(0,0,0,0.12)',
} as const;

export const LABEL_CONFIG = {
  fontSize: 14,
  offsetY: 100,
  fontFamily: 'Inter',
  fontWeight: 500,
} as const;

export const TIMING = {
  rowStagger: 15,
  iconStagger: 3,
  entryDuration: 20,
  pulseDuration: 30,
  labelFadeStart: 20,
  labelFadeEnd: 35,
} as const;

export const ICONS_DATA = [
  { id: 1, icon: 'ChartBar', color: COLORS.chartBar, label: 'Analytics', row: 0, col: 0 },
  { id: 2, icon: 'Lightning', color: COLORS.lightning, label: 'Performance', row: 0, col: 1 },
  { id: 3, icon: 'Shield', color: COLORS.shield, label: 'Security', row: 0, col: 2 },
  { id: 4, icon: 'Code', color: COLORS.code, label: 'Development', row: 1, col: 0 },
  { id: 5, icon: 'Sparkles', color: COLORS.sparkles, label: 'Design', row: 1, col: 1 },
  { id: 6, icon: 'Rocket', color: COLORS.rocket, label: 'Deploy', row: 1, col: 2 },
  { id: 7, icon: 'Layers', color: COLORS.layers, label: 'Scale', row: 2, col: 0 },
  { id: 8, icon: 'Zap', color: COLORS.zap, label: 'Optimize', row: 2, col: 1 },
  { id: 9, icon: 'Heart', color: COLORS.heart, label: 'Reliable', row: 2, col: 2 },
] as const;
