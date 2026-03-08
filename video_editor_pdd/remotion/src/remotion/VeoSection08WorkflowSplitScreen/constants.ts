/**
 * Constants for VeoSection08WorkflowSplitScreen component
 */

export const COLORS = {
  background: '#0F1419',
  traditional: {
    background: '#1A1214',
    primary: '#EF4444',
    cardBg: '#2A1E1F',
  },
  veo2: {
    background: '#121A14',
    primary: '#10B981',
    cardBg: '#1E2A21',
  },
  text: {
    primary: '#E0E6ED',
    secondary: '#9CA3AF',
  },
};

export const DIMENSIONS = {
  canvas: {
    width: 1920,
    height: 1080,
  },
  divider: {
    x: 960,
    width: 4,
  },
  stepCard: {
    traditional: {
      width: 360,
      height: 70,
      spacing: 15,
      iconSize: 32,
    },
    veo2: {
      width: 360,
      height: 100,
      spacing: 40,
      iconSize: 48,
    },
  },
};

export const TRADITIONAL_STEPS = [
  { name: 'Storyboard Review', duration: '1-2 days', icon: '📋', delay: 0 },
  { name: 'Equipment Setup', duration: '3-5 days', icon: '📷', delay: 10 },
  { name: 'Location Scouting', duration: '2-3 days', icon: '🗺️', delay: 20 },
  { name: 'Filming Day 1-3', duration: '3 days', icon: '🎬', delay: 30 },
  { name: 'Post-Production', duration: '5-7 days', icon: '✂️', delay: 40 },
  { name: 'Review Cycles', duration: '3-4 days', icon: '🔄', delay: 50 },
  { name: 'Final Export', duration: '1 day', icon: '⬇️', delay: 60 },
];

export const VEO2_STEPS = [
  { name: 'Write Prompt', duration: '5 min', icon: '✏️', delay: 0, y: 300 },
  { name: 'Generate Video', duration: '2-3 min', icon: '✨', delay: 30, y: 440 },
  { name: 'Export & Share', duration: '1 min', icon: '⬆️', delay: 60, y: 580 },
];

export const TIMING = {
  titleAppear: 0,
  leftStepsStart: 15,
  rightStepsStart: 30,
  checkmarksStart: 120,
  duration: 180,
};
