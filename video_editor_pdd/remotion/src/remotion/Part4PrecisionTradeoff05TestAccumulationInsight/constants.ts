// constants.ts — colors, dimensions, stage data

export const CANVAS = {
  WIDTH: 1920,
  HEIGHT: 1080,
  BG: '#0A0F1A',
} as const;

export const COLORS = {
  title: '#E2E8F0',
  promptLine: '#4A90D9',
  wall: '#D9944A',
  fill: '#4A90D9',
  arrowLine: '#334155',
  arrowText: '#64748B',
  callout: '#E2E8F0',
  simpler: '#4A90D9',
  safer: '#5AAA6E',
  docBg: '#1E293B',
  timelineTrack: '#1E293B',
} as const;

export const STAGES = [
  {
    label: 'DAY 1',
    promptLines: 30,
    promptHeight: 180,
    wallCount: 3,
    wallStroke: 4,
    fillOpacity: 0.06,
    description: 'Prompt carries the weight',
    color: '#D9944A',
    x: 160,
  },
  {
    label: 'MONTH 1',
    promptLines: 15,
    promptHeight: 100,
    wallCount: 15,
    wallStroke: 4,
    fillOpacity: 0.1,
    description: 'Tests take over',
    color: '#94A3B8',
    x: 710,
  },
  {
    label: 'MONTH 6',
    promptLines: 5,
    promptHeight: 50,
    wallCount: 40,
    wallStroke: 3,
    fillOpacity: 0.15,
    description: 'Intent is enough',
    color: '#5AAA6E',
    x: 1260,
  },
] as const;

export const COLUMN_WIDTH = 500;
export const DOC_WIDTH = 120;
export const MOLD_WIDTH = 120;
export const MOLD_HEIGHT = 150;

// Animation frame ranges
export const ANIM = {
  titleIn: { start: 0, dur: 20 },
  stage1: { start: 30, dur: 60 },
  arrow1: { start: 90, dur: 15 },
  stage2: { start: 120, dur: 60 },
  arrow2: { start: 180, dur: 15 },
  stage3: { start: 210, dur: 50 },
  timeline: { start: 260, dur: 40 },
  callout: { start: 260, dur: 20 },
} as const;
