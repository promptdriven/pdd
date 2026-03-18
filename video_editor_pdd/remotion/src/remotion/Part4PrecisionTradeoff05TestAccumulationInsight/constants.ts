// constants.ts — Colors, dimensions, and stage data

export const CANVAS = {
  width: 1920,
  height: 1080,
  background: '#0A0F1A',
} as const;

export const COLORS = {
  titleText: '#E2E8F0',
  promptLine: '#4A90D9',
  wallColor: '#D9944A',
  arrowColor: '#334155',
  arrowText: '#64748B',
  timelineTrack: '#1E293B',
  calloutText: '#E2E8F0',
  simplerHighlight: '#4A90D9',
  saferHighlight: '#5AAA6E',
  docBackground: '#1E293B',
  moldFill: '#4A90D9',
} as const;

export const STAGE_COLORS = {
  day1: '#D9944A',
  month1: '#94A3B8',
  month6: '#5AAA6E',
} as const;

export interface StageData {
  label: string;
  promptLines: number;
  promptHeight: number;
  wallCount: number;
  description: string;
  color: string;
  fillOpacity: number;
  wallStroke: number;
}

export const STAGES: StageData[] = [
  {
    label: 'DAY 1',
    promptLines: 30,
    promptHeight: 180,
    wallCount: 3,
    description: 'Prompt carries the weight',
    color: STAGE_COLORS.day1,
    fillOpacity: 0.06,
    wallStroke: 4,
  },
  {
    label: 'MONTH 1',
    promptLines: 15,
    promptHeight: 100,
    wallCount: 15,
    description: 'Tests take over',
    color: STAGE_COLORS.month1,
    fillOpacity: 0.1,
    wallStroke: 4,
  },
  {
    label: 'MONTH 6',
    promptLines: 5,
    promptHeight: 50,
    wallCount: 40,
    description: 'Intent is enough',
    color: STAGE_COLORS.month6,
    fillOpacity: 0.15,
    wallStroke: 3,
  },
];

// Column X positions (center of each column)
export const COLUMN_X = [160, 710, 1260] as const;
export const COLUMN_WIDTH = 500;
export const PROMPT_DOC_WIDTH = 120;
export const MOLD_WIDTH = 120;
export const MOLD_HEIGHT = 150;

// Vertical positions
export const TITLE_Y = 50;
export const HEADER_Y = 120;
export const PROMPT_Y = 160;
export const MOLD_GAP = 30; // gap between prompt doc bottom and mold top
export const LABEL_GAP = 20; // gap between mold bottom and label

// Timeline
export const TIMELINE_Y = 900;
export const TIMELINE_HEIGHT = 8;
export const TIMELINE_X_START = 160;
export const TIMELINE_X_END = 1760;

// Callout
export const CALLOUT_Y = 980;

// Animation frames
export const ANIM = {
  titleStart: 0,
  titleDur: 20,
  timelineDrawStart: 0,
  timelineDrawDur: 30,
  stage1Start: 30,
  stage1Dur: 60,
  arrow1Start: 90,
  arrow1Dur: 15,
  stage2Start: 120,
  stage2Dur: 60,
  arrow2Start: 180,
  arrow2Dur: 15,
  stage3Start: 210,
  stage3Dur: 50,
  timelineFillStart: 260,
  timelineFillDur: 40,
  calloutStart: 260,
  calloutDur: 20,
} as const;
