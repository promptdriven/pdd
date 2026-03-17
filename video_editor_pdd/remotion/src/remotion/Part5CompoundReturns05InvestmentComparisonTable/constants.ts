// Colors
export const COLORS = {
  background: '#0F172A',
  headerBg: '#1E293B',
  border: '#334155',
  text: '#E2E8F0',
  muted: '#94A3B8',
  patching: '#D9944A',
  pdd: '#4A90D9',
  altRowBg: '#111827',
  pillBg: '#1E293B',
} as const;

// Table dimensions
export const TABLE = {
  width: 900,
  headerHeight: 50,
  rowHeight: 70,
  colWidth: 300,
  borderRadius: 8,
  centerX: 960,
  centerY: 460,
} as const;

// Row data
export interface RowData {
  investment: string;
  icon: 'bug' | 'code' | 'document';
  patching: string;
  pdd: string;
  pddGlow: number;
  pddOpacity: number;
  alternate: boolean;
}

export const ROWS: RowData[] = [
  {
    investment: 'Fix a bug',
    icon: 'bug',
    patching: 'One place, once',
    pdd: 'Impossible forever',
    pddGlow: 0.04,
    pddOpacity: 0.8,
    alternate: false,
  },
  {
    investment: 'Improve code',
    icon: 'code',
    patching: 'One version',
    pdd: 'All future versions',
    pddGlow: 0.06,
    pddOpacity: 0.9,
    alternate: true,
  },
  {
    investment: 'Document intent',
    icon: 'document',
    patching: 'One snapshot',
    pdd: 'Living specification',
    pddGlow: 0.08,
    pddOpacity: 1.0,
    alternate: false,
  },
];

// Animation frame ranges
export const ANIM = {
  tableAppear: { start: 0, duration: 20 },
  row1: { start: 30, slideDuration: 20, cellStagger: 10 },
  row2: { start: 90, slideDuration: 20, cellStagger: 10 },
  row3: { start: 150, slideDuration: 20, cellStagger: 10 },
  pddPulse: { start: 210, duration: 30 },
  summary: { start: 270, slideDuration: 25 },
  totalFrames: 420,
} as const;
