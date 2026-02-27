import { describe, it, expect, vi } from 'vitest';

// computeGroupLayout is a pure math helper — mock everything else so the module loads.
vi.mock('reactflow', () => ({
  default: vi.fn(),
  MarkerType: { ArrowClosed: 'arrowclosed' },
  BackgroundVariant: { Dots: 'dots' },
  ConnectionMode: { Loose: 'loose', Strict: 'strict' },
  addEdge: vi.fn(),
  useNodesState: () => [[], vi.fn(), vi.fn()],
  useEdgesState: () => [[], vi.fn(), vi.fn()],
  useViewport: () => ({ zoom: 1, x: 0, y: 0 }),
  Panel: vi.fn(),
  Controls: vi.fn(),
  MiniMap: vi.fn(),
  Background: vi.fn(),
  BaseEdge: vi.fn(),
  getBezierPath: vi.fn(() => ['', 0, 0]),
}));

vi.mock('../api', () => ({ PromptInfo: {} }));
vi.mock('../lib/batchUtils', () => ({ getBatchForModule: vi.fn() }));
vi.mock('../components/ModuleNode', () => ({ default: vi.fn() }));
vi.mock('../components/GroupNode', () => ({
  default: vi.fn(),
  GROUP_NODE_WIDTH: 220,
  GROUP_NODE_HEIGHT: 56,
}));
vi.mock('../components/BatchFilterDropdown', () => ({ default: vi.fn() }));
vi.mock('../components/Icon', () => ({
  ChevronDownIcon: vi.fn(),
  ChevronUpIcon: vi.fn(),
  SparklesIcon: vi.fn(),
  DocumentArrowDownIcon: vi.fn(),
  SpinnerIcon: vi.fn(),
}));
vi.mock('../components/Tooltip', () => ({ default: vi.fn() }));

import { computeGroupLayout } from '../components/DependencyViewer';

// Layout constants (must match DependencyViewer.tsx)
const NODE_WIDTH = 200;
const NODE_HEIGHT = 85;
const HEADER_HEIGHT = 56;
const INNER_PAD = 20;
const CHILD_GAP = 16;
const CHILD_COLS = 2;

const makeChild = (filename: string) => ({
  filename,
  reason: '',
  description: '',
  dependencies: [] as string[],
  priority: 1,
  filepath: `src/${filename}`,
  tags: [] as string[],
  group: 'g',
});

describe('computeGroupLayout', () => {
  it('1 child → 1 column, containerW fits one node', () => {
    const { containerW } = computeGroupLayout([makeChild('a')]);
    // cols=1: INNER_PAD*2 + 1*(NODE_WIDTH+CHILD_GAP) - CHILD_GAP
    expect(containerW).toBe(INNER_PAD * 2 + 1 * (NODE_WIDTH + CHILD_GAP) - CHILD_GAP);
  });

  it('2 children → 2 columns, containerW fits two nodes + gap', () => {
    const { containerW } = computeGroupLayout([makeChild('a'), makeChild('b')]);
    // cols=2: INNER_PAD*2 + 2*(NODE_WIDTH+CHILD_GAP) - CHILD_GAP
    expect(containerW).toBe(INNER_PAD * 2 + 2 * (NODE_WIDTH + CHILD_GAP) - CHILD_GAP);
  });

  it('3 children → 2 columns, 2 rows, containerH fits header + 2 rows', () => {
    const { containerH } = computeGroupLayout([makeChild('a'), makeChild('b'), makeChild('c')]);
    // rows=2: HEADER_HEIGHT + INNER_PAD*2 + 2*(NODE_HEIGHT+CHILD_GAP) - CHILD_GAP
    expect(containerH).toBe(HEADER_HEIGHT + INNER_PAD * 2 + 2 * (NODE_HEIGHT + CHILD_GAP) - CHILD_GAP);
  });

  it('4 children → 2×2 grid', () => {
    const { containerW, containerH, childPositions } = computeGroupLayout([
      makeChild('a'), makeChild('b'), makeChild('c'), makeChild('d'),
    ]);
    expect(containerW).toBe(INNER_PAD * 2 + 2 * (NODE_WIDTH + CHILD_GAP) - CHILD_GAP);
    expect(containerH).toBe(HEADER_HEIGHT + INNER_PAD * 2 + 2 * (NODE_HEIGHT + CHILD_GAP) - CHILD_GAP);
    expect(childPositions).toHaveLength(4);
  });

  it('child[0] relative position: x=INNER_PAD, y=HEADER_HEIGHT+INNER_PAD', () => {
    const { childPositions } = computeGroupLayout([makeChild('a'), makeChild('b')]);
    expect(childPositions[0].x).toBe(INNER_PAD);
    expect(childPositions[0].y).toBe(HEADER_HEIGHT + INNER_PAD);
  });

  it('child[1] relative position: x=INNER_PAD+(NODE_WIDTH+CHILD_GAP), y=same row', () => {
    const { childPositions } = computeGroupLayout([makeChild('a'), makeChild('b')]);
    expect(childPositions[1].x).toBe(INNER_PAD + (NODE_WIDTH + CHILD_GAP));
    expect(childPositions[1].y).toBe(HEADER_HEIGHT + INNER_PAD); // same row
  });

  it('child[2] relative position: x=INNER_PAD, y=next row (wraps to row 2)', () => {
    const { childPositions } = computeGroupLayout([makeChild('a'), makeChild('b'), makeChild('c')]);
    expect(childPositions[2].x).toBe(INNER_PAD); // col 0
    expect(childPositions[2].y).toBe(HEADER_HEIGHT + INNER_PAD + (NODE_HEIGHT + CHILD_GAP)); // row 1
  });

  it('containerH = HEADER_HEIGHT + INNER_PAD*2 + rows*(NODE_HEIGHT+CHILD_GAP) - CHILD_GAP', () => {
    // 1 row
    const { containerH: h1 } = computeGroupLayout([makeChild('a')]);
    expect(h1).toBe(HEADER_HEIGHT + INNER_PAD * 2 + 1 * (NODE_HEIGHT + CHILD_GAP) - CHILD_GAP);

    // 2 rows
    const { containerH: h2 } = computeGroupLayout([
      makeChild('a'), makeChild('b'), makeChild('c'),
    ]);
    expect(h2).toBe(HEADER_HEIGHT + INNER_PAD * 2 + 2 * (NODE_HEIGHT + CHILD_GAP) - CHILD_GAP);
  });

  it('childPositions contain correct filename for each child', () => {
    const children = [makeChild('alpha'), makeChild('beta'), makeChild('gamma')];
    const { childPositions } = computeGroupLayout(children);
    expect(childPositions.map(p => p.filename)).toEqual(['alpha', 'beta', 'gamma']);
  });
});
