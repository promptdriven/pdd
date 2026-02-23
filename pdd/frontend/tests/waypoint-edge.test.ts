import { describe, it, expect, vi } from 'vitest';

// ---- Silence React / ReactFlow / UI component imports ----
// DependencyViewer.tsx is a full React component, but getLayoutedElements is a
// pure function (uses dagre, not React hooks).  We mock everything else so the
// module loads without a DOM renderer.

vi.mock('reactflow', () => ({
  default: vi.fn(),
  MarkerType: { ArrowClosed: 'arrowclosed' },
  BackgroundVariant: { Dots: 'dots' },
  ConnectionMode: { Loose: 'loose', Strict: 'strict' },
  addEdge: vi.fn(),
  useNodesState: () => [[], vi.fn(), vi.fn()],
  useEdgesState: () => [[], vi.fn(), vi.fn()],
  Panel: vi.fn(),
  Controls: vi.fn(),
  MiniMap: vi.fn(),
  Background: vi.fn(),
  BaseEdge: vi.fn(),
}));

vi.mock('../api', () => ({ PromptInfo: {} }));
vi.mock('../lib/batchUtils', () => ({ getBatchForModule: vi.fn() }));
vi.mock('../components/ModuleNode', () => ({ default: vi.fn() }));
vi.mock('../components/BatchFilterDropdown', () => ({ default: vi.fn() }));
vi.mock('../components/Icon', () => ({
  ChevronDownIcon: vi.fn(),
  ChevronUpIcon: vi.fn(),
  SparklesIcon: vi.fn(),
  DocumentArrowDownIcon: vi.fn(),
  SpinnerIcon: vi.fn(),
}));
vi.mock('../components/Tooltip', () => ({ default: vi.fn() }));

import { getLayoutedElements, buildEdgePath } from '../components/DependencyViewer';

describe('buildEdgePath – smooth curves through waypoints', () => {
  it('uses Q (quadratic bezier) commands instead of L (line) commands', () => {
    const path = buildEdgePath(0, 0, [{ x: 50, y: 50 }], 100, 100);
    expect(path).toContain('Q');
    expect(path).not.toMatch(/\bL\b/);
  });

  it('single waypoint: Q control=waypoint end=target', () => {
    const path = buildEdgePath(0, 0, [{ x: 50, y: 30 }], 100, 60);
    expect(path).toBe('M 0 0 Q 50 30 100 60');
  });

  it('two waypoints: first segment ends at midpoint, second ends at target', () => {
    const path = buildEdgePath(0, 0, [{ x: 40, y: 20 }, { x: 80, y: 40 }], 120, 60);
    // i=1: ctrl={40,20}, end=mid({40,20},{80,40})={60,30}
    // i=2: ctrl={80,40}, end=target={120,60}
    expect(path).toBe('M 0 0 Q 40 20 60 30 Q 80 40 120 60');
  });
});

describe('getLayoutedElements – waypoint edges', () => {
  it('attaches type: waypointEdge and data.waypoints to every edge', () => {
    const nodes = [
      { id: 'A', position: { x: 0, y: 0 }, data: {} },
      { id: 'B', position: { x: 0, y: 100 }, data: {} },
      { id: 'C', position: { x: 0, y: 200 }, data: {} },
    ];
    const edges = [
      { id: 'A->B', source: 'A', target: 'B' },
      { id: 'B->C', source: 'B', target: 'C' },
    ];

    const { edges: layoutedEdges } = getLayoutedElements(nodes as any, edges as any);

    for (const edge of layoutedEdges) {
      expect(edge.type).toBe('waypointEdge');
      expect(Array.isArray((edge as any).data?.waypoints)).toBe(true);
    }
  });
});
