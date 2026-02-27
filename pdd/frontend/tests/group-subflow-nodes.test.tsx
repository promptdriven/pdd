import { render } from '@testing-library/react';
import { vi, describe, it, expect, beforeEach } from 'vitest';
import React from 'react';

// Capture the nodes prop passed to ReactFlow on each render
let capturedNodes: any[] = [];

vi.mock('reactflow', () => ({
  default: ({ nodes }: any) => {
    capturedNodes = nodes ?? [];
    return null;
  },
  MarkerType: { ArrowClosed: 'arrowclosed' },
  BackgroundVariant: { Dots: 'dots' },
  ConnectionMode: { Loose: 'loose', Strict: 'strict' },
  addEdge: vi.fn(),
  useNodesState: (initial: any[]) => [initial, vi.fn(), vi.fn()],
  useEdgesState: (initial: any[]) => [initial, vi.fn(), vi.fn()],
  useViewport: () => ({ zoom: 1, x: 0, y: 0 }),
  Panel: () => null,
  Controls: () => null,
  MiniMap: () => null,
  Background: () => null,
  BaseEdge: () => null,
  getBezierPath: vi.fn(() => ['', 0, 0]),
  Handle: () => null,
  Position: { Top: 'top', Bottom: 'bottom', Left: 'left', Right: 'right' },
}));

vi.mock('../api', () => ({ PromptInfo: {} }));
vi.mock('../lib/batchUtils', () => ({ getBatchForModule: vi.fn(() => undefined) }));
vi.mock('../components/ModuleNode', () => ({ default: () => null, ModuleNodeData: {} }));
vi.mock('../components/GroupNode', () => ({
  default: () => null,
  GROUP_NODE_WIDTH: 220,
  GROUP_NODE_HEIGHT: 56,
}));
vi.mock('../components/BatchFilterDropdown', () => ({ default: () => null }));
vi.mock('../components/Icon', () => ({
  ChevronDownIcon: () => null,
  ChevronUpIcon: () => null,
  SparklesIcon: () => null,
  DocumentArrowDownIcon: () => null,
  SpinnerIcon: () => null,
}));
vi.mock('../components/Tooltip', () => ({ default: () => null }));

import DependencyViewer, { computeGroupLayout } from '../components/DependencyViewer';

const makeModule = (filename: string, group?: string, dependencies: string[] = []) => ({
  filename,
  reason: '',
  description: '',
  dependencies,
  priority: 1,
  filepath: `src/${filename}`,
  tags: [] as string[],
  group,
});

const baseProps = {
  prdContent: '',
  onModuleClick: vi.fn(),
};

describe('DependencyViewer sub-flow nodes (expanded group)', () => {
  beforeEach(() => {
    capturedNodes = [];
    vi.clearAllMocks();
  });

  it('child nodes have parentNode set to group container ID', () => {
    const architecture = [
      makeModule('mod_a.prompt', 'myGroup'),
      makeModule('mod_b.prompt', 'myGroup'),
    ];
    render(
      <DependencyViewer
        {...baseProps}
        architecture={architecture}
        expandedGroups={new Set(['myGroup'])}
      />
    );
    const childA = capturedNodes.find(n => n.id === 'mod_a.prompt');
    const childB = capturedNodes.find(n => n.id === 'mod_b.prompt');
    expect(childA?.parentNode).toBe('__group__myGroup');
    expect(childB?.parentNode).toBe('__group__myGroup');
  });

  it('child nodes have positions relative to container (matching computeGroupLayout)', () => {
    const architecture = [
      makeModule('mod_a.prompt', 'myGroup'),
      makeModule('mod_b.prompt', 'myGroup'),
    ];
    render(
      <DependencyViewer
        {...baseProps}
        architecture={architecture}
        expandedGroups={new Set(['myGroup'])}
      />
    );
    const layout = computeGroupLayout(architecture);
    const childA = capturedNodes.find(n => n.id === 'mod_a.prompt');
    const childB = capturedNodes.find(n => n.id === 'mod_b.prompt');
    expect(childA?.position).toEqual({ x: layout.childPositions[0].x, y: layout.childPositions[0].y });
    expect(childB?.position).toEqual({ x: layout.childPositions[1].x, y: layout.childPositions[1].y });
  });

  it('child nodes have draggable: false', () => {
    const architecture = [
      makeModule('mod_a.prompt', 'myGroup'),
      makeModule('mod_b.prompt', 'myGroup'),
    ];
    render(
      <DependencyViewer
        {...baseProps}
        architecture={architecture}
        expandedGroups={new Set(['myGroup'])}
      />
    );
    const childA = capturedNodes.find(n => n.id === 'mod_a.prompt');
    expect(childA?.draggable).toBe(false);
  });

  it('group container node has style.width = computeGroupLayout containerW', () => {
    const architecture = [
      makeModule('mod_a.prompt', 'myGroup'),
      makeModule('mod_b.prompt', 'myGroup'),
    ];
    render(
      <DependencyViewer
        {...baseProps}
        architecture={architecture}
        expandedGroups={new Set(['myGroup'])}
      />
    );
    const { containerW } = computeGroupLayout(architecture);
    const groupNode = capturedNodes.find(n => n.id === '__group__myGroup');
    expect(groupNode?.style?.width).toBe(containerW);
  });

  it('group container node has style.height = computeGroupLayout containerH', () => {
    const architecture = [
      makeModule('mod_a.prompt', 'myGroup'),
      makeModule('mod_b.prompt', 'myGroup'),
    ];
    render(
      <DependencyViewer
        {...baseProps}
        architecture={architecture}
        expandedGroups={new Set(['myGroup'])}
      />
    );
    const { containerH } = computeGroupLayout(architecture);
    const groupNode = capturedNodes.find(n => n.id === '__group__myGroup');
    expect(groupNode?.style?.height).toBe(containerH);
  });

  it('no __bg__ nodes are present in initialNodes', () => {
    const architecture = [
      makeModule('mod_a.prompt', 'myGroup'),
      makeModule('mod_b.prompt', 'myGroup'),
    ];
    render(
      <DependencyViewer
        {...baseProps}
        architecture={architecture}
        expandedGroups={new Set(['myGroup'])}
      />
    );
    const bgNodes = capturedNodes.filter(n => n.id.startsWith('__bg__'));
    expect(bgNodes).toHaveLength(0);
  });

  it('collapsed group children are absent from nodes entirely', () => {
    const architecture = [
      makeModule('mod_a.prompt', 'myGroup'),
      makeModule('mod_b.prompt', 'myGroup'),
    ];
    // Render with empty expandedGroups (collapsed)
    render(
      <DependencyViewer
        {...baseProps}
        architecture={architecture}
        expandedGroups={new Set()}
      />
    );
    // Children should not appear in nodes at all
    const childA = capturedNodes.find(n => n.id === 'mod_a.prompt');
    const childB = capturedNodes.find(n => n.id === 'mod_b.prompt');
    expect(childA).toBeUndefined();
    expect(childB).toBeUndefined();
    // Only the group container should be present
    const groupNode = capturedNodes.find(n => n.id === '__group__myGroup');
    expect(groupNode).toBeDefined();
  });

  it('ungrouped module nodes have no parentNode', () => {
    const architecture = [
      makeModule('mod_a.prompt', 'myGroup'),
      makeModule('mod_b.prompt', 'myGroup'),
      makeModule('standalone.prompt'), // no group
    ];
    render(
      <DependencyViewer
        {...baseProps}
        architecture={architecture}
        expandedGroups={new Set(['myGroup'])}
      />
    );
    const standalone = capturedNodes.find(n => n.id === 'standalone.prompt');
    expect(standalone).toBeDefined();
    expect(standalone?.parentNode).toBeUndefined();
  });

  it('child nodes of expanded group have extent: "parent"', () => {
    const architecture = [makeModule('mod_a.prompt', 'myGroup')];
    render(
      <DependencyViewer
        {...baseProps}
        architecture={architecture}
        expandedGroups={new Set(['myGroup'])}
      />
    );
    const childA = capturedNodes.find(n => n.id === 'mod_a.prompt');
    expect(childA?.extent).toBe('parent');
  });
});
