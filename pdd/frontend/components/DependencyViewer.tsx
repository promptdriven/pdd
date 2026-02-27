import React, { useMemo, useState, useCallback, useEffect, useRef } from 'react';
import ReactFlow, {
  Node,
  Edge,
  Controls,
  MiniMap,
  Background,
  useNodesState,
  useEdgesState,
  NodeTypes,
  BackgroundVariant,
  Panel,
  Connection,
  ConnectionMode,
  addEdge,
  MarkerType,
  EdgeProps,
  BaseEdge,
  getBezierPath,
  Viewport,
  useViewport,
} from 'reactflow';
import dagre from 'dagre';
import 'reactflow/dist/style.css';

import { ArchitectureModule, PromptInfo } from '../api';
import { ChevronDownIcon, ChevronUpIcon, SparklesIcon, DocumentArrowDownIcon, SpinnerIcon } from './Icon';
import Tooltip from './Tooltip';
import ModuleNode, { ModuleNodeData } from './ModuleNode';
import GroupNode, { GroupNodeData, GROUP_NODE_WIDTH } from './GroupNode';
import BatchFilterDropdown from './BatchFilterDropdown';
import type { Batch } from '../lib/batchUtils';
import { getBatchForModule } from '../lib/batchUtils';

const NODE_WIDTH = 200;
const NODE_HEIGHT = 85;

const HEADER_HEIGHT = 56;
const INNER_PAD = 20;
const CHILD_GAP = 16;
const CHILD_COLS = 2;

export function computeGroupLayout(children: ArchitectureModule[]) {
  const cols = Math.min(children.length, CHILD_COLS);
  const rows = Math.ceil(children.length / cols);
  const containerW = INNER_PAD * 2 + cols * (NODE_WIDTH + CHILD_GAP) - CHILD_GAP;
  const containerH = HEADER_HEIGHT + INNER_PAD * 2 + rows * (NODE_HEIGHT + CHILD_GAP) - CHILD_GAP;
  const childPositions = children.map((m, i) => ({
    filename: m.filename,
    x: INNER_PAD + (i % cols) * (NODE_WIDTH + CHILD_GAP),
    y: HEADER_HEIGHT + INNER_PAD + Math.floor(i / cols) * (NODE_HEIGHT + CHILD_GAP),
  }));
  return { containerW, containerH, childPositions };
}

// Pure math helper that mirrors the CSS expression used in compact nodes:
//   font-size: calc(14px / var(--vp-zoom, 1))
// React Flow scales the viewport with transform:scale(zoom), so a node-space
// font of (14/zoom)px always APPEARS as 14px on screen regardless of zoom.
// No capping — CSS truncate handles overflow at extreme zoom levels.
export function getCompactFontPx(zoom: number): number {
  return Math.round(14 / zoom);
}

// VpZoomSync keeps the CSS custom property --vp-zoom on a target element in
// sync with the current React Flow viewport zoom. It must be rendered as a
// direct child of <ReactFlow> so it can access the viewport context via
// useViewport().
//
// Unlike onMove (which only fires on user interaction), useViewport() is
// reactive to ALL viewport changes — including programmatic ones like fitView
// on initial load. This ensures compact-node font sizes are correct from the
// very first frame, not just after the user pans or zooms.
export const VpZoomSync: React.FC<{ target: HTMLElement | null }> = ({ target }) => {
  const { zoom } = useViewport();
  useEffect(() => {
    target?.style.setProperty('--vp-zoom', String(zoom));
  }, [zoom, target]);
  return null;
};

interface DependencyViewerProps {
  architecture: ArchitectureModule[];
  prdContent: string;
  appName?: string;
  onModuleClick: (module: ArchitectureModule) => void;
  onRunSync?: (module: ArchitectureModule) => void;  // Run pdd sync command for a module
  onGeneratePrompts?: () => void;
  isGeneratingPrompts?: boolean;
  existingPrompts?: Set<string>;
  promptsInfo?: PromptInfo[];
  // Edit mode props
  editMode?: boolean;
  onModuleEdit?: (module: ArchitectureModule) => void;
  onModuleDelete?: (filename: string) => void;
  onDependencyAdd?: (targetFilename: string, sourceFilename: string) => void;
  onDependencyRemove?: (targetFilename: string, sourceFilename: string) => void;
  onPositionsChange?: (positions: Map<string, { x: number; y: number }>) => void;
  highlightedModules?: Set<string>;  // For error highlighting
  // Callback when Dagre calculates initial positions (for auto-saving)
  onInitialPositionsCalculated?: (positions: Map<string, { x: number; y: number }>) => void;
  // Batch (connected component) filtering props
  batches?: Batch[];
  selectedBatch?: Batch | null;
  onBatchSelect?: (batch: Batch | null) => void;
  onSyncBatch?: (batch: Batch) => void;
  remainingCountByBatch?: Map<number, number>;
  rearrangeVersion?: number;
  // Group collapse/expand props
  expandedGroups?: Set<string>;
  onToggleGroup?: (groupName: string) => void;
  onEditGroup?: (groupName: string) => void;
}

// Determine category based on tags
const getCategory = (module: ArchitectureModule): 'frontend' | 'backend' | 'shared' => {
  const tags = module.tags || [];
  const frontendTags = ['frontend', 'react', 'nextjs', 'ui', 'page', 'component', 'css', 'html'];
  const backendTags = ['backend', 'api', 'database', 'sqlalchemy', 'fastapi', 'python', 'server'];

  if (tags.some(t => frontendTags.includes(t.toLowerCase()))) return 'frontend';
  if (tags.some(t => backendTags.includes(t.toLowerCase()))) return 'backend';
  return 'shared';
};

// Get color classes based on category
const getCategoryColors = (category: 'frontend' | 'backend' | 'shared') => {
  switch (category) {
    case 'frontend':
      return {
        bg: 'bg-orange-500/20',
        border: 'border-orange-500/50',
        hover: 'hover:border-orange-400',
        text: 'text-orange-300',
      };
    case 'backend':
      return {
        bg: 'bg-blue-500/20',
        border: 'border-blue-500/50',
        hover: 'hover:border-blue-400',
        text: 'text-blue-300',
      };
    default:
      return {
        bg: 'bg-green-500/20',
        border: 'border-green-500/50',
        hover: 'hover:border-green-400',
        text: 'text-green-300',
      };
  }
};

// Dagre layout algorithm
// layoutOnlyEdges: edges added to Dagre for layout but not returned in output (e.g., group→child virtual edges)
export const getLayoutedElements = (
  nodes: Node<ModuleNodeData | GroupNodeData>[],
  edges: Edge[],
  direction: 'TB' | 'LR' = 'TB',
  layoutOnlyEdges: { source: string; target: string }[] = []
) => {
  const g = new dagre.graphlib.Graph();
  g.setGraph({ rankdir: direction, nodesep: 80, ranksep: 150, edgesep: 20 });
  g.setDefaultEdgeLabel(() => ({}));

  nodes.forEach((node) => {
    const w = (node.style as any)?.width ?? NODE_WIDTH;
    const h = (node.style as any)?.height ?? NODE_HEIGHT;
    g.setNode(node.id, { width: w, height: h });
  });

  edges.forEach((edge) => {
    g.setEdge(edge.source, edge.target);
  });

  layoutOnlyEdges.forEach((edge) => {
    if (g.hasNode(edge.source) && g.hasNode(edge.target)) {
      g.setEdge(edge.source, edge.target);
    }
  });

  dagre.layout(g);

  const layoutedNodes = nodes.map((node) => {
    const nodeWithPosition = g.node(node.id);
    const w = (node.style as any)?.width ?? NODE_WIDTH;
    const h = (node.style as any)?.height ?? NODE_HEIGHT;
    return {
      ...node,
      position: {
        x: nodeWithPosition.x - w / 2,
        y: nodeWithPosition.y - h / 2,
      },
    };
  });

  const layoutedEdges = edges.map((edge) => {
    const dagreEdge = g.edge({ v: edge.source, w: edge.target });
    return {
      ...edge,
      type: 'waypointEdge',
      data: { ...edge.data, waypoints: dagreEdge?.points ?? [] },
    };
  });

  return { nodes: layoutedNodes, edges: layoutedEdges };
};

// Pure path builder for smooth quadratic-bezier spline through Dagre waypoints.
// Each waypoint is a quadratic control point; the endpoint of each segment is
// the midpoint to the next waypoint (C1 continuity — no sharp corners).
// The final segment terminates at the actual target position.
export function buildEdgePath(
  sourceX: number,
  sourceY: number,
  waypoints: { x: number; y: number }[],
  targetX: number,
  targetY: number,
): string {
  const all = [{ x: sourceX, y: sourceY }, ...waypoints, { x: targetX, y: targetY }];
  const parts: string[] = [`M ${all[0].x} ${all[0].y}`];
  for (let i = 1; i < all.length - 1; i++) {
    const ctrl = all[i];
    const isLast = i === all.length - 2;
    const end = isLast
      ? all[all.length - 1]
      : { x: (all[i].x + all[i + 1].x) / 2, y: (all[i].y + all[i + 1].y) / 2 };
    parts.push(`Q ${ctrl.x} ${ctrl.y} ${end.x} ${end.y}`);
  }
  return parts.join(' ');
}

// Custom edge type that follows Dagre waypoints with smooth curves
const WaypointEdge: React.FC<EdgeProps> = ({
  id, sourceX, sourceY, sourcePosition, targetX, targetY, targetPosition, data, markerEnd, style,
}) => {
  const pts: { x: number; y: number }[] = data?.waypoints ?? [];
  const pathD = pts.length === 0
    // No waypoints — use ReactFlow's bezier for a natural swooping curve
    ? getBezierPath({ sourceX, sourceY, sourcePosition, targetX, targetY, targetPosition })[0]
    : buildEdgePath(sourceX, sourceY, pts, targetX, targetY);
  return <BaseEdge id={id} path={pathD} markerEnd={markerEnd} style={style} />;
};

// Custom node types
const nodeTypes: NodeTypes = {
  moduleNode: ModuleNode,
  groupNode: GroupNode,
};

const edgeTypes = { waypointEdge: WaypointEdge };

const DependencyViewer: React.FC<DependencyViewerProps> = ({
  architecture,
  prdContent,
  appName,
  onModuleClick,
  onRunSync,
  onGeneratePrompts,
  isGeneratingPrompts = false,
  existingPrompts = new Set<string>(),
  promptsInfo = [],
  editMode = false,
  onModuleEdit,
  onModuleDelete,
  onDependencyAdd,
  onDependencyRemove,
  onPositionsChange,
  highlightedModules = new Set(),
  onInitialPositionsCalculated,
  batches = [],
  selectedBatch = null,
  onBatchSelect,
  onSyncBatch,
  remainingCountByBatch = new Map(),
  rearrangeVersion,
  expandedGroups = new Set(),
  onToggleGroup,
  onEditGroup,
}) => {
  const [isPrdVisible, setIsPrdVisible] = useState(false);
  const [contextMenu, setContextMenu] = useState<{
    x: number;
    y: number;
    edge: Edge;
  } | null>(null);

  // Focus mode: clicking a node dims nodes not in its 1-2 hop neighborhood
  const [focusedModule, setFocusedModule] = useState<string | null>(null);

  // Compute the 1-hop neighborhood of the focused module (both in and out edges)
  const focusNeighborhood = useMemo(() => {
    if (!focusedModule) return null;
    const neighborhood = new Set<string>();
    neighborhood.add(focusedModule);
    // Direct dependencies (1 hop out)
    const focused = architecture.find(m => m.filename === focusedModule);
    if (focused) {
      focused.dependencies.forEach(dep => neighborhood.add(dep));
    }
    // Modules that depend on focused (1 hop in)
    architecture.forEach(m => {
      if (m.dependencies.includes(focusedModule)) neighborhood.add(m.filename);
    });
    return neighborhood;
  }, [focusedModule, architecture]);

  // Auto-clear focus mode when the focused module's group becomes collapsed
  // (all visible nodes would appear dimmed otherwise)
  useEffect(() => {
    if (!focusedModule) return;
    const focusedMod = architecture.find(m => m.filename === focusedModule);
    if (focusedMod?.group && !expandedGroups.has(focusedMod.group)) {
      setFocusedModule(null);
    }
  }, [expandedGroups, focusedModule, architecture]);

  // Create a lookup map from module filename to PromptInfo for file tracking
  const promptInfoMap = useMemo(() => {
    const map = new Map<string, PromptInfo>();
    for (const p of promptsInfo) {
      const filename = p.prompt.split('/').pop() || '';
      map.set(filename, p);
    }
    return map;
  }, [promptsInfo]);

  // Pre-compute position status for reuse across useMemo and useEffect
  // Groups always need Dagre (synthetic group nodes have no saved positions)
  const allHavePositions = useMemo(
    () => !architecture.some(m => m.group) && architecture.every((m) => m.position),
    [architecture]
  );

  // Convert architecture to React Flow nodes and edges, with group support
  const { initialNodes, initialEdges } = useMemo(() => {
    // --- Group computation ---
    const groupMap = new Map<string, ArchitectureModule[]>();
    for (const m of architecture) {
      if (m.group) {
        const existing = groupMap.get(m.group) || [];
        existing.push(m);
        groupMap.set(m.group, existing);
      }
    }

    // Modules hidden because their group is collapsed
    const collapsedGroupChildren = new Set<string>();
    for (const [gName, children] of groupMap.entries()) {
      if (!expandedGroups.has(gName)) {
        children.forEach(m => collapsedGroupChildren.add(m.filename));
      }
    }

    // Modules that are visible (not hidden by collapsed groups)
    const visibleModules = architecture.filter(m => !collapsedGroupChildren.has(m.filename));

    const hasGroups = groupMap.size > 0;
    const noneHavePositions = visibleModules.every((m) => !m.position);

    // Build O(1) lookup map for group assignments
    const moduleGroupMap = new Map(architecture.map(m => [m.filename, m.group]));

    // Helper: map a module filename to its effective node ID (group node when collapsed)
    const getEffectiveId = (filename: string): string => {
      if (collapsedGroupChildren.has(filename)) {
        const group = moduleGroupMap.get(filename);
        if (group) return `__group__${group}`;
      }
      return filename;
    };

    // Pre-compute layout for each expanded group
    const groupLayouts = new Map<string, ReturnType<typeof computeGroupLayout>>();
    for (const [gName, children] of groupMap.entries()) {
      if (expandedGroups.has(gName)) {
        groupLayouts.set(gName, computeGroupLayout(children));
      }
    }

    // --- Build module nodes ---
    const moduleNodes: Node<ModuleNodeData>[] = visibleModules.map((m) => {
      const category = getCategory(m);
      const hasPrompt = existingPrompts.has(m.filename);
      const isHighlighted = highlightedModules.has(m.filename);
      const isDimmed = focusNeighborhood !== null && !focusNeighborhood.has(m.filename);
      const batch = getBatchForModule(m.filename, batches);

      const parentGroupName = m.group && expandedGroups.has(m.group) ? m.group : undefined;
      const layout = parentGroupName ? groupLayouts.get(parentGroupName) : undefined;
      const childPos = layout?.childPositions.find(p => p.filename === m.filename);

      return {
        id: m.filename,
        type: 'moduleNode',
        parentNode: parentGroupName ? `__group__${parentGroupName}` : undefined,
        extent: parentGroupName ? ('parent' as const) : undefined,
        draggable: parentGroupName ? false : undefined,
        zIndex: parentGroupName ? 10 : undefined,
        position: childPos ? { x: childPos.x, y: childPos.y } : (m.position || { x: 0, y: 0 }),
        data: {
          label: m.filename.replace(/_[A-Za-z]+\.prompt$/, '').replace(/\.prompt$/, ''),
          module: m,
          promptInfo: promptInfoMap.get(m.filename),
          hasPrompt,
          colors: getCategoryColors(category),
          onClick: (mod: ArchitectureModule) => {
            if (!editMode) {
              setFocusedModule(prev => prev === mod.filename ? null : mod.filename);
            }
            onModuleClick(mod);
          },
          onRunSync: onRunSync,
          editMode,
          onEdit: onModuleEdit,
          onDelete: onModuleDelete,
          isHighlighted,
          isDimmed,
          batchId: batch?.id,
          batchColor: batch?.color,
          batchName: batch?.name,
        },
      };
    });

    // --- Build group nodes ---
    const groupNodes: Node<GroupNodeData>[] = [];
    for (const [gName, children] of groupMap.entries()) {
      const isExpanded = expandedGroups.has(gName);
      // Group is dimmed if it has no members in focus neighborhood
      const isDimmedGroup = focusNeighborhood !== null
        && !children.some(c => focusNeighborhood.has(c.filename));
      const layout = groupLayouts.get(gName);
      groupNodes.push({
        id: `__group__${gName}`,
        type: 'groupNode',
        zIndex: isExpanded ? 0 : 10,
        position: { x: 0, y: 0 },
        style: isExpanded
          ? { width: layout?.containerW ?? GROUP_NODE_WIDTH,
              height: layout?.containerH ?? HEADER_HEIGHT,
              opacity: isDimmedGroup ? 0.25 : 1 }
          : { width: 200, minHeight: 85, opacity: isDimmedGroup ? 0.25 : 1 },
        data: {
          groupName: gName,
          modules: children,
          isExpanded,
          onToggle: onToggleGroup || (() => {}),
          existingPrompts,
          editMode,
          onEditGroup,
          containerW: layout?.containerW,
          containerH: layout?.containerH,
        },
      });
    }

    const allNodes: Node<ModuleNodeData | GroupNodeData>[] = [...moduleNodes, ...groupNodes];

    // --- Build edges with rerouting for collapsed groups ---
    const visibleNodeIds = new Set(allNodes.map(n => n.id));
    const edgeSet = new Set<string>();
    const edges: Edge[] = [];

    for (const m of architecture) {
      for (const dep of m.dependencies) {
        const targetId = getEffectiveId(m.filename);
        const sourceId = getEffectiveId(dep);

        if (targetId === sourceId) continue; // skip self-edges after rerouting
        if (!visibleNodeIds.has(sourceId) || !visibleNodeIds.has(targetId)) continue;

        const edgeId = `${sourceId}->${targetId}`;
        if (edgeSet.has(edgeId)) continue;
        edgeSet.add(edgeId);

        const isGroupEdge = sourceId.startsWith('__group__') || targetId.startsWith('__group__');
        edges.push({
          id: edgeId,
          source: sourceId,
          target: targetId,
          type: 'waypointEdge',
          style: { stroke: '#60a5fa', strokeWidth: 2 },
          markerEnd: {
            type: MarkerType.ArrowClosed,
            color: '#60a5fa',
            width: 20,
            height: 20,
          },
          animated: false,
          deletable: editMode && !isGroupEdge,
          interactionWidth: 20,
        } as Edge);
      }
    }

    // --- Position handling ---
    // When no groups and all modules have saved positions → skip Dagre
    if (!hasGroups && !noneHavePositions && allHavePositions) {
      return { initialNodes: allNodes, initialEdges: edges };
    }

    // Separate top-level nodes (go into Dagre) from child nodes (inside expanded group containers)
    const topLevelNodes = allNodes.filter(n => !n.parentNode);
    const childNodes = allNodes.filter(n => n.parentNode);

    // Run Dagre layout on top-level nodes only (children have pre-computed relative positions)
    const layouted = getLayoutedElements(topLevelNodes, edges, 'TB');

    let positionedTopLevelNodes: Node<ModuleNodeData | GroupNodeData>[];
    if (!noneHavePositions) {
      // Hybrid: use Dagre positions but override top-level module nodes with saved positions
      const savedPositions = new Map(
        visibleModules
          .filter((m) => m.position && !(m.group && expandedGroups.has(m.group)))
          .map((m) => [m.filename, m.position!])
      );
      positionedTopLevelNodes = layouted.nodes.map((node) => {
        const savedPos = savedPositions.get(node.id);
        return savedPos ? { ...node, position: savedPos } : node;
      });
    } else {
      positionedTopLevelNodes = layouted.nodes;
    }

    return { initialNodes: [...positionedTopLevelNodes, ...childNodes], initialEdges: layouted.edges };
  }, [
    architecture, existingPrompts, promptInfoMap, onModuleClick, onRunSync,
    editMode, onModuleEdit, onModuleDelete, highlightedModules, batches,
    expandedGroups, onToggleGroup, onEditGroup, focusNeighborhood, allHavePositions,
  ]);

  const [nodes, setNodes, onNodesChange] = useNodesState(initialNodes);
  const [edges, setEdges, onEdgesChange] = useEdgesState(initialEdges);

  // Track the graph wrapper div via useState (not useRef) so that DependencyViewer
  // re-renders after the div mounts. This guarantees VpZoomSync receives a non-null
  // target before React Flow's fitView fires its useEffect, ensuring --vp-zoom is
  // set correctly on initial load (not just after user pan/zoom).
  const [graphContainer, setGraphContainer] = useState<HTMLDivElement | null>(null);

  // Belt-and-suspenders: also update --vp-zoom on every user pan/zoom via onMove.
  // VpZoomSync (inside <ReactFlow>) handles fitView and programmatic changes;
  // onMove catches any edge cases where the store subscription may lag.
  const handleMove = useCallback((_: MouseEvent | TouchEvent | null, vp: Viewport) => {
    graphContainer?.style.setProperty('--vp-zoom', String(vp.zoom));
  }, [graphContainer]);

  // Track previous editMode to detect when entering edit mode
  const prevEditModeRef = useRef(editMode);

  // Persist ALL current positions when entering edit mode
  // This ensures Dagre-calculated positions are captured before any edits
  useEffect(() => {
    const wasNotEditing = !prevEditModeRef.current;
    const nowEditing = editMode;
    prevEditModeRef.current = editMode;

    // Only fire when transitioning from non-edit to edit mode
    if (wasNotEditing && nowEditing && onPositionsChange && nodes.length > 0) {
      const positions = new Map<string, { x: number; y: number }>();
      nodes.forEach((n) => {
        // Exclude synthetic group nodes and child nodes (relative positions) from position saving
        if (!n.id.startsWith('__group__') && !n.parentNode) {
          positions.set(n.id, { x: n.position.x, y: n.position.y });
        }
      });
      onPositionsChange(positions);
    }
  }, [editMode, nodes, onPositionsChange]);

  // Track whether we've already fired the initial positions callback
  const initialPositionsCalledRef = useRef(false);

  // Fire callback when Dagre calculates initial positions (for modules without saved positions)
  // This allows the parent to auto-save positions even before entering edit mode
  useEffect(() => {
    // Only fire once per component mount, when we have nodes and the callback is provided
    if (
      !initialPositionsCalledRef.current &&
      onInitialPositionsCalculated &&
      nodes.length > 0 &&
      // Only fire if Dagre was applied (i.e., not all modules had saved positions)
      !allHavePositions
    ) {
      initialPositionsCalledRef.current = true;
      const positions = new Map<string, { x: number; y: number }>();
      nodes.forEach((n) => {
        // Only report positions for real top-level module nodes (not synthetic group nodes or children)
        if (!n.id.startsWith('__group__') && !n.parentNode) {
          positions.set(n.id, { x: n.position.x, y: n.position.y });
        }
      });
      onInitialPositionsCalculated(positions);
    }
  }, [nodes, allHavePositions, onInitialPositionsCalculated]);

  // Re-layout when clicking the layout button
  const handleRelayout = useCallback(() => {
    const dagreNodes = nodes.filter(n => !n.parentNode);
    const childNodes = nodes.filter(n => n.parentNode);
    const layouted = getLayoutedElements(dagreNodes, edges, 'TB');
    setNodes([...layouted.nodes, ...childNodes]);
    setEdges(layouted.edges);
    // Persist the new Dagre positions if in edit mode (top-level module nodes only)
    if (editMode && onPositionsChange) {
      const positions = new Map<string, { x: number; y: number }>();
      layouted.nodes.forEach((n) => {
        if (!n.id.startsWith('__group__') && !n.parentNode) {
          positions.set(n.id, { x: n.position.x, y: n.position.y });
        }
      });
      onPositionsChange(positions);
    }
  }, [nodes, edges, setNodes, setEdges, editMode, onPositionsChange]);

  // Handle edge creation (dependency added)
  const handleConnect = useCallback(
    (connection: Connection) => {
      if (!editMode || !connection.source || !connection.target) return;
      // Skip connections involving group nodes
      if (connection.source.startsWith('__group__') || connection.target.startsWith('__group__')) return;
      // In our architecture: source = dependency (what is being used)
      // target = the module that depends on source
      // So we add source to target's dependencies
      onDependencyAdd?.(connection.target, connection.source);
      // Add edge visually
      setEdges((eds) =>
        addEdge(
          {
            ...connection,
            id: `${connection.source}->${connection.target}`,
            type: 'waypointEdge',
            style: { stroke: '#60a5fa', strokeWidth: 2 },
            markerEnd: {
              type: MarkerType.ArrowClosed,
              color: '#60a5fa',
              width: 20,
              height: 20,
            },
            animated: false,
          },
          eds
        )
      );
    },
    [editMode, onDependencyAdd, setEdges]
  );

  // Handle edge deletion (dependency removed) — skip group-node edges
  const handleEdgesDelete = useCallback(
    (deletedEdges: Edge[]) => {
      if (!editMode) return;
      for (const edge of deletedEdges) {
        if (edge.source.startsWith('__group__') || edge.target.startsWith('__group__')) continue;
        // edge.source = dependency, edge.target = dependent module
        onDependencyRemove?.(edge.target, edge.source);
      }
    },
    [editMode, onDependencyRemove]
  );

  // Handle edge click to ensure proper selection
  const handleEdgeClick = useCallback(
    (_event: React.MouseEvent, edge: Edge) => {
      if (!editMode) return;
      // Close context menu if open
      setContextMenu(null);
      // Explicitly set the clicked edge as selected with different styling
      setEdges((eds) =>
        eds.map((e) => ({
          ...e,
          selected: e.id === edge.id,
          style: {
            ...e.style,
            stroke: e.id === edge.id ? '#ef4444' : '#60a5fa', // Red when selected
            strokeWidth: e.id === edge.id ? 3 : 2,
          },
          markerEnd: e.markerEnd ? {
            ...e.markerEnd,
            color: e.id === edge.id ? '#ef4444' : '#60a5fa',
          } : undefined,
        }))
      );
    },
    [editMode, setEdges]
  );

  // Handle edge right-click (context menu)
  const handleEdgeContextMenu = useCallback(
    (event: React.MouseEvent, edge: Edge) => {
      if (!editMode) return;
      event.preventDefault();
      setContextMenu({
        x: event.clientX,
        y: event.clientY,
        edge,
      });
    },
    [editMode]
  );

  // Handle deleting edge from context menu
  const handleDeleteEdgeFromMenu = useCallback(() => {
    if (!contextMenu) return;
    const edge = contextMenu.edge;
    // Remove from data
    onDependencyRemove?.(edge.target, edge.source);
    // Remove from visual edges
    setEdges((eds) => eds.filter((e) => e.id !== edge.id));
    setContextMenu(null);
  }, [contextMenu, onDependencyRemove, setEdges]);

  // Close context menu and clear focus mode when clicking pane background
  const handlePaneClick = useCallback(() => {
    setContextMenu(null);
    setFocusedModule(null);
  }, []);

  // Handle node deletion (module removed) — skip synthetic group nodes and child nodes
  const handleNodesDelete = useCallback(
    (deletedNodes: Node[]) => {
      if (!editMode) return;
      for (const node of deletedNodes) {
        if (!node.id.startsWith('__group__') && !node.parentNode) {
          onModuleDelete?.(node.id);
        }
      }
    },
    [editMode, onModuleDelete]
  );

  // Handle node drag end to save ALL positions (so they're all captured for saving)
  const handleNodeDragStop = useCallback(
    (_event: React.MouseEvent, _node: Node, allNodes: Node[]) => {
      if (!editMode) return;
      // Send all top-level node positions to parent, excluding synthetic group nodes and children
      const positions = new Map<string, { x: number; y: number }>();
      allNodes.forEach((n) => {
        if (!n.id.startsWith('__group__') && !n.parentNode) {
          positions.set(n.id, { x: n.position.x, y: n.position.y });
        }
      });
      onPositionsChange?.(positions);
    },
    [editMode, onPositionsChange]
  );

  // Track previous architecture to detect structural changes (not just position changes)
  const prevArchitectureRef = React.useRef<ArchitectureModule[]>(architecture);

  // Track previous rearrangeVersion to detect when a re-arrange has completed
  const prevRearrangeVersionRef = useRef(rearrangeVersion ?? 0);

  // Track previous expandedGroups to detect group expand/collapse changes
  const prevExpandedGroupsRef = useRef(expandedGroups);

  // Helper to check if architecture structure changed (ignoring positions)
  const getStructuralFingerprint = useCallback((modules: ArchitectureModule[]) => {
    return modules.map(m => ({
      filename: m.filename,
      dependencies: [...m.dependencies].sort().join(','),
      group: m.group || '',
    })).sort((a, b) => a.filename.localeCompare(b.filename))
      .map(m => `${m.filename}:${m.dependencies}:${m.group}`).join('|');
  }, []);

  // Update nodes/edges when architecture STRUCTURE changes (not just positions)
  React.useEffect(() => {
    const rearrangeVersionChanged =
      rearrangeVersion !== undefined &&
      rearrangeVersion !== prevRearrangeVersionRef.current;
    prevRearrangeVersionRef.current = rearrangeVersion ?? 0;

    const prevFingerprint = getStructuralFingerprint(prevArchitectureRef.current);
    const currentFingerprint = getStructuralFingerprint(architecture);
    const structureChanged = prevFingerprint !== currentFingerprint;

    prevArchitectureRef.current = architecture;

    const expandedGroupsChanged = prevExpandedGroupsRef.current !== expandedGroups;
    prevExpandedGroupsRef.current = expandedGroups;

    // Only sync if:
    // 1) Structure changed (modules added/removed, dependencies changed)
    // 2) Not in edit mode (initial load or exiting edit mode)
    // 3) Re-arrange completed (positions updated by agent)
    // 4) Group expand/collapse state changed
    if (structureChanged || !editMode || rearrangeVersionChanged || expandedGroupsChanged) {
      setNodes(initialNodes);
      setEdges(initialEdges);
    }
  }, [initialNodes, initialEdges, setNodes, setEdges, editMode, architecture, getStructuralFingerprint, rearrangeVersion, expandedGroups]);

  return (
    <div className="glass rounded-xl border border-surface-700/50 overflow-hidden h-full flex flex-col">
      {/* PRD Viewer Header */}
      <div className="bg-surface-800/80 border-b border-surface-700/50 flex-shrink-0">
        <div className="flex justify-between items-center p-3">
          <div
            className="flex-1 min-w-0 cursor-pointer"
            onClick={() => setIsPrdVisible(!isPrdVisible)}
          >
            <h3 className="font-semibold text-sm text-white">
              {appName || 'Product Requirements Document'}
            </h3>
            <p className="text-xs text-surface-400">
              {architecture.length} modules
              {focusedModule && <span className="text-violet-400 ml-2">· focus: {focusedModule.replace(/\.prompt$/, '')}</span>}
            </p>
          </div>
          <div className="flex items-center gap-2 flex-shrink-0 ml-4">
            <Tooltip content={isPrdVisible ? 'Collapse' : 'Expand'}>
              <button
                onClick={() => setIsPrdVisible(!isPrdVisible)}
                className="p-1.5 rounded-lg hover:bg-surface-700 transition-colors"
              >
                {isPrdVisible ? (
                  <ChevronUpIcon className="w-4 h-4 text-surface-400" />
                ) : (
                  <ChevronDownIcon className="w-4 h-4 text-surface-400" />
                )}
              </button>
            </Tooltip>
          </div>
        </div>

        {isPrdVisible && (
          <div className="border-t border-surface-700/50">
            <pre className="p-3 text-xs text-surface-300 whitespace-pre-wrap overflow-auto max-h-[200px] font-mono">
              {prdContent || 'No PRD content available'}
            </pre>
          </div>
        )}
      </div>

      {/* React Flow Graph - edges render behind nodes via CSS */}
      {/* --vp-zoom is written here; VpZoomSync inside <ReactFlow> keeps it current */}
      <div
        ref={setGraphContainer}
        className="flex-1 min-h-0 [&_.react-flow__edges]:z-0 [&_.react-flow__nodes]:z-10"
        style={{ '--vp-zoom': '1' } as React.CSSProperties}
      >
        <ReactFlow
          nodes={nodes}
          edges={edges}
          onNodesChange={onNodesChange}
          onEdgesChange={onEdgesChange}
          onConnect={editMode ? handleConnect : undefined}
          onEdgeClick={editMode ? handleEdgeClick : undefined}
          onEdgeContextMenu={editMode ? handleEdgeContextMenu : undefined}
          onMove={handleMove}
          onPaneClick={handlePaneClick}
          onNodeDragStop={editMode ? handleNodeDragStop : undefined}
          onEdgesDelete={editMode ? handleEdgesDelete : undefined}
          onNodesDelete={editMode ? handleNodesDelete : undefined}
          nodeTypes={nodeTypes}
          edgeTypes={edgeTypes}
          fitView
          fitViewOptions={{ padding: 0.2 }}
          minZoom={0.1}
          maxZoom={2}
          defaultEdgeOptions={{
            style: { stroke: '#60a5fa', strokeWidth: 2 },
            type: 'waypointEdge',
            markerEnd: {
              type: MarkerType.ArrowClosed,
              color: '#60a5fa',
              width: 20,
              height: 20,
            },
            interactionWidth: 20,
          }}
          connectionMode={editMode ? ConnectionMode.Loose : ConnectionMode.Strict}
          deleteKeyCode={editMode ? ['Backspace', 'Delete'] : null}
          edgesUpdatable={editMode}
          edgesFocusable={editMode}
          elementsSelectable={editMode}
          selectNodesOnDrag={false}
          proOptions={{ hideAttribution: true }}
        >
          {/* VpZoomSync lives inside <ReactFlow> so it can access useViewport().
              It fires for ALL viewport changes (including fitView on initial load),
              unlike onMove which only fires on user interaction. */}
          <VpZoomSync target={graphContainer} />
          <Background variant={BackgroundVariant.Dots} gap={20} size={1} color="#374151" />
          <Controls
            className="!bg-surface-800 !border-surface-700 !rounded-lg [&>button]:!bg-surface-700 [&>button]:!border-surface-600 [&>button]:!text-surface-300 [&>button:hover]:!bg-surface-600"
          />
          <MiniMap
            className="!bg-surface-800 !border-surface-700 !rounded-lg"
            nodeColor={(node) => {
              if (node.type === 'groupNode') return '#8b5cf6';
              const data = node.data as ModuleNodeData;
              if (data.hasPrompt) return '#10b981';
              if (data.colors?.bg?.includes('orange')) return '#f97316';
              if (data.colors?.bg?.includes('blue')) return '#3b82f6';
              return '#22c55e';
            }}
            maskColor="rgba(0, 0, 0, 0.6)"
          />

          {/* Batch Filter Panel */}
          {batches.length > 1 && (
            <Panel position="top-left" className="!m-4">
              <div className="bg-surface-800/90 rounded-lg p-2 border border-surface-700/50 backdrop-blur-sm">
                <BatchFilterDropdown
                  batches={batches}
                  selectedBatch={selectedBatch}
                  onSelectBatch={onBatchSelect || (() => {})}
                  onSyncBatch={onSyncBatch}
                  remainingCountByBatch={remainingCountByBatch}
                  disabled={editMode}
                />
              </div>
            </Panel>
          )}

          {/* Legend Panel */}
          <Panel position="bottom-right" className="!m-4">
            <div className="bg-surface-800/90 rounded-lg p-3 border border-surface-700/50 backdrop-blur-sm">
              <div className="flex items-center justify-between mb-2">
                <p className="text-xs text-surface-400 font-medium">Legend</p>
                <button
                  onClick={handleRelayout}
                  className="text-[10px] px-2 py-0.5 bg-surface-700 hover:bg-surface-600 text-surface-300 rounded transition-colors"
                  title="Reset layout"
                >
                  Re-layout
                </button>
              </div>
              <div className="space-y-1.5">
                <div className="flex items-center gap-2">
                  <div className="w-3 h-3 rounded bg-orange-500/40 border border-orange-500/50" />
                  <span className="text-xs text-surface-300">Frontend</span>
                </div>
                <div className="flex items-center gap-2">
                  <div className="w-3 h-3 rounded bg-blue-500/40 border border-blue-500/50" />
                  <span className="text-xs text-surface-300">Backend</span>
                </div>
                <div className="flex items-center gap-2">
                  <div className="w-3 h-3 rounded bg-green-500/40 border border-green-500/50" />
                  <span className="text-xs text-surface-300">Shared</span>
                </div>
                <div className="flex items-center gap-2 pt-1 border-t border-surface-700/50 mt-1">
                  <div className="w-3 h-3 rounded-full bg-emerald-500 flex items-center justify-center">
                    <svg className="w-2 h-2 text-white" fill="none" stroke="currentColor" viewBox="0 0 24 24">
                      <path strokeLinecap="round" strokeLinejoin="round" strokeWidth={3} d="M5 13l4 4L19 7" />
                    </svg>
                  </div>
                  <span className="text-xs text-surface-300">Prompt exists</span>
                </div>
                <div className="flex items-center gap-2 pt-1 border-t border-surface-700/50 mt-1">
                  <div className="flex gap-0.5">
                    <div className="w-3 h-3 rounded-full bg-green-500 flex items-center justify-center text-[7px] font-bold text-white">C</div>
                    <div className="w-3 h-3 rounded-full bg-yellow-500 flex items-center justify-center text-[7px] font-bold text-white">T</div>
                    <div className="w-3 h-3 rounded-full bg-blue-500 flex items-center justify-center text-[7px] font-bold text-white">E</div>
                  </div>
                  <span className="text-xs text-surface-300">Code/Test/Example</span>
                </div>
                <div className="flex items-center gap-2 pt-1 border-t border-surface-700/50 mt-1">
                  <div className="flex items-center">
                    <svg className="w-6 h-3" viewBox="0 0 24 12">
                      <defs>
                        <marker id="arrow-legend" markerWidth="10" markerHeight="10" refX="8" refY="3" orient="auto" markerUnits="strokeWidth">
                          <path d="M0,0 L0,6 L9,3 z" fill="#60a5fa" />
                        </marker>
                      </defs>
                      <line x1="0" y1="6" x2="20" y2="6" stroke="#60a5fa" strokeWidth="2" markerEnd="url(#arrow-legend)" />
                    </svg>
                  </div>
                  <span className="text-xs text-surface-300">Arrow shows dependency direction</span>
                </div>
                {batches.length > 1 && (
                  <div className="flex items-center gap-2 pt-1 border-t border-surface-700/50 mt-1">
                    <div className="flex gap-0.5">
                      {batches.slice(0, 4).map((b) => (
                        <div
                          key={b.id}
                          className="w-1.5 h-3 rounded-full"
                          style={{ backgroundColor: b.color }}
                        />
                      ))}
                      {batches.length > 4 && <span className="text-[8px] text-surface-500">...</span>}
                    </div>
                    <span className="text-xs text-surface-300">Batch groups</span>
                  </div>
                )}
                {architecture.some(m => m.group) && (
                  <div className="flex items-center gap-2 pt-1 border-t border-surface-700/50 mt-1">
                    <div className="w-3 h-3 rounded bg-violet-500/40 border border-violet-500/50" />
                    <span className="text-xs text-surface-300">Group (click to collapse)</span>
                  </div>
                )}
                {!editMode && (
                  <div className="pt-1 border-t border-surface-700/50 mt-1">
                    <p className="text-[10px] text-surface-400 leading-relaxed">
                      <span className="text-violet-400">Click node</span> to focus its dependencies
                    </p>
                  </div>
                )}
                {editMode && (
                  <div className="pt-1 border-t border-surface-700/50 mt-1">
                    <p className="text-[10px] text-surface-400 leading-relaxed">
                      <span className="text-orange-400">Edit mode:</span> Right-click edge to delete, or click + Delete/Backspace
                    </p>
                  </div>
                )}
              </div>
            </div>
          </Panel>
        </ReactFlow>
      </div>

      {/* Edge Context Menu */}
      {contextMenu && (
        <div
          className="fixed z-50 bg-surface-800 border border-surface-700 rounded-lg shadow-xl py-1 min-w-[150px]"
          style={{
            top: contextMenu.y,
            left: contextMenu.x,
          }}
          onClick={(e) => e.stopPropagation()}
        >
          <button
            onClick={handleDeleteEdgeFromMenu}
            className="w-full px-4 py-2 text-left text-sm text-red-400 hover:bg-surface-700 transition-colors flex items-center gap-2"
          >
            <svg className="w-4 h-4" fill="none" stroke="currentColor" viewBox="0 0 24 24">
              <path strokeLinecap="round" strokeLinejoin="round" strokeWidth={2} d="M19 7l-.867 12.142A2 2 0 0116.138 21H7.862a2 2 0 01-1.995-1.858L5 7m5 4v6m4-6v6m1-10V4a1 1 0 00-1-1h-4a1 1 0 00-1 1v3M4 7h16" />
            </svg>
            Delete Edge
          </button>
          <div className="px-4 py-2 text-xs text-surface-500 border-t border-surface-700">
            <div className="font-mono">
              {contextMenu.edge.source} → {contextMenu.edge.target}
            </div>
          </div>
        </div>
      )}
    </div>
  );
};

export default DependencyViewer;
