import React, { useMemo, useState, useCallback } from 'react';
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
} from 'reactflow';
import dagre from 'dagre';
import 'reactflow/dist/style.css';

import { ArchitectureModule, PromptInfo } from '../api';
import { ChevronDownIcon, ChevronUpIcon, SparklesIcon, DocumentArrowDownIcon, SpinnerIcon } from './Icon';
import Tooltip from './Tooltip';
import ModuleNode, { ModuleNodeData } from './ModuleNode';

const NODE_WIDTH = 200;
const NODE_HEIGHT = 85;

interface DependencyViewerProps {
  architecture: ArchitectureModule[];
  prdContent: string;
  appName?: string;
  onRegenerate: () => void;
  onModuleClick: (module: ArchitectureModule) => void;
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
const getLayoutedElements = (
  nodes: Node<ModuleNodeData>[],
  edges: Edge[],
  direction: 'TB' | 'LR' = 'TB'
) => {
  const g = new dagre.graphlib.Graph();
  g.setGraph({ rankdir: direction, nodesep: 50, ranksep: 100, edgesep: 20 });
  g.setDefaultEdgeLabel(() => ({}));

  nodes.forEach((node) => {
    g.setNode(node.id, { width: NODE_WIDTH, height: NODE_HEIGHT });
  });

  edges.forEach((edge) => {
    g.setEdge(edge.source, edge.target);
  });

  dagre.layout(g);

  const layoutedNodes = nodes.map((node) => {
    const nodeWithPosition = g.node(node.id);
    return {
      ...node,
      position: {
        x: nodeWithPosition.x - NODE_WIDTH / 2,
        y: nodeWithPosition.y - NODE_HEIGHT / 2,
      },
    };
  });

  return { nodes: layoutedNodes, edges };
};

// Custom node types
const nodeTypes: NodeTypes = {
  moduleNode: ModuleNode,
};

const DependencyViewer: React.FC<DependencyViewerProps> = ({
  architecture,
  prdContent,
  appName,
  onRegenerate,
  onModuleClick,
  onGeneratePrompts,
  isGeneratingPrompts = false,
  existingPrompts = new Set(),
  promptsInfo = [],
  editMode = false,
  onModuleEdit,
  onModuleDelete,
  onDependencyAdd,
  onDependencyRemove,
  onPositionsChange,
  highlightedModules = new Set(),
}) => {
  const [isPrdVisible, setIsPrdVisible] = useState(false);
  const [contextMenu, setContextMenu] = useState<{
    x: number;
    y: number;
    edge: Edge;
  } | null>(null);

  // Create a lookup map from module filename to PromptInfo for file tracking
  const promptInfoMap = useMemo(() => {
    const map = new Map<string, PromptInfo>();
    for (const p of promptsInfo) {
      const filename = p.prompt.split('/').pop() || '';
      map.set(filename, p);
    }
    return map;
  }, [promptsInfo]);

  // Convert architecture to React Flow nodes and edges
  const { initialNodes, initialEdges } = useMemo(() => {
    // Check if any modules have saved positions
    const hasSavedPositions = architecture.some((m) => m.position);

    const nodes: Node<ModuleNodeData>[] = architecture.map((m) => {
      const category = getCategory(m);
      const hasPrompt = existingPrompts.has(m.filename);
      const isHighlighted = highlightedModules.has(m.filename);
      return {
        id: m.filename,
        type: 'moduleNode',
        // Use saved position if available, otherwise will be set by Dagre
        position: m.position || { x: 0, y: 0 },
        data: {
          label: m.filename.replace(/_[A-Za-z]+\.prompt$/, '').replace(/\.prompt$/, ''),
          module: m,
          promptInfo: promptInfoMap.get(m.filename),
          hasPrompt,
          colors: getCategoryColors(category),
          onClick: onModuleClick,
          editMode,
          onEdit: onModuleEdit,
          onDelete: onModuleDelete,
          isHighlighted,
        },
      };
    });

    const nodeIds = new Set(architecture.map((m) => m.filename));
    const edges: Edge[] = architecture.flatMap((m) =>
      m.dependencies
        .filter((dep) => nodeIds.has(dep))
        .map((dep) => ({
          id: `${dep}->${m.filename}`,
          source: dep,
          target: m.filename,
          type: 'smoothstep',
          style: { stroke: '#60a5fa', strokeWidth: 2 },
          markerEnd: {
            type: 'arrowclosed' as const,
            color: '#60a5fa',
            width: 20,
            height: 20,
          },
          animated: false,
          selectable: editMode,
          focusable: editMode,
          deletable: editMode,
          interactionWidth: 20, // Makes edge easier to click
        }))
    );

    // Only apply Dagre layout if no saved positions exist
    if (!hasSavedPositions) {
      const layouted = getLayoutedElements(nodes, edges, 'TB');
      return { initialNodes: layouted.nodes, initialEdges: layouted.edges };
    }

    return { initialNodes: nodes, initialEdges: edges };
  }, [architecture, existingPrompts, promptInfoMap, onModuleClick, editMode, onModuleEdit, onModuleDelete, highlightedModules]);

  const [nodes, setNodes, onNodesChange] = useNodesState(initialNodes);
  const [edges, setEdges, onEdgesChange] = useEdgesState(initialEdges);

  // Re-layout when clicking the layout button
  const handleRelayout = useCallback(() => {
    const layouted = getLayoutedElements(nodes, edges, 'TB');
    setNodes(layouted.nodes);
    setEdges(layouted.edges);
  }, [nodes, edges, setNodes, setEdges]);

  // Handle edge creation (dependency added)
  const handleConnect = useCallback(
    (connection: Connection) => {
      if (!editMode || !connection.source || !connection.target) return;
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
            type: 'smoothstep',
            style: { stroke: '#60a5fa', strokeWidth: 2 },
            markerEnd: {
              type: 'arrowclosed' as const,
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

  // Handle edge deletion (dependency removed)
  const handleEdgesDelete = useCallback(
    (deletedEdges: Edge[]) => {
      if (!editMode) return;
      for (const edge of deletedEdges) {
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

  // Close context menu when clicking elsewhere
  const handlePaneClick = useCallback(() => {
    setContextMenu(null);
  }, []);

  // Handle node deletion (module removed)
  const handleNodesDelete = useCallback(
    (deletedNodes: Node[]) => {
      if (!editMode) return;
      for (const node of deletedNodes) {
        onModuleDelete?.(node.id);
      }
    },
    [editMode, onModuleDelete]
  );

  // Handle node drag end to save ALL positions (so they're all captured for saving)
  const handleNodeDragStop = useCallback(
    (_event: React.MouseEvent, _node: Node, allNodes: Node[]) => {
      if (!editMode) return;
      // Send all node positions to parent
      const positions = new Map<string, { x: number; y: number }>();
      allNodes.forEach((n) => {
        positions.set(n.id, { x: n.position.x, y: n.position.y });
      });
      onPositionsChange?.(positions);
    },
    [editMode, onPositionsChange]
  );

  // Track previous architecture to detect structural changes (not just position changes)
  const prevArchitectureRef = React.useRef<ArchitectureModule[]>(architecture);

  // Helper to check if architecture structure changed (ignoring positions)
  const getStructuralFingerprint = useCallback((modules: ArchitectureModule[]) => {
    return modules.map(m => ({
      filename: m.filename,
      dependencies: [...m.dependencies].sort().join(','),
    })).sort((a, b) => a.filename.localeCompare(b.filename))
      .map(m => `${m.filename}:${m.dependencies}`).join('|');
  }, []);

  // Update nodes/edges when architecture STRUCTURE changes (not just positions)
  React.useEffect(() => {
    const prevFingerprint = getStructuralFingerprint(prevArchitectureRef.current);
    const currentFingerprint = getStructuralFingerprint(architecture);
    const structureChanged = prevFingerprint !== currentFingerprint;

    prevArchitectureRef.current = architecture;

    // Only sync if:
    // 1) Structure changed (modules added/removed, dependencies changed)
    // 2) Not in edit mode (initial load or exiting edit mode)
    if (structureChanged || !editMode) {
      setNodes(initialNodes);
      setEdges(initialEdges);
    }
  }, [initialNodes, initialEdges, setNodes, setEdges, editMode, architecture, getStructuralFingerprint]);

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
            <p className="text-xs text-surface-400">{architecture.length} modules</p>
          </div>
          <div className="flex items-center gap-2 flex-shrink-0 ml-4">
            {onGeneratePrompts && (
              <Tooltip content="Generate prompt files for all modules">
                <button
                  onClick={onGeneratePrompts}
                  disabled={isGeneratingPrompts}
                  className="flex items-center gap-1.5 px-3 py-1.5 rounded-lg text-xs font-medium bg-emerald-600 text-white hover:bg-emerald-500 disabled:opacity-50 disabled:cursor-not-allowed transition-colors"
                >
                  {isGeneratingPrompts ? (
                    <SpinnerIcon className="w-3.5 h-3.5 animate-spin" />
                  ) : (
                    <DocumentArrowDownIcon className="w-3.5 h-3.5" />
                  )}
                  <span>{isGeneratingPrompts ? 'Generating...' : 'Generate Prompts'}</span>
                </button>
              </Tooltip>
            )}
            <Tooltip content="Regenerate architecture from PRD">
              <button
                onClick={onRegenerate}
                className="flex items-center gap-1.5 px-3 py-1.5 rounded-lg text-xs font-medium bg-accent-600 text-white hover:bg-accent-500 transition-colors"
              >
                <SparklesIcon className="w-3.5 h-3.5" />
                <span>Regenerate</span>
              </button>
            </Tooltip>
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

      {/* React Flow Graph */}
      <div className="flex-1 min-h-0">
        <ReactFlow
          nodes={nodes}
          edges={edges}
          onNodesChange={onNodesChange}
          onEdgesChange={onEdgesChange}
          onConnect={editMode ? handleConnect : undefined}
          onEdgeClick={editMode ? handleEdgeClick : undefined}
          onEdgeContextMenu={editMode ? handleEdgeContextMenu : undefined}
          onPaneClick={handlePaneClick}
          onNodeDragStop={editMode ? handleNodeDragStop : undefined}
          onEdgesDelete={editMode ? handleEdgesDelete : undefined}
          onNodesDelete={editMode ? handleNodesDelete : undefined}
          nodeTypes={nodeTypes}
          fitView
          fitViewOptions={{ padding: 0.2 }}
          minZoom={0.1}
          maxZoom={2}
          defaultEdgeOptions={{
            style: { stroke: '#60a5fa', strokeWidth: 2 },
            type: 'smoothstep',
            markerEnd: {
              type: 'arrowclosed',
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
          <Background variant={BackgroundVariant.Dots} gap={20} size={1} color="#374151" />
          <Controls
            className="!bg-surface-800 !border-surface-700 !rounded-lg [&>button]:!bg-surface-700 [&>button]:!border-surface-600 [&>button]:!text-surface-300 [&>button:hover]:!bg-surface-600"
          />
          <MiniMap
            className="!bg-surface-800 !border-surface-700 !rounded-lg"
            nodeColor={(node) => {
              const data = node.data as ModuleNodeData;
              if (data.hasPrompt) return '#10b981';
              if (data.colors.bg.includes('orange')) return '#f97316';
              if (data.colors.bg.includes('blue')) return '#3b82f6';
              return '#22c55e';
            }}
            maskColor="rgba(0, 0, 0, 0.6)"
          />

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
