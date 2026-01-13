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
const NODE_HEIGHT = 70;

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
  highlightedModules = new Set(),
}) => {
  const [isPrdVisible, setIsPrdVisible] = useState(false);

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
    const nodes: Node<ModuleNodeData>[] = architecture.map((m) => {
      const category = getCategory(m);
      const hasPrompt = existingPrompts.has(m.filename);
      const isHighlighted = highlightedModules.has(m.filename);
      return {
        id: m.filename,
        type: 'moduleNode',
        position: { x: 0, y: 0 }, // Will be set by Dagre
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
          style: { stroke: '#60a5fa', strokeWidth: 1.5 },
          animated: false,
          selectable: editMode,
          interactionWidth: 20, // Makes edge easier to click
        }))
    );

    const layouted = getLayoutedElements(nodes, edges, 'TB');
    return { initialNodes: layouted.nodes, initialEdges: layouted.edges };
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
            style: { stroke: '#60a5fa', strokeWidth: 1.5 },
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

  // Update nodes when architecture changes
  React.useEffect(() => {
    setNodes(initialNodes);
    setEdges(initialEdges);
  }, [initialNodes, initialEdges, setNodes, setEdges]);

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
          onEdgesDelete={editMode ? handleEdgesDelete : undefined}
          onNodesDelete={editMode ? handleNodesDelete : undefined}
          nodeTypes={nodeTypes}
          fitView
          fitViewOptions={{ padding: 0.2 }}
          minZoom={0.1}
          maxZoom={2}
          defaultEdgeOptions={{
            style: { stroke: '#60a5fa', strokeWidth: 1.5 },
            type: 'smoothstep',
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
                {editMode && (
                  <div className="pt-1 border-t border-surface-700/50 mt-1">
                    <p className="text-[10px] text-surface-400 leading-relaxed">
                      <span className="text-orange-400">Edit mode:</span> Click edge to select, then Delete/Backspace to remove
                    </p>
                  </div>
                )}
              </div>
            </div>
          </Panel>
        </ReactFlow>
      </div>
    </div>
  );
};

export default DependencyViewer;
