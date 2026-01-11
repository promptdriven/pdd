import React, { useMemo, useState } from 'react';
import { ArchitectureModule, PromptInfo } from '../api';
import { ChevronDownIcon, ChevronUpIcon, SparklesIcon, DocumentArrowDownIcon, SpinnerIcon } from './Icon';
import Tooltip from './Tooltip';

const NODE_WIDTH = 200;
const NODE_HEIGHT = 70;
const HORIZONTAL_SPACING = 30;
const VERTICAL_SPACING = 100;
const PRD_HEADER_HEIGHT = 72;
const PRD_CONTENT_HEIGHT = 250;
const PRD_MARGIN_BOTTOM = 60;

interface PositionedModule extends ArchitectureModule {
  id: string;
  label: string;
  x: number;
  y: number;
  category: 'frontend' | 'backend' | 'shared';
}

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
}) => {
  const [isPrdVisible, setIsPrdVisible] = useState(false);

  // Create a lookup map from module filename to PromptInfo for file tracking
  const promptInfoMap = useMemo(() => {
    const map = new Map<string, PromptInfo>();
    for (const p of promptsInfo) {
      // Extract filename from path (e.g., "prompts/calculator_python.prompt" -> "calculator_python.prompt")
      const filename = p.prompt.split('/').pop() || '';
      map.set(filename, p);
    }
    return map;
  }, [promptsInfo]);

  const layout = useMemo(() => {
    // Convert architecture modules to graph nodes
    const nodes: PositionedModule[] = architecture.map(m => ({
      ...m,
      id: m.filename,
      label: m.filename.replace(/_[A-Za-z]+\.prompt$/, '').replace(/\.prompt$/, ''),
      x: 0,
      y: 0,
      category: getCategory(m),
    }));

    // Build edge list and parent/child maps
    const edges: { id: string; source: string; target: string }[] = [];
    const nodeMap = new Map(nodes.map(n => [n.id, n]));
    const childrenMap = new Map<string, string[]>();
    const parentMap = new Map<string, string[]>();

    for (const node of nodes) {
      if (!childrenMap.has(node.id)) childrenMap.set(node.id, []);
      if (!parentMap.has(node.id)) parentMap.set(node.id, []);

      for (const dep of node.dependencies) {
        if (nodeMap.has(dep)) {
          edges.push({
            id: `${dep}->${node.id}`,
            source: dep,
            target: node.id,
          });
          childrenMap.get(dep)?.push(node.id);
          parentMap.get(node.id)?.push(dep);
        }
      }
    }

    // Layer nodes using topological sort
    const layers: string[][] = [];
    const layeredNodes = new Set<string>();

    // Start with nodes that have no parents (root nodes)
    let currentLayerNodes = nodes
      .filter(n => (parentMap.get(n.id) || []).length === 0)
      .map(n => n.id);

    while (currentLayerNodes.length > 0) {
      layers.push(currentLayerNodes);
      currentLayerNodes.forEach(id => layeredNodes.add(id));

      const nextLayerNodes = new Set<string>();
      for (const nodeId of currentLayerNodes) {
        const children = childrenMap.get(nodeId) || [];
        for (const childId of children) {
          if (!layeredNodes.has(childId)) {
            const parents = parentMap.get(childId) || [];
            if (parents.every(p => layeredNodes.has(p))) {
              nextLayerNodes.add(childId);
            }
          }
        }
      }
      currentLayerNodes = Array.from(nextLayerNodes);
    }

    // Add any unlayered nodes (cycles or disconnected)
    const unlayeredNodes = nodes.filter(n => !layeredNodes.has(n.id)).map(n => n.id);
    if (unlayeredNodes.length > 0) {
      layers.push(unlayeredNodes);
    }

    // Calculate dimensions
    const maxNodesInLayer = Math.max(...layers.map(l => l.length), 1);
    const totalWidth = maxNodesInLayer * (NODE_WIDTH + HORIZONTAL_SPACING) - HORIZONTAL_SPACING;
    const totalHeight = layers.length * (NODE_HEIGHT + VERTICAL_SPACING) - VERTICAL_SPACING;

    // Position nodes
    const positionedNodes: PositionedModule[] = [];
    for (let i = 0; i < layers.length; i++) {
      const layer = layers[i];
      const layerWidth = layer.length * (NODE_WIDTH + HORIZONTAL_SPACING) - HORIZONTAL_SPACING;
      const startX = (totalWidth - layerWidth) / 2;
      for (let j = 0; j < layer.length; j++) {
        const node = nodeMap.get(layer[j]);
        if (node) {
          positionedNodes.push({
            ...node,
            x: startX + j * (NODE_WIDTH + HORIZONTAL_SPACING),
            y: i * (NODE_HEIGHT + VERTICAL_SPACING),
          });
        }
      }
    }

    const positionedNodeMap = new Map(positionedNodes.map(n => [n.id, n]));
    const containerWidth = Math.max(800, totalWidth + 80);
    const containerHeight = Math.max(400, totalHeight + 80);

    return { nodes: positionedNodes, edges, nodeMap: positionedNodeMap, width: containerWidth, height: containerHeight, layers };
  }, [architecture]);

  const prdContainerHeight = isPrdVisible ? PRD_HEADER_HEIGHT + PRD_CONTENT_HEIGHT : PRD_HEADER_HEIGHT;
  const yOffset = prdContainerHeight + PRD_MARGIN_BOTTOM;
  const totalHeight = layout.height + yOffset;

  // Calculate connector target for PRD arrow
  const connectorTarget = useMemo(() => {
    if (layout.layers.length === 0 || layout.layers[0].length === 0) {
      return { x: layout.width / 2, y: yOffset };
    }
    const firstLayerNodes = layout.layers[0]
      .map(id => layout.nodeMap.get(id))
      .filter(Boolean) as PositionedModule[];

    if (firstLayerNodes.length === 0) {
      return { x: layout.width / 2, y: yOffset };
    }

    const firstLayerMinX = Math.min(...firstLayerNodes.map(n => n.x));
    const firstLayerMaxX = Math.max(...firstLayerNodes.map(n => n.x + NODE_WIDTH));
    return {
      x: (firstLayerMinX + firstLayerMaxX) / 2,
      y: yOffset,
    };
  }, [layout, yOffset]);

  return (
    <div className="glass rounded-xl border border-surface-700/50 overflow-auto h-full">
      <div
        className="relative"
        style={{ width: layout.width, height: totalHeight, minWidth: '100%' }}
        aria-label="Architecture dependency graph"
      >
        {/* PRD Viewer */}
        <div
          className="absolute top-4 left-4 right-4 bg-surface-800/80 rounded-xl border border-surface-700/50 transition-all duration-300 ease-in-out z-10"
          style={{ maxWidth: layout.width - 32 }}
        >
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

        {/* SVG for edges */}
        <svg
          width={layout.width}
          height={totalHeight}
          className="absolute top-0 left-0 pointer-events-none"
        >
          <defs>
            <marker
              id="arrowhead"
              markerWidth="8"
              markerHeight="6"
              refX="7"
              refY="3"
              orient="auto"
            >
              <polygon points="0 0, 8 3, 0 6" fill="#60a5fa" />
            </marker>
            <marker
              id="arrowhead-prd"
              markerWidth="8"
              markerHeight="6"
              refX="7"
              refY="3"
              orient="auto"
            >
              <polygon points="0 0, 8 3, 0 6" fill="#0ea5e9" />
            </marker>
          </defs>

          {/* PRD Connector */}
          <path
            d={`M ${layout.width / 2} ${prdContainerHeight + 20} C ${layout.width / 2} ${prdContainerHeight + 50}, ${connectorTarget.x} ${connectorTarget.y - 30}, ${connectorTarget.x} ${connectorTarget.y}`}
            stroke="#0ea5e9"
            strokeWidth="2"
            strokeDasharray="5 5"
            fill="none"
            markerEnd="url(#arrowhead-prd)"
          />

          {/* Dependency edges */}
          {layout.edges.map(edge => {
            const sourceNode = layout.nodeMap.get(edge.source);
            const targetNode = layout.nodeMap.get(edge.target);
            if (!sourceNode || !targetNode) return null;

            const sourceX = sourceNode.x + NODE_WIDTH / 2;
            const sourceY = sourceNode.y + NODE_HEIGHT + yOffset;
            const targetX = targetNode.x + NODE_WIDTH / 2;
            const targetY = targetNode.y + yOffset;

            const dy = targetY - sourceY;
            const controlY1 = sourceY + dy / 2;
            const controlY2 = targetY - dy / 2;

            return (
              <path
                key={edge.id}
                d={`M ${sourceX} ${sourceY} C ${sourceX} ${controlY1}, ${targetX} ${controlY2}, ${targetX} ${targetY}`}
                stroke="#60a5fa"
                strokeWidth="1.5"
                fill="none"
                markerEnd="url(#arrowhead)"
              />
            );
          })}
        </svg>

        {/* Module nodes */}
        {layout.nodes.map(node => {
          const colors = getCategoryColors(node.category);
          const hasPrompt = existingPrompts.has(node.id);
          const promptInfo = promptInfoMap.get(node.id);
          const hasCode = !!promptInfo?.code;
          const hasTest = !!promptInfo?.test;
          const hasExample = !!promptInfo?.example;
          return (
            <Tooltip
              key={node.id}
              content={
                <div className="max-w-xs">
                  <div className="font-medium">{node.filename}</div>
                  <div className="text-xs text-surface-400 mt-1">{node.filepath}</div>
                  <div className="text-xs mt-2">{node.description.substring(0, 100)}...</div>
                  {hasPrompt && (
                    <div className="mt-2 pt-2 border-t border-surface-700/50">
                      <div className="text-xs text-emerald-400 flex items-center gap-1 mb-1">
                        <svg className="w-3 h-3" fill="none" stroke="currentColor" viewBox="0 0 24 24">
                          <path strokeLinecap="round" strokeLinejoin="round" strokeWidth={2} d="M5 13l4 4L19 7" />
                        </svg>
                        Prompt exists
                      </div>
                      <div className="flex items-center gap-2 text-xs mt-1">
                        <span className={hasCode ? 'text-green-400' : 'text-surface-500'}>{hasCode ? '✓' : '✗'} Code</span>
                        <span className={hasTest ? 'text-yellow-400' : 'text-surface-500'}>{hasTest ? '✓' : '✗'} Test</span>
                        <span className={hasExample ? 'text-blue-400' : 'text-surface-500'}>{hasExample ? '✓' : '✗'} Example</span>
                      </div>
                    </div>
                  )}
                </div>
              }
            >
              <button
                onClick={() => onModuleClick(node)}
                className={`absolute ${colors.bg} ${colors.border} ${colors.hover} border rounded-xl p-3 flex flex-col justify-center items-center text-center cursor-pointer focus:outline-none focus:ring-2 focus:ring-accent-500 transition-all duration-200 hover:scale-105 ${hasPrompt ? 'ring-2 ring-emerald-500/50' : ''}`}
                style={{
                  width: NODE_WIDTH,
                  height: NODE_HEIGHT,
                  transform: `translate(${node.x}px, ${node.y + yOffset}px)`,
                }}
              >
                {/* Prompt status indicator */}
                {hasPrompt && (
                  <div className="absolute -top-1.5 -right-1.5 w-5 h-5 bg-emerald-500 rounded-full flex items-center justify-center shadow-lg">
                    <svg className="w-3 h-3 text-white" fill="none" stroke="currentColor" viewBox="0 0 24 24">
                      <path strokeLinecap="round" strokeLinejoin="round" strokeWidth={3} d="M5 13l4 4L19 7" />
                    </svg>
                  </div>
                )}
                {/* File status indicators - shown when prompt exists */}
                {hasPrompt && (
                  <div className="absolute -bottom-1.5 right-1 flex gap-0.5">
                    <div className={`w-3.5 h-3.5 rounded-full flex items-center justify-center text-[8px] font-bold ${hasCode ? 'bg-green-500 text-white' : 'bg-surface-700 text-surface-500'}`} title={hasCode ? 'Code exists' : 'No code file'}>
                      C
                    </div>
                    <div className={`w-3.5 h-3.5 rounded-full flex items-center justify-center text-[8px] font-bold ${hasTest ? 'bg-yellow-500 text-white' : 'bg-surface-700 text-surface-500'}`} title={hasTest ? 'Test exists' : 'No test file'}>
                      T
                    </div>
                    <div className={`w-3.5 h-3.5 rounded-full flex items-center justify-center text-[8px] font-bold ${hasExample ? 'bg-blue-500 text-white' : 'bg-surface-700 text-surface-500'}`} title={hasExample ? 'Example exists' : 'No example file'}>
                      E
                    </div>
                  </div>
                )}
                <p className="font-medium text-sm text-white truncate w-full">{node.label}</p>
                <p className={`text-xs ${colors.text} truncate w-full`}>
                  {node.interface?.type || 'module'}
                </p>
                <p className="text-xs text-surface-500 truncate w-full">
                  Priority: {node.priority}
                </p>
              </button>
            </Tooltip>
          );
        })}

        {/* Legend */}
        <div className="absolute bottom-4 right-4 bg-surface-800/80 rounded-lg p-3 border border-surface-700/50">
          <p className="text-xs text-surface-400 mb-2 font-medium">Legend</p>
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
          </div>
        </div>
      </div>
    </div>
  );
};

export default DependencyViewer;
