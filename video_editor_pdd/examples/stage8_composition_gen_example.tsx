/**
 * Example usage of Stage8CompositionGen component.
 *
 * Stage8CompositionGen is a client-side React component for managing
 * Remotion composition generation, previewing component stills, and
 * staging VEO assets in a video production pipeline.
 *
 * Props:
 *   - onAdvance: () => void
 *       Callback invoked when the user clicks "Continue" to proceed
 *       to the next pipeline stage. The parent component is responsible
 *       for updating the pipeline stage state accordingly.
 *
 * Behavior:
 *   - On mount, fetches composition list from GET /api/pipeline/compositions/list
 *     and staging manifest from GET /api/pipeline/veo/staging-manifest.
 *   - Left panel displays components grouped by collapsible sections.
 *     Each component shows a status badge (done/missing/error/running/pending)
 *     and provides Preview (opens a modal with a PNG still) and Regenerate buttons.
 *   - Section wrappers are listed below the component sections.
 *   - "Generate All Compositions" triggers POST /api/pipeline/compositions/run.
 *   - Right panel shows an asset staging manifest table with filename,
 *     expected/present status, and per-file "Stage Now" buttons.
 *   - "Stage All Missing" triggers POST /api/pipeline/asset-staging/run
 *     with all missing filenames.
 *   - An expandable Job Logs drawer uses SseLogPanel to stream SSE logs
 *     for the active job. When a job completes or errors, data is refreshed.
 *   - Section collapse state is persisted to localStorage under
 *     'stage8-collapsed-sections'.
 *
 * API Endpoints consumed:
 *   GET  /api/pipeline/compositions/list
 *     Returns: { sections: [{ id, label, components: [{ name, status, error? }], wrappers? }] }
 *
 *   GET  /api/pipeline/veo/staging-manifest
 *     Returns: [{ filename, expected, present }]
 *
 *   GET  /api/pipeline/compositions/preview?component={name}
 *     Returns: { url: string } or plain text URL for a PNG still
 *
 *   POST /api/pipeline/compositions/run
 *     Body (optional): { components: [name] } for single component regeneration
 *     Returns: { jobId: string }
 *
 *   POST /api/pipeline/asset-staging/run
 *     Body: { files: [filename] }
 *     Returns: { jobId: string }
 */

import React, { useState } from 'react';
import Stage8CompositionGen from '../components/stages/Stage8CompositionGen';

/**
 * Example 1: Basic integration within a pipeline stepper.
 *
 * The parent component manages which stage is active and provides
 * the onAdvance callback to move to the next stage.
 */
function PipelineStepper() {
  const [currentStage, setCurrentStage] = useState(8);

  const handleAdvance = () => {
    // Move to stage 9 (render) when user clicks "Continue"
    console.log('Advancing from Stage 8 (Composition Gen) to Stage 9 (Render)');
    setCurrentStage(9);
  };

  if (currentStage !== 8) {
    return <div>Current stage: {currentStage} (not Stage 8)</div>;
  }

  return (
    <div className="h-screen p-4">
      {/*
        Stage8CompositionGen fills its container using flex layout.
        Wrap it in a full-height container for proper rendering.
      */}
      <Stage8CompositionGen onAdvance={handleAdvance} />
    </div>
  );
}

/**
 * Example 2: Integration within a multi-stage layout with
 * conditional rendering based on pipeline state.
 */
type PipelineStage =
  | 'setup' | 'script' | 'tts-script' | 'tts-render'
  | 'audio-sync' | 'specs' | 'veo' | 'compositions' | 'render' | 'audit';

function FullPipelineApp() {
  const [activeStage, setActiveStage] = useState<PipelineStage>('compositions');

  const stages: PipelineStage[] = [
    'setup', 'script', 'tts-script', 'tts-render',
    'audio-sync', 'specs', 'veo', 'compositions', 'render', 'audit',
  ];

  const advanceToNextStage = () => {
    const currentIndex = stages.indexOf(activeStage);
    if (currentIndex < stages.length - 1) {
      setActiveStage(stages[currentIndex + 1]);
    }
  };

  return (
    <div className="flex h-screen flex-col">
      {/* Stage navigation bar */}
      <nav className="flex gap-1 border-b bg-white p-2">
        {stages.map((stage) => (
          <button
            key={stage}
            className={`rounded px-3 py-1 text-xs font-medium ${
              stage === activeStage
                ? 'bg-blue-600 text-white'
                : 'bg-slate-100 text-slate-600 hover:bg-slate-200'
            }`}
            onClick={() => setActiveStage(stage)}
          >
            {stage}
          </button>
        ))}
      </nav>

      {/* Stage content area */}
      <main className="flex-1 overflow-auto p-4">
        {activeStage === 'compositions' && (
          <Stage8CompositionGen onAdvance={advanceToNextStage} />
        )}
        {activeStage !== 'compositions' && (
          <p className="text-slate-500">
            Active stage: <strong>{activeStage}</strong>
          </p>
        )}
      </main>
    </div>
  );
}

/**
 * Example 3: Minimal standalone usage for testing or development.
 *
 * This is the simplest possible integration — just render the component
 * with a no-op or logging callback.
 */
function MinimalExample() {
  return (
    <div style={{ height: '100vh', padding: '1rem' }}>
      <Stage8CompositionGen
        onAdvance={() => {
          alert('Stage 8 complete — advancing to render stage.');
        }}
      />
    </div>
  );
}

/**
 * Example 4: Mock API responses for local development.
 *
 * When building API route handlers to support Stage8CompositionGen,
 * the following response shapes are expected:
 */

// GET /api/pipeline/compositions/list response shape:
const mockCompositionListResponse = {
  sections: [
    {
      id: 'intro',
      label: 'Introduction',
      components: [
        { name: 'IntroTitle', status: 'done' as const, error: null },
        { name: 'IntroBackground', status: 'missing' as const, error: null },
        {
          name: 'IntroOverlay',
          status: 'error' as const,
          error: 'Failed to resolve asset: overlay.png not found in public/',
        },
      ],
      wrappers: [
        { name: 'IntroWrapper', status: 'done' as const, error: null },
      ],
    },
    {
      id: 'main',
      label: 'Main Content',
      components: [
        { name: 'MainNarration', status: 'done' as const },
        { name: 'MainChart', status: 'pending' as const },
        { name: 'MainDemo', status: 'running' as const },
      ],
      wrappers: [
        { name: 'MainWrapper', status: 'missing' as const },
      ],
    },
  ],
};

// GET /api/pipeline/veo/staging-manifest response shape:
const mockStagingManifest = [
  { filename: 'intro-bg.mp4', expected: true, present: true },
  { filename: 'main-demo.mp4', expected: true, present: false },
  { filename: 'outro-fade.mp4', expected: true, present: false },
  { filename: 'bonus-clip.mp4', expected: false, present: false },
];

// POST /api/pipeline/compositions/run response shape:
const mockRunResponse = { jobId: 'job-comp-abc123' };

// POST /api/pipeline/asset-staging/run response shape:
const mockStagingRunResponse = { jobId: 'job-stage-def456' };

// GET /api/pipeline/compositions/preview?component=IntroTitle response shape:
const mockPreviewResponse = { url: '/output/previews/IntroTitle.png' };

export { PipelineStepper, FullPipelineApp, MinimalExample };
export default MinimalExample;