/**
 * Example: Using the StageSidebar component in a parent layout.
 *
 * StageSidebar renders a vertical navigation sidebar for a 10-stage video
 * production pipeline. It displays each stage with a number, label, and
 * live status badge that polls GET /api/pipeline/status every 5 seconds.
 *
 * Props:
 *   - activeStage: PipelineStage
 *       The currently selected pipeline stage. One of:
 *       'setup' | 'script' | 'tts-script' | 'tts-render' | 'audio-sync' |
 *       'specs' | 'veo' | 'compositions' | 'render' | 'audit'
 *       The active stage row is highlighted with a blue left border and
 *       a subtle background tint.
 *
 *   - onStageSelect: (stage: PipelineStage) => void
 *       Callback invoked when the user clicks a stage row. Receives the
 *       PipelineStage string identifier of the clicked stage. Use this
 *       to update your parent state and render the corresponding stage panel.
 *
 * Behavior:
 *   - On mount and every 5 seconds, fetches /api/pipeline/status which should
 *     return a JSON object: Record<PipelineStage, { status: StageStatus; error?: string | null }>
 *   - Status badges:
 *       ○  not_started  (muted color, class: text-stage-not-started)
 *       ◌  running      (animated pulse, class: text-stage-running animate-stage-running)
 *       ●  done         (green, class: text-stage-done)
 *       ✕  error        (red, class: text-stage-error, tooltip shows error message)
 *   - Before the first poll completes, all stages default to 'not_started'.
 *   - Poll errors are silently swallowed; the sidebar retains the last known state.
 *
 * Styling requirements (Tailwind CSS):
 *   - Sidebar container: w-48, bg-sidebar, border-r border-border, h-screen
 *   - Custom color utilities expected: text-stage-done, text-stage-running,
 *     text-stage-error, text-stage-not-started, bg-sidebar, border-border
 *   - Custom animation: animate-stage-running (pulse effect for running stages)
 *
 * Example tailwind.config.js extension:
 *   theme: {
 *     extend: {
 *       colors: {
 *         sidebar: '#1a1a2e',
 *         border: '#2a2a3e',
 *         'stage-done': '#22c55e',
 *         'stage-running': '#3b82f6',
 *         'stage-error': '#ef4444',
 *         'stage-not-started': '#6b7280',
 *       },
 *       animation: {
 *         'stage-running': 'pulse 1.5s cubic-bezier(0.4, 0, 0.6, 1) infinite',
 *       },
 *     },
 *   }
 */

'use client';

import React, { useState } from 'react';
import type { PipelineStage } from '../lib/types';
import StageSidebar from '../components/StageSidebar';

/**
 * PipelineLayout demonstrates how to integrate StageSidebar into a page layout.
 *
 * It manages the activeStage state and renders the sidebar alongside a main
 * content area that changes based on the selected stage.
 */
export default function PipelineLayout() {
  // Track which stage is currently selected; defaults to 'setup'
  const [activeStage, setActiveStage] = useState<PipelineStage>('setup');

  /**
   * Handler passed to StageSidebar's onStageSelect prop.
   * Called with the PipelineStage identifier when a user clicks a row.
   *
   * @param stage - The PipelineStage that was clicked, e.g. 'script', 'veo', etc.
   */
  const handleStageSelect = (stage: PipelineStage) => {
    console.log(`Navigating to stage: ${stage}`);
    setActiveStage(stage);
  };

  return (
    <div className="flex h-screen bg-gray-950 text-white">
      {/*
        StageSidebar occupies the left 192px (w-48) column.
        It polls /api/pipeline/status every 5s and updates badges automatically.
        No additional configuration is needed for polling — it starts on mount.
      */}
      <StageSidebar
        activeStage={activeStage}
        onStageSelect={handleStageSelect}
      />

      {/* Main content area — render stage-specific UI based on activeStage */}
      <main className="flex-1 p-6 overflow-y-auto">
        <h1 className="text-2xl font-bold mb-4">
          Stage: {activeStage}
        </h1>
        <p className="text-gray-400">
          Select a stage from the sidebar to view its details.
          The sidebar badges update automatically every 5 seconds.
        </p>

        {/* Example: conditionally render stage-specific panels */}
        {activeStage === 'setup' && (
          <div className="mt-6 p-4 border border-gray-700 rounded">
            <h2 className="text-lg font-semibold">Project Setup</h2>
            <p className="text-sm text-gray-400 mt-2">
              Configure project name, resolution, and section structure.
            </p>
          </div>
        )}

        {activeStage === 'script' && (
          <div className="mt-6 p-4 border border-gray-700 rounded">
            <h2 className="text-lg font-semibold">Script Editor</h2>
            <p className="text-sm text-gray-400 mt-2">
              Write and edit the narration script for each section.
            </p>
          </div>
        )}

        {activeStage === 'audit' && (
          <div className="mt-6 p-4 border border-gray-700 rounded">
            <h2 className="text-lg font-semibold">Audit & Review</h2>
            <p className="text-sm text-gray-400 mt-2">
              Review annotations, apply fixes, and finalize the video.
            </p>
          </div>
        )}
      </main>
    </div>
  );
}

/**
 * ============================================================================
 * API Route Example: GET /api/pipeline/status
 * ============================================================================
 *
 * The StageSidebar expects this endpoint to return a JSON object mapping
 * each PipelineStage to its current status. Example response:
 *
 * {
 *   "setup":        { "status": "done",        "error": null },
 *   "script":       { "status": "done",        "error": null },
 *   "tts-script":   { "status": "running",     "error": null },
 *   "tts-render":   { "status": "not_started",  "error": null },
 *   "audio-sync":   { "status": "not_started",  "error": null },
 *   "specs":        { "status": "not_started",  "error": null },
 *   "veo":          { "status": "not_started",  "error": null },
 *   "compositions": { "status": "not_started",  "error": null },
 *   "render":       { "status": "not_started",  "error": null },
 *   "audit":        { "status": "error",        "error": "Audit failed: missing section 'outro'" }
 * }
 *
 * StageStatus values: 'not_started' | 'running' | 'done' | 'error'
 *
 * When status is 'error', the 'error' field should contain a descriptive
 * message. This message is displayed as a tooltip when the user hovers
 * over the error badge (✕) or the stage row in the sidebar.
 *
 * Example Next.js API route (app/api/pipeline/status/route.ts):
 *
 *   import { NextResponse } from 'next/server';
 *
 *   export async function GET() {
 *     // Query your database or in-memory state for current stage statuses
 *     const statuses = await getStageStatuses();
 *     return NextResponse.json(statuses);
 *   }
 */