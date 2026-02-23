/**
 * Example usage of Stage2ScriptEditor component.
 *
 * Stage2ScriptEditor is a dual-pane script editing interface for a video
 * production pipeline. It provides:
 *
 * - A CodeMirror 6 markdown editor (left pane) that loads content from
 *   GET /api/project/script and auto-saves via PUT /api/project/script
 *   with a 1-second debounce.
 *
 * - A structured preview (right pane) that parses the markdown content
 *   and renders color-coded blocks:
 *     • Lines starting with "NARRATOR:" → blue ■ prefix
 *     • Lines starting with "[VISUAL:" → teal ▣ prefix
 *     • Lines starting with "## " → gray uppercase section header
 *     • Other non-empty lines → plain text
 *
 * - A resizable split pane with a draggable divider. The split ratio
 *   is persisted in localStorage under the key 'script-editor-split-ratio'.
 *
 * - A "Generate TTS Script →" button that is enabled only when at least
 *   one NARRATOR: line exists. Clicking it POSTs to
 *   /api/pipeline/tts-script/run, receives a { jobId } response, displays
 *   an SseLogPanel for real-time job logs, and calls onAdvance().
 *
 * Props:
 *   @param onAdvance - () => void
 *     Callback invoked after TTS script generation is successfully triggered.
 *     Typically used to advance the pipeline stepper to the next stage.
 *
 * Required API endpoints (must exist in your Next.js app):
 *   GET  /api/project/script          → { content: string }
 *   PUT  /api/project/script          ← { content: string }
 *   POST /api/pipeline/tts-script/run → { jobId: string }
 *
 * Required dependencies:
 *   @codemirror/view, @codemirror/state, @codemirror/lang-markdown,
 *   @codemirror/commands, and the SseLogPanel component at
 *   @/components/SseLogPanel.
 */

'use client';

import React, { useState } from 'react';
import Stage2ScriptEditor from '../components/stages/Stage2ScriptEditor';

/**
 * ExamplePipelinePage demonstrates how to embed Stage2ScriptEditor
 * within a parent page that manages pipeline stage navigation.
 *
 * The parent provides the onAdvance callback, which is called when
 * the user successfully triggers TTS generation. In a real app,
 * this would transition the UI to Stage 3 (TTS Script Review).
 */
export default function ExamplePipelinePage() {
  const [currentStage, setCurrentStage] = useState<number>(2);

  /**
   * onAdvance callback — called by Stage2ScriptEditor after a successful
   * POST to /api/pipeline/tts-script/run.
   *
   * In this example, we simply increment the stage counter.
   * In a production app, this might update a global pipeline state,
   * navigate to a new route, or trigger additional side effects.
   */
  const handleAdvance = () => {
    console.log('TTS generation triggered — advancing from Stage 2 to Stage 3');
    setCurrentStage((prev) => prev + 1);
  };

  return (
    <div className="h-screen flex flex-col">
      {/* Pipeline stage indicator */}
      <header className="px-6 py-3 bg-slate-800 text-white text-sm">
        Current Pipeline Stage: <strong>{currentStage}</strong>
        {currentStage > 2 && (
          <span className="ml-4 text-green-400">
            ✓ TTS Script generation started
          </span>
        )}
      </header>

      {/*
        Stage2ScriptEditor fills the remaining vertical space.
        It expects to be placed in a flex container with a defined height.

        The component handles:
        1. Fetching the script content on mount (GET /api/project/script)
        2. Rendering the CodeMirror editor with markdown highlighting
        3. Auto-saving edits after 1 second of inactivity
        4. Parsing and displaying the structured preview
        5. Enabling the TTS button when NARRATOR: lines are present
        6. Showing SSE logs after generation is triggered
      */}
      <div className="flex-1 overflow-hidden">
        <Stage2ScriptEditor onAdvance={handleAdvance} />
      </div>
    </div>
  );
}

/**
 * Example script content that the editor expects from the API.
 * This illustrates the markdown format the preview parser understands:
 *
 * ```markdown
 * ## Introduction
 *
 * NARRATOR: Welcome to our product launch video. Today we're excited
 * to share something truly revolutionary.
 *
 * [VISUAL: Wide aerial shot of company headquarters at sunrise]
 *
 * NARRATOR: Our team has been working for over two years to bring
 * this vision to life.
 *
 * [VISUAL: Close-up montage of team members collaborating]
 *
 * ## Main Features
 *
 * NARRATOR: Let's dive into the three key features that set us apart.
 *
 * [VISUAL: Animated feature comparison chart]
 *
 * ## Closing
 *
 * NARRATOR: Thank you for watching. Visit our website to learn more.
 *
 * [VISUAL: Logo animation with website URL]
 * ```
 *
 * The preview pane will render:
 * - "Introduction" as a gray uppercase section label
 * - NARRATOR lines with a blue ■ prefix
 * - VISUAL lines with a teal ▣ prefix
 * - Other non-empty lines as plain text
 */