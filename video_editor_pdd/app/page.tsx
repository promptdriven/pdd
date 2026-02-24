'use client';

import React, { useCallback, useEffect, useMemo, useState } from 'react';
import type {
  PipelineStage,
  ProjectConfig,
  Annotation,
  AnnotationCaptureData,
  Section,
} from '@/lib/types';

import StageSidebar from '@/components/StageSidebar';
import VideoPlayer from '@/components/VideoPlayer';
import AnnotationPanel from '@/components/AnnotationPanel';

// Stage panels
import Stage1ProjectSetup from '@/components/stages/Stage1ProjectSetup';
import Stage2ScriptEditor from '@/components/stages/Stage2ScriptEditor';
import Stage3TtsScriptGen from '@/components/stages/Stage3TtsScriptGen';
import Stage4TtsRendering from '@/components/stages/Stage4TtsRendering';
import Stage5AudioSync from '@/components/stages/Stage5AudioSync';
import Stage6SpecGeneration from '@/components/stages/Stage6SpecGeneration';
import Stage7VeoGeneration from '@/components/stages/Stage7VeoGeneration';
import Stage8CompositionGen from '@/components/stages/Stage8CompositionGen';
import Stage9RenderStitch from '@/components/stages/Stage9RenderStitch';
import Stage10Audit from '@/components/stages/Stage10Audit';

type TabKey = 'pipeline' | 'review';

const STAGE_ORDER: PipelineStage[] = [
  'setup',
  'script',
  'tts-script',
  'tts-render',
  'audio-sync',
  'specs',
  'veo',
  'compositions',
  'render',
  'audit',
];

type StagePanelProps = {
  onAdvance: () => void;
  projectConfig: ProjectConfig | null;
  onCreateAnnotation?: (data: AnnotationCaptureData) => void;
};

const STAGE_PANELS: Record<PipelineStage, React.ComponentType<StagePanelProps>> = {
  setup: Stage1ProjectSetup,
  script: Stage2ScriptEditor,
  'tts-script': Stage3TtsScriptGen,
  'tts-render': Stage4TtsRendering,
  'audio-sync': Stage5AudioSync,
  specs: Stage6SpecGeneration,
  veo: Stage7VeoGeneration,
  compositions: Stage8CompositionGen,
  render: Stage9RenderStitch,
  audit: Stage10Audit,
};

export default function Page() {
  const [activeTab, setActiveTab] = useState<TabKey>('pipeline');
  const [activeStage, setActiveStage] = useState<PipelineStage>('setup');
  const [projectConfig, setProjectConfig] = useState<ProjectConfig | null>(null);
  const [annotationPreFill, setAnnotationPreFill] =
    useState<AnnotationCaptureData | null>(null);
  const [annotations, setAnnotations] = useState<Annotation[]>([]);
  const [selectedSectionId, setSelectedSectionId] = useState<string | null>(null);
  const [loadingProject, setLoadingProject] = useState<boolean>(false);
  const [loadingAnnotations, setLoadingAnnotations] = useState<boolean>(false);

  // Load project config on mount
  useEffect(() => {
    let cancelled = false;
    const loadProject = async () => {
      setLoadingProject(true);
      try {
        const res = await fetch('/api/project');
        if (!res.ok) throw new Error('Failed to load project');
        const data = (await res.json()) as ProjectConfig;
        if (cancelled) return;
        setProjectConfig(data);
        const firstSection = data.sections?.[0];
        if (firstSection) {
          setSelectedSectionId(firstSection.id);
        }
      } catch (err) {
        console.error(err);
      } finally {
        if (!cancelled) setLoadingProject(false);
      }
    };
    loadProject();
    return () => {
      cancelled = true;
    };
  }, []);

  const selectedSection: Section | undefined = useMemo(() => {
    if (!projectConfig?.sections?.length) return undefined;
    return projectConfig.sections.find((s) => s.id === selectedSectionId);
  }, [projectConfig, selectedSectionId]);

  const loadAnnotations = useCallback(async () => {
    if (!selectedSectionId) return;
    setLoadingAnnotations(true);
    try {
      const url = `/api/annotations?section=${selectedSectionId}`;
      const res = await fetch(url);
      if (!res.ok) throw new Error('Failed to load annotations');
      const data = await res.json();
      setAnnotations(data.annotations);
    } catch (err) {
      console.error(err);
    } finally {
      setLoadingAnnotations(false);
    }
  }, [selectedSectionId]);

  // Load annotations when switching to Review tab or when section changes
  useEffect(() => {
    if (activeTab === 'review') {
      loadAnnotations();
    }
  }, [activeTab, loadAnnotations]);

  const handleAdvanceStage = useCallback(() => {
    const idx = STAGE_ORDER.indexOf(activeStage);
    const next = STAGE_ORDER[idx + 1];
    if (next) setActiveStage(next);
  }, [activeStage]);

  const handleCreateAnnotationFromAudit = useCallback(
    (data: AnnotationCaptureData) => {
      setAnnotationPreFill(data);
      setActiveTab('review');
    },
    []
  );

  const handleAnnotationCapture = useCallback(
    async (data: AnnotationCaptureData) => {
      if (!selectedSectionId) return;
      try {
        await fetch('/api/annotations', {
          method: 'POST',
          headers: { 'Content-Type': 'application/json' },
          body: JSON.stringify({
            sectionId: selectedSectionId,
            timestamp: data.timestamp,
            text: data.text,
            drawingDataUrl: data.drawingDataUrl,
            compositeDataUrl: data.compositeDataUrl,
            videoFile: data.videoFile,
          }),
        });
        await loadAnnotations();
      } catch (err) {
        console.error(err);
      }
    },
    [selectedSectionId, loadAnnotations]
  );

  const handleBatchResolve = useCallback(async (_jobId: string) => {
    // After batch resolve completes, refresh annotations
    await loadAnnotations();
  }, [loadAnnotations]);

  const StagePanel = STAGE_PANELS[activeStage];

  return (
    <div className="flex flex-col h-screen bg-gray-950 text-white">
      {/* Tab bar */}
      <div className="flex border-b border-border">
        <button
          onClick={() => setActiveTab('pipeline')}
          className={`px-4 py-3 text-sm font-semibold ${
            activeTab === 'pipeline'
              ? 'text-white border-b-2 border-blue-500'
              : 'text-gray-400 hover:text-white'
          }`}
        >
          Pipeline
        </button>
        <button
          onClick={() => setActiveTab('review')}
          className={`px-4 py-3 text-sm font-semibold ${
            activeTab === 'review'
              ? 'text-white border-b-2 border-blue-500'
              : 'text-gray-400 hover:text-white'
          }`}
        >
          Review
        </button>
      </div>

      {/* Two-column layout */}
      <div className="flex h-full">
        {activeTab === 'pipeline' && (
          <>
            <StageSidebar activeStage={activeStage} onStageSelect={setActiveStage} />
            <main className="flex-1 p-6 overflow-y-auto">
              {loadingProject && (
                <div className="text-gray-400 mb-4">Loading project...</div>
              )}
              <StagePanel
                onAdvance={handleAdvanceStage}
                projectConfig={projectConfig}
                onCreateAnnotation={handleCreateAnnotationFromAudit}
              />
            </main>
          </>
        )}

        {activeTab === 'review' && (
          <>
            <div className="w-2/3 border-r border-border">
              <VideoPlayer
                src="/api/video/outputs/full_video.mp4"
                annotations={annotations}
                onAnnotationCapture={handleAnnotationCapture}
                // @ts-expect-error optional prop for prefill is supported by UI layer
                annotationPreFill={annotationPreFill ?? undefined}
              />
            </div>
            <div className="flex-1">
              {loadingAnnotations && (
                <div className="p-4 text-gray-400">Loading annotations...</div>
              )}
              <AnnotationPanel
                annotations={annotations}
                sectionId={selectedSection?.id ?? selectedSectionId ?? ''}
                onBatchResolve={handleBatchResolve}
              />
            </div>
          </>
        )}
      </div>
    </div>
  );
}