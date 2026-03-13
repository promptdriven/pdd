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

type ReviewRenderStatus = {
  sections: Array<{
    id: string;
    status: 'missing' | 'rendering' | 'done' | 'error';
    updatedAtMs?: number;
  }>;
  fullVideo: {
    exists: boolean;
    stale?: boolean;
    updatedAtMs?: number;
  };
};

type ProjectOption = {
  id: string;
  name: string;
};

const FULL_VIDEO_SRC = '/api/video/outputs/full_video.mp4';
const REVIEW_SECTION_STORAGE_KEY = 'video-editor-review-section';

const buildSectionVideoSrc = (sectionId: string) =>
  `/api/video/outputs/sections/${sectionId}.mp4`;

const appendVersion = (src: string, updatedAtMs?: number) => {
  if (!updatedAtMs) {
    return src;
  }

  if (src.includes('?')) {
    return `${src}&v=${updatedAtMs}`;
  }

  return `${src}?v=${updatedAtMs}`;
};

const resolveSectionIdForGlobalTime = (
  projectConfig: ProjectConfig | null,
  currentTime: number | null
): string | null => {
  if (!projectConfig || currentTime == null) {
    return null;
  }

  const sections = projectConfig.sections ?? [];
  for (let index = 0; index < sections.length; index += 1) {
    const section = sections[index];
    const start = section.offsetSeconds ?? 0;
    const end = start + section.durationSeconds;
    const isLastSection = index === sections.length - 1;

    if (currentTime >= start && (currentTime < end || (isLastSection && currentTime <= end))) {
      return section.id;
    }
  }

  return null;
};

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
  const [projectOptions, setProjectOptions] = useState<ProjectOption[]>([]);
  const [selectedProjectOptionId, setSelectedProjectOptionId] = useState<string | null>(null);
  const [switchingProject, setSwitchingProject] = useState(false);
  const [loadingAnnotations, setLoadingAnnotations] = useState<boolean>(false);
  const [reviewRenderStatus, setReviewRenderStatus] =
    useState<ReviewRenderStatus | null>(null);
  const [reviewCurrentTime, setReviewCurrentTime] = useState<number | null>(null);
  const [selectedAnnotationId, setSelectedAnnotationId] = useState<string | null>(null);
  const [annotationSeekRequest, setAnnotationSeekRequest] = useState<{
    annotationId: string;
    timestamp: number;
  } | null>(null);

  // Load project config on mount
  useEffect(() => {
    let cancelled = false;
    const loadProject = async () => {
      setLoadingProject(true);
      try {
        let data: ProjectConfig | null = null;
        let lastError: Error | null = null;

        for (let attempt = 0; attempt < 5; attempt++) {
          try {
            const res = await fetch('/api/project');
            if (!res.ok) throw new Error('Failed to load project');
            const raw = await res.text();
            if (!raw.trim()) throw new Error('Failed to load project');
            data = JSON.parse(raw) as ProjectConfig;
            break;
          } catch (err) {
            lastError =
              err instanceof Error ? err : new Error('Failed to load project');

            if (attempt < 4) {
              await new Promise((resolve) => window.setTimeout(resolve, 500));
            }
          }
        }

        if (!data) {
          throw lastError ?? new Error('Failed to load project');
        }

        if (cancelled) return;
        setProjectConfig(data);
        const storedSectionId =
          typeof window !== 'undefined'
            ? window.localStorage.getItem(REVIEW_SECTION_STORAGE_KEY)
            : null;
        const initialSection =
          data.sections?.find((section) => section.id === storedSectionId) ??
          data.sections?.[0];
        if (initialSection) {
          setSelectedSectionId(initialSection.id);
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

  useEffect(() => {
    let cancelled = false;

    const loadProjects = async () => {
      try {
        const res = await fetch('/api/projects');
        if (!res.ok) {
          throw new Error('Failed to load project list');
        }
        const data = await res.json();
        if (cancelled) return;
        setProjectOptions(data.projects ?? []);
        setSelectedProjectOptionId(data.selectedProjectId ?? null);
      } catch (err) {
        console.error(err);
      }
    };

    void loadProjects();

    return () => {
      cancelled = true;
    };
  }, []);

  useEffect(() => {
    if (typeof window === 'undefined' || !selectedSectionId) return;
    window.localStorage.setItem(REVIEW_SECTION_STORAGE_KEY, selectedSectionId);
  }, [selectedSectionId]);

  const selectedSection: Section | undefined = useMemo(() => {
    if (!projectConfig?.sections?.length) return undefined;
    return projectConfig.sections.find((s) => s.id === selectedSectionId);
  }, [projectConfig, selectedSectionId]);

  const reviewUsesFreshFullVideo = Boolean(
    reviewRenderStatus?.fullVideo?.exists && !reviewRenderStatus?.fullVideo?.stale
  );

  const annotationScopeSectionId = useMemo(() => {
    if (!reviewUsesFreshFullVideo) {
      return selectedSectionId;
    }

    return (
      resolveSectionIdForGlobalTime(projectConfig, reviewCurrentTime) ??
      selectedSectionId
    );
  }, [projectConfig, reviewCurrentTime, reviewUsesFreshFullVideo, selectedSectionId]);

  const annotationScopeSection: Section | undefined = useMemo(() => {
    if (!projectConfig?.sections?.length || !annotationScopeSectionId) return undefined;
    return projectConfig.sections.find((section) => section.id === annotationScopeSectionId);
  }, [annotationScopeSectionId, projectConfig]);

  const sectionOffsetsById = useMemo(() => {
    const offsets = new Map<string, number>();
    for (const section of projectConfig?.sections ?? []) {
      offsets.set(section.id, section.offsetSeconds ?? 0);
    }
    return offsets;
  }, [projectConfig]);

  const reviewVideoSrc = useMemo(() => {
    if (!selectedSectionId) {
      return appendVersion(FULL_VIDEO_SRC, reviewRenderStatus?.fullVideo?.updatedAtMs);
    }

    const sectionVideoSrc = buildSectionVideoSrc(selectedSectionId);
    const sectionStatus = reviewRenderStatus?.sections?.find(
      (section) => section.id === selectedSectionId
    );

    if (reviewRenderStatus?.fullVideo?.exists && !reviewRenderStatus?.fullVideo?.stale) {
      return appendVersion(FULL_VIDEO_SRC, reviewRenderStatus?.fullVideo?.updatedAtMs);
    }

    if (sectionStatus?.status === 'done') {
      return appendVersion(sectionVideoSrc, sectionStatus.updatedAtMs);
    }

    if (reviewRenderStatus?.fullVideo?.exists) {
      return appendVersion(FULL_VIDEO_SRC, reviewRenderStatus?.fullVideo?.updatedAtMs);
    }

    return appendVersion(sectionVideoSrc, sectionStatus?.updatedAtMs);
  }, [reviewRenderStatus, selectedSectionId]);

  const reviewAnnotations = useMemo(() => {
    if (!reviewUsesFreshFullVideo) {
      return annotations;
    }

    return annotations.map((annotation) => ({
      ...annotation,
      timestamp:
        annotation.timestamp == null
          ? annotation.timestamp
          : annotation.timestamp + (sectionOffsetsById.get(annotation.sectionId) ?? 0),
    }));
  }, [annotations, reviewUsesFreshFullVideo, sectionOffsetsById]);

  const resolveReviewAnnotationTimestamp = useCallback(
    (annotation: Annotation) => {
      if (annotation.timestamp == null) {
        return null;
      }

      if (!reviewUsesFreshFullVideo) {
        return annotation.timestamp;
      }

      return annotation.timestamp + (sectionOffsetsById.get(annotation.sectionId) ?? 0);
    },
    [reviewUsesFreshFullVideo, sectionOffsetsById]
  );

  const loadAnnotations = useCallback(async (sectionIdOverride?: string) => {
    const targetSectionId = sectionIdOverride ?? annotationScopeSectionId;
    if (!reviewUsesFreshFullVideo && !targetSectionId) return;
    setLoadingAnnotations(true);
    try {
      const url = reviewUsesFreshFullVideo
        ? '/api/annotations'
        : `/api/annotations?section=${targetSectionId}`;
      const res = await fetch(url);
      if (!res.ok) throw new Error('Failed to load annotations');
      const data = await res.json();
      setAnnotations(data.annotations);
    } catch (err) {
      console.error(err);
    } finally {
      setLoadingAnnotations(false);
    }
  }, [annotationScopeSectionId, reviewUsesFreshFullVideo]);

  const loadReviewRenderStatus = useCallback(async () => {
    try {
      const res = await fetch('/api/pipeline/render/status');
      if (!res.ok) throw new Error('Failed to load render status');
      const data = (await res.json()) as ReviewRenderStatus;
      setReviewRenderStatus(data);
    } catch (err) {
      console.error(err);
      setReviewRenderStatus(null);
    }
  }, []);

  // Load annotations when switching to Review tab or when section changes
  useEffect(() => {
    if (activeTab !== 'review') return;
    loadReviewRenderStatus();
  }, [activeTab, loadReviewRenderStatus]);

  useEffect(() => {
    if (activeTab !== 'review') return;
    if (!reviewUsesFreshFullVideo && !annotationScopeSectionId) return;
    loadAnnotations(annotationScopeSectionId ?? undefined);
  }, [activeTab, annotationScopeSectionId, loadAnnotations, reviewUsesFreshFullVideo]);

  const handleAdvanceStage = useCallback(() => {
    // Stage 9 continue action should switch to the Review tab
    if (activeStage === 'render') {
      setActiveTab('review');
      return;
    }
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
      const captureSectionId = annotationScopeSectionId ?? selectedSectionId;
      if (!captureSectionId) return;
      const globalTimestamp = reviewUsesFreshFullVideo
        ? reviewCurrentTime ?? data.timestamp
        : undefined;
      const effectiveSectionId =
        reviewUsesFreshFullVideo && globalTimestamp != null
          ? resolveSectionIdForGlobalTime(projectConfig, globalTimestamp) ?? captureSectionId
          : captureSectionId;
      const effectiveSection =
        projectConfig?.sections?.find((section) => section.id === effectiveSectionId) ?? null;
      const sectionTimestamp =
        reviewUsesFreshFullVideo && globalTimestamp != null && effectiveSection
          ? Math.max(0, globalTimestamp - (effectiveSection.offsetSeconds ?? 0))
          : data.timestamp;
      try {
        const createResponse = await fetch('/api/annotations', {
          method: 'POST',
          headers: { 'Content-Type': 'application/json' },
          body: JSON.stringify({
            sectionId: effectiveSectionId,
            timestamp: sectionTimestamp,
            globalTimestamp,
            sectionTimestamp,
            text: data.text,
            drawingDataUrl: data.drawingDataUrl,
            compositeDataUrl: data.compositeDataUrl,
            videoFile: data.videoFile,
            inputMethod: data.inputMethod,
          }),
        });

        if (!createResponse.ok) {
          throw new Error('Failed to create annotation');
        }

        const createdAnnotation = await createResponse.json();
        const targetSectionId = createdAnnotation?.sectionId ?? effectiveSectionId;

        if (!reviewUsesFreshFullVideo && targetSectionId !== captureSectionId) {
          setSelectedSectionId(targetSectionId);
          setAnnotations([createdAnnotation]);
        } else {
          setAnnotations((prev) => [...prev, createdAnnotation]);
        }

        if (createdAnnotation?.id) {
          void (async () => {
            try {
              const analyzeResponse = await fetch(
                `/api/annotations/${createdAnnotation.id}/analyze`,
                { method: 'POST' }
              );

              if (!analyzeResponse.ok) {
                console.error('Failed to analyze annotation', createdAnnotation.id);
              }
            } catch (analysisErr) {
              console.error(analysisErr);
            }
            await loadAnnotations(reviewUsesFreshFullVideo ? undefined : targetSectionId);
          })();
        } else {
          await loadAnnotations(reviewUsesFreshFullVideo ? undefined : targetSectionId);
        }
      } catch (err) {
        console.error(err);
      }
    },
    [
      annotationScopeSectionId,
      loadAnnotations,
      projectConfig,
      reviewCurrentTime,
      reviewUsesFreshFullVideo,
      selectedSectionId,
    ]
  );

  const handleBatchResolve = useCallback(async (_jobId: string) => {
    // After batch resolve completes, refresh annotations
    await Promise.all([loadAnnotations(), loadReviewRenderStatus()]);
  }, [loadAnnotations, loadReviewRenderStatus]);

  const handleAnnotationDeleted = useCallback((annotationId: string) => {
    setAnnotations((prev) => prev.filter((annotation) => annotation.id !== annotationId));
    setSelectedAnnotationId((prev) => (prev === annotationId ? null : prev));
  }, []);

  const handleAnnotationReverted = useCallback(async (_annotationId: string) => {
    await Promise.all([loadAnnotations(), loadReviewRenderStatus()]);
  }, [loadAnnotations, loadReviewRenderStatus]);

  const handleAnnotationUpdated = useCallback((annotation: Annotation) => {
    setAnnotations((prev) =>
      prev.map((entry) => (entry.id === annotation.id ? annotation : entry))
    );
  }, []);

  const handleAnnotationSelected = useCallback(
    (annotationId: string) => {
      const annotation = annotations.find((entry) => entry.id === annotationId);
      if (!annotation) return;

      const timestamp = resolveReviewAnnotationTimestamp(annotation);
      setSelectedAnnotationId(annotationId);

      if (timestamp == null) {
        return;
      }

      setAnnotationSeekRequest({
        annotationId,
        timestamp,
      });
    },
    [annotations, resolveReviewAnnotationTimestamp]
  );

  const handleTimelineAnnotationSelected = useCallback((annotationId: string) => {
    setSelectedAnnotationId(annotationId);
  }, []);

  const handleProjectSelection = useCallback(async (projectId: string) => {
    if (!projectId || projectId === selectedProjectOptionId) {
      return;
    }

    setSwitchingProject(true);
    try {
      const res = await fetch('/api/projects/select', {
        method: 'POST',
        headers: { 'Content-Type': 'application/json' },
        body: JSON.stringify({ projectId }),
      });
      if (!res.ok) {
        throw new Error('Failed to switch project');
      }
      window.location.reload();
    } catch (err) {
      console.error(err);
      setSwitchingProject(false);
    }
  }, [selectedProjectOptionId]);

  const StagePanel = STAGE_PANELS[activeStage];

  return (
    <div className="flex flex-col h-screen bg-gray-950 text-white">
      {/* Tab bar */}
      <div className="flex items-center justify-between border-b border-border pr-4">
        <div className="flex">
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
        <label className="flex items-center gap-2 text-xs text-gray-400">
          <span>Project</span>
          <select
            value={selectedProjectOptionId ?? ''}
            onChange={(event) => void handleProjectSelection(event.target.value)}
            disabled={switchingProject || projectOptions.length <= 1}
            className="rounded border border-border bg-gray-900 px-2 py-1 text-sm text-white disabled:opacity-60"
          >
            {projectOptions.map((project) => (
              <option key={project.id} value={project.id}>
                {project.name}
              </option>
            ))}
          </select>
        </label>
      </div>

      {/* Two-column layout */}
      <div className="flex flex-1 min-h-0">
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
                src={reviewVideoSrc}
                annotations={reviewAnnotations}
                onAnnotationCapture={handleAnnotationCapture}
                onTimeChange={setReviewCurrentTime}
                onAnnotationSelect={handleTimelineAnnotationSelected}
                seekRequest={annotationSeekRequest}
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
                sectionId={annotationScopeSection?.id ?? annotationScopeSectionId ?? ''}
                onBatchResolve={handleBatchResolve}
                onAnnotationDeleted={handleAnnotationDeleted}
                onAnnotationReverted={handleAnnotationReverted}
                onAnnotationSelect={handleAnnotationSelected}
                onAnnotationUpdated={handleAnnotationUpdated}
                selectedAnnotationId={selectedAnnotationId}
              />
            </div>
          </>
        )}
      </div>
    </div>
  );
}
