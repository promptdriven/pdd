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
import PipelineAdvanceButton from '@/components/PipelineAdvanceButton';
import {
  getPipelineAutomationDescription,
  getPipelineAutomationPlanSummary,
  type PipelineRenderStatusSnapshot,
  resolvePipelineRunPlan,
  resolveRunRemainingButtonLabel,
  type PipelineRunStep,
  type PipelineStageStatusEntry,
} from '@/lib/client/pipeline-runner';

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

type PipelineRunStepStatus = 'pending' | 'running' | 'done' | 'error';

type PipelineRunStepState = PipelineRunStep & {
  status: PipelineRunStepStatus;
  error?: string | null;
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
  auditResultsRefreshToken?: number;
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
  const [isRunningRemainingStages, setIsRunningRemainingStages] = useState(false);
  const [pipelineRunSteps, setPipelineRunSteps] = useState<PipelineRunStepState[]>([]);
  const [pipelineRunError, setPipelineRunError] = useState<string | null>(null);
  const [pipelineRunCurrentStepLabel, setPipelineRunCurrentStepLabel] = useState<string | null>(
    null
  );
  const [auditResultsRefreshToken, setAuditResultsRefreshToken] = useState<number>(0);
  const [pipelineStageStatuses, setPipelineStageStatuses] = useState<
    Partial<Record<PipelineStage, PipelineStageStatusEntry>>
  >({});
  const [pipelineRenderSnapshot, setPipelineRenderSnapshot] =
    useState<PipelineRenderStatusSnapshot | null>(null);

  const loadProjectConfig = useCallback(async () => {
    setLoadingProject(true);
    try {
      let data: ProjectConfig | null = null;
      let lastError: Error | null = null;

      for (let attempt = 0; attempt < 5; attempt += 1) {
        try {
          const res = await fetch('/api/project');
          if (!res.ok) throw new Error('Failed to load project');
          const raw = await res.text();
          if (!raw.trim()) throw new Error('Failed to load project');
          data = JSON.parse(raw) as ProjectConfig;
          break;
        } catch (err) {
          lastError = err instanceof Error ? err : new Error('Failed to load project');

          if (attempt < 4) {
            await new Promise((resolve) => window.setTimeout(resolve, 500));
          }
        }
      }

      if (!data) {
        throw lastError ?? new Error('Failed to load project');
      }

      setProjectConfig(data);
      const storedSectionId =
        typeof window !== 'undefined'
          ? window.localStorage.getItem(REVIEW_SECTION_STORAGE_KEY)
          : null;
      const initialSection =
        data.sections?.find((section) => section.id === storedSectionId) ?? data.sections?.[0];
      if (initialSection) {
        setSelectedSectionId(initialSection.id);
      }
    } catch (err) {
      console.error(err);
    } finally {
      setLoadingProject(false);
    }
  }, []);

  // Load project config on mount
  useEffect(() => {
    void loadProjectConfig();
  }, [loadProjectConfig]);

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

  const runPlan = useMemo(
    () =>
      resolvePipelineRunPlan(activeStage, {
        stageStatuses: pipelineStageStatuses,
        renderStatus: pipelineRenderSnapshot,
      }),
    [activeStage, pipelineRenderSnapshot, pipelineStageStatuses]
  );

  useEffect(() => {
    if (isRunningRemainingStages) {
      return;
    }

    setPipelineRunSteps(
      runPlan.map((step) => ({
        ...step,
        status: 'pending',
        error: null,
      }))
    );
    setPipelineRunCurrentStepLabel(null);
  }, [isRunningRemainingStages, runPlan]);

  useEffect(() => {
    if (isRunningRemainingStages) {
      return;
    }

    setPipelineRunError(null);
  }, [activeStage, isRunningRemainingStages]);

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
      setPipelineRenderSnapshot(data);
    } catch (err) {
      console.error(err);
      setReviewRenderStatus(null);
      setPipelineRenderSnapshot(null);
    }
  }, []);

  const loadPipelineAutomationContext = useCallback(async () => {
    let stageStatuses: Partial<Record<PipelineStage, PipelineStageStatusEntry>> = {};
    let renderSnapshot: PipelineRenderStatusSnapshot | null = null;

    try {
      const [statusRes, renderRes] = await Promise.all([
        fetch('/api/pipeline/status'),
        fetch('/api/pipeline/render/status'),
      ]);

      if (statusRes.ok) {
        const statusPayload = (await statusRes.json()) as {
          stages?: Partial<Record<PipelineStage, PipelineStageStatusEntry>>;
        };
        stageStatuses = statusPayload.stages ?? {};
        setPipelineStageStatuses(stageStatuses);
      }

      if (renderRes.ok) {
        const renderPayload = (await renderRes.json()) as ReviewRenderStatus;
        renderSnapshot = renderPayload;
        setPipelineRenderSnapshot(renderPayload);
      }
    } catch (err) {
      console.error(err);
    }

    return {
      stageStatuses,
      renderStatus: renderSnapshot,
    };
  }, []);

  const markPipelineRunStep = useCallback(
    (stepId: PipelineRunStep['id'], status: PipelineRunStepStatus, error?: string | null) => {
      setPipelineRunSteps((prev) =>
        prev.map((step) => (step.id === stepId ? { ...step, status, error: error ?? null } : step))
      );
    },
    []
  );

  const consumeSseResponse = useCallback(
    async (
      response: Response,
      onData?: (data: Record<string, unknown>, eventName: string | null) => void
    ) => {
      if (!response.body) {
        return;
      }

      const reader = response.body.getReader();
      const decoder = new TextDecoder();
      let buffer = '';

      const processChunk = (chunk: string) => {
        const lines = chunk.split('\n').filter(Boolean);
        const eventName =
          lines.find((line) => line.startsWith('event:'))?.slice(6).trim() ?? null;
        const dataLine = lines.find((line) => line.startsWith('data:'));

        if (!dataLine) {
          return;
        }

        let payload: Record<string, unknown> = {};
        try {
          payload = JSON.parse(dataLine.slice(5).trim()) as Record<string, unknown>;
        } catch {
          return;
        }

        onData?.(payload, eventName);

        if (eventName === 'error' || payload.type === 'error') {
          const message =
            typeof payload.message === 'string' ? payload.message : 'Pipeline step failed';
          throw new Error(message);
        }
      };

      while (true) {
        const { done, value } = await reader.read();
        if (done) {
          break;
        }

        buffer += decoder.decode(value, { stream: true });
        const parts = buffer.split('\n\n');
        buffer = parts.pop() ?? '';

        for (const part of parts) {
          processChunk(part);
        }
      }

      if (buffer.trim()) {
        processChunk(buffer);
      }
    },
    []
  );

  const waitForJobCompletion = useCallback(async (jobId: string) => {
    while (true) {
      const res = await fetch(`/api/jobs/${jobId}`);
      if (!res.ok) {
        throw new Error(`Failed to poll job ${jobId}`);
      }

      const job = (await res.json()) as {
        status?: string;
        error?: string | null;
      };

      if (job.status === 'done') {
        return;
      }

      if (job.status === 'error') {
        throw new Error(job.error || `Job ${jobId} failed`);
      }

      await new Promise((resolve) => window.setTimeout(resolve, 1000));
    }
  }, []);

  const executePipelineRunStep = useCallback(
    async (step: PipelineRunStep) => {
      if (step.mode === 'setup') {
        let extractedSections: Section[] | null = null;
        const response = await fetch(step.endpoint, { method: 'POST' });
        if (!response.ok) {
          throw new Error(`Setup request failed (${response.status})`);
        }

        await consumeSseResponse(response, (data) => {
          if (data.type === 'sections' && Array.isArray(data.sections)) {
            extractedSections = data.sections as Section[];
          }
        });

        if (!extractedSections) {
          throw new Error('Section extraction did not return any sections');
        }

        const projectResponse = await fetch('/api/project');
        if (!projectResponse.ok) {
          throw new Error('Failed to load project before saving extracted sections');
        }

        const latestProject = (await projectResponse.json()) as ProjectConfig;
        const saveResponse = await fetch('/api/project', {
          method: 'PUT',
          headers: { 'Content-Type': 'application/json' },
          body: JSON.stringify({
            ...latestProject,
            sections: extractedSections,
          }),
        });

        if (!saveResponse.ok) {
          throw new Error('Failed to save extracted sections');
        }

        await loadProjectConfig();
        return;
      }

      if (step.mode === 'job') {
        const response = await fetch(step.endpoint, {
          method: 'POST',
          headers: step.body ? { 'Content-Type': 'application/json' } : undefined,
          body: step.body ? JSON.stringify(step.body) : undefined,
        });

        const payload = (await response.json().catch(() => ({}))) as {
          error?: string;
          jobId?: string;
        };

        if (!response.ok) {
          throw new Error(payload.error || `Request failed (${response.status})`);
        }

        if (!payload.jobId) {
          throw new Error(`No job ID returned for ${step.label}`);
        }

        await waitForJobCompletion(payload.jobId);
      } else {
        const response = await fetch(step.endpoint, {
          method: 'POST',
          headers: step.body ? { 'Content-Type': 'application/json' } : undefined,
          body: step.body ? JSON.stringify(step.body) : undefined,
        });

        if (!response.ok) {
          const message = await response.text().catch(() => '');
          throw new Error(message || `Request failed (${response.status})`);
        }

        if (step.mode === 'sse') {
          await consumeSseResponse(response);
        } else {
          await response.json().catch(() => ({}));
        }
      }

      if (step.id === 'compositions' || step.id === 'render') {
        await loadProjectConfig();
      }

      if (step.id === 'render' || step.id === 'stitch' || step.id === 'audit') {
        await loadReviewRenderStatus();
      }

      if (step.id === 'audit') {
        setAuditResultsRefreshToken((current) => current + 1);
      }

      await loadPipelineAutomationContext();
    },
    [
      consumeSseResponse,
      loadPipelineAutomationContext,
      loadProjectConfig,
      loadReviewRenderStatus,
      waitForJobCompletion,
    ]
  );

  const handleRunRemainingStages = useCallback(async () => {
    if (isRunningRemainingStages) {
      return;
    }

    const latestContext = await loadPipelineAutomationContext();

    const plan = resolvePipelineRunPlan(activeStage, {
      stageStatuses: latestContext.stageStatuses,
      renderStatus: latestContext.renderStatus,
    });
    if (!plan.length) {
      setPipelineRunSteps([]);
      return;
    }

    setActiveTab('pipeline');
    setPipelineRunError(null);
    setPipelineRunSteps(
      plan.map((step) => ({
        ...step,
        status: 'pending',
        error: null,
      }))
    );
    setIsRunningRemainingStages(true);

    try {
      for (const step of plan) {
        setActiveStage(step.stage);
        setPipelineRunCurrentStepLabel(step.label);
        markPipelineRunStep(step.id, 'running');

        try {
          await executePipelineRunStep(step);
          markPipelineRunStep(step.id, 'done');
        } catch (err) {
          const message = err instanceof Error ? err.message : 'Pipeline step failed';
          markPipelineRunStep(step.id, 'error', message);
          setPipelineRunError(`${step.label} failed: ${message}`);
          return;
        }
      }
    } finally {
      setPipelineRunCurrentStepLabel(null);
      setIsRunningRemainingStages(false);
    }
  }, [
    activeStage,
    executePipelineRunStep,
    isRunningRemainingStages,
    loadPipelineAutomationContext,
    markPipelineRunStep,
  ]);

  // Load annotations when switching to Review tab or when section changes
  useEffect(() => {
    if (activeTab !== 'review') return;
    loadReviewRenderStatus();
  }, [activeTab, loadReviewRenderStatus]);

  useEffect(() => {
    if (activeTab !== 'pipeline') return;
    void loadPipelineAutomationContext();
  }, [activeStage, activeTab, loadPipelineAutomationContext]);

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

  const persistAnnotation = useCallback(
    async (
      data: AnnotationCaptureData & { sectionId?: string },
      options?: {
        sectionId?: string;
        switchToReview?: boolean;
      }
    ) => {
      const captureSectionId = options?.sectionId ?? data.sectionId ?? annotationScopeSectionId ?? selectedSectionId;
      if (!captureSectionId) return;

      const shouldSwitchToReview = options?.switchToReview ?? false;
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

      if (shouldSwitchToReview) {
        setSelectedSectionId(targetSectionId);
        setActiveTab('review');
      } else if (!reviewUsesFreshFullVideo && targetSectionId !== captureSectionId) {
        setSelectedSectionId(targetSectionId);
      }

      if (!reviewUsesFreshFullVideo && targetSectionId !== captureSectionId) {
        setAnnotations([createdAnnotation]);
      } else {
        setAnnotations((prev) => [...prev, createdAnnotation]);
      }

      if (createdAnnotation?.id) {
        setSelectedAnnotationId(createdAnnotation.id);
        setAnnotationSeekRequest({
          annotationId: createdAnnotation.id,
          timestamp:
            reviewUsesFreshFullVideo && globalTimestamp != null
              ? globalTimestamp
              : sectionTimestamp,
        });

        try {
          const analyzeResponse = await fetch(`/api/annotations/${createdAnnotation.id}/analyze`, {
            method: 'POST',
          });
          if (!analyzeResponse.ok) {
            console.error('Failed to analyze annotation', createdAnnotation.id);
          }
        } catch (analysisErr) {
          console.error(analysisErr);
        }
      }

      await loadAnnotations(reviewUsesFreshFullVideo ? undefined : targetSectionId);
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

  const handleCreateAnnotationFromAudit = useCallback(
    async (data: AnnotationCaptureData & { sectionId?: string }) => {
      setAnnotationPreFill(data);
      try {
        await persistAnnotation(data, {
          sectionId: data.sectionId,
          switchToReview: true,
        });
      } catch (err) {
        console.error(err);
        setActiveTab('review');
      }
    },
    [persistAnnotation]
  );

  const handleAnnotationCapture = useCallback(
    async (data: AnnotationCaptureData) => {
      try {
        await persistAnnotation(data);
      } catch (err) {
        console.error(err);
      }
    },
    [persistAnnotation]
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
  const pipelineRunButtonLabel = resolveRunRemainingButtonLabel({
    activeStage,
    isRunning: isRunningRemainingStages,
    currentStepLabel: pipelineRunCurrentStepLabel,
    hasError: pipelineRunError != null,
    hasRemainingSteps: runPlan.length > 0,
  });
  const pipelineAutomationDescription = getPipelineAutomationDescription(activeStage);
  const pipelineAutomationPlanSummary = getPipelineAutomationPlanSummary(runPlan);

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
              <section className="mb-6 rounded-xl border border-emerald-900/60 bg-emerald-950/30 p-4 shadow-sm">
                <div className="flex flex-col gap-4 lg:flex-row lg:items-start lg:justify-between">
                  <div className="space-y-2">
                    <div className="text-xs font-semibold uppercase tracking-[0.24em] text-emerald-300">
                      Pipeline Automation
                    </div>
                    <h2 className="text-lg font-semibold text-white">Run Remaining Stages</h2>
                    <p className="max-w-3xl text-sm text-emerald-100/80">
                      {pipelineAutomationDescription}
                    </p>
                    <p className="max-w-3xl text-sm text-emerald-200/90">
                      {pipelineAutomationPlanSummary}
                    </p>
                  </div>
                  <PipelineAdvanceButton
                    onClick={() => void handleRunRemainingStages()}
                    disabled={loadingProject || isRunningRemainingStages || runPlan.length === 0}
                    label={pipelineRunButtonLabel}
                    className="self-start rounded-lg"
                  />
                </div>

                {pipelineRunError && (
                  <div className="mt-4 rounded-lg border border-red-900/80 bg-red-950/40 px-3 py-2 text-sm text-red-200">
                    {pipelineRunError}
                  </div>
                )}

                <div className="mt-4 flex flex-wrap gap-2">
                  {pipelineRunSteps.map((step) => {
                    const badgeClassName =
                      step.status === 'done'
                        ? 'border-emerald-500/60 bg-emerald-500/15 text-emerald-200'
                        : step.status === 'running'
                        ? 'border-blue-500/60 bg-blue-500/15 text-blue-200'
                        : step.status === 'error'
                        ? 'border-red-500/60 bg-red-500/15 text-red-200'
                        : 'border-slate-700 bg-slate-900/80 text-slate-300';
                    const statusLabel =
                      step.status === 'done'
                        ? 'Done'
                        : step.status === 'running'
                        ? 'Running'
                        : step.status === 'error'
                        ? 'Error'
                        : 'Queued';

                    return (
                      <div
                        key={step.id}
                        className={`rounded-full border px-3 py-1.5 text-xs font-medium ${badgeClassName}`}
                        title={step.error ?? undefined}
                      >
                        {step.label} · {statusLabel}
                      </div>
                    );
                  })}
                </div>
              </section>
              {loadingProject && (
                <div className="text-gray-400 mb-4">Loading project...</div>
              )}
              <StagePanel
                onAdvance={handleAdvanceStage}
                projectConfig={projectConfig}
                auditResultsRefreshToken={auditResultsRefreshToken}
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
