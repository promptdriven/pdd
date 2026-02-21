// example_usage.ts
// Comprehensive usage example for lib/types.ts
// All types are imported from the central type definitions module.

import type {
  // 1. Pipeline Stage & Status Types
  PipelineStage,
  StageStatus,

  // 2. Job Types
  JobStatus,
  Job,

  // 3. Annotation Types
  FixType,
  AnnotationAnalysis,
  Annotation,
  AnnotationCaptureData,
  ClaudeFixResult,

  // 4. Section & Project Config Types
  Section,
  TtsConfig,
  VeoConfig,
  RenderConfig,
  AudioSyncConfig,
  ProjectConfig,

  // 5. Utility / Helper Types
  RenderProgress,
  SseSend,
} from './lib/types';

// ============================================================================
// Example 1: Defining the ordered pipeline stages and tracking their status
// ============================================================================

/**
 * ALL_STAGES: The canonical ordering of pipeline stages.
 * This ordering drives the UI stepper and determines execution sequence.
 */
const ALL_STAGES: PipelineStage[] = [
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

/**
 * Build an initial stage-status map where every stage starts as 'not_started'.
 * Returns: Record<PipelineStage, StageStatus>
 */
function initStageMap(): Record<PipelineStage, StageStatus> {
  const map = {} as Record<PipelineStage, StageStatus>;
  for (const stage of ALL_STAGES) {
    map[stage] = 'not_started';
  }
  return map;
}

const stageMap = initStageMap();
stageMap['setup'] = 'done';
stageMap['script'] = 'running';
console.log('Stage map:', stageMap);
// => { setup: 'done', script: 'running', 'tts-script': 'not_started', ... }

// ============================================================================
// Example 2: Creating and inspecting a Job
// ============================================================================

/**
 * Construct a Job object representing a TTS render task.
 *
 * Fields:
 *   id          – unique job identifier (UUID)
 *   stage       – which PipelineStage this job belongs to
 *   status      – current JobStatus lifecycle state
 *   progress    – 0-100 integer percentage
 *   error       – error message string, or null if no error
 *   params      – opaque Record<string, unknown> serialized as JSON in SQLite
 *   createdAt   – ISO 8601 timestamp
 *   updatedAt   – ISO 8601 timestamp
 */
const ttsJob: Job = {
  id: 'job-abc-123',
  stage: 'tts-render',
  status: 'running',
  progress: 45,
  error: null,
  params: {
    sectionId: 'intro',
    voice: 'en-US-Neural2-F',
    retryCount: 0,
  },
  createdAt: '2025-01-15T10:00:00Z',
  updatedAt: '2025-01-15T10:02:30Z',
};

/** Type guard: check if a job has completed (successfully or with error). */
function isJobTerminal(job: Job): boolean {
  return job.status === 'done' || job.status === 'error';
}

console.log(`Job ${ttsJob.id} terminal?`, isJobTerminal(ttsJob)); // false

// Simulate job completion
const completedJob: Job = { ...ttsJob, status: 'done', progress: 100 };
console.log(`Job ${completedJob.id} terminal?`, isJobTerminal(completedJob)); // true

// ============================================================================
// Example 3: Working with Annotations and AnnotationAnalysis
// ============================================================================

/**
 * AnnotationAnalysis is the structured result Claude returns when analyzing
 * a user annotation. The JSON schema Claude is prompted with matches this
 * interface exactly.
 *
 * Fields:
 *   severity            – 'critical' | 'major' | 'minor' | 'pass'
 *   fixType             – which automated fix pipeline to invoke
 *   technicalAssessment – free-text explanation from Claude
 *   suggestedFixes      – array of actionable fix descriptions
 *   confidence          – float 0.0–1.0
 */
const analysis: AnnotationAnalysis = {
  severity: 'major',
  fixType: 'remotion',
  technicalAssessment:
    'Text overlay at 3.2s is clipped by the safe-zone boundary on the right edge.',
  suggestedFixes: [
    'Reduce font size from 48px to 40px',
    'Add paddingRight: 60 to the text container style',
  ],
  confidence: 0.87,
};

/**
 * An Annotation represents a user-created note on a specific section's video.
 *
 * Fields:
 *   id               – unique annotation ID
 *   sectionId        – which Section this annotation targets
 *   timestamp        – playback time in seconds where the issue occurs
 *   text             – user-provided description of the issue
 *   videoFile        – path to the video file at time of annotation (nullable)
 *   drawingDataUrl   – base64 data URL of the user's freehand drawing (nullable)
 *   compositeDataUrl – base64 data URL of video frame + drawing overlay (nullable)
 *   analysis         – Claude's structured analysis result (nullable until analyzed)
 *   resolved         – whether the annotation has been fixed
 *   resolveJobId     – ID of the Job that attempted the fix (nullable)
 *   createdAt        – ISO 8601 timestamp
 */
const annotation: Annotation = {
  id: 'ann-001',
  sectionId: 'section-intro',
  timestamp: 3.2,
  text: 'Text is cut off on the right side',
  videoFile: 'output/intro.mp4',
  drawingDataUrl: 'data:image/png;base64,iVBORw0KGgo...',
  compositeDataUrl: 'data:image/png;base64,iVBORw0KGgo...',
  analysis,
  resolved: false,
  resolveJobId: null,
  createdAt: '2025-01-15T11:00:00Z',
};

console.log(
  `Annotation "${annotation.text}" severity: ${annotation.analysis?.severity}`
);

// ============================================================================
// Example 4: AnnotationCaptureData from the VideoPlayer component
// ============================================================================

/**
 * AnnotationCaptureData is emitted by the VideoPlayer UI component when a user
 * pauses the video, draws on the frame, and submits an annotation.
 *
 * Fields:
 *   timestamp        – current playback position in seconds
 *   text             – user-entered annotation text
 *   drawingDataUrl   – base64 PNG of the drawing layer (nullable if no drawing)
 *   compositeDataUrl – base64 PNG of frame + drawing merged (nullable)
 *   videoFile        – relative path to the video being annotated
 */
function handleAnnotationCapture(data: AnnotationCaptureData): Annotation {
  return {
    id: `ann-1771715694829`,
    sectionId: 'section-intro', // determined by current UI context
    timestamp: data.timestamp,
    text: data.text,
    videoFile: data.videoFile,
    drawingDataUrl: data.drawingDataUrl,
    compositeDataUrl: data.compositeDataUrl,
    analysis: null, // not yet analyzed
    resolved: false,
    resolveJobId: null,
    createdAt: new Date().toISOString(),
  };
}

const captureData: AnnotationCaptureData = {
  timestamp: 5.4,
  text: 'Logo appears too late',
  drawingDataUrl: null,
  compositeDataUrl: null,
  videoFile: 'output/intro.mp4',
};

const newAnnotation = handleAnnotationCapture(captureData);
console.log('Created annotation:', newAnnotation.id);

// ============================================================================
// Example 5: ClaudeFixResult after an automated fix attempt
// ============================================================================

/**
 * ClaudeFixResult is returned after Claude applies an automated fix.
 *
 * Fields:
 *   fixType           – which fix pipeline was used ('remotion' | 'veo' | 'tts' | 'none')
 *   filesModified     – list of file paths that were changed
 *   changeDescription – human-readable summary of what was changed
 *   confidence        – float 0.0–1.0 indicating fix confidence
 */
const fixResult: ClaudeFixResult = {
  fixType: 'remotion',
  filesModified: [
    'remotion/intro/TextOverlay.tsx',
    'remotion/intro/styles.ts',
  ],
  changeDescription:
    'Reduced font size from 48px to 40px and added 60px right padding to prevent text clipping.',
  confidence: 0.92,
};

console.log(`Fix applied to ${fixResult.filesModified.length} files`);

// ============================================================================
// Example 6: Building a complete ProjectConfig (matches project.json on disk)
// ============================================================================

/**
 * Section represents one video segment. Ordering in the sections array
 * determines ffmpeg concat order and cumulative audio offset calculations.
 *
 * Fields:
 *   id              – unique section identifier
 *   label           – human-readable name shown in the UI
 *   videoFile       – relative path from project root to the rendered MP4
 *   specDir         – directory containing spec files for this section
 *   remotionDir     – directory containing Remotion composition source
 *   compositionId   – Remotion composition ID used for rendering
 *   durationSeconds – duration of this section in seconds
 *   offsetSeconds   – cumulative offset from the start of the final video
 */
const sections: Section[] = [
  {
    id: 'intro',
    label: 'Introduction',
    videoFile: 'output/sections/intro.mp4',
    specDir: 'specs/intro',
    remotionDir: 'remotion/intro',
    compositionId: 'IntroComposition',
    durationSeconds: 12.5,
    offsetSeconds: 0,
  },
  {
    id: 'main',
    label: 'Main Content',
    videoFile: 'output/sections/main.mp4',
    specDir: 'specs/main',
    remotionDir: 'remotion/main',
    compositionId: 'MainComposition',
    durationSeconds: 45.0,
    offsetSeconds: 12.5, // starts after intro
  },
  {
    id: 'outro',
    label: 'Outro',
    videoFile: 'output/sections/outro.mp4',
    specDir: 'specs/outro',
    remotionDir: 'remotion/outro',
    compositionId: 'OutroComposition',
    durationSeconds: 8.0,
    offsetSeconds: 57.5, // starts after intro + main
  },
];

const ttsConfig: TtsConfig = {
  voice: 'en-US-Neural2-F',
  rate: 1.0,
  model: 'google-tts-v2',
};

const veoConfig: VeoConfig = {
  model: 'veo-2.0-generate-001',
  aspectRatio: '16:9',
  referenceImages: {
    logo: 'assets/logo.png',
    background: 'assets/bg-gradient.png',
  },
};

const renderConfig: RenderConfig = {
  maxParallelRenders: 3,
  outputDir: 'output/final',
  fps: 30,
  width: 1920,
  height: 1080,
};

const audioSyncConfig: AudioSyncConfig = {
  sectionGroups: {
    narration: ['intro', 'main', 'outro'],
    music: ['intro', 'outro'],
  },
};

/**
 * ProjectConfig is the top-level configuration that maps 1:1 to the on-disk
 * project.json file. Zod validation in lib/project.ts validates against this shape.
 *
 * Fields:
 *   name             – project display name
 *   outputResolution – final video resolution ('1920x1080' or '1280x720')
 *   tts              – text-to-speech engine settings
 *   sections         – ordered array of video sections
 *   audioSync        – audio synchronization group mappings
 *   veo              – Google Veo video generation settings
 *   render           – Remotion/ffmpeg render settings
 */
const projectConfig: ProjectConfig = {
  name: 'Product Launch Video',
  outputResolution: '1920x1080',
  tts: ttsConfig,
  sections,
  audioSync: audioSyncConfig,
  veo: veoConfig,
  render: renderConfig,
};

console.log(`Project "${projectConfig.name}" has ${projectConfig.sections.length} sections`);
console.log(
  'Total duration:',
  projectConfig.sections.reduce((sum, s) => sum + s.durationSeconds, 0),
  'seconds'
);

// ============================================================================
// Example 7: Using RenderProgress and SseSend for streaming render updates
// ============================================================================

/**
 * SseSend is a callback type used across API routes and lib/jobs.ts to push
 * Server-Sent Events data to the client.
 *
 * Signature: (data: object) => void
 */

/**
 * RenderProgress represents a progress update emitted during rendering.
 *
 * Fields:
 *   percent – completion percentage (0–100)
 *   message – human-readable status message
 */

/**
 * Simulates a render pipeline that emits progress updates via SSE.
 *
 * @param config   - The project's render configuration
 * @param sections - Ordered sections to render
 * @param send     - SSE callback to stream progress to the client
 */
async function simulateRender(
  config: RenderConfig,
  sections: Section[],
  send: SseSend
): Promise<void> {
  for (let i = 0; i < sections.length; i++) {
    const section = sections[i];
    const progress: RenderProgress = {
      percent: Math.round(((i + 1) / sections.length) * 100),
      message: `Rendering ${section.label} at ${config.fps}fps (${config.width}x${config.height})`,
    };

    // Send progress update via SSE
    send({
      type: 'render-progress',
      sectionId: section.id,
      ...progress,
    });

    console.log(`[${progress.percent}%] ${progress.message}`);
  }

  send({ type: 'render-complete', totalSections: sections.length });
}

// Example SSE send function (in a real app this writes to a Response stream)
const mockSseSend: SseSend = (data: object) => {
  console.log('SSE →', JSON.stringify(data));
};

// Run the simulated render
simulateRender(projectConfig.render, projectConfig.sections, mockSseSend);

// ============================================================================
// Example 8: Type-safe stage transitions
// ============================================================================

/**
 * Demonstrates using PipelineStage and StageStatus together to build
 * a type-safe state machine for pipeline progression.
 */
interface StageTransition {
  from: PipelineStage;
  to: PipelineStage;
  fromStatus: StageStatus;
  toStatus: StageStatus;
}

function advanceStage(
  current: PipelineStage,
  stageStatuses: Record<PipelineStage, StageStatus>
): StageTransition | null {
  const currentIndex = ALL_STAGES.indexOf(current);
  if (currentIndex < 0 || currentIndex >= ALL_STAGES.length - 1) return null;
  if (stageStatuses[current] !== 'done') return null;

  const next = ALL_STAGES[currentIndex + 1];
  stageStatuses[next] = 'running';

  return {
    from: current,
    to: next,
    fromStatus: 'done',
    toStatus: 'running',
  };
}

const statuses = initStageMap();
statuses['setup'] = 'done';

const transition = advanceStage('setup', statuses);
console.log('Transition:', transition);
// => { from: 'setup', to: 'script', fromStatus: 'done', toStatus: 'running' }

// ============================================================================
// Example 9: Filtering annotations by severity using FixType
// ============================================================================

/**
 * Filter annotations that need automated fixes (fixType !== 'none')
 * and sort by severity priority.
 */
function getActionableAnnotations(annotations: Annotation[]): Annotation[] {
  const severityOrder: Record<string, number> = {
    critical: 0,
    major: 1,
    minor: 2,
    pass: 3,
  };

  return annotations
    .filter((a) => a.analysis !== null && a.analysis.fixType !== 'none' && !a.resolved)
    .sort(
      (a, b) =>
        severityOrder[a.analysis!.severity] - severityOrder[b.analysis!.severity]
    );
}

const sampleAnnotations: Annotation[] = [
  annotation, // major severity, fixType: 'remotion'
  {
    ...annotation,
    id: 'ann-002',
    text: 'Audio slightly off',
    analysis: {
      severity: 'minor',
      fixType: 'tts',
      technicalAssessment: 'TTS timing drift of ~200ms',
      suggestedFixes: ['Re-render TTS with adjusted pacing'],
      confidence: 0.75,
    },
  },
  {
    ...annotation,
    id: 'ann-003',
    text: 'Looks good here',
    analysis: {
      severity: 'pass',
      fixType: 'none',
      technicalAssessment: 'No issues detected',
      suggestedFixes: [],
      confidence: 0.95,
    },
  },
];

const actionable = getActionableAnnotations(sampleAnnotations);
console.log(
  'Actionable annotations:',
  actionable.map((a) => `${a.id} (${a.analysis!.severity})`)
);
// => ['ann-001 (major)', 'ann-002 (minor)']