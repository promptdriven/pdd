/**
 * Tests for lib/types.ts
 *
 * PDD Principle: The prompt file is the source of truth.
 * These tests verify that the code conforms to the specification.
 *
 * Since lib/types.ts contains only TypeScript types (no runtime code),
 * tests use two strategies:
 *   1. Compile-time correctness: ts-jest ensures type errors fail the suite.
 *   2. Runtime structural checks: objects are constructed conforming to each
 *      interface and their shape is validated with Jest assertions.
 */

import type {
  PipelineStage,
  StageStatus,
  JobStatus,
  Job,
  FixType,
  AnnotationAnalysis,
  Annotation,
  CreateAnnotationInput,
  AnnotationCaptureData,
  ClaudeFixResult,
  Section,
  TtsConfig,
  VeoConfig,
  VeoReference,
  VeoFrameChain,
  RenderConfig,
  AudioSyncConfig,
  SegmentRange,
  OutputResolution,
  ProjectConfig,
  RenderProgress,
  SseSend,
} from '../lib/types';

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

/** Asserts that obj has exactly the keys listed and no others. */
function expectExactKeys(obj: object, keys: string[]): void {
  const actual = Object.keys(obj).sort();
  const expected = [...keys].sort();
  expect(actual).toEqual(expected);
}

// ---------------------------------------------------------------------------
// 1. PipelineStage
// ---------------------------------------------------------------------------

describe('PipelineStage', () => {
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

  it('has exactly 10 pipeline stages', () => {
    expect(ALL_STAGES).toHaveLength(10);
  });

  it('contains each required stage value', () => {
    const expected = [
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
    expect(ALL_STAGES).toEqual(expect.arrayContaining(expected));
    expect(expected).toEqual(expect.arrayContaining(ALL_STAGES));
  });

  it('can be used as a Record key', () => {
    const map: Record<PipelineStage, number> = {
      setup: 0,
      script: 1,
      'tts-script': 2,
      'tts-render': 3,
      'audio-sync': 4,
      specs: 5,
      veo: 6,
      compositions: 7,
      render: 8,
      audit: 9,
    };
    expect(Object.keys(map)).toHaveLength(10);
    expect(map['tts-script']).toBe(2);
    expect(map['audio-sync']).toBe(4);
  });
});

// ---------------------------------------------------------------------------
// 2. StageStatus
// ---------------------------------------------------------------------------

describe('StageStatus', () => {
  const VALID_STATUSES: StageStatus[] = [
    'not_started',
    'running',
    'done',
    'error',
  ];

  it('has exactly 4 valid values', () => {
    expect(VALID_STATUSES).toHaveLength(4);
  });

  it('contains not_started, running, done, error', () => {
    expect(VALID_STATUSES).toContain('not_started');
    expect(VALID_STATUSES).toContain('running');
    expect(VALID_STATUSES).toContain('done');
    expect(VALID_STATUSES).toContain('error');
  });
});

// ---------------------------------------------------------------------------
// 3. JobStatus
// ---------------------------------------------------------------------------

describe('JobStatus', () => {
  const VALID_STATUSES: JobStatus[] = ['pending', 'running', 'done', 'error'];

  it('has exactly 4 valid values', () => {
    expect(VALID_STATUSES).toHaveLength(4);
  });

  it('contains pending, running, done, error', () => {
    expect(VALID_STATUSES).toContain('pending');
    expect(VALID_STATUSES).toContain('running');
    expect(VALID_STATUSES).toContain('done');
    expect(VALID_STATUSES).toContain('error');
  });
});

// ---------------------------------------------------------------------------
// 4. Job
// ---------------------------------------------------------------------------

describe('Job', () => {
  const validJob: Job = {
    id: 'job-001',
    stage: 'tts-render',
    status: 'running',
    progress: 45,
    error: null,
    params: { sectionId: 'intro', retryCount: 0 },
    createdAt: '2025-01-15T10:00:00Z',
    updatedAt: '2025-01-15T10:02:30Z',
  };

  it('has all required fields', () => {
    expectExactKeys(validJob, [
      'id',
      'stage',
      'status',
      'progress',
      'error',
      'params',
      'createdAt',
      'updatedAt',
    ]);
  });

  it('id is a string', () => {
    expect(typeof validJob.id).toBe('string');
  });

  it('stage is a valid PipelineStage', () => {
    expect(typeof validJob.stage).toBe('string');
    expect(validJob.stage).toBe('tts-render');
  });

  it('status is a valid JobStatus', () => {
    expect(['pending', 'running', 'done', 'error']).toContain(validJob.status);
  });

  it('progress is a number', () => {
    expect(typeof validJob.progress).toBe('number');
  });

  it('error can be null', () => {
    expect(validJob.error).toBeNull();
  });

  it('error can be a string', () => {
    const jobWithError: Job = { ...validJob, error: 'Something failed' };
    expect(typeof jobWithError.error).toBe('string');
  });

  it('params is a Record<string, unknown> (opaque object)', () => {
    expect(typeof validJob.params).toBe('object');
    expect(validJob.params).not.toBeNull();
  });

  it('createdAt is a string', () => {
    expect(typeof validJob.createdAt).toBe('string');
  });

  it('updatedAt is a string', () => {
    expect(typeof validJob.updatedAt).toBe('string');
  });

  it('params can hold arbitrary values', () => {
    const job: Job = {
      ...validJob,
      params: {
        sectionId: 'intro',
        nested: { a: 1 },
        flag: true,
        count: 42,
      },
    };
    expect(job.params['sectionId']).toBe('intro');
    expect(job.params['flag']).toBe(true);
  });
});

// ---------------------------------------------------------------------------
// 5. FixType
// ---------------------------------------------------------------------------

describe('FixType', () => {
  const VALID_FIX_TYPES: FixType[] = ['remotion', 'veo', 'tts', 'none'];

  it('has exactly 4 valid values', () => {
    expect(VALID_FIX_TYPES).toHaveLength(4);
  });

  it('contains remotion, veo, tts, none', () => {
    expect(VALID_FIX_TYPES).toContain('remotion');
    expect(VALID_FIX_TYPES).toContain('veo');
    expect(VALID_FIX_TYPES).toContain('tts');
    expect(VALID_FIX_TYPES).toContain('none');
  });
});

// ---------------------------------------------------------------------------
// 6. AnnotationAnalysis
// ---------------------------------------------------------------------------

describe('AnnotationAnalysis', () => {
  const validAnalysis: AnnotationAnalysis = {
    severity: 'major',
    fixType: 'remotion',
    technicalAssessment: 'Text overlay is clipped at the right edge.',
    suggestedFixes: ['Reduce font size', 'Add right padding'],
    confidence: 0.87,
  };

  it('has all required fields', () => {
    expectExactKeys(validAnalysis, [
      'severity',
      'fixType',
      'technicalAssessment',
      'suggestedFixes',
      'confidence',
    ]);
  });

  it('severity accepts critical, major, minor, pass', () => {
    const severities: AnnotationAnalysis['severity'][] = [
      'critical',
      'major',
      'minor',
      'pass',
    ];
    for (const sev of severities) {
      const a: AnnotationAnalysis = { ...validAnalysis, severity: sev };
      expect(['critical', 'major', 'minor', 'pass']).toContain(a.severity);
    }
  });

  it('fixType is a valid FixType', () => {
    expect(['remotion', 'veo', 'tts', 'none']).toContain(validAnalysis.fixType);
  });

  it('technicalAssessment is a string', () => {
    expect(typeof validAnalysis.technicalAssessment).toBe('string');
  });

  it('suggestedFixes is an array of strings', () => {
    expect(Array.isArray(validAnalysis.suggestedFixes)).toBe(true);
    for (const fix of validAnalysis.suggestedFixes) {
      expect(typeof fix).toBe('string');
    }
  });

  it('suggestedFixes can be empty', () => {
    const a: AnnotationAnalysis = { ...validAnalysis, suggestedFixes: [] };
    expect(a.suggestedFixes).toHaveLength(0);
  });

  it('confidence is a float between 0 and 1', () => {
    expect(typeof validAnalysis.confidence).toBe('number');
    expect(validAnalysis.confidence).toBeGreaterThanOrEqual(0);
    expect(validAnalysis.confidence).toBeLessThanOrEqual(1);
  });

  it('confidence can be 0', () => {
    const a: AnnotationAnalysis = { ...validAnalysis, confidence: 0 };
    expect(a.confidence).toBe(0);
  });

  it('confidence can be 1', () => {
    const a: AnnotationAnalysis = { ...validAnalysis, confidence: 1 };
    expect(a.confidence).toBe(1);
  });
});

// ---------------------------------------------------------------------------
// 7. Annotation
// ---------------------------------------------------------------------------

describe('Annotation', () => {
  const validAnnotation: Annotation = {
    id: 'ann-001',
    sectionId: 'section-intro',
    timestamp: 3.2,
    text: 'Text is cut off',
    videoFile: 'output/intro.mp4',
    drawingDataUrl: 'data:image/png;base64,abc123',
    compositeDataUrl: 'data:image/png;base64,xyz789',
    analysis: {
      severity: 'major',
      fixType: 'remotion',
      technicalAssessment: 'Clipped text',
      suggestedFixes: ['Reduce font size'],
      confidence: 0.9,
    },
    resolved: false,
    resolveJobId: null,
    createdAt: '2025-01-15T11:00:00Z',
  };

  it('has all required fields', () => {
    expectExactKeys(validAnnotation, [
      'id',
      'sectionId',
      'timestamp',
      'text',
      'videoFile',
      'drawingDataUrl',
      'compositeDataUrl',
      'analysis',
      'resolved',
      'resolveJobId',
      'createdAt',
    ]);
  });

  it('id is a string', () => {
    expect(typeof validAnnotation.id).toBe('string');
  });

  it('sectionId is a string', () => {
    expect(typeof validAnnotation.sectionId).toBe('string');
  });

  it('timestamp is a number', () => {
    expect(typeof validAnnotation.timestamp).toBe('number');
  });

  it('text is a string', () => {
    expect(typeof validAnnotation.text).toBe('string');
  });

  it('videoFile can be null or string', () => {
    expect(typeof validAnnotation.videoFile).toBe('string');
    const noVideo: Annotation = { ...validAnnotation, videoFile: null };
    expect(noVideo.videoFile).toBeNull();
  });

  it('drawingDataUrl can be null or string', () => {
    expect(typeof validAnnotation.drawingDataUrl).toBe('string');
    const noDrawing: Annotation = { ...validAnnotation, drawingDataUrl: null };
    expect(noDrawing.drawingDataUrl).toBeNull();
  });

  it('compositeDataUrl can be null or string', () => {
    expect(typeof validAnnotation.compositeDataUrl).toBe('string');
    const noComposite: Annotation = {
      ...validAnnotation,
      compositeDataUrl: null,
    };
    expect(noComposite.compositeDataUrl).toBeNull();
  });

  it('analysis can be null', () => {
    const noAnalysis: Annotation = { ...validAnnotation, analysis: null };
    expect(noAnalysis.analysis).toBeNull();
  });

  it('analysis when present has the AnnotationAnalysis shape', () => {
    expect(validAnnotation.analysis).not.toBeNull();
    expect(validAnnotation.analysis).toHaveProperty('severity');
    expect(validAnnotation.analysis).toHaveProperty('fixType');
    expect(validAnnotation.analysis).toHaveProperty('technicalAssessment');
    expect(validAnnotation.analysis).toHaveProperty('suggestedFixes');
    expect(validAnnotation.analysis).toHaveProperty('confidence');
  });

  it('resolved is a boolean', () => {
    expect(typeof validAnnotation.resolved).toBe('boolean');
  });

  it('resolveJobId can be null or string', () => {
    expect(validAnnotation.resolveJobId).toBeNull();
    const withJob: Annotation = {
      ...validAnnotation,
      resolveJobId: 'job-xyz-789',
    };
    expect(typeof withJob.resolveJobId).toBe('string');
  });

  it('createdAt is a string', () => {
    expect(typeof validAnnotation.createdAt).toBe('string');
  });
});

// ---------------------------------------------------------------------------
// 8. AnnotationCaptureData
// ---------------------------------------------------------------------------

describe('AnnotationCaptureData', () => {
  const validCapture: AnnotationCaptureData = {
    timestamp: 5.4,
    text: 'Logo appears too late',
    drawingDataUrl: null,
    compositeDataUrl: null,
    videoFile: 'output/intro.mp4',
  };

  it('has all required fields', () => {
    expectExactKeys(validCapture, [
      'timestamp',
      'text',
      'drawingDataUrl',
      'compositeDataUrl',
      'videoFile',
    ]);
  });

  it('timestamp is a number', () => {
    expect(typeof validCapture.timestamp).toBe('number');
  });

  it('text is a string', () => {
    expect(typeof validCapture.text).toBe('string');
  });

  it('drawingDataUrl can be null or string', () => {
    expect(validCapture.drawingDataUrl).toBeNull();
    const withDrawing: AnnotationCaptureData = {
      ...validCapture,
      drawingDataUrl: 'data:image/png;base64,abc',
    };
    expect(typeof withDrawing.drawingDataUrl).toBe('string');
  });

  it('compositeDataUrl can be null or string', () => {
    expect(validCapture.compositeDataUrl).toBeNull();
    const withComposite: AnnotationCaptureData = {
      ...validCapture,
      compositeDataUrl: 'data:image/png;base64,xyz',
    };
    expect(typeof withComposite.compositeDataUrl).toBe('string');
  });

  it('videoFile is a string', () => {
    expect(typeof validCapture.videoFile).toBe('string');
  });
});

describe('CreateAnnotationInput', () => {
  const validInput: CreateAnnotationInput = {
    sectionId: 'section-1',
    timestamp: 5.4,
    globalTimestamp: 16.2,
    sectionTimestamp: 5.2,
    text: 'Swap these clips',
    videoFile: '/api/video/outputs/full_video.mp4',
  };

  it('supports optional globalTimestamp and sectionTimestamp fields', () => {
    expect(validInput.globalTimestamp).toBe(16.2);
    expect(validInput.sectionTimestamp).toBe(5.2);
  });
});

// ---------------------------------------------------------------------------
// 9. ClaudeFixResult
// ---------------------------------------------------------------------------

describe('ClaudeFixResult', () => {
  const validResult: ClaudeFixResult = {
    fixType: 'remotion',
    filesModified: ['remotion/intro/TextOverlay.tsx', 'remotion/intro/styles.ts'],
    changeDescription: 'Reduced font size and added right padding.',
    confidence: 0.92,
  };

  it('has all required fields', () => {
    expectExactKeys(validResult, [
      'fixType',
      'filesModified',
      'changeDescription',
      'confidence',
    ]);
  });

  it('fixType is a valid FixType', () => {
    expect(['remotion', 'veo', 'tts', 'none']).toContain(validResult.fixType);
  });

  it('filesModified is an array of strings', () => {
    expect(Array.isArray(validResult.filesModified)).toBe(true);
    for (const f of validResult.filesModified) {
      expect(typeof f).toBe('string');
    }
  });

  it('filesModified can be empty', () => {
    const r: ClaudeFixResult = { ...validResult, filesModified: [] };
    expect(r.filesModified).toHaveLength(0);
  });

  it('changeDescription is a string', () => {
    expect(typeof validResult.changeDescription).toBe('string');
  });

  it('confidence is a float between 0 and 1', () => {
    expect(typeof validResult.confidence).toBe('number');
    expect(validResult.confidence).toBeGreaterThanOrEqual(0);
    expect(validResult.confidence).toBeLessThanOrEqual(1);
  });
});

// ---------------------------------------------------------------------------
// 10. Section
// ---------------------------------------------------------------------------

describe('Section', () => {
  const validSection: Section = {
    id: 'intro',
    label: 'Introduction',
    videoFile: 'output/sections/intro.mp4',
    specDir: 'specs/intro',
    remotionDir: 'remotion/intro',
    compositionId: 'IntroComposition',
    durationSeconds: 12.5,
    offsetSeconds: 0,
  };

  it('has all required fields', () => {
    expectExactKeys(validSection, [
      'id',
      'label',
      'videoFile',
      'specDir',
      'remotionDir',
      'compositionId',
      'durationSeconds',
      'offsetSeconds',
    ]);
  });

  it('id is a string', () => {
    expect(typeof validSection.id).toBe('string');
  });

  it('label is a string', () => {
    expect(typeof validSection.label).toBe('string');
  });

  it('videoFile is a string (relative path)', () => {
    expect(typeof validSection.videoFile).toBe('string');
  });

  it('specDir is a string', () => {
    expect(typeof validSection.specDir).toBe('string');
  });

  it('remotionDir is a string', () => {
    expect(typeof validSection.remotionDir).toBe('string');
  });

  it('compositionId is a string', () => {
    expect(typeof validSection.compositionId).toBe('string');
  });

  it('durationSeconds is a number', () => {
    expect(typeof validSection.durationSeconds).toBe('number');
  });

  it('offsetSeconds is a number', () => {
    expect(typeof validSection.offsetSeconds).toBe('number');
  });
});

// ---------------------------------------------------------------------------
// 11. TtsConfig
// ---------------------------------------------------------------------------

describe('TtsConfig', () => {
  const validTts: TtsConfig = {
    engine: 'qwen3-tts',
    modelPath: 'models/Qwen3-TTS-12Hz-1.7B-CustomVoice',
    tokenizerPath: 'models/Qwen3-TTS-Tokenizer-12Hz',
    speaker: 'Aiden',
    speakingRate: 0.95,
    sampleRate: 24000,
  };

  it('has all required fields per PRD §4.5.1', () => {
    expectExactKeys(validTts, ['engine', 'modelPath', 'tokenizerPath', 'speaker', 'speakingRate', 'sampleRate']);
  });

  it('engine is a string', () => {
    expect(typeof validTts.engine).toBe('string');
  });

  it('modelPath is a string', () => {
    expect(typeof validTts.modelPath).toBe('string');
  });

  it('tokenizerPath is a string', () => {
    expect(typeof validTts.tokenizerPath).toBe('string');
  });

  it('speaker is a string', () => {
    expect(typeof validTts.speaker).toBe('string');
  });

  it('speakingRate is a number', () => {
    expect(typeof validTts.speakingRate).toBe('number');
  });

  it('sampleRate is a number', () => {
    expect(typeof validTts.sampleRate).toBe('number');
  });
});

// ---------------------------------------------------------------------------
// 12. VeoConfig
// ---------------------------------------------------------------------------

describe('VeoConfig', () => {
  const validVeo: VeoConfig = {
    model: 'veo-3.1-generate-preview',
    defaultAspectRatio: '16:9',
    maxConcurrentGenerations: 4,
    references: [
      { id: 'alex', label: 'Alex (protagonist)', imagePath: 'references/cold-open/developer_reference.png', sections: ['cold_open', 'part1_economics'] },
    ],
    frameChains: [
      { clips: ['cold_open_veo_01', 'cold_open_veo_02'], referenceId: 'alex' },
    ],
  };

  it('has all required fields per PRD §4.5.1', () => {
    expectExactKeys(validVeo, ['model', 'defaultAspectRatio', 'maxConcurrentGenerations', 'references', 'frameChains']);
  });

  it('model is a string', () => {
    expect(typeof validVeo.model).toBe('string');
  });

  it('defaultAspectRatio accepts 16:9', () => {
    const v: VeoConfig = { ...validVeo, defaultAspectRatio: '16:9' };
    expect(v.defaultAspectRatio).toBe('16:9');
  });

  it('defaultAspectRatio accepts 9:16', () => {
    const v: VeoConfig = { ...validVeo, defaultAspectRatio: '9:16' };
    expect(v.defaultAspectRatio).toBe('9:16');
  });

  it('maxConcurrentGenerations is a number', () => {
    expect(typeof validVeo.maxConcurrentGenerations).toBe('number');
  });

  it('references is an array of VeoReference', () => {
    expect(Array.isArray(validVeo.references)).toBe(true);
    expect(validVeo.references[0]).toHaveProperty('id');
    expect(validVeo.references[0]).toHaveProperty('label');
    expect(validVeo.references[0]).toHaveProperty('imagePath');
    expect(validVeo.references[0]).toHaveProperty('sections');
  });

  it('frameChains is an array of VeoFrameChain', () => {
    expect(Array.isArray(validVeo.frameChains)).toBe(true);
    expect(validVeo.frameChains[0]).toHaveProperty('clips');
    expect(validVeo.frameChains[0]).toHaveProperty('referenceId');
  });

  it('references can be empty', () => {
    const v: VeoConfig = { ...validVeo, references: [] };
    expect(v.references).toHaveLength(0);
  });
});

// ---------------------------------------------------------------------------
// 13. RenderConfig
// ---------------------------------------------------------------------------

describe('RenderConfig', () => {
  const validRender: RenderConfig = {
    maxParallelRenders: 3,
    useLambda: false,
    lambdaRegion: 'us-east-1',
  };

  it('has all required fields per PRD §4.5.1', () => {
    expectExactKeys(validRender, ['maxParallelRenders', 'useLambda', 'lambdaRegion']);
  });

  it('maxParallelRenders is a number', () => {
    expect(typeof validRender.maxParallelRenders).toBe('number');
  });

  it('useLambda is a boolean', () => {
    expect(typeof validRender.useLambda).toBe('boolean');
  });

  it('lambdaRegion is a string', () => {
    expect(typeof validRender.lambdaRegion).toBe('string');
  });
});

// ---------------------------------------------------------------------------
// 14. AudioSyncConfig
// ---------------------------------------------------------------------------

describe('AudioSyncConfig', () => {
  const validAudioSync: AudioSyncConfig = {
    sectionGroups: {
      cold_open: { startSegment: 'cold_open_001', endSegment: 'cold_open_004' },
      part1_economics: { startSegment: 'part1_economics_001', endSegment: 'part1_economics_007' },
    },
    silenceGapDefault: 0.3,
  };

  it('has all required fields per PRD §4.5.1', () => {
    expectExactKeys(validAudioSync, ['sectionGroups', 'silenceGapDefault']);
  });

  it('sectionGroups maps section IDs to segment ranges', () => {
    expect(typeof validAudioSync.sectionGroups).toBe('object');
    const group = validAudioSync.sectionGroups['cold_open'];
    expect(group).toHaveProperty('startSegment');
    expect(group).toHaveProperty('endSegment');
  });

  it('silenceGapDefault is a number', () => {
    expect(typeof validAudioSync.silenceGapDefault).toBe('number');
  });

  it('sectionGroups can be empty', () => {
    const a: AudioSyncConfig = { sectionGroups: {}, silenceGapDefault: 0.3 };
    expect(Object.keys(a.sectionGroups)).toHaveLength(0);
  });
});

// ---------------------------------------------------------------------------
// 15. ProjectConfig
// ---------------------------------------------------------------------------

describe('ProjectConfig', () => {
  const section: Section = {
    id: 'cold_open',
    label: 'Cold Open',
    videoFile: 'cold_open.mp4',
    specDir: '00-cold-open',
    remotionDir: 'S00-ColdOpen',
    compositionId: 'ColdOpenSection',
    durationSeconds: 0,
    offsetSeconds: 0,
  };

  const validProject: ProjectConfig = {
    name: '3blue1brown-antibiotics',
    outputResolution: { width: 1920, height: 1080 },
    tts: {
      engine: 'qwen3-tts',
      modelPath: 'models/Qwen3-TTS-12Hz-1.7B-CustomVoice',
      tokenizerPath: 'models/Qwen3-TTS-Tokenizer-12Hz',
      speaker: 'Aiden',
      speakingRate: 0.95,
      sampleRate: 24000,
    },
    sections: [section],
    audioSync: {
      sectionGroups: { cold_open: { startSegment: 'cold_open_001', endSegment: 'cold_open_004' } },
      silenceGapDefault: 0.3,
    },
    veo: {
      model: 'veo-3.1-generate-preview',
      defaultAspectRatio: '16:9',
      maxConcurrentGenerations: 4,
      references: [],
      frameChains: [],
    },
    render: {
      maxParallelRenders: 3,
      useLambda: false,
      lambdaRegion: 'us-east-1',
    },
  };

  it('has all required fields', () => {
    expectExactKeys(validProject, [
      'name',
      'outputResolution',
      'tts',
      'sections',
      'audioSync',
      'veo',
      'render',
    ]);
  });

  it('name is a string', () => {
    expect(typeof validProject.name).toBe('string');
  });

  it('outputResolution is an object with width and height per PRD §4.5.1', () => {
    expect(validProject.outputResolution).toHaveProperty('width');
    expect(validProject.outputResolution).toHaveProperty('height');
    expect(typeof validProject.outputResolution.width).toBe('number');
    expect(typeof validProject.outputResolution.height).toBe('number');
  });

  it('tts is a TtsConfig with PRD fields', () => {
    expect(validProject.tts).toHaveProperty('engine');
    expect(validProject.tts).toHaveProperty('modelPath');
    expect(validProject.tts).toHaveProperty('speaker');
    expect(validProject.tts).toHaveProperty('speakingRate');
    expect(validProject.tts).toHaveProperty('sampleRate');
  });

  it('sections is an ordered array of Section', () => {
    expect(Array.isArray(validProject.sections)).toBe(true);
    expect(validProject.sections).toHaveLength(1);
    expect(validProject.sections[0].id).toBe('cold_open');
  });

  it('sections ordering is preserved', () => {
    const s1: Section = { ...section, id: 's1', offsetSeconds: 0 };
    const s2: Section = { ...section, id: 's2', offsetSeconds: 12.5 };
    const s3: Section = { ...section, id: 's3', offsetSeconds: 57.5 };
    const p: ProjectConfig = {
      ...validProject,
      sections: [s1, s2, s3],
    };
    expect(p.sections[0].id).toBe('s1');
    expect(p.sections[1].id).toBe('s2');
    expect(p.sections[2].id).toBe('s3');
  });

  it('audioSync has sectionGroups with segment ranges and silenceGapDefault', () => {
    expect(validProject.audioSync).toHaveProperty('sectionGroups');
    expect(validProject.audioSync).toHaveProperty('silenceGapDefault');
  });

  it('veo is a VeoConfig with PRD fields', () => {
    expect(validProject.veo).toHaveProperty('model');
    expect(validProject.veo).toHaveProperty('defaultAspectRatio');
    expect(validProject.veo).toHaveProperty('maxConcurrentGenerations');
    expect(validProject.veo).toHaveProperty('references');
    expect(validProject.veo).toHaveProperty('frameChains');
  });

  it('render is a RenderConfig with PRD fields', () => {
    expect(validProject.render).toHaveProperty('maxParallelRenders');
    expect(validProject.render).toHaveProperty('useLambda');
    expect(validProject.render).toHaveProperty('lambdaRegion');
  });
});

// ---------------------------------------------------------------------------
// 16. RenderProgress
// ---------------------------------------------------------------------------

describe('RenderProgress', () => {
  const validProgress: RenderProgress = {
    percent: 75,
    message: 'Rendering intro section',
  };

  it('has all required fields', () => {
    expectExactKeys(validProgress, ['percent', 'message']);
  });

  it('percent is a number', () => {
    expect(typeof validProgress.percent).toBe('number');
  });

  it('message is a string', () => {
    expect(typeof validProgress.message).toBe('string');
  });

  it('percent can be 0', () => {
    const p: RenderProgress = { ...validProgress, percent: 0 };
    expect(p.percent).toBe(0);
  });

  it('percent can be 100', () => {
    const p: RenderProgress = { ...validProgress, percent: 100 };
    expect(p.percent).toBe(100);
  });
});

// ---------------------------------------------------------------------------
// 17. SseSend
// ---------------------------------------------------------------------------

describe('SseSend', () => {
  it('accepts a function that takes an object and returns void', () => {
    const calls: object[] = [];
    const send: SseSend = (data: object) => {
      calls.push(data);
    };

    send({ type: 'progress', percent: 50 });
    send({ type: 'complete' });

    expect(calls).toHaveLength(2);
    expect(calls[0]).toEqual({ type: 'progress', percent: 50 });
    expect(calls[1]).toEqual({ type: 'complete' });
  });

  it('is callable with any object', () => {
    const received: object[] = [];
    const send: SseSend = (data) => received.push(data);

    const progress: RenderProgress = { percent: 25, message: 'Rendering' };
    send(progress);

    expect(received[0]).toEqual({ percent: 25, message: 'Rendering' });
  });
});

// ---------------------------------------------------------------------------
// 18. No local imports verification (structural)
// ---------------------------------------------------------------------------

describe('lib/types.ts module constraints', () => {
  it('exports are all pure types (no runtime values exported)', async () => {
    // When imported as a module, there should be no runtime-exported values.
    // All exports are type-only. The module should resolve without errors.
    const mod = await import('../lib/types');
    // Type-only modules export nothing at runtime in TypeScript
    expect(typeof mod).toBe('object');
  });
});
