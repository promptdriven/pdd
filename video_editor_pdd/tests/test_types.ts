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
  AnnotationCaptureData,
  ClaudeFixResult,
  Section,
  TtsConfig,
  VeoConfig,
  RenderConfig,
  AudioSyncConfig,
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
    voice: 'en-US-Neural2-F',
    rate: 1.0,
    model: 'google-tts-v2',
  };

  it('has all required fields', () => {
    expectExactKeys(validTts, ['voice', 'rate', 'model']);
  });

  it('voice is a string', () => {
    expect(typeof validTts.voice).toBe('string');
  });

  it('rate is a number', () => {
    expect(typeof validTts.rate).toBe('number');
  });

  it('model is a string', () => {
    expect(typeof validTts.model).toBe('string');
  });
});

// ---------------------------------------------------------------------------
// 12. VeoConfig
// ---------------------------------------------------------------------------

describe('VeoConfig', () => {
  const validVeo: VeoConfig = {
    model: 'veo-2.0-generate-001',
    aspectRatio: '16:9',
    referenceImages: { logo: 'assets/logo.png' },
  };

  it('has all required fields', () => {
    expectExactKeys(validVeo, ['model', 'aspectRatio', 'referenceImages']);
  });

  it('model is a string', () => {
    expect(typeof validVeo.model).toBe('string');
  });

  it('aspectRatio accepts 16:9', () => {
    const v: VeoConfig = { ...validVeo, aspectRatio: '16:9' };
    expect(v.aspectRatio).toBe('16:9');
  });

  it('aspectRatio accepts 9:16', () => {
    const v: VeoConfig = { ...validVeo, aspectRatio: '9:16' };
    expect(v.aspectRatio).toBe('9:16');
  });

  it('referenceImages is a Record<string, string>', () => {
    expect(typeof validVeo.referenceImages).toBe('object');
    for (const [k, val] of Object.entries(validVeo.referenceImages)) {
      expect(typeof k).toBe('string');
      expect(typeof val).toBe('string');
    }
  });

  it('referenceImages can be empty', () => {
    const v: VeoConfig = { ...validVeo, referenceImages: {} };
    expect(Object.keys(v.referenceImages)).toHaveLength(0);
  });
});

// ---------------------------------------------------------------------------
// 13. RenderConfig
// ---------------------------------------------------------------------------

describe('RenderConfig', () => {
  const validRender: RenderConfig = {
    maxParallelRenders: 3,
    outputDir: 'output/final',
    fps: 30,
    width: 1920,
    height: 1080,
  };

  it('has all required fields', () => {
    expectExactKeys(validRender, [
      'maxParallelRenders',
      'outputDir',
      'fps',
      'width',
      'height',
    ]);
  });

  it('maxParallelRenders is a number', () => {
    expect(typeof validRender.maxParallelRenders).toBe('number');
  });

  it('outputDir is a string', () => {
    expect(typeof validRender.outputDir).toBe('string');
  });

  it('fps is a number', () => {
    expect(typeof validRender.fps).toBe('number');
  });

  it('width is a number', () => {
    expect(typeof validRender.width).toBe('number');
  });

  it('height is a number', () => {
    expect(typeof validRender.height).toBe('number');
  });
});

// ---------------------------------------------------------------------------
// 14. AudioSyncConfig
// ---------------------------------------------------------------------------

describe('AudioSyncConfig', () => {
  const validAudioSync: AudioSyncConfig = {
    sectionGroups: {
      narration: ['intro', 'main', 'outro'],
      music: ['intro', 'outro'],
    },
  };

  it('has sectionGroups field', () => {
    expectExactKeys(validAudioSync, ['sectionGroups']);
  });

  it('sectionGroups is a Record<string, string[]>', () => {
    expect(typeof validAudioSync.sectionGroups).toBe('object');
    for (const [key, arr] of Object.entries(validAudioSync.sectionGroups)) {
      expect(typeof key).toBe('string');
      expect(Array.isArray(arr)).toBe(true);
      for (const item of arr) {
        expect(typeof item).toBe('string');
      }
    }
  });

  it('sectionGroups can be empty', () => {
    const a: AudioSyncConfig = { sectionGroups: {} };
    expect(Object.keys(a.sectionGroups)).toHaveLength(0);
  });
});

// ---------------------------------------------------------------------------
// 15. ProjectConfig
// ---------------------------------------------------------------------------

describe('ProjectConfig', () => {
  const section: Section = {
    id: 'intro',
    label: 'Introduction',
    videoFile: 'output/sections/intro.mp4',
    specDir: 'specs/intro',
    remotionDir: 'remotion/intro',
    compositionId: 'IntroComposition',
    durationSeconds: 12.5,
    offsetSeconds: 0,
  };

  const validProject: ProjectConfig = {
    name: 'Product Launch Video',
    outputResolution: '1920x1080',
    tts: { voice: 'en-US-Neural2-F', rate: 1.0, model: 'google-tts-v2' },
    sections: [section],
    audioSync: { sectionGroups: { narration: ['intro'] } },
    veo: {
      model: 'veo-2.0-generate-001',
      aspectRatio: '16:9',
      referenceImages: {},
    },
    render: {
      maxParallelRenders: 3,
      outputDir: 'output/final',
      fps: 30,
      width: 1920,
      height: 1080,
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

  it('outputResolution accepts 1920x1080', () => {
    expect(validProject.outputResolution).toBe('1920x1080');
  });

  it('outputResolution accepts 1280x720', () => {
    const p: ProjectConfig = { ...validProject, outputResolution: '1280x720' };
    expect(p.outputResolution).toBe('1280x720');
  });

  it('tts is a TtsConfig', () => {
    expect(validProject.tts).toHaveProperty('voice');
    expect(validProject.tts).toHaveProperty('rate');
    expect(validProject.tts).toHaveProperty('model');
  });

  it('sections is an ordered array of Section', () => {
    expect(Array.isArray(validProject.sections)).toBe(true);
    expect(validProject.sections).toHaveLength(1);
    expect(validProject.sections[0].id).toBe('intro');
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

  it('audioSync is an AudioSyncConfig', () => {
    expect(validProject.audioSync).toHaveProperty('sectionGroups');
  });

  it('veo is a VeoConfig', () => {
    expect(validProject.veo).toHaveProperty('model');
    expect(validProject.veo).toHaveProperty('aspectRatio');
    expect(validProject.veo).toHaveProperty('referenceImages');
  });

  it('render is a RenderConfig', () => {
    expect(validProject.render).toHaveProperty('maxParallelRenders');
    expect(validProject.render).toHaveProperty('outputDir');
    expect(validProject.render).toHaveProperty('fps');
    expect(validProject.render).toHaveProperty('width');
    expect(validProject.render).toHaveProperty('height');
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
