const request = require('supertest');
const fs = require('fs');
const path = require('path');
const { EventEmitter } = require('events');

// --- Mock child_process.spawn before requiring server ---
const mockSpawn = jest.fn();
jest.mock('child_process', () => ({
  spawn: (...args) => mockSpawn(...args),
}));

// --- Test data directory setup ---
const DATA_DIR = path.join(__dirname, '..', 'data');
const DATA_FILE = path.join(DATA_DIR, 'annotations.json');
const THUMBNAILS_DIR = path.join(DATA_DIR, 'thumbnails');
const ANALYSIS_TEMP_DIR = path.join(DATA_DIR, '.analysis-temp');

function seedAnnotations(annotations = []) {
  const data = { version: '1.0', annotations };
  fs.writeFileSync(DATA_FILE, JSON.stringify(data, null, 2));
  return data;
}

function readAnnotationsFile() {
  return JSON.parse(fs.readFileSync(DATA_FILE, 'utf-8'));
}

function makeAnnotation(overrides = {}) {
  return {
    id: `ann_test_${Date.now()}_${Math.random().toString(36).slice(2, 6)}`,
    video: { source: 'full', sectionId: 'cold_open', file: 'full_video.mp4', timestamp: 5.0, timestampFormatted: '00:05.0' },
    text: { content: 'Test annotation text', inputMethod: 'keyboard' },
    drawing: null,
    analysis: { status: 'pending' },
    tags: [],
    resolved: false,
    createdAt: new Date().toISOString(),
    ...overrides,
  };
}

/**
 * Create a fake child process EventEmitter with stdin/stdout/stderr.
 */
function createFakeChild() {
  const stdin = { write: jest.fn(), end: jest.fn() };
  const stdout = new EventEmitter();
  const stderr = new EventEmitter();
  const child = new EventEmitter();
  child.stdin = stdin;
  child.stdout = stdout;
  child.stderr = stderr;

  child.emitStdout = (data) => stdout.emit('data', Buffer.from(data));
  child.emitStderr = (data) => stderr.emit('data', Buffer.from(data));
  child.close = (code) => child.emit('close', code);
  child.emitError = (err) => child.emit('error', err);

  return child;
}

/**
 * Configure mockSpawn to return a fakeChild that auto-completes via process.nextTick.
 * Events fire AFTER the server attaches its handlers (since handlers are sync after spawn()).
 */
function setupMockClaude({ exitCode = 0, stdout = '', stderr = '', error = null } = {}) {
  mockSpawn.mockImplementationOnce(() => {
    const fakeChild = createFakeChild();
    process.nextTick(() => {
      if (error) {
        fakeChild.emitError(error);
        return;
      }
      if (stdout) fakeChild.emitStdout(stdout);
      if (stderr) fakeChild.emitStderr(stderr);
      fakeChild.close(exitCode);
    });
    return fakeChild;
  });
}

/** Helper: wrap Claude analysis JSON in the CLI wrapper format */
function claudeOutput(analysisObj) {
  return JSON.stringify({ result: JSON.stringify(analysisObj) });
}

// Backup the real annotations file
let originalAnnotations;

beforeAll(() => {
  fs.mkdirSync(DATA_DIR, { recursive: true });
  fs.mkdirSync(THUMBNAILS_DIR, { recursive: true });
  fs.mkdirSync(ANALYSIS_TEMP_DIR, { recursive: true });
  if (fs.existsSync(DATA_FILE)) {
    originalAnnotations = fs.readFileSync(DATA_FILE, 'utf-8');
  }
});

afterAll(() => {
  if (originalAnnotations !== undefined) {
    fs.writeFileSync(DATA_FILE, originalAnnotations);
  }
});

beforeEach(() => {
  mockSpawn.mockReset();
});

// Load app after mocks are in place
const app = require('../server');

// =============================================================================
// Group A: Error detection (Bug 1)
// =============================================================================

describe('Group A: Error detection', () => {
  test('CLI exit code non-zero → 500 response, file untouched', async () => {
    const ann = makeAnnotation({ id: 'ann_err_exit' });
    seedAnnotations([ann]);

    setupMockClaude({ exitCode: 1, stderr: 'Something went wrong in the CLI' });

    const res = await request(app)
      .post('/api/annotations/ann_err_exit/analyze')
      .send();

    expect(res.status).toBe(500);
    expect(res.body.error).toMatch(/claude exited with code 1/);

    // File should still have status: pending (untouched)
    const saved = readAnnotationsFile();
    const savedAnn = saved.annotations.find(a => a.id === 'ann_err_exit');
    expect(savedAnn.analysis.status).toBe('pending');
  });

  test('CLI succeeds → analysis persisted to disk with status completed', async () => {
    const ann = makeAnnotation({ id: 'ann_ok' });
    seedAnnotations([ann]);

    const analysis = {
      severity: 'medium',
      category: 'animation-timing',
      summary: 'Animation is slightly off',
      technicalAssessment: 'The timing is wrong',
      suggestedFixes: ['Adjust keyframes'],
      relevantFiles: ['remotion/Scene1.tsx'],
      specReference: 'specs/00-cold-open/01_intro.md',
    };

    setupMockClaude({ stdout: claudeOutput(analysis) });

    const res = await request(app)
      .post('/api/annotations/ann_ok/analyze')
      .send();

    expect(res.status).toBe(200);
    expect(res.body.analysis.status).toBe('completed');
    expect(res.body.analysis.severity).toBe('medium');

    const saved = readAnnotationsFile();
    const savedAnn = saved.annotations.find(a => a.id === 'ann_ok');
    expect(savedAnn.analysis.status).toBe('completed');
    expect(savedAnn.analysis.severity).toBe('medium');
  });

  test('CLI returns non-JSON result → graceful fallback with raw: true', async () => {
    const wrapper = { result: 'This is just plain text, not JSON.' };
    setupMockClaude({ stdout: JSON.stringify(wrapper) });

    const ann = makeAnnotation({ id: 'ann_raw' });
    seedAnnotations([ann]);

    const res = await request(app)
      .post('/api/annotations/ann_raw/analyze')
      .send();

    expect(res.status).toBe(200);
    expect(res.body.analysis.status).toBe('completed');
    expect(res.body.analysis.raw).toBe(true);
    expect(res.body.analysis.summary).toContain('plain text');
  });

  test('CLI stdout is not valid JSON wrapper → fallback', async () => {
    setupMockClaude({ stdout: 'this is not json at all {{{' });

    const ann = makeAnnotation({ id: 'ann_badjson' });
    seedAnnotations([ann]);

    const res = await request(app)
      .post('/api/annotations/ann_badjson/analyze')
      .send();

    expect(res.status).toBe(200);
    expect(res.body.analysis.status).toBe('completed');
    expect(res.body.analysis.raw).toBe(true);
  });

  test('CLI ENOENT (not found) → 500 with descriptive error', async () => {
    const enoent = new Error('spawn claude ENOENT');
    enoent.code = 'ENOENT';
    setupMockClaude({ error: enoent });

    const ann = makeAnnotation({ id: 'ann_enoent' });
    seedAnnotations([ann]);

    const res = await request(app)
      .post('/api/annotations/ann_enoent/analyze')
      .send();

    expect(res.status).toBe(500);
    expect(res.body.error).toMatch(/claude CLI not found/);
  });
});

// =============================================================================
// Group B: Concurrent write safety (Bug 2)
// =============================================================================

describe('Group B: Concurrent write safety', () => {
  test('3 concurrent analyses → all 3 persist', async () => {
    const ann1 = makeAnnotation({ id: 'ann_c1' });
    const ann2 = makeAnnotation({ id: 'ann_c2' });
    const ann3 = makeAnnotation({ id: 'ann_c3' });
    seedAnnotations([ann1, ann2, ann3]);

    // Each mock auto-completes via process.nextTick after spawn is called
    setupMockClaude({ stdout: claudeOutput({ severity: 'low', summary: 'Analysis for ann_c1' }) });
    setupMockClaude({ stdout: claudeOutput({ severity: 'low', summary: 'Analysis for ann_c2' }) });
    setupMockClaude({ stdout: claudeOutput({ severity: 'low', summary: 'Analysis for ann_c3' }) });

    const results = await Promise.all([
      request(app).post('/api/annotations/ann_c1/analyze').send(),
      request(app).post('/api/annotations/ann_c2/analyze').send(),
      request(app).post('/api/annotations/ann_c3/analyze').send(),
    ]);

    for (const res of results) {
      expect(res.status).toBe(200);
      expect(res.body.analysis.status).toBe('completed');
    }

    // All 3 analyses should be persisted to disk (key regression for Bug 2)
    const saved = readAnnotationsFile();
    for (const id of ['ann_c1', 'ann_c2', 'ann_c3']) {
      const savedAnn = saved.annotations.find(a => a.id === id);
      expect(savedAnn.analysis.status).toBe('completed');
      expect(savedAnn.analysis.summary).toContain(id);
    }
  }, 15000);

  test('Annotation deleted while analysis in flight → no crash', async () => {
    const ann = makeAnnotation({ id: 'ann_del_inflight' });
    seedAnnotations([ann]);

    // Custom mock: delete the annotation from disk BEFORE completing the analysis.
    // This simulates a user deleting the annotation while Claude is thinking.
    mockSpawn.mockImplementationOnce(() => {
      const fakeChild = createFakeChild();
      setImmediate(() => {
        // Delete the annotation from disk mid-flight
        const data = readAnnotationsFile();
        data.annotations = data.annotations.filter(a => a.id !== 'ann_del_inflight');
        fs.writeFileSync(DATA_FILE, JSON.stringify(data, null, 2));

        // Then complete the analysis
        setImmediate(() => {
          fakeChild.emitStdout(claudeOutput({ severity: 'low', summary: 'Too late' }));
          fakeChild.close(0);
        });
      });
      return fakeChild;
    });

    const res = await request(app)
      .post('/api/annotations/ann_del_inflight/analyze')
      .send();

    // Should not crash — the key assertion is no 500
    expect(res.status).toBe(200);
  });
});

// =============================================================================
// Group C: Edge cases
// =============================================================================

describe('Group C: Edge cases', () => {
  test('Analyze non-existent annotation → 404', async () => {
    seedAnnotations([]);

    const res = await request(app)
      .post('/api/annotations/ann_doesnt_exist/analyze')
      .send();

    expect(res.status).toBe(404);
    expect(res.body.error).toMatch(/Not found/i);
  });

  test('Analyze annotation with no text → 400', async () => {
    const ann = makeAnnotation({ id: 'ann_notext', text: { content: '', inputMethod: 'keyboard' } });
    seedAnnotations([ann]);

    const res = await request(app)
      .post('/api/annotations/ann_notext/analyze')
      .send();

    expect(res.status).toBe(400);
    expect(res.body.error).toMatch(/no annotation text/i);
  });

  test('Analyze annotation with null text object → 400', async () => {
    const ann = makeAnnotation({ id: 'ann_nulltext', text: null });
    seedAnnotations([ann]);

    const res = await request(app)
      .post('/api/annotations/ann_nulltext/analyze')
      .send();

    expect(res.status).toBe(400);
    expect(res.body.error).toMatch(/no annotation text/i);
  });
});

// =============================================================================
// Group D: Enhanced analysis context
// =============================================================================

describe('Group D: Enhanced analysis context', () => {
  test('Spawn args include --allowedTools with Read,Glob,Write', async () => {
    const ann = makeAnnotation({ id: 'ann_tools' });
    seedAnnotations([ann]);

    setupMockClaude({ stdout: claudeOutput({ severity: 'low', summary: 'test' }) });

    await request(app)
      .post('/api/annotations/ann_tools/analyze')
      .send();

    expect(mockSpawn).toHaveBeenCalledTimes(1);
    const spawnArgs = mockSpawn.mock.calls[0][1];
    expect(spawnArgs).toContain('--allowedTools');
    expect(spawnArgs).toContain('Read,Glob,Write');
  });

  test('Prompt includes image paths when annotation has thumbnails', async () => {
    // Create a dummy thumbnail file
    const dummyThumb = 'thumb_test_dummy.jpg';
    fs.writeFileSync(path.join(THUMBNAILS_DIR, dummyThumb), 'fake-image-data');

    const ann = makeAnnotation({
      id: 'ann_thumb',
      video: {
        source: 'full',
        sectionId: 'cold_open',
        file: 'full_video.mp4',
        timestamp: 5.0,
        timestampFormatted: '00:05.0',
        frameThumbnail: `/thumbnails/${dummyThumb}`,
      },
    });
    seedAnnotations([ann]);

    setupMockClaude({ stdout: claudeOutput({ severity: 'low', summary: 'test' }) });

    await request(app)
      .post('/api/annotations/ann_thumb/analyze')
      .send();

    const writtenPrompt = mockSpawn.mock.results[0].value.stdin.write.mock.calls[0][0];
    expect(writtenPrompt).toContain(`review-app/data/thumbnails/${dummyThumb}`);
    expect(writtenPrompt).toContain('SCREENSHOT');

    // Clean up
    fs.unlinkSync(path.join(THUMBNAILS_DIR, dummyThumb));
  });

  test('Prompt references Remotion dir for the section', async () => {
    const ann = makeAnnotation({ id: 'ann_remotion' });
    seedAnnotations([ann]);

    setupMockClaude({ stdout: claudeOutput({ severity: 'low', summary: 'test' }) });

    await request(app)
      .post('/api/annotations/ann_remotion/analyze')
      .send();

    const writtenPrompt = mockSpawn.mock.results[0].value.stdin.write.mock.calls[0][0];
    expect(writtenPrompt).toContain('remotion/src/remotion/S00-ColdOpen/');
  });

  test('Prompt references main script', async () => {
    const ann = makeAnnotation({ id: 'ann_script' });
    seedAnnotations([ann]);

    setupMockClaude({ stdout: claudeOutput({ severity: 'low', summary: 'test' }) });

    await request(app)
      .post('/api/annotations/ann_script/analyze')
      .send();

    const writtenPrompt = mockSpawn.mock.results[0].value.stdin.write.mock.calls[0][0];
    expect(writtenPrompt).toContain('narrative/main_script.md');
  });

  test('Image paths omitted when thumbnail files do not exist on disk', async () => {
    const ann = makeAnnotation({
      id: 'ann_nothumb',
      video: {
        source: 'full',
        sectionId: 'cold_open',
        file: 'full_video.mp4',
        timestamp: 5.0,
        timestampFormatted: '00:05.0',
        frameThumbnail: '/thumbnails/nonexistent_thumb.jpg',
      },
    });
    seedAnnotations([ann]);

    setupMockClaude({ stdout: claudeOutput({ severity: 'low', summary: 'test' }) });

    await request(app)
      .post('/api/annotations/ann_nothumb/analyze')
      .send();

    const writtenPrompt = mockSpawn.mock.results[0].value.stdin.write.mock.calls[0][0];
    expect(writtenPrompt).not.toContain('SCREENSHOT');
    expect(writtenPrompt).not.toContain('nonexistent_thumb.jpg');
  });

  test('File-based output is preferred when temp file exists', async () => {
    const ann = makeAnnotation({ id: 'ann_filebased' });
    seedAnnotations([ann]);

    const fileAnalysis = { severity: 'high', category: 'layout', summary: 'From file' };

    mockSpawn.mockImplementationOnce(() => {
      const fakeChild = createFakeChild();
      process.nextTick(() => {
        // Extract temp file path from the prompt Claude received
        const prompt = fakeChild.stdin.write.mock.calls[0][0];
        const match = prompt.match(/Write tool to save.*:\n(.+\.json)/);
        expect(match).not.toBeNull();
        fs.writeFileSync(match[1], JSON.stringify(fileAnalysis));
        // Emit stdout with different data to prove file takes priority
        fakeChild.emitStdout(claudeOutput({ severity: 'low', summary: 'From stdout' }));
        fakeChild.close(0);
      });
      return fakeChild;
    });

    const res = await request(app).post('/api/annotations/ann_filebased/analyze').send();

    expect(res.status).toBe(200);
    expect(res.body.analysis.severity).toBe('high');
    expect(res.body.analysis.summary).toBe('From file');
    expect(res.body.analysis.raw).toBeUndefined();
  });

  test('Prose-wrapped stdout with fenced JSON parses correctly', async () => {
    const ann = makeAnnotation({ id: 'ann_prose' });
    seedAnnotations([ann]);

    const analysis = { severity: 'medium', category: 'visual-design', summary: 'Fenced result' };
    const proseWrapped = JSON.stringify({
      result: 'I analyzed the scene.\n\n```json\n' + JSON.stringify(analysis) + '\n```'
    });
    setupMockClaude({ stdout: proseWrapped });

    const res = await request(app).post('/api/annotations/ann_prose/analyze').send();

    expect(res.status).toBe(200);
    expect(res.body.analysis.severity).toBe('medium');
    expect(res.body.analysis.summary).toBe('Fenced result');
    expect(res.body.analysis.raw).toBeUndefined();
  });
});
