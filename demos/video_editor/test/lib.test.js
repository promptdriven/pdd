/**
 * Tests for lib modules: config, annotations, claude (JSON extraction), jobs.
 * These test the core business logic without needing Next.js runtime.
 */

const fs = require('fs');
const path = require('path');

// ============================================================================
// Setup: ensure data directories exist before requiring modules
// ============================================================================

const DATA_DIR = path.join(__dirname, '..', 'data');
const THUMBNAILS_DIR = path.join(DATA_DIR, 'thumbnails');
const ANALYSIS_TEMP_DIR = path.join(DATA_DIR, '.analysis-temp');

beforeAll(() => {
  fs.mkdirSync(DATA_DIR, { recursive: true });
  fs.mkdirSync(THUMBNAILS_DIR, { recursive: true });
  fs.mkdirSync(ANALYSIS_TEMP_DIR, { recursive: true });
});

// ============================================================================
// Test: Config module
// ============================================================================

describe('Config module', () => {
  const config = require('../lib/config');

  test('loadProjectConfig returns config from project.json', () => {
    const cfg = config.loadProjectConfig();
    expect(cfg.name).toBeDefined();
    expect(cfg.sections).toBeInstanceOf(Array);
    expect(cfg.sections.length).toBeGreaterThan(0);
  });

  test('getSections returns sections array', () => {
    const sections = config.getSections();
    expect(sections).toBeInstanceOf(Array);
    expect(sections[0]).toHaveProperty('id');
    expect(sections[0]).toHaveProperty('label');
    expect(sections[0]).toHaveProperty('videoFile');
    expect(sections[0]).toHaveProperty('specDir');
    expect(sections[0]).toHaveProperty('remotionDir');
    expect(sections[0]).toHaveProperty('compositionId');
  });

  test('getSection returns matching section or null', () => {
    const found = config.getSection('cold_open');
    expect(found).not.toBeNull();
    expect(found.id).toBe('cold_open');
    expect(found.label).toBe('Cold Open');

    const missing = config.getSection('nonexistent');
    expect(missing).toBeNull();
  });

  test('getAllowedVideoFiles returns Set of video filenames', () => {
    const allowed = config.getAllowedVideoFiles();
    expect(allowed).toBeInstanceOf(Set);
    expect(allowed.has('cold_open.mp4')).toBe(true);
    expect(allowed.has('nonexistent.mp4')).toBe(false);
  });

  test('saveProjectConfig writes and reloads correctly', () => {
    const original = config.loadProjectConfig();
    const modified = { ...original, name: 'test-save-project' };
    config.saveProjectConfig(modified);

    const reloaded = config.loadProjectConfig();
    expect(reloaded.name).toBe('test-save-project');

    // Restore
    config.saveProjectConfig(original);
  });
});

// ============================================================================
// Test: Annotations module
// ============================================================================

describe('Annotations module', () => {
  const annotations = require('../lib/annotations');

  let backupData;

  beforeEach(() => {
    if (fs.existsSync(annotations.DATA_FILE)) {
      backupData = fs.readFileSync(annotations.DATA_FILE, 'utf-8');
    }
    // Start with clean state
    fs.writeFileSync(annotations.DATA_FILE, JSON.stringify({ version: '1.0', annotations: [] }, null, 2));
  });

  afterEach(() => {
    if (backupData !== undefined) {
      fs.writeFileSync(annotations.DATA_FILE, backupData);
    }
  });

  test('readAnnotations returns initial structure when file is empty', () => {
    const data = annotations.readAnnotations();
    expect(data.version).toBe('1.0');
    expect(data.annotations).toBeInstanceOf(Array);
  });

  test('createAnnotation adds annotation with generated id and timestamp', () => {
    const ann = annotations.createAnnotation({
      text: { content: 'Test issue', inputMethod: 'typed' },
      video: { sectionId: 'cold_open', timestamp: 5.0 },
    });

    expect(ann.id).toMatch(/^ann_\d+_[a-z0-9]+$/);
    expect(ann.createdAt).toBeDefined();
    expect(ann.text.content).toBe('Test issue');

    const data = annotations.readAnnotations();
    expect(data.annotations).toHaveLength(1);
    expect(data.annotations[0].id).toBe(ann.id);
  });

  test('getAnnotation returns annotation by id', () => {
    const created = annotations.createAnnotation({ text: { content: 'Find me' } });
    const found = annotations.getAnnotation(created.id);
    expect(found).not.toBeNull();
    expect(found.text.content).toBe('Find me');

    const missing = annotations.getAnnotation('ann_nonexistent');
    expect(missing).toBeNull();
  });

  test('updateAnnotation merges updates and preserves id', () => {
    const created = annotations.createAnnotation({ text: { content: 'Original' }, resolved: false });
    const updated = annotations.updateAnnotation(created.id, { resolved: true, text: { content: 'Updated' } });

    expect(updated).not.toBeNull();
    expect(updated.id).toBe(created.id);
    expect(updated.resolved).toBe(true);
    expect(updated.text.content).toBe('Updated');
  });

  test('updateAnnotation returns null for missing id', () => {
    const result = annotations.updateAnnotation('ann_missing', { resolved: true });
    expect(result).toBeNull();
  });

  test('deleteAnnotation removes annotation and returns true', () => {
    const created = annotations.createAnnotation({ text: { content: 'Delete me' } });
    expect(annotations.deleteAnnotation(created.id)).toBe(true);

    const data = annotations.readAnnotations();
    expect(data.annotations).toHaveLength(0);
  });

  test('deleteAnnotation returns false for missing id', () => {
    expect(annotations.deleteAnnotation('ann_missing')).toBe(false);
  });

  test('safeWriteAnnotations serializes concurrent writes', async () => {
    // Create 3 annotations first
    annotations.createAnnotation({ text: { content: 'a1' } });
    annotations.createAnnotation({ text: { content: 'a2' } });
    annotations.createAnnotation({ text: { content: 'a3' } });

    // Concurrently update all 3
    const ops = [];
    const data = annotations.readAnnotations();
    for (const ann of data.annotations) {
      ops.push(annotations.safeWriteAnnotations((d) => {
        const idx = d.annotations.findIndex(a => a.id === ann.id);
        if (idx !== -1) d.annotations[idx].resolved = true;
      }));
    }

    await Promise.all(ops);

    const final = annotations.readAnnotations();
    for (const ann of final.annotations) {
      expect(ann.resolved).toBe(true);
    }
  });

  test('recoverStaleJobs marks pending/running jobs as error', () => {
    const ann1 = annotations.createAnnotation({
      text: { content: 'stale1' },
      resolveJob: { jobId: 'job_1', status: 'pending' },
    });
    const ann2 = annotations.createAnnotation({
      text: { content: 'stale2' },
      resolveJob: { jobId: 'job_2', status: 'running' },
    });
    const ann3 = annotations.createAnnotation({
      text: { content: 'done' },
      resolveJob: { jobId: 'job_3', status: 'done' },
    });

    annotations.recoverStaleJobs();

    const data = annotations.readAnnotations();
    const s1 = data.annotations.find(a => a.id === ann1.id);
    const s2 = data.annotations.find(a => a.id === ann2.id);
    const s3 = data.annotations.find(a => a.id === ann3.id);

    expect(s1.resolveJob.status).toBe('error');
    expect(s1.resolveJob.error).toMatch(/Server restarted/);
    expect(s2.resolveJob.status).toBe('error');
    expect(s3.resolveJob.status).toBe('done');
  });
});

// ============================================================================
// Test: Claude JSON extraction
// ============================================================================

describe('Claude JSON extraction', () => {
  const { extractJsonFromText } = require('../lib/claude');

  test('Strategy A: pure JSON string', () => {
    const input = JSON.stringify({ severity: 'high', summary: 'Direct parse' });
    const result = extractJsonFromText(input);
    expect(result).not.toBeNull();
    expect(result.severity).toBe('high');
    expect(result.summary).toBe('Direct parse');
  });

  test('Strategy B: fenced JSON block', () => {
    const input = 'Here is my analysis:\n\n```json\n{"severity":"medium","summary":"Fenced"}\n```';
    const result = extractJsonFromText(input);
    expect(result).not.toBeNull();
    expect(result.severity).toBe('medium');
    expect(result.summary).toBe('Fenced');
  });

  test('Strategy B: fenced JSON with no closing fence', () => {
    const input = 'Analysis:\n```json\n{"severity":"high","summary":"No closing fence"}';
    const result = extractJsonFromText(input);
    expect(result).not.toBeNull();
    expect(result.severity).toBe('high');
    expect(result.summary).toBe('No closing fence');
  });

  test('Strategy B: multi-line pretty-printed fenced JSON', () => {
    const obj = { severity: 'low', category: 'layout', summary: 'Pretty printed' };
    const input = 'I analyzed the scene.\n\n```json\n' + JSON.stringify(obj, null, 2) + '\n```';
    const result = extractJsonFromText(input);
    expect(result).not.toBeNull();
    expect(result.severity).toBe('low');
    expect(result.summary).toBe('Pretty printed');
  });

  test('Strategy C: brace matching from prose', () => {
    const input = 'Here is the result: {"severity":"low","summary":"Brace match"} and some more text';
    const result = extractJsonFromText(input);
    expect(result).not.toBeNull();
    expect(result.severity).toBe('low');
    expect(result.summary).toBe('Brace match');
  });

  test('Prefers fenced JSON over code braces in prose', () => {
    const obj = { severity: 'medium', summary: 'Flash frame at loop boundary' };
    const input = 'Uses `<Loop durationInFrames={240}>` and `from={BEATS.START}`.\n\n```json\n' +
      JSON.stringify(obj, null, 2) + '\n```';
    const result = extractJsonFromText(input);
    expect(result).not.toBeNull();
    expect(result.severity).toBe('medium');
    expect(result.summary).toBe('Flash frame at loop boundary');
  });

  test('Returns null for non-JSON text', () => {
    expect(extractJsonFromText('Just plain text')).toBeNull();
    expect(extractJsonFromText('broken {{{ not json')).toBeNull();
  });

  test('Returns null for non-string input', () => {
    expect(extractJsonFromText(null)).toBeNull();
    expect(extractJsonFromText(undefined)).toBeNull();
    expect(extractJsonFromText(42)).toBeNull();
  });

  test('Returns null for arrays (only objects)', () => {
    expect(extractJsonFromText('[1,2,3]')).toBeNull();
    expect(extractJsonFromText('```json\n[1,2,3]\n```')).toBeNull();
  });
});

// ============================================================================
// Test: Jobs module
// ============================================================================

describe('Jobs module', () => {
  const jobs = require('../lib/jobs');

  test('createJob creates a job with unique id', () => {
    const job = jobs.createJob({ sectionId: 'cold_open', stage: 'resolve-batch' });
    expect(job.id).toMatch(/^job_\d+_[a-z0-9]+$/);
    expect(job.status).toBe('pending');
    expect(job.sectionId).toBe('cold_open');
    expect(job.stage).toBe('resolve-batch');
    expect(job.progress).toBe(0);
  });

  test('getJob returns job by id', () => {
    const created = jobs.createJob({ sectionId: 'part1_economics' });
    const found = jobs.getJob(created.id);
    expect(found).not.toBeNull();
    expect(found.id).toBe(created.id);

    expect(jobs.getJob('job_nonexistent')).toBeNull();
  });

  test('emitJobUpdate updates job fields', () => {
    const job = jobs.createJob({});
    jobs.emitJobUpdate(job, { status: 'running', step: 'fixing', progress: 50 });

    expect(job.status).toBe('running');
    expect(job.step).toBe('fixing');
    expect(job.progress).toBe(50);
  });

  test('emitJobUpdate sends SSE to subscribers', () => {
    const job = jobs.createJob({});
    const messages = [];
    const mockWriter = { write: (msg) => messages.push(msg) };
    job.subscribers.push(mockWriter);

    jobs.emitJobUpdate(job, { status: 'running', progress: 25 });

    expect(messages).toHaveLength(1);
    const parsed = JSON.parse(messages[0].split('data: ')[1]);
    expect(parsed.status).toBe('running');
    expect(parsed.progress).toBe(25);
  });

  test('emitJobUpdate removes failed subscribers', () => {
    const job = jobs.createJob({});
    const failWriter = { write: () => { throw new Error('connection closed'); } };
    const goodWriter = { write: jest.fn() };
    job.subscribers = [failWriter, goodWriter];

    jobs.emitJobUpdate(job, { status: 'running' });

    expect(job.subscribers).toHaveLength(1);
    expect(job.subscribers[0]).toBe(goodWriter);
    expect(goodWriter.write).toHaveBeenCalled();
  });

  test('addSubscriber sends current state and adds to list', () => {
    const job = jobs.createJob({});
    jobs.emitJobUpdate(job, { status: 'running', progress: 42 });

    const messages = [];
    const writer = { write: (msg) => messages.push(msg) };

    const result = jobs.addSubscriber(job.id, writer);
    expect(result).not.toBeNull();
    expect(messages).toHaveLength(1);
    expect(job.subscribers).toContain(writer);
  });

  test('addSubscriber for terminal job sends state but does not subscribe', () => {
    const job = jobs.createJob({});
    jobs.emitJobUpdate(job, { status: 'done', progress: 100 });

    const messages = [];
    const writer = { write: (msg) => messages.push(msg) };

    const result = jobs.addSubscriber(job.id, writer);
    expect(result).not.toBeNull();
    expect(messages).toHaveLength(1);
    // Should NOT be added to subscribers since job is terminal
    expect(job.subscribers).not.toContain(writer);
  });

  test('addSubscriber returns null for nonexistent job', () => {
    const writer = { write: jest.fn() };
    expect(jobs.addSubscriber('job_nonexistent', writer)).toBeNull();
  });

  test('removeSubscriber removes writer from job', () => {
    const job = jobs.createJob({});
    const writer = { write: jest.fn() };
    job.subscribers.push(writer);

    jobs.removeSubscriber(job.id, writer);
    expect(job.subscribers).not.toContain(writer);
  });

  test('getPipelineStatus returns status map', () => {
    const status = jobs.getPipelineStatus();
    expect(status).toHaveProperty('project-setup');
    expect(status).toHaveProperty('render');
    expect(status).toHaveProperty('audit');
  });

  test('setPipelineStageStatus updates a stage', () => {
    jobs.setPipelineStageStatus('render', 'running');
    const status = jobs.getPipelineStatus();
    expect(status['render']).toBe('running');

    // Reset
    jobs.setPipelineStageStatus('render', 'not_started');
  });
});

// ============================================================================
// Test: Claude prompt building
// ============================================================================

describe('Claude prompt building', () => {
  const { buildAnalysisPrompt, buildFixPrompt } = require('../lib/claude');

  const sections = [
    { id: 'cold_open', label: 'Cold Open', specDir: '00-cold-open', remotionDir: 'S00-ColdOpen', compositionId: 'ColdOpenSection' },
  ];

  test('buildAnalysisPrompt includes section label and annotation text', () => {
    const prompt = buildAnalysisPrompt('The animation is off', 'cold_open', '00:05.0', { sections });
    expect(prompt).toContain('Cold Open');
    expect(prompt).toContain('The animation is off');
    expect(prompt).toContain('00:05.0');
    expect(prompt).toContain('specs/00-cold-open/');
    expect(prompt).toContain('remotion/src/remotion/S00-ColdOpen/');
    expect(prompt).toContain('narrative/main_script.md');
    expect(prompt).toContain('fixType');
  });

  test('buildAnalysisPrompt handles unknown section gracefully', () => {
    const prompt = buildAnalysisPrompt('Some text', 'nonexistent', null, { sections });
    expect(prompt).toContain('Unknown section');
    expect(prompt).not.toContain('SPEC FILES');
    expect(prompt).not.toContain('REMOTION SOURCE');
  });

  test('buildAnalysisPrompt includes thumbnail references when files exist', () => {
    // Create a dummy thumbnail
    const thumbFile = path.join(THUMBNAILS_DIR, 'test_thumb.jpg');
    fs.writeFileSync(thumbFile, 'fake');

    const annotation = {
      video: { frameThumbnail: '/thumbnails/test_thumb.jpg', sectionId: 'cold_open' },
    };
    const prompt = buildAnalysisPrompt('Test', 'cold_open', '00:01.0', { annotation, sections });
    expect(prompt).toContain('SCREENSHOT');
    expect(prompt).toContain('test_thumb.jpg');

    fs.unlinkSync(thumbFile);
  });

  test('buildAnalysisPrompt omits thumbnails when files do not exist', () => {
    const annotation = {
      video: { frameThumbnail: '/thumbnails/nonexistent.jpg', sectionId: 'cold_open' },
    };
    const prompt = buildAnalysisPrompt('Test', 'cold_open', '00:01.0', { annotation, sections });
    expect(prompt).not.toContain('SCREENSHOT');
  });

  test('buildFixPrompt includes analysis details and scoping instructions', () => {
    const section = sections[0];
    const annotation = {
      text: { content: 'Color is wrong' },
      video: { timestampFormatted: '00:10.0' },
      analysis: {
        severity: 'high',
        category: 'visual-design',
        technicalAssessment: 'Color palette mismatch',
        suggestedFixes: ['Update hex values'],
        relevantFiles: ['remotion/src/remotion/S00-ColdOpen/constants.ts'],
      },
    };
    const prompt = buildFixPrompt(annotation, section);
    expect(prompt).toContain('Color is wrong');
    expect(prompt).toContain('high');
    expect(prompt).toContain('visual-design');
    expect(prompt).toContain('Color palette mismatch');
    expect(prompt).toContain('Only edit files within remotion/src/remotion/S00-ColdOpen/');
    expect(prompt).toContain('specs/00-cold-open/');
  });
});
