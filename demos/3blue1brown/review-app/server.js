const express = require('express');
const fs = require('fs');
const path = require('path');
const { pipeline } = require('stream');
const { spawn } = require('child_process');

const app = express();
const PORT = 3847;

const OUTPUTS_DIR = path.join(__dirname, '..', 'outputs');
const SECTIONS_DIR = path.join(OUTPUTS_DIR, 'sections');
const SPECS_DIR = path.join(__dirname, '..', 'specs');
const DATA_FILE = path.join(__dirname, 'data', 'annotations.json');

app.use(express.json({ limit: '50mb' }));
app.use(express.static(path.join(__dirname, 'public')));

// --- Thumbnail storage ---
const THUMBNAILS_DIR = path.join(__dirname, 'data', 'thumbnails');
fs.mkdirSync(THUMBNAILS_DIR, { recursive: true });

// --- Temp directory for Claude analysis output ---
const ANALYSIS_TEMP_DIR = path.join(__dirname, 'data', '.analysis-temp');
fs.mkdirSync(ANALYSIS_TEMP_DIR, { recursive: true });
app.use('/thumbnails', express.static(THUMBNAILS_DIR));

// --- Section metadata ---

const SECTIONS = [
  { id: 'cold_open', file: 'cold_open.mp4', label: 'Cold Open', specDir: '00-cold-open', remotionDir: 'S00-ColdOpen', compositionId: 'ColdOpenSection' },
  { id: 'part1_economics', file: 'part1_economics.mp4', label: 'Part 1: Economics', specDir: '01-economics', remotionDir: 'S01-Economics', compositionId: 'Part1Economics' },
  { id: 'part2_paradigm_shift', file: 'part2_paradigm_shift.mp4', label: 'Part 2: Paradigm Shift', specDir: '02-paradigm-shift', remotionDir: 'S02-ParadigmShift', compositionId: 'Part2ParadigmShift' },
  { id: 'part3_mold', file: 'part3_mold.mp4', label: 'Part 3: Mold Has Three Parts', specDir: '03-mold-has-three-parts', remotionDir: 'S03-MoldThreeParts', compositionId: 'Part3MoldThreeParts' },
  { id: 'part4_precision', file: 'part4_precision.mp4', label: 'Part 4: Precision Tradeoff', specDir: '04-precision-tradeoff', remotionDir: 'S04-PrecisionTradeoff', compositionId: 'Part4PrecisionTradeoff' },
  { id: 'part5_compound', file: 'part5_compound.mp4', label: 'Part 5: Compound Returns', specDir: '05-compound-returns', remotionDir: 'S05-CompoundReturns', compositionId: 'Part5CompoundReturns' },
  { id: 'closing', file: 'closing.mp4', label: 'Closing', specDir: '06-closing', remotionDir: 'S06-Closing', compositionId: 'ClosingSection' },
];

const ALLOWED_SECTION_FILES = new Set(SECTIONS.map(s => s.file));

app.get('/api/sections', (req, res) => {
  res.json(SECTIONS);
});

// --- Video streaming with range requests ---

function streamVideo(filePath, req, res) {
  if (!fs.existsSync(filePath)) {
    return res.status(404).json({ error: 'Video not found' });
  }

  const stat = fs.statSync(filePath);
  const fileSize = stat.size;
  const range = req.headers.range;

  let stream;
  if (range) {
    const parts = range.replace(/bytes=/, '').split('-');
    const start = parseInt(parts[0], 10);
    const end = parts[1] ? parseInt(parts[1], 10) : fileSize - 1;
    const chunkSize = end - start + 1;
    res.writeHead(206, {
      'Content-Range': `bytes ${start}-${end}/${fileSize}`,
      'Accept-Ranges': 'bytes',
      'Content-Length': chunkSize,
      'Content-Type': 'video/mp4',
    });
    stream = fs.createReadStream(filePath, { start, end });
  } else {
    res.writeHead(200, {
      'Content-Length': fileSize,
      'Content-Type': 'video/mp4',
      'Accept-Ranges': 'bytes',
    });
    stream = fs.createReadStream(filePath);
  }

  pipeline(stream, res, (err) => {
    if (err && err.code !== 'ERR_STREAM_PREMATURE_CLOSE') {
      console.error('Stream error:', err.message);
    }
  });
}

app.get('/video/full', (req, res) => {
  streamVideo(path.join(OUTPUTS_DIR, 'full_video.mp4'), req, res);
});

app.get('/video/sections/:file', (req, res) => {
  const file = req.params.file;
  if (!ALLOWED_SECTION_FILES.has(file)) {
    return res.status(403).json({ error: 'File not allowed' });
  }
  streamVideo(path.join(SECTIONS_DIR, file), req, res);
});

// --- Thumbnail upload ---

app.post('/api/thumbnails', (req, res) => {
  const { dataUrl } = req.body;
  if (!dataUrl || !dataUrl.startsWith('data:image/')) {
    return res.status(400).json({ error: 'Invalid data URL' });
  }
  const base64Data = dataUrl.replace(/^data:image\/\w+;base64,/, '');
  const filename = `thumb_${Date.now()}_${Math.random().toString(36).slice(2, 6)}.jpg`;
  fs.writeFileSync(path.join(THUMBNAILS_DIR, filename), Buffer.from(base64Data, 'base64'));
  res.json({ url: `/thumbnails/${filename}` });
});

// --- Annotations CRUD ---

function readAnnotations() {
  if (!fs.existsSync(DATA_FILE)) {
    const initial = { version: '1.0', annotations: [] };
    fs.writeFileSync(DATA_FILE, JSON.stringify(initial, null, 2));
    return initial;
  }
  return JSON.parse(fs.readFileSync(DATA_FILE, 'utf-8'));
}

function writeAnnotations(data) {
  fs.writeFileSync(DATA_FILE, JSON.stringify(data, null, 2));
}

app.get('/api/annotations', (req, res) => {
  res.json(readAnnotations());
});

app.post('/api/annotations', (req, res) => {
  const data = readAnnotations();
  const annotation = req.body;
  annotation.id = `ann_${Date.now()}_${Math.random().toString(36).slice(2, 6)}`;
  annotation.createdAt = new Date().toISOString();
  data.annotations.push(annotation);
  writeAnnotations(data);
  res.status(201).json(annotation);
});

app.put('/api/annotations/:id', (req, res) => {
  const data = readAnnotations();
  const idx = data.annotations.findIndex(a => a.id === req.params.id);
  if (idx === -1) return res.status(404).json({ error: 'Not found' });
  data.annotations[idx] = { ...data.annotations[idx], ...req.body, id: req.params.id };
  writeAnnotations(data);
  res.json(data.annotations[idx]);
});

app.delete('/api/annotations/:id', (req, res) => {
  const data = readAnnotations();
  const idx = data.annotations.findIndex(a => a.id === req.params.id);
  if (idx === -1) return res.status(404).json({ error: 'Not found' });
  data.annotations.splice(idx, 1);
  writeAnnotations(data);
  res.status(204).end();
});

// --- Load specs for a section ---

function loadSectionSpecs(sectionId) {
  const section = SECTIONS.find(s => s.id === sectionId);
  if (!section) return '';

  const specPath = path.join(SPECS_DIR, section.specDir);
  if (!fs.existsSync(specPath)) return '';

  const files = fs.readdirSync(specPath).filter(f =>
    f.endsWith('.md') && !f.startsWith('AUDIT_')
  ).sort();

  let combined = '';
  for (const file of files) {
    const filePath = path.join(specPath, file);
    const stat = fs.statSync(filePath);
    if (stat.isFile()) {
      combined += `\n--- ${file} ---\n`;
      combined += fs.readFileSync(filePath, 'utf-8');
      combined += '\n';
    }
  }
  return combined;
}

// --- Write queue for serialized file access ---

let writeQueue = Promise.resolve();

function safeWriteAnnotations(mutate) {
  const op = writeQueue.then(() => {
    const data = readAnnotations();
    mutate(data);
    writeAnnotations(data);
    return data;
  });
  writeQueue = op.catch(() => {});
  return op;
}

// --- JSON extraction helper ---

function extractJsonFromText(text) {
  if (typeof text !== 'string') return null;

  // Strategy A: Direct parse (text is pure JSON)
  try {
    const obj = JSON.parse(text);
    if (obj && typeof obj === 'object' && !Array.isArray(obj)) return obj;
  } catch { /* not pure JSON */ }

  // Strategy B: Extract from markdown code fence
  // Handles both ```json\n{...}\n``` and ```json\n{...}EOF (no closing fence)
  const fenceOpenRegex = /```(?:json)?\s*\n/g;
  let fenceOpen;
  while ((fenceOpen = fenceOpenRegex.exec(text)) !== null) {
    const afterFence = text.slice(fenceOpen.index + fenceOpen[0].length);
    const closingIdx = afterFence.indexOf('\n```');
    const content = (closingIdx >= 0 ? afterFence.slice(0, closingIdx) : afterFence).trim();

    // Try direct parse
    try {
      const obj = JSON.parse(content);
      if (obj && typeof obj === 'object' && !Array.isArray(obj)) return obj;
    } catch { /* try brace matching within fence content */ }

    // Brace matching scoped to fence content (avoids prose {…} before fence)
    const firstBrace = content.indexOf('{');
    const lastBrace = content.lastIndexOf('}');
    if (firstBrace >= 0 && lastBrace > firstBrace) {
      try {
        const obj = JSON.parse(content.slice(firstBrace, lastBrace + 1));
        if (obj && typeof obj === 'object' && !Array.isArray(obj)) return obj;
      } catch { /* not valid JSON in this fence */ }
    }
  }

  // Strategy C: Brace matching — find outermost { } pair
  const firstBrace = text.indexOf('{');
  const lastBrace = text.lastIndexOf('}');
  if (firstBrace >= 0 && lastBrace > firstBrace) {
    try {
      const obj = JSON.parse(text.slice(firstBrace, lastBrace + 1));
      if (obj && typeof obj === 'object' && !Array.isArray(obj)) return obj;
    } catch { /* extraction failed */ }
  }

  return null;
}

// --- Claude analysis ---

function buildAnalysisPrompt(text, sectionId, timestamp, { annotation } = {}) {
  const section = SECTIONS.find(s => s.id === sectionId);
  const sectionLabel = section ? section.label : 'Unknown section';
  const specDir = section ? section.specDir : null;
  const remotionDir = section ? section.remotionDir : null;

  const resources = [];
  let resourceNum = 1;

  if (specDir) {
    resources.push(`${resourceNum}. SPEC FILES — read all .md files (excluding AUDIT_* files) in:\n   specs/${specDir}/`);
    resourceNum++;
  }

  resources.push(`${resourceNum}. MAIN SCRIPT — read the "${sectionLabel}" section from:\n   narrative/main_script.md`);
  resourceNum++;

  if (remotionDir) {
    resources.push(`${resourceNum}. REMOTION SOURCE — read the main component .tsx and constants.ts from:\n   remotion/src/remotion/${remotionDir}/`);
    resourceNum++;
  }

  if (annotation && annotation.video) {
    if (annotation.video.frameThumbnail) {
      const thumbBasename = path.basename(annotation.video.frameThumbnail);
      const thumbPath = path.join(__dirname, 'data', 'thumbnails', thumbBasename);
      if (fs.existsSync(thumbPath)) {
        resources.push(`${resourceNum}. SCREENSHOT — read this image to see the exact frame the reviewer paused on:\n   review-app/data/thumbnails/${thumbBasename}`);
        resourceNum++;
      }
    }
    if (annotation.video.compositeImage) {
      const compBasename = path.basename(annotation.video.compositeImage);
      const compPath = path.join(__dirname, 'data', 'thumbnails', compBasename);
      if (fs.existsSync(compPath)) {
        resources.push(`${resourceNum}. REVIEWER'S MARKUP — read this image showing the reviewer's drawn annotations:\n   review-app/data/thumbnails/${compBasename}`);
        resourceNum++;
      }
    }
  }

  return `You are reviewing an animated video for a 3Blue1Brown-style educational video called "Why You're Still Darning Socks". A reviewer has paused at timestamp ${timestamp || 'unknown'} in the "${sectionLabel}" section and left this annotation:

"${text}"

Use your Read and Glob tools to examine the following resources before analyzing:

${resources.join('\n\n')}

After reading the resources above, produce your analysis as a JSON object with these fields:
{
  "severity": "critical|high|medium|low|informational",
  "category": "one of: animation-timing, visual-design, readability, audio-sync, color-contrast, layout, typography, data-accuracy, transition, continuity, other",
  "summary": "one-sentence summary of the issue",
  "technicalAssessment": "detailed technical analysis of what might be wrong and why",
  "suggestedFixes": ["array of specific actionable fix suggestions"],
  "relevantFiles": ["array of likely relevant source file paths in the remotion/ directory"],
  "specReference": "the most relevant spec file path, e.g. specs/01-economics/01_sock_price_chart.md"
}`;
}

app.post('/api/analyze', async (req, res) => {
  const { text, sectionId, timestamp } = req.body;
  if (!text) return res.status(400).json({ error: 'Annotation text is required' });

  try {
    const prompt = buildAnalysisPrompt(text, sectionId, timestamp);
    const result = await runClaude(prompt);
    res.json(result);
  } catch (err) {
    console.error('Claude analysis error:', err.message);
    res.json({ status: 'error', error: err.message });
  }
});

app.post('/api/annotations/:id/analyze', async (req, res) => {
  const data = readAnnotations();
  const ann = data.annotations.find(a => a.id === req.params.id);
  if (!ann) return res.status(404).json({ error: 'Not found' });

  const text = ann.text && ann.text.content;
  if (!text) return res.status(400).json({ error: 'No annotation text' });

  try {
    const prompt = buildAnalysisPrompt(text, ann.video && ann.video.sectionId, ann.video && ann.video.timestampFormatted, { annotation: ann });
    const result = await runClaude(prompt);

    const freshData = await safeWriteAnnotations((d) => {
      const idx = d.annotations.findIndex(a => a.id === req.params.id);
      if (idx !== -1) d.annotations[idx].analysis = { ...result, status: 'completed' };
    });
    const updated = freshData.annotations.find(a => a.id === req.params.id);
    res.json(updated || { error: 'Not found after write' });
  } catch (err) {
    console.error('Annotation analysis error:', err.message);
    res.status(500).json({ error: err.message });
  }
});

function runClaude(prompt) {
  return new Promise((resolve, reject) => {
    const outputFile = path.join(ANALYSIS_TEMP_DIR, `analysis_${Date.now()}_${Math.random().toString(36).slice(2, 6)}.json`);
    const fullPrompt = prompt + `\n\nIMPORTANT: After your analysis, use the Write tool to save ONLY the JSON object (no other text) to this exact file path:\n${outputFile}`;

    const args = [
      '-p', '--model', 'claude-opus-4-6', '--output-format', 'json', '--no-session-persistence',
      '--allowedTools', 'Read,Glob,Write',
    ];
    const child = spawn('claude', args, {
      stdio: ['pipe', 'pipe', 'pipe'],
      cwd: path.join(__dirname, '..'),
    });

    let stdout = '';
    let stderr = '';

    child.stdout.on('data', chunk => { stdout += chunk.toString(); });
    child.stderr.on('data', chunk => { stderr += chunk.toString(); });

    child.on('error', err => {
      if (err.code === 'ENOENT') {
        reject(new Error('claude CLI not found. Install it or ensure it is on PATH.'));
      } else {
        reject(err);
      }
    });

    child.on('close', code => {
      if (code !== 0) {
        reject(new Error(`claude exited with code ${code}: ${stderr}`));
        return;
      }

      // Strategy 1: Read from temp file (Claude wrote JSON directly via Write tool)
      try {
        if (fs.existsSync(outputFile)) {
          const fileContent = fs.readFileSync(outputFile, 'utf-8');
          fs.unlinkSync(outputFile);
          const analysis = JSON.parse(fileContent);
          analysis.status = 'completed';
          resolve(analysis);
          return;
        }
      } catch { /* fall through to stdout */ }

      // Strategy 2: Parse from stdout (fallback — extract JSON via brace matching)
      let text = stdout;
      try {
        const wrapper = JSON.parse(stdout);
        if (typeof wrapper.result === 'string') {
          text = wrapper.result;
        } else if (wrapper.result && typeof wrapper.result === 'object') {
          const blocks = wrapper.result.content || [];
          const textBlock = blocks.find(b => b.type === 'text');
          if (textBlock) text = textBlock.text;
        }
      } catch { /* stdout isn't a JSON wrapper — use raw stdout as text */ }

      const analysis = extractJsonFromText(text);
      if (analysis) {
        analysis.status = 'completed';
        resolve(analysis);
      } else {
        resolve({ status: 'completed', summary: text, raw: true });
      }
    });

    child.stdin.write(fullPrompt);
    child.stdin.end();
  });
}

// --- Resolve pipeline: job manager + endpoints ---

const jobs = new Map();
const sectionQueues = new Map();

function createJob(annotationId, sectionId) {
  const id = `job_${Date.now()}_${Math.random().toString(36).slice(2, 6)}`;
  const job = {
    id,
    annotationId,
    sectionId,
    status: 'pending',
    step: null,
    progress: 0,
    error: null,
    log: [],
    startedAt: new Date().toISOString(),
    completedAt: null,
    subscribers: [],
  };
  jobs.set(id, job);
  return job;
}

function emitJobUpdate(job, update) {
  Object.assign(job, update);
  const payload = {
    id: job.id,
    status: job.status,
    step: job.step,
    progress: job.progress,
    error: job.error,
    completedAt: job.completedAt,
  };
  const msg = `data: ${JSON.stringify(payload)}\n\n`;
  job.subscribers = job.subscribers.filter(res => {
    try { res.write(msg); return true; } catch { return false; }
  });
}

function buildFixPrompt(annotation, section) {
  const text = annotation.text && annotation.text.content;
  const timestamp = annotation.video && annotation.video.timestampFormatted;
  const analysis = annotation.analysis || {};

  const resources = [];
  let n = 1;

  if (section.specDir) {
    resources.push(`${n}. SPEC FILES — read all .md files (excluding AUDIT_* files) in:\n   specs/${section.specDir}/`);
    n++;
  }

  if (section.remotionDir) {
    resources.push(`${n}. REMOTION SOURCE — read all .tsx and .ts files in:\n   remotion/src/remotion/${section.remotionDir}/`);
    n++;
  }

  if (annotation.video && annotation.video.frameThumbnail) {
    const thumbBasename = path.basename(annotation.video.frameThumbnail);
    const thumbPath = path.join(__dirname, 'data', 'thumbnails', thumbBasename);
    if (fs.existsSync(thumbPath)) {
      resources.push(`${n}. SCREENSHOT — read this image to see the exact frame:\n   review-app/data/thumbnails/${thumbBasename}`);
      n++;
    }
  }

  if (annotation.drawing && annotation.drawing.compositeImage) {
    const compBasename = path.basename(annotation.drawing.compositeImage);
    const compPath = path.join(__dirname, 'data', 'thumbnails', compBasename);
    if (fs.existsSync(compPath)) {
      resources.push(`${n}. REVIEWER'S MARKUP — read this image showing drawn annotations:\n   review-app/data/thumbnails/${compBasename}`);
      n++;
    }
  }

  return `You are fixing an issue in the Remotion source code for a 3Blue1Brown-style educational video called "Why You're Still Darning Socks".

A reviewer paused at timestamp ${timestamp || 'unknown'} in the "${section.label}" section and reported:

"${text}"

## Analysis
- Severity: ${analysis.severity || 'unknown'}
- Category: ${analysis.category || 'unknown'}
- Technical Assessment: ${analysis.technicalAssessment || 'N/A'}
- Suggested Fixes: ${analysis.suggestedFixes ? analysis.suggestedFixes.join('; ') : 'N/A'}
- Relevant Files: ${analysis.relevantFiles ? analysis.relevantFiles.join(', ') : 'N/A'}

## Instructions
1. Read the following resources:

${resources.join('\n\n')}

2. Based on the analysis and resources, edit the Remotion source files to fix the issue.
3. Only edit files within remotion/src/remotion/${section.remotionDir}/ — do not modify files outside this directory.
4. Keep changes minimal and focused on the reported issue.
5. Preserve timing and animation structure unless timing IS the reported issue.

After making your fixes, output a JSON summary:
{
  "filesModified": ["array of modified file paths"],
  "changeDescription": "brief description of what was changed",
  "confidence": "high|medium|low"
}`;
}

function fixWithClaude(job, annotation, section) {
  return new Promise((resolve, reject) => {
    emitJobUpdate(job, { status: 'running', step: 'fixing', progress: 0 });

    const outputFile = path.join(ANALYSIS_TEMP_DIR, `fix_${Date.now()}_${Math.random().toString(36).slice(2, 6)}.json`);
    const prompt = buildFixPrompt(annotation, section);
    const fullPrompt = prompt + `\n\nIMPORTANT: After making your fixes, use the Write tool to save ONLY the JSON summary (no other text) to this exact file path:\n${outputFile}`;

    const args = [
      '-p', '--model', 'claude-opus-4-6', '--output-format', 'json', '--no-session-persistence',
      '--allowedTools', 'Read,Write,Edit,Glob,Grep',
    ];
    const child = spawn('claude', args, {
      stdio: ['pipe', 'pipe', 'pipe'],
      cwd: path.join(__dirname, '..'),
    });

    let stdout = '';

    child.stdout.on('data', chunk => { stdout += chunk.toString(); });
    child.stderr.on('data', chunk => {
      const line = chunk.toString();
      job.log.push(line);
      // Try to parse progress from claude output
      const pctMatch = line.match(/(\d+)%/);
      if (pctMatch) {
        emitJobUpdate(job, { progress: parseInt(pctMatch[1], 10) });
      }
    });

    child.on('error', err => {
      if (err.code === 'ENOENT') {
        reject(new Error('claude CLI not found'));
      } else {
        reject(err);
      }
    });

    child.on('close', code => {
      if (code !== 0) {
        reject(new Error(`claude exited with code ${code}`));
        return;
      }

      // Try reading from temp file first
      let result = null;
      try {
        if (fs.existsSync(outputFile)) {
          const content = fs.readFileSync(outputFile, 'utf-8');
          fs.unlinkSync(outputFile);
          result = JSON.parse(content);
        }
      } catch { /* fall through */ }

      if (!result) {
        let text = stdout;
        try {
          const wrapper = JSON.parse(stdout);
          if (typeof wrapper.result === 'string') {
            text = wrapper.result;
          } else if (wrapper.result && typeof wrapper.result === 'object') {
            const blocks = wrapper.result.content || [];
            const textBlock = blocks.find(b => b.type === 'text');
            if (textBlock) text = textBlock.text;
          }
        } catch { /* use raw stdout */ }
        result = extractJsonFromText(text) || { filesModified: [], changeDescription: 'Fix applied', confidence: 'medium' };
      }

      emitJobUpdate(job, { step: 'fixing', progress: 100 });
      resolve(result);
    });

    child.stdin.write(fullPrompt);
    child.stdin.end();
  });
}

function renderSection(job, section) {
  return new Promise((resolve, reject) => {
    emitJobUpdate(job, { step: 'rendering', progress: 0 });

    const outputPath = path.join('..', 'outputs', 'sections', section.file);
    const args = [
      'remotion', 'render', 'src/remotion/index.ts', section.compositionId,
      '--output', outputPath, '--overwrite',
    ];
    const child = spawn('npx', args, {
      stdio: ['pipe', 'pipe', 'pipe'],
      cwd: path.join(__dirname, '..', 'remotion'),
    });

    child.stdout.on('data', chunk => {
      const line = chunk.toString();
      job.log.push(line);
      const pctMatch = line.match(/(\d+)%/);
      if (pctMatch) {
        emitJobUpdate(job, { progress: parseInt(pctMatch[1], 10) });
      }
    });

    child.stderr.on('data', chunk => {
      const line = chunk.toString();
      job.log.push(line);
      const pctMatch = line.match(/(\d+)%/);
      if (pctMatch) {
        emitJobUpdate(job, { progress: parseInt(pctMatch[1], 10) });
      }
    });

    child.on('error', err => reject(err));
    child.on('close', code => {
      if (code !== 0) {
        reject(new Error(`Remotion render exited with code ${code}`));
        return;
      }
      emitJobUpdate(job, { step: 'rendering', progress: 100 });
      resolve();
    });
  });
}

function stitchFullVideo(job) {
  return new Promise((resolve, reject) => {
    emitJobUpdate(job, { step: 'stitching', progress: 0 });

    const sectionsDir = path.join(OUTPUTS_DIR, 'sections');
    const concatListPath = path.join(sectionsDir, 'concat_list.txt');

    if (!fs.existsSync(concatListPath)) {
      reject(new Error('concat_list.txt not found in outputs/sections/'));
      return;
    }

    const args = [
      '-y', '-f', 'concat', '-safe', '0',
      '-i', 'concat_list.txt',
      '-c', 'copy',
      path.join('..', 'full_video.mp4'),
    ];
    const child = spawn('ffmpeg', args, {
      stdio: ['pipe', 'pipe', 'pipe'],
      cwd: sectionsDir,
    });

    child.stdout.on('data', () => {});
    child.stderr.on('data', chunk => {
      job.log.push(chunk.toString());
    });

    child.on('error', err => reject(err));
    child.on('close', code => {
      if (code !== 0) {
        reject(new Error(`ffmpeg stitch exited with code ${code}`));
        return;
      }
      emitJobUpdate(job, { step: 'stitching', progress: 100 });
      resolve();
    });
  });
}

async function runResolvePipeline(job) {
  try {
    const data = readAnnotations();
    const ann = data.annotations.find(a => a.id === job.annotationId);
    if (!ann) throw new Error('Annotation not found');

    const section = SECTIONS.find(s => s.id === (ann.video && ann.video.sectionId));
    if (!section) throw new Error('Section not found');

    // Step 1: Fix with Claude
    await fixWithClaude(job, ann, section);

    // Step 2: Render the section
    await renderSection(job, section);

    // Step 3: Stitch full video
    await stitchFullVideo(job);

    // Mark done
    emitJobUpdate(job, { status: 'done', step: null, progress: 100, completedAt: new Date().toISOString() });

    await safeWriteAnnotations((d) => {
      const idx = d.annotations.findIndex(a => a.id === job.annotationId);
      if (idx !== -1) {
        d.annotations[idx].resolved = true;
        d.annotations[idx].resolveJob = { jobId: job.id, status: 'done' };
      }
    });
  } catch (err) {
    const errMsg = err.message || String(err);
    emitJobUpdate(job, { status: 'error', error: errMsg, completedAt: new Date().toISOString() });

    await safeWriteAnnotations((d) => {
      const idx = d.annotations.findIndex(a => a.id === job.annotationId);
      if (idx !== -1) {
        d.annotations[idx].resolveJob = { jobId: job.id, status: 'error', error: errMsg };
      }
    });
  } finally {
    // Close all SSE connections
    for (const sub of job.subscribers) {
      try { sub.end(); } catch { /* ignore */ }
    }
    job.subscribers = [];
  }
}

function enqueueResolve(job, sectionId) {
  if (!sectionQueues.has(sectionId)) {
    sectionQueues.set(sectionId, Promise.resolve());
  }
  const prev = sectionQueues.get(sectionId);
  const next = prev.then(() => runResolvePipeline(job)).catch(() => {});
  sectionQueues.set(sectionId, next);
}

// POST /api/annotations/:id/resolve — kick off resolve pipeline
app.post('/api/annotations/:id/resolve', (req, res) => {
  const data = readAnnotations();
  const ann = data.annotations.find(a => a.id === req.params.id);
  if (!ann) return res.status(404).json({ error: 'Not found' });

  if (!ann.analysis || ann.analysis.status !== 'completed') {
    return res.status(400).json({ error: 'Analysis must be completed before resolving' });
  }

  const sectionId = ann.video && ann.video.sectionId;
  if (!sectionId) return res.status(400).json({ error: 'Annotation has no section' });

  const job = createJob(ann.id, sectionId);

  // Save job reference to annotation
  safeWriteAnnotations((d) => {
    const idx = d.annotations.findIndex(a => a.id === req.params.id);
    if (idx !== -1) {
      d.annotations[idx].resolveJob = { jobId: job.id, status: 'pending' };
    }
  });

  enqueueResolve(job, sectionId);

  res.status(202).json({ jobId: job.id });
});

// GET /api/jobs/:id/stream — SSE stream for job progress
app.get('/api/jobs/:id/stream', (req, res) => {
  const job = jobs.get(req.params.id);
  if (!job) return res.status(404).json({ error: 'Job not found' });

  res.writeHead(200, {
    'Content-Type': 'text/event-stream',
    'Cache-Control': 'no-cache',
    'Connection': 'keep-alive',
  });

  // Send current state immediately
  const payload = {
    id: job.id,
    status: job.status,
    step: job.step,
    progress: job.progress,
    error: job.error,
    completedAt: job.completedAt,
  };
  res.write(`data: ${JSON.stringify(payload)}\n\n`);

  // If already terminal, close
  if (job.status === 'done' || job.status === 'error') {
    res.end();
    return;
  }

  job.subscribers.push(res);
  req.on('close', () => {
    job.subscribers = job.subscribers.filter(s => s !== res);
  });
});

// GET /api/jobs/:id — polling fallback
app.get('/api/jobs/:id', (req, res) => {
  const job = jobs.get(req.params.id);
  if (!job) return res.status(404).json({ error: 'Job not found' });

  res.json({
    id: job.id,
    status: job.status,
    step: job.step,
    progress: job.progress,
    error: job.error,
    completedAt: job.completedAt,
  });
});

// --- Export ---

app.get('/api/export', (req, res) => {
  const data = readAnnotations();
  res.setHeader('Content-Disposition', 'attachment; filename="annotations.json"');
  res.setHeader('Content-Type', 'application/json');
  res.json(data);
});

// --- Recover stale jobs on startup ---

(function recoverStaleJobs() {
  try {
    const data = readAnnotations();
    let changed = false;
    for (const ann of data.annotations) {
      if (ann.resolveJob && (ann.resolveJob.status === 'pending' || ann.resolveJob.status === 'running')) {
        ann.resolveJob.status = 'error';
        ann.resolveJob.error = 'Server restarted during pipeline';
        changed = true;
      }
    }
    if (changed) writeAnnotations(data);
  } catch { /* no annotations file yet */ }
})();

// --- Start ---

if (require.main === module) {
  app.listen(PORT, () => {
    console.log(`Review app running at http://localhost:${PORT}`);
    console.log(`Serving videos from: ${OUTPUTS_DIR}`);
  });
}

module.exports = app;
