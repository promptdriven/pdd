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
app.use('/thumbnails', express.static(THUMBNAILS_DIR));

// --- Section metadata ---

const SECTIONS = [
  { id: 'cold_open', file: 'cold_open.mp4', label: 'Cold Open', specDir: '00-cold-open' },
  { id: 'part1_economics', file: 'part1_economics.mp4', label: 'Part 1: Economics', specDir: '01-economics' },
  { id: 'part2_paradigm_shift', file: 'part2_paradigm_shift.mp4', label: 'Part 2: Paradigm Shift', specDir: '02-paradigm-shift' },
  { id: 'part3_mold', file: 'part3_mold.mp4', label: 'Part 3: Mold Has Three Parts', specDir: '03-mold-has-three-parts' },
  { id: 'part4_precision', file: 'part4_precision.mp4', label: 'Part 4: Precision Tradeoff', specDir: '04-precision-tradeoff' },
  { id: 'part5_compound', file: 'part5_compound.mp4', label: 'Part 5: Compound Returns', specDir: '05-compound-returns' },
  { id: 'closing', file: 'closing.mp4', label: 'Closing', specDir: '06-closing' },
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

// --- Claude analysis ---

function buildAnalysisPrompt(text, sectionId, timestamp) {
  const specs = loadSectionSpecs(sectionId);
  const section = SECTIONS.find(s => s.id === sectionId);
  const sectionLabel = section ? section.label : 'Unknown section';

  return `You are reviewing an animated video for a 3Blue1Brown-style educational video called "Why You're Still Darning Socks". A reviewer has paused at timestamp ${timestamp || 'unknown'} in the "${sectionLabel}" section and left this annotation:

"${text}"

Here are the scene specification files for this section to help you understand what was intended:

${specs || '(No specs available for this section)'}

Based on the annotation and the specs, provide a structured analysis. Return ONLY valid JSON (no markdown fencing) with these fields:
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
    const prompt = buildAnalysisPrompt(text, ann.video && ann.video.sectionId, ann.video && ann.video.timestampFormatted);
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
    const args = ['-p', '--model', 'claude-opus-4-6', '--output-format', 'json', '--no-session-persistence'];
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
      try {
        const wrapper = JSON.parse(stdout);
        let text = wrapper.result || stdout;
        // Strip markdown fencing (```json ... ```) that Claude often wraps around JSON
        text = text.replace(/^```(?:json)?\s*\n?/i, '').replace(/\n?```\s*$/i, '').trim();
        // Try to parse the result as JSON (Claude's response)
        try {
          const analysis = JSON.parse(text);
          analysis.status = 'completed';
          resolve(analysis);
        } catch {
          // If Claude's response isn't valid JSON, return it as a summary
          resolve({ status: 'completed', summary: text, raw: true });
        }
      } catch {
        // stdout wasn't valid JSON wrapper either
        resolve({ status: 'completed', summary: stdout, raw: true });
      }
    });

    child.stdin.write(prompt);
    child.stdin.end();
  });
}

// --- Export ---

app.get('/api/export', (req, res) => {
  const data = readAnnotations();
  res.setHeader('Content-Disposition', 'attachment; filename="annotations.json"');
  res.setHeader('Content-Type', 'application/json');
  res.json(data);
});

// --- Start ---

if (require.main === module) {
  app.listen(PORT, () => {
    console.log(`Review app running at http://localhost:${PORT}`);
    console.log(`Serving videos from: ${OUTPUTS_DIR}`);
  });
}

module.exports = app;
