// ===== File: automations.js =====
const fs = require('fs/promises');
const fssync = require('fs');
const path = require('path');
const { app } = require('electron');
const { nanoid } = require('nanoid');
const puppeteer = require('puppeteer');

class Automations {
  constructor(options = {}) {
    this.baseDir = options.baseDir || path.join(app.getPath('userData'), 'automations');
    if (!fssync.existsSync(this.baseDir)) {
      fssync.mkdirSync(this.baseDir, { recursive: true });
    }
    this.browser = null; // puppeteer browser instance for replay
  }

  // Schema: { id, name, createdAt, updatedAt, meta, steps: [ { action, selector?, value?, url?, waitFor?, timeout?, options? } ] }
  validateAutomation(automation) {
    if (!automation) throw new Error('Automation is required');
    if (!automation.steps || !Array.isArray(automation.steps)) {
      throw new Error('Automation.steps must be an array');
    }
    automation.name = automation.name || 'Untitled';
    automation.meta = automation.meta || {};
    return automation;
  }

  uuid() {
    return nanoid();
  }

  fileFor(id) {
    return path.join(this.baseDir, `${id}.json`);
  }

  async list() {
    const files = await fs.readdir(this.baseDir);
    const out = [];
    for (const f of files) {
      if (!f.endsWith('.json')) continue;
      try {
        const raw = await fs.readFile(path.join(this.baseDir, f), 'utf8');
        const obj = JSON.parse(raw);
        out.push({
          id: obj.id,
          name: obj.name,
          createdAt: obj.createdAt,
          updatedAt: obj.updatedAt,
          meta: obj.meta || {},
          stepCount: Array.isArray(obj.steps) ? obj.steps.length : 0
        });
      } catch {}
    }
    // newest first
    out.sort((a, b) => (b.updatedAt || 0) - (a.updatedAt || 0));
    return out;
  }

  async load(id) {
    const file = this.fileFor(id);
    const raw = await fs.readFile(file, 'utf8');
    return JSON.parse(raw);
  }

  async delete(id) {
    const file = this.fileFor(id);
    await fs.rm(file, { force: true });
    return true;
  }

  async save({ id, name, steps, meta }) {
    const now = Date.now();
    const record = this.validateAutomation({
      id: id || this.uuid(),
      name,
      steps,
      meta,
      createdAt: now,
      updatedAt: now
    });

    // If updating existing, preserve createdAt
    const file = this.fileFor(record.id);
    if (fssync.existsSync(file)) {
      try {
        const prev = JSON.parse(await fs.readFile(file, 'utf8'));
        record.createdAt = prev.createdAt || now;
      } catch {}
    }

    await fs.writeFile(file, JSON.stringify(record, null, 2), 'utf8');
    return record;
  }

  // Normalize a subset of Puppeteer-like events into our step schema
  // Accepts array of steps like: { type: 'goto'|'click'|'type'|'waitForSelector'|'waitForTimeout', selector?, value?, url?, timeout? }
  importFromPuppeteerSteps(name, puppeteerSteps = [], meta = {}) {
    const steps = puppeteerSteps.map(s => {
      switch (s.type) {
        case 'goto':
          return { action: 'navigate', url: s.url };
        case 'click':
          return { action: 'click', selector: s.selector, options: s.options || {} };
        case 'type':
          return { action: 'type', selector: s.selector, value: s.text, options: s.options || {} };
        case 'waitForSelector':
          return { action: 'waitForSelector', selector: s.selector, timeout: s.timeout };
        case 'waitForTimeout':
          return { action: 'wait', timeout: s.timeout || s.ms || 0 };
        case 'scroll':
          return { action: 'scroll', x: s.x || 0, y: s.y || 0, behavior: s.behavior || 'smooth' };
        case 'setViewport':
          return { action: 'setViewport', width: s.width, height: s.height, deviceScaleFactor: s.deviceScaleFactor || 1 };
        default:
          return { action: 'noop', meta: { original: s } };
      }
    });
    return { name, steps, meta };
  }

  // Replay in a new Chromium tab using Puppeteer
  async replay(id, options = {}) {
    const { headless = 'new', slowMo = 0, defaultTimeout = 15000 } = options;
    const automation = await this.load(id);
    if (!this.browser) {
      this.browser = await puppeteer.launch({ headless, slowMo });
    }
    const page = await this.browser.newPage();
    page.setDefaultTimeout(defaultTimeout);

    await this.executeSteps(page, automation.steps);
    return true;
  }

  async closeBrowser() {
    if (this.browser) {
      await this.browser.close();
      this.browser = null;
    }
  }

  async executeSteps(page, steps = []) {
    for (const step of steps) {
      const action = step.action;
      switch (action) {
        case 'navigate': {
          if (!step.url) throw new Error('navigate requires url');
          await page.goto(step.url, { waitUntil: 'domcontentloaded' });
          break;
        }
        case 'waitForSelector': {
          if (!step.selector) throw new Error('waitForSelector requires selector');
          await page.waitForSelector(step.selector, { timeout: step.timeout || 15000 });
          break;
        }
        case 'click': {
          if (!step.selector) throw new Error('click requires selector');
          await page.waitForSelector(step.selector);
          await page.click(step.selector, step.options || {});
          break;
        }
        case 'type': {
          if (!step.selector) throw new Error('type requires selector');
          await page.waitForSelector(step.selector);
          if (step.clear) {
            await page.click(step.selector, { clickCount: 3 });
            await page.keyboard.press('Backspace');
          }
          await page.type(step.selector, String(step.value ?? ''), step.options || {});
          break;
        }
        case 'wait': {
          await page.waitForTimeout(step.timeout || 500);
          break;
        }
        case 'scroll': {
          const { x = 0, y = 0, behavior = 'instant' } = step;
          await page.evaluate(({ x, y, behavior }) => {
            window.scrollTo({ left: x, top: y, behavior });
          }, { x, y, behavior });
          break;
        }
        case 'setViewport': {
          const { width = 1280, height = 800, deviceScaleFactor = 1 } = step;
          await page.setViewport({ width, height, deviceScaleFactor });
          break;
        }
        case 'noop': {
          // ignore unknown
          break;
        }
        default:
          throw new Error(`Unknown step action: ${action}`);
      }
    }
  }
}

module.exports = { Automations };


// ===== File: main.js =====
const { app, BrowserWindow, ipcMain } = require('electron');
const path = require('path');
const { Automations } = require('./automations');

let mainWindow;
const automations = new Automations();

function createWindow() {
  mainWindow = new BrowserWindow({
    width: 1200,
    height: 800,
    webPreferences: {
      preload: path.join(__dirname, 'preload.js'),
      nodeIntegration: false,
      contextIsolation: true
    }
  });

  mainWindow.loadFile('index.html');
}

app.whenReady().then(() => {
  createWindow();

  ipcMain.handle('automations:list', async () => {
    return automations.list();
  });

  ipcMain.handle('automations:load', async (_e, id) => {
    return automations.load(id);
  });

  ipcMain.handle('automations:save', async (_e, payload) => {
    // payload: { id?, name, steps, meta? }
    return automations.save(payload);
  });

  ipcMain.handle('automations:delete', async (_e, id) => {
    return automations.delete(id);
  });

  ipcMain.handle('automations:replay', async (_e, id, options) => {
    return automations.replay(id, options);
  });

  ipcMain.handle('automations:importPuppeteer', async (_e, { name, puppeteerSteps, meta }) => {
    const normalized = automations.importFromPuppeteerSteps(name, puppeteerSteps, meta);
    return automations.save(normalized);
  });

  app.on('activate', () => {
    if (BrowserWindow.getAllWindows().length === 0) createWindow();
  });
});

app.on('window-all-closed', async () => {
  await automations.closeBrowser();
  if (process.platform !== 'darwin') {
    app.quit();
  }
});


// ===== File: preload.js =====
const { contextBridge, ipcRenderer } = require('electron');

contextBridge.exposeInMainWorld('automations', {
  list: () => ipcRenderer.invoke('automations:list'),
  load: (id) => ipcRenderer.invoke('automations:load', id),
  save: (payload) => ipcRenderer.invoke('automations:save', payload),
  delete: (id) => ipcRenderer.invoke('automations:delete', id),
  replay: (id, options) => ipcRenderer.invoke('automations:replay', id, options),
  importPuppeteer: (payload) => ipcRenderer.invoke('automations:importPuppeteer', payload)
});


// ===== File: renderer.js =====
const toolbarEl = document.getElementById('toolbar');
const recordBtn = document.getElementById('btn-record');
const stopBtn = document.getElementById('btn-stop');
const saveBtn = document.getElementById('btn-save');
const nameInput = document.getElementById('automation-name');
const listEl = document.getElementById('automation-list');

let recording = false;
let currentSteps = [];
let navigationCaptured = false;

function cssPath(el) {
  if (!(el instanceof Element)) return '';
  const path = [];
  while (el.nodeType === Node.ELEMENT_NODE) {
    let selector = el.nodeName.toLowerCase();
    if (el.id) {
      selector += '#' + el.id;
      path.unshift(selector);
      break;
    } else {
      let sib = el, nth = 1;
      while ((sib = sib.previousElementSibling)) {
        if (sib.nodeName.toLowerCase() === selector) nth++;
      }
      selector += `:nth-of-type(${nth})`;
    }
    path.unshift(selector);
    el = el.parentNode;
  }
  return path.join(' > ');
}

function startRecording() {
  recording = true;
  currentSteps = [];
  navigationCaptured = false;

  // Capture initial URL as navigation
  currentSteps.push({ action: 'navigate', url: location.href });

  document.addEventListener('click', onClick, true);
  document.addEventListener('input', onInput, true);
  window.addEventListener('beforeunload', onBeforeUnload, true);
}

function stopRecording() {
  recording = false;
  document.removeEventListener('click', onClick, true);
  document.removeEventListener('input', onInput, true);
  window.removeEventListener('beforeunload', onBeforeUnload, true);
}

function onClick(e) {
  if (!recording) return;
  const selector = cssPath(e.target);
  currentSteps.push({ action: 'click', selector });
}

function onInput(e) {
  if (!recording) return;
  const t = e.target;
  if (!(t instanceof HTMLInputElement || t instanceof HTMLTextAreaElement || t.isContentEditable)) return;
  const selector = cssPath(t);
  const value = t.isContentEditable ? t.innerText : t.value;
  currentSteps.push({ action: 'type', selector, value, clear: true });
}

function onBeforeUnload() {
  if (!recording) return;
  // Capture navigation on unload
  currentSteps.push({ action: 'wait', timeout: 1000 });
}

async function refreshList() {
  const items = await window.automations.list();
  listEl.innerHTML = '';
  for (const item of items) {
    const li = document.createElement('li');
    li.textContent = `${item.name} (${item.stepCount} steps)`;
    const play = document.createElement('button');
    play.textContent = 'Replay';
    play.onclick = () => window.automations.replay(item.id, { headless: 'new' });

    const del = document.createElement('button');
    del.textContent = 'Delete';
    del.onclick = async () => {
      await window.automations.delete(item.id);
      refreshList();
    };

    li.appendChild(play);
    li.appendChild(del);
    listEl.appendChild(li);
  }
}

recordBtn.addEventListener('click', () => startRecording());
stopBtn.addEventListener('click', () => stopRecording());
saveBtn.addEventListener('click', async () => {
  stopRecording();
  const name = nameInput.value || 'Untitled';
  await window.automations.save({ name, steps: currentSteps, meta: { source: 'renderer-recorder' } });
  currentSteps = [];
  nameInput.value = '';
  refreshList();
});

document.addEventListener('DOMContentLoaded', () => {
  refreshList();
});


// ===== File: index.html =====
<!doctype html>
<html>
  <head>
    <meta charset="utf-8" />
    <title>Automations</title>
    <style>
      #toolbar { display: flex; gap: 8px; margin-bottom: 8px; }
      #automation-list li { margin: 6px 0; }
      button { padding: 6px 10px; }
      input { padding: 6px; }
    </style>
  </head>
  <body>
    <div id="toolbar">
      <button id="btn-record">Record</button>
      <button id="btn-stop">Stop</button>
      <input id="automation-name" placeholder="Automation name" />
      <button id="btn-save">Save</button>
    </div>
    <ul id="automation-list"></ul>
    <script src="./renderer.js"></script>
  </body>
</html>
