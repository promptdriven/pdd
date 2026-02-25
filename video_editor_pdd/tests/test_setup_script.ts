import { describe, it, expect } from '@jest/globals';
import fs from 'fs';
import path from 'path';

describe('setup.sh', () => {
  const setupPath = path.join(__dirname, '..', 'setup.sh');

  it('file exists', () => {
    expect(fs.existsSync(setupPath)).toBe(true);
  });

  it('is executable', () => {
    const stat = fs.statSync(setupPath);
    // Check if owner execute bit is set
    expect(stat.mode & 0o100).toBeTruthy();
  });

  it('starts with bash shebang', () => {
    const content = fs.readFileSync(setupPath, 'utf-8');
    expect(content.startsWith('#!/usr/bin/env bash')).toBe(true);
  });

  it('uses set -euo pipefail', () => {
    const content = fs.readFileSync(setupPath, 'utf-8');
    expect(content).toContain('set -euo pipefail');
  });

  it('checks for Node.js', () => {
    const content = fs.readFileSync(setupPath, 'utf-8');
    expect(content).toContain('node');
    expect(content).toContain('Node.js');
  });

  it('checks for Python', () => {
    const content = fs.readFileSync(setupPath, 'utf-8');
    expect(content).toContain('python3');
  });

  it('checks for ffmpeg', () => {
    const content = fs.readFileSync(setupPath, 'utf-8');
    expect(content).toContain('ffmpeg');
  });

  it('runs npm install', () => {
    const content = fs.readFileSync(setupPath, 'utf-8');
    expect(content).toContain('npm install');
  });

  it('creates output directories', () => {
    const content = fs.readFileSync(setupPath, 'utf-8');
    expect(content).toContain('mkdir -p');
    expect(content).toContain('outputs');
  });

  it('initializes the database', () => {
    const content = fs.readFileSync(setupPath, 'utf-8');
    expect(content).toContain('getDb');
  });
});

describe('requirements.txt', () => {
  const reqPath = path.join(__dirname, '..', 'requirements.txt');

  it('file exists', () => {
    expect(fs.existsSync(reqPath)).toBe(true);
  });

  it('includes key Python dependencies', () => {
    const content = fs.readFileSync(reqPath, 'utf-8');
    expect(content).toContain('numpy');
    expect(content).toContain('soundfile');
    expect(content).toContain('faster-whisper');
    expect(content).toContain('pydub');
  });
});

describe('Makefile', () => {
  const makefilePath = path.join(__dirname, '..', 'Makefile');

  it('file exists', () => {
    expect(fs.existsSync(makefilePath)).toBe(true);
  });

  it('has setup target', () => {
    const content = fs.readFileSync(makefilePath, 'utf-8');
    expect(content).toContain('setup:');
  });
});
