/**
 * Tests for US17 — Speech Input UI indicator in VideoPlayer
 *
 * Verifies that VideoPlayer.tsx includes:
 *   1. speechAvailable state that checks for Web Speech API on mount
 *   2. inputMethod state to track typed vs speech input
 *   3. M-key toggle for speech mode in keyboard handler
 *   4. Microphone indicator in the overlay UI
 *   5. M key hint in the bottom controls area
 *   6. inputMethod included in AnnotationCaptureData
 */

import fs from 'fs';
import path from 'path';

describe('VideoPlayer speech input (US17)', () => {
  let sourceCode: string;

  beforeAll(() => {
    sourceCode = fs.readFileSync(
      path.join(__dirname, '..', 'components', 'VideoPlayer.tsx'),
      'utf-8'
    );
  });

  it('has speechAvailable state', () => {
    expect(sourceCode).toMatch(/speechAvailable/);
  });

  it('has inputMethod state', () => {
    expect(sourceCode).toMatch(/inputMethod/);
  });

  it('includes microphone indicator UI', () => {
    expect(sourceCode).toMatch(/1F3A4/);
  });

  it('has M-key toggle for speech mode', () => {
    expect(sourceCode).toMatch(/['"]m['"]/i);
  });

  it('includes inputMethod in capture data', () => {
    expect(sourceCode).toMatch(/inputMethod/);
  });

  it('initializes speechAvailable as false', () => {
    expect(sourceCode).toMatch(/useState\s*<?\s*\(?\s*false\s*\)?/);
    expect(sourceCode).toMatch(/setSpeechAvailable/);
  });

  it('sets speechAvailable to true when Web Speech API is present', () => {
    expect(sourceCode).toMatch(/setSpeechAvailable\s*\(\s*true\s*\)/);
  });

  it('defaults to speech input when Web Speech API is present', () => {
    expect(sourceCode).toMatch(/setInputMethod\s*\(\s*['"]speech['"]\s*\)/);
  });

  it('initializes inputMethod as typed', () => {
    expect(sourceCode).toMatch(/useState\s*<\s*['"]typed['"]\s*\|\s*['"]speech['"]\s*>\s*\(\s*['"]typed['"]\s*\)/);
  });

  it('toggles inputMethod between typed and speech on M key', () => {
    expect(sourceCode).toMatch(/setInputMethod/);
    expect(sourceCode).toMatch(/prev\s*===\s*['"]typed['"]\s*\?\s*['"]speech['"]\s*:\s*['"]typed['"]/);
  });

  it('only toggles speech when speechAvailable is true', () => {
    expect(sourceCode).toMatch(/if\s*\(\s*speechAvailable\s*\)/);
  });

  it('shows microphone ON state with green color', () => {
    expect(sourceCode).toMatch(/text-green-400/);
  });

  it('shows microphone off state with dim color', () => {
    expect(sourceCode).toMatch(/text-white\/40/);
  });

  it('displays M = Mic shortcut hint in controls', () => {
    expect(sourceCode).toMatch(/M\s*=\s*Mic/);
  });

  it('includes inputMethod in AnnotationCaptureData object', () => {
    // Verify inputMethod is included in the data object literal passed to onAnnotationCapture
    expect(sourceCode).toMatch(/const\s+data\s*:\s*AnnotationCaptureData\s*=\s*\{[\s\S]*?inputMethod[\s\S]*?\}/);
  });

  it('sets speech recognition language to en-US', () => {
    expect(sourceCode).toMatch(/recognition\.lang\s*=\s*['"]en-US['"]/);
  });

  it('tracks interim transcript separately from final transcript', () => {
    expect(sourceCode).toMatch(/interimTranscriptRef/);
  });

  it('starts speech recognition only when inputMethod is speech', () => {
    expect(sourceCode).toMatch(/if\s*\(\s*inputMethod\s*===\s*['"]speech['"]\s*\)\s*\{\s*startSpeechRecognition/);
  });

  it('waits for speech recognition to end before final capture', () => {
    expect(sourceCode).toMatch(/const\s+capturedTranscript\s*=\s*inputMethod\s*===\s*['"]speech['"]\s*\?\s*await\s+stopSpeechRecognition/);
  });

  it('uses the captured transcript override when creating annotation data', () => {
    expect(sourceCode).toMatch(/const\s+textToPersist\s*=/);
    expect(sourceCode).toMatch(/capturedTranscript/);
  });
});
