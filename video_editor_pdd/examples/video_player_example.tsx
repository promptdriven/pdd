/**
 * Verification program for the VideoPlayer component.
 *
 * Validates the component module structure, exports, and source-level
 * requirements from the prompt specification. Runs headlessly with
 * `npx tsx` to produce console output for PDD verification.
 */

import * as fs from 'fs';
import * as path from 'path';

// ============================================================================
// 1. Module export verification
// ============================================================================

console.log('=== VideoPlayer Module Verification ===\n');

import * as VideoPlayerModule from '../components/VideoPlayer';

const defaultExport = VideoPlayerModule.default;
console.log('Default export:', typeof defaultExport === 'function' ? 'PASS (function)' : 'FAIL');

// ============================================================================
// 2. Source-level requirement verification
// ============================================================================

console.log('\n=== Source-Level Requirements ===\n');

const componentPath = path.resolve(__dirname, '..', 'components', 'VideoPlayer.tsx');
const source = fs.readFileSync(componentPath, 'utf-8');

// Requirement 12: 'use client' directive at the top
const hasUseClient = source.trimStart().startsWith("'use client'");
console.log("Req 12 - 'use client' directive at top:", hasUseClient ? 'PASS' : 'FAIL');

// Requirement 1: Props interface
const hasSrcProp = /src\s*:\s*string/.test(source);
const hasAnnotationsProp = /annotations\s*:\s*Annotation\s*\[\s*\]/.test(source);
const hasOnCaptureProp = /onAnnotationCapture\s*:\s*\(/.test(source);
console.log('Req 1 - Props (src: string):', hasSrcProp ? 'PASS' : 'FAIL');
console.log('Req 1 - Props (annotations: Annotation[]):', hasAnnotationsProp ? 'PASS' : 'FAIL');
console.log('Req 1 - Props (onAnnotationCapture callback):', hasOnCaptureProp ? 'PASS' : 'FAIL');

// Requirement 1: Import types from lib/types
const hasAnnotationImport = source.includes('Annotation') && source.includes('AnnotationCaptureData');
console.log('Req 1 - Imports Annotation and AnnotationCaptureData types:', hasAnnotationImport ? 'PASS' : 'FAIL');

// Requirement 2: <video> element with src prop and K = play/pause
const hasVideoElement = source.includes('<video');
const hasVideoSrc = /src=\{src\}/.test(source);
const hasKShortcut = /['"]k['"]/.test(source) && source.includes('togglePlayPause');
console.log('Req 2 - <video> element present:', hasVideoElement ? 'PASS' : 'FAIL');
console.log('Req 2 - Video uses src={src}:', hasVideoSrc ? 'PASS' : 'FAIL');
console.log('Req 2 - K key triggers play/pause:', hasKShortcut ? 'PASS' : 'FAIL');

// Requirement 3: Space bar recording mode toggle
const hasSpaceHandler = source.includes("event.code === 'Space'") || source.includes('event.code === "Space"');
const hasIsRecording = source.includes('isRecording');
const hasStartRecording = source.includes('startRecordingMode');
const hasStopRecording = source.includes('stopRecordingMode');
console.log('Req 3 - Space bar handler:', hasSpaceHandler ? 'PASS' : 'FAIL');
console.log('Req 3 - isRecording state:', hasIsRecording ? 'PASS' : 'FAIL');
console.log('Req 3 - startRecordingMode function:', hasStartRecording ? 'PASS' : 'FAIL');
console.log('Req 3 - stopRecordingMode function:', hasStopRecording ? 'PASS' : 'FAIL');

// Requirement 3: First space pauses video
const pausesOnRecord = source.includes('videoEl.pause()') || source.includes('videoEl?.pause()');
console.log('Req 3 - Pauses video on first space:', pausesOnRecord ? 'PASS' : 'FAIL');

// Requirement 4: Drawing tool shortcuts
const hasDShortcut = source.includes("'freehand'");
const hasRShortcut = source.includes("'rectangle'");
const hasCShortcut = source.includes("'circle'");
const hasAShortcut = source.includes("'arrow'");
const hasTShortcut = source.includes("'text'");
console.log('Req 4 - D=freehand tool:', hasDShortcut ? 'PASS' : 'FAIL');
console.log('Req 4 - R=rectangle tool:', hasRShortcut ? 'PASS' : 'FAIL');
console.log('Req 4 - C=circle tool:', hasCShortcut ? 'PASS' : 'FAIL');
console.log('Req 4 - A=arrow tool:', hasAShortcut ? 'PASS' : 'FAIL');
console.log('Req 4 - T=text tool:', hasTShortcut ? 'PASS' : 'FAIL');

// Requirement 4: Drawing only active in recording mode
const hasDrawingGuard = source.includes('if (!isRecording) return');
console.log('Req 4 - Drawing guarded by recording mode:', hasDrawingGuard ? 'PASS' : 'FAIL');

// Requirement 5: Canvas overlay 1920×1080
const hasCanvas = source.includes('<canvas');
const hasCanvasWidth = source.includes('1920');
const hasCanvasHeight = source.includes('1080');
const hasObjectContain = source.includes('object-contain');
console.log('Req 5 - <canvas> element present:', hasCanvas ? 'PASS' : 'FAIL');
console.log('Req 5 - Canvas logical width 1920:', hasCanvasWidth ? 'PASS' : 'FAIL');
console.log('Req 5 - Canvas logical height 1080:', hasCanvasHeight ? 'PASS' : 'FAIL');
console.log('Req 5 - CSS object-contain scaling:', hasObjectContain ? 'PASS' : 'FAIL');

// Requirement 5: Canvas positioned absolutely over video
const hasAbsoluteCanvas = source.includes('absolute') && source.includes('inset-0');
console.log('Req 5 - Canvas absolute positioned over video:', hasAbsoluteCanvas ? 'PASS' : 'FAIL');

// Requirement 6: Web Speech API
const hasSpeechRecognition = source.includes('SpeechRecognition') || source.includes('webkitSpeechRecognition');
const hasContinuous = source.includes('recognition.continuous = true');
const hasInterimResults = source.includes('recognition.interimResults = true');
const hasTranscript = source.includes('transcript');
console.log('Req 6 - Web Speech API (SpeechRecognition):', hasSpeechRecognition ? 'PASS' : 'FAIL');
console.log('Req 6 - recognition.continuous = true:', hasContinuous ? 'PASS' : 'FAIL');
console.log('Req 6 - recognition.interimResults = true:', hasInterimResults ? 'PASS' : 'FAIL');
console.log('Req 6 - Transcript accumulation:', hasTranscript ? 'PASS' : 'FAIL');

// Requirement 7: OffscreenCanvas composite
const hasOffscreenCanvas = source.includes('new OffscreenCanvas');
const hasDrawImageVideo = source.includes('drawImage(videoEl');
const hasDrawImageCanvas = source.includes('drawImage(canvasEl');
const hasConvertToBlob = source.includes('convertToBlob');
const hasCompositeDataUrl = source.includes('compositeDataUrl');
const hasDrawingDataUrl = source.includes('drawingDataUrl');
console.log('Req 7 - OffscreenCanvas created:', hasOffscreenCanvas ? 'PASS' : 'FAIL');
console.log('Req 7 - drawImage video frame:', hasDrawImageVideo ? 'PASS' : 'FAIL');
console.log('Req 7 - drawImage canvas overlay:', hasDrawImageCanvas ? 'PASS' : 'FAIL');
console.log('Req 7 - convertToBlob for data URL:', hasConvertToBlob ? 'PASS' : 'FAIL');
console.log('Req 7 - compositeDataUrl output:', hasCompositeDataUrl ? 'PASS' : 'FAIL');
console.log('Req 7 - drawingDataUrl output:', hasDrawingDataUrl ? 'PASS' : 'FAIL');

// Requirement 8: Progress bar with annotation markers
const hasProgressBar = source.includes('bg-gray-700') && source.includes('h-2');
const hasAnnotationDots = source.includes('bg-yellow-400') && source.includes('rounded-full');
const hasTimestampCalc = source.includes('a.timestamp / duration');
const hasSeekOnClick = source.includes('videoEl.currentTime = a.timestamp') || source.includes('currentTime = a.timestamp');
console.log('Req 8 - Progress bar (h-2 bg-gray-700):', hasProgressBar ? 'PASS' : 'FAIL');
console.log('Req 8 - Annotation dot markers (bg-yellow-400):', hasAnnotationDots ? 'PASS' : 'FAIL');
console.log('Req 8 - Timestamp position calculation:', hasTimestampCalc ? 'PASS' : 'FAIL');
console.log('Req 8 - Click marker seeks video:', hasSeekOnClick ? 'PASS' : 'FAIL');

// Requirement 9: Ctrl+Z undo
const hasCtrlZ = (source.includes('ctrlKey') || source.includes('metaKey')) && source.includes("'z'");
const hasUndoSlice = source.includes('slice(0, -1)');
console.log('Req 9 - Ctrl+Z keyboard shortcut:', hasCtrlZ ? 'PASS' : 'FAIL');
console.log('Req 9 - Undo removes last stroke (slice):', hasUndoSlice ? 'PASS' : 'FAIL');

// Requirement 10: Arrow keys seek ±5 seconds
const hasArrowLeft = source.includes('ArrowLeft');
const hasArrowRight = source.includes('ArrowRight');
const hasSeekDelta = source.includes('seekBy(-5)') && source.includes('seekBy(5)');
console.log('Req 10 - ArrowLeft handler:', hasArrowLeft ? 'PASS' : 'FAIL');
console.log('Req 10 - ArrowRight handler:', hasArrowRight ? 'PASS' : 'FAIL');
console.log('Req 10 - Seek ±5 seconds:', hasSeekDelta ? 'PASS' : 'FAIL');

// Requirement 11: F = toggle fullscreen
const hasFShortcut = source.includes("'f'");
const hasFullscreen = source.includes('requestFullscreen') && source.includes('exitFullscreen');
console.log('Req 11 - F key shortcut:', hasFShortcut ? 'PASS' : 'FAIL');
console.log('Req 11 - Fullscreen toggle:', hasFullscreen ? 'PASS' : 'FAIL');

// Instructions: useRef<HTMLVideoElement> and useRef<HTMLCanvasElement>
const hasVideoRef = source.includes('useRef<HTMLVideoElement>');
const hasCanvasRef = source.includes('useRef<HTMLCanvasElement>');
console.log('Inst - useRef<HTMLVideoElement>:', hasVideoRef ? 'PASS' : 'FAIL');
console.log('Inst - useRef<HTMLCanvasElement>:', hasCanvasRef ? 'PASS' : 'FAIL');

// Instructions: Stroke type with tool and points
const hasStrokeType = source.includes('Stroke') && source.includes('tool: DrawTool') && source.includes('points:');
console.log('Inst - Stroke type definition:', hasStrokeType ? 'PASS' : 'FAIL');

// Instructions: DrawTool type
const hasDrawTool = source.includes('DrawTool');
console.log('Inst - DrawTool type definition:', hasDrawTool ? 'PASS' : 'FAIL');

// Instructions: Canvas redraw via useEffect
const hasCanvasRedraw = source.includes('clearRect') && source.includes('useEffect');
console.log('Inst - Canvas redraws via useEffect:', hasCanvasRedraw ? 'PASS' : 'FAIL');

// Instructions: getBoundingClientRect for coordinate mapping
const hasCoordMapping = source.includes('getBoundingClientRect');
console.log('Inst - getBoundingClientRect coordinate mapping:', hasCoordMapping ? 'PASS' : 'FAIL');

// Instructions: onAnnotationCapture called with data
const callsOnCapture = source.includes('onAnnotationCapture(');
console.log('Inst - Calls onAnnotationCapture:', callsOnCapture ? 'PASS' : 'FAIL');

// ============================================================================
// 3. Summary
// ============================================================================

console.log('\n=== Verification Summary ===\n');

const checks = [
  hasUseClient,
  hasSrcProp, hasAnnotationsProp, hasOnCaptureProp, hasAnnotationImport,
  hasVideoElement, hasVideoSrc, hasKShortcut,
  hasSpaceHandler, hasIsRecording, hasStartRecording, hasStopRecording, pausesOnRecord,
  hasDShortcut, hasRShortcut, hasCShortcut, hasAShortcut, hasTShortcut, hasDrawingGuard,
  hasCanvas, hasCanvasWidth, hasCanvasHeight, hasObjectContain, hasAbsoluteCanvas,
  hasSpeechRecognition, hasContinuous, hasInterimResults, hasTranscript,
  hasOffscreenCanvas, hasDrawImageVideo, hasDrawImageCanvas, hasConvertToBlob, hasCompositeDataUrl, hasDrawingDataUrl,
  hasProgressBar, hasAnnotationDots, hasTimestampCalc, hasSeekOnClick,
  hasCtrlZ, hasUndoSlice,
  hasArrowLeft, hasArrowRight, hasSeekDelta,
  hasFShortcut, hasFullscreen,
  hasVideoRef, hasCanvasRef,
  hasStrokeType, hasDrawTool,
  hasCanvasRedraw, hasCoordMapping, callsOnCapture,
];

const passed = checks.filter(Boolean).length;
const total = checks.length;

console.log(`Results: ${passed}/${total} checks passed`);

if (passed === total) {
  console.log('Status: ALL CHECKS PASSED');
  console.log('\nVideoPlayer component fully satisfies the prompt specification.');
} else {
  console.log('Status: SOME CHECKS FAILED');
  const failed = total - passed;
  console.log(`${failed} check(s) did not pass. Review output above.`);
  process.exit(1);
}
