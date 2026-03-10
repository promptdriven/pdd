/**
 * Tests for components/VideoPlayer.tsx
 *
 * PDD Principle: The prompt file is the source of truth.
 * These tests verify that the code conforms to the specification in
 * prompts/video_player_typescriptreact.prompt.
 *
 * Spec requirements verified:
 *   1. Props: src: string, annotations: Annotation[], onAnnotationCapture: (data: AnnotationCaptureData) => void
 *   2. <video> element with src prop. Keyboard shortcut K = play/pause.
 *   3. Space bar: first press pauses and enters recording mode. Second press: captures + emits + exits.
 *   4. Drawing tools (D=freehand, R=rectangle, C=circle, A=arrow, T=text) active only in recording mode.
 *   5. Canvas overlay (1920x1080 logical, CSS-scaled).
 *   6. Web Speech API: start on first space, accumulate transcript, stop on second space.
 *   7. On capture: OffscreenCanvas composite + drawing-only data URL.
 *   8. Progress bar: annotation dot markers, click to seek.
 *   9. Ctrl+Z: undo last stroke.
 *  10. Arrow keys: seek ±5 seconds.
 *  11. F: toggle fullscreen.
 *  12. 'use client' directive.
 */

import fs from "fs";
import path from "path";

// ---------------------------------------------------------------------------
// Source code (loaded once for structural tests)
// ---------------------------------------------------------------------------

const SOURCE_PATH = path.join(__dirname, "..", "components", "VideoPlayer.tsx");
const sourceCode = fs.readFileSync(SOURCE_PATH, "utf-8");

// ---------------------------------------------------------------------------
// 1. 'use client' directive
// ---------------------------------------------------------------------------

describe("'use client' directive", () => {
  it("has 'use client' as the very first line", () => {
    const firstLine = sourceCode.split("\n")[0].trim();
    expect(firstLine).toBe("'use client';");
  });
});

// ---------------------------------------------------------------------------
// 2. Module structure
// ---------------------------------------------------------------------------

describe("module structure", () => {
  it("file exists at expected path", () => {
    expect(fs.existsSync(SOURCE_PATH)).toBe(true);
  });

  it("is a TypeScript React file", () => {
    expect(SOURCE_PATH).toMatch(/\.tsx$/);
  });

  it("exports VideoPlayer as default export", () => {
    expect(sourceCode).toMatch(/export\s+default\s+function\s+VideoPlayer/);
  });
});

// ---------------------------------------------------------------------------
// 3. Props interface
// ---------------------------------------------------------------------------

describe("VideoPlayer props", () => {
  it("declares src: string prop", () => {
    expect(sourceCode).toMatch(/src\s*:\s*string/);
  });

  it("declares annotations: Annotation[] prop", () => {
    expect(sourceCode).toMatch(/annotations\s*:\s*Annotation\[\]/);
  });

  it("declares onAnnotationCapture callback prop", () => {
    expect(sourceCode).toMatch(/onAnnotationCapture\s*:\s*\(data\s*:\s*AnnotationCaptureData\)\s*=>\s*void/);
  });

  it("declares optional onTimeChange callback prop", () => {
    expect(sourceCode).toMatch(/onTimeChange\?\s*:\s*\(seconds\s*:\s*number\)\s*=>\s*void/);
  });
});

// ---------------------------------------------------------------------------
// 4. Import structure
// ---------------------------------------------------------------------------

describe("import structure", () => {
  it("imports React hooks from react", () => {
    expect(sourceCode).toMatch(/import\s+React\s*,\s*\{.*useRef.*\}\s*from\s+['"]react['"]/);
  });

  it("imports Annotation and AnnotationCaptureData types", () => {
    expect(sourceCode).toMatch(/import\s+type\s*\{.*Annotation.*AnnotationCaptureData.*\}/);
  });

  it("imports types from ../lib/types", () => {
    expect(sourceCode).toMatch(/from\s+['"]\.\.\/lib\/types['"]/);
  });
});

// ---------------------------------------------------------------------------
// 5. Refs — useRef<HTMLVideoElement> and useRef<HTMLCanvasElement>
// ---------------------------------------------------------------------------

describe("DOM refs", () => {
  it("uses useRef<HTMLVideoElement> for video ref", () => {
    expect(sourceCode).toMatch(/useRef\s*<\s*HTMLVideoElement\s*>/);
  });

  it("uses useRef<HTMLCanvasElement> for canvas ref", () => {
    expect(sourceCode).toMatch(/useRef\s*<\s*HTMLCanvasElement\s*>/);
  });
});

// ---------------------------------------------------------------------------
// 6. Video element
// ---------------------------------------------------------------------------

describe("video element", () => {
  it("renders a <video> element", () => {
    expect(sourceCode).toMatch(/<video/);
  });

  it("passes src prop to video element", () => {
    expect(sourceCode).toMatch(/src=\{src\}/);
  });

  it("disables native controls", () => {
    expect(sourceCode).toMatch(/controls=\{false\}/);
  });
});

// ---------------------------------------------------------------------------
// 7. Canvas overlay — 1920x1080 logical dimensions
// ---------------------------------------------------------------------------

describe("canvas overlay", () => {
  it("renders a <canvas> element", () => {
    expect(sourceCode).toMatch(/<canvas/);
  });

  it("defines CANVAS_WIDTH as 1920", () => {
    expect(sourceCode).toMatch(/CANVAS_WIDTH\s*=\s*1920/);
  });

  it("defines CANVAS_HEIGHT as 1080", () => {
    expect(sourceCode).toMatch(/CANVAS_HEIGHT\s*=\s*1080/);
  });

  it("sets canvas width to CANVAS_WIDTH", () => {
    expect(sourceCode).toMatch(/width=\{CANVAS_WIDTH\}/);
  });

  it("sets canvas height to CANVAS_HEIGHT", () => {
    expect(sourceCode).toMatch(/height=\{CANVAS_HEIGHT\}/);
  });

  it("positions canvas absolutely over the video", () => {
    expect(sourceCode).toMatch(/absolute/);
    expect(sourceCode).toMatch(/inset-0/);
  });

  it("uses object-contain on canvas for CSS scaling", () => {
    expect(sourceCode).toMatch(/object-contain/);
  });

  it("disables pointer events when not recording", () => {
    expect(sourceCode).toMatch(/pointerEvents\s*:\s*isRecording\s*\?\s*['"]auto['"]\s*:\s*['"]none['"]/);
  });
});

// ---------------------------------------------------------------------------
// 8. Drawing tools (DrawTool type)
// ---------------------------------------------------------------------------

describe("DrawTool type", () => {
  it("defines DrawTool as a union of freehand, rectangle, circle, arrow, text", () => {
    expect(sourceCode).toMatch(/type\s+DrawTool\s*=/);
    expect(sourceCode).toMatch(/'freehand'/);
    expect(sourceCode).toMatch(/'rectangle'/);
    expect(sourceCode).toMatch(/'circle'/);
    expect(sourceCode).toMatch(/'arrow'/);
    expect(sourceCode).toMatch(/'text'/);
  });
});

// ---------------------------------------------------------------------------
// 9. Stroke type
// ---------------------------------------------------------------------------

describe("Stroke type", () => {
  it("defines Stroke type with tool: DrawTool", () => {
    expect(sourceCode).toMatch(/tool\s*:\s*DrawTool/);
  });

  it("defines Stroke type with points: [number, number][]", () => {
    expect(sourceCode).toMatch(/points\s*:\s*\[number\s*,\s*number\]\[\]/);
  });

  it("defines optional text field on Stroke", () => {
    expect(sourceCode).toMatch(/text\?\s*:\s*string/);
  });
});

// ---------------------------------------------------------------------------
// 10. Stroke state management — useState<Stroke[]>
// ---------------------------------------------------------------------------

describe("stroke state management", () => {
  it("uses useState<Stroke[]> for strokes", () => {
    expect(sourceCode).toMatch(/useState\s*<\s*Stroke\[\]\s*>/);
  });

  it("tracks currentStroke state", () => {
    expect(sourceCode).toMatch(/useState\s*<\s*Stroke\s*\|\s*null\s*>/);
  });
});

// ---------------------------------------------------------------------------
// 11. Canvas redraws on stroke changes via useEffect
// ---------------------------------------------------------------------------

describe("canvas redraw", () => {
  it("clears canvas on each redraw", () => {
    expect(sourceCode).toMatch(/clearRect\s*\(\s*0\s*,\s*0\s*,\s*canvas\.width\s*,\s*canvas\.height\s*\)/);
  });

  it("draws all strokes including currentStroke", () => {
    expect(sourceCode).toMatch(/currentStroke\s*\?\s*\[\s*\.\.\.strokes\s*,\s*currentStroke\s*\]\s*:\s*strokes/);
  });

  it("has drawStroke function that handles freehand tool", () => {
    expect(sourceCode).toMatch(/stroke\.tool\s*===\s*'freehand'/);
  });

  it("has drawStroke function that handles rectangle tool", () => {
    expect(sourceCode).toMatch(/stroke\.tool\s*===\s*'rectangle'/);
  });

  it("has drawStroke function that handles circle tool", () => {
    expect(sourceCode).toMatch(/stroke\.tool\s*===\s*'circle'/);
  });

  it("has drawStroke function that handles arrow tool", () => {
    expect(sourceCode).toMatch(/stroke\.tool\s*===\s*'arrow'/);
  });

  it("has drawStroke function that handles text tool", () => {
    expect(sourceCode).toMatch(/stroke\.tool\s*===\s*'text'/);
  });
});

// ---------------------------------------------------------------------------
// 12. Coordinate mapping — getBoundingClientRect
// ---------------------------------------------------------------------------

describe("coordinate mapping", () => {
  it("uses getBoundingClientRect for mouse-to-canvas mapping", () => {
    expect(sourceCode).toMatch(/getBoundingClientRect\s*\(\s*\)/);
  });

  it("maps clientX to canvas logical coordinates using CANVAS_WIDTH", () => {
    expect(sourceCode).toMatch(/CANVAS_WIDTH/);
  });

  it("maps clientY to canvas logical coordinates using CANVAS_HEIGHT", () => {
    expect(sourceCode).toMatch(/CANVAS_HEIGHT/);
  });

  it("clamps coordinates to canvas bounds", () => {
    expect(sourceCode).toMatch(/clamp/);
  });
});

// ---------------------------------------------------------------------------
// 13. Keyboard shortcuts — drawing tool selection
// ---------------------------------------------------------------------------

describe("keyboard shortcuts — drawing tools", () => {
  it("D selects freehand tool", () => {
    expect(sourceCode).toMatch(/['"]d['"]\)\s*setSelectedTool\s*\(\s*['"]freehand['"]\s*\)/);
  });

  it("R selects rectangle tool", () => {
    expect(sourceCode).toMatch(/['"]r['"]\)\s*setSelectedTool\s*\(\s*['"]rectangle['"]\s*\)/);
  });

  it("C selects circle tool", () => {
    expect(sourceCode).toMatch(/['"]c['"]\)\s*setSelectedTool\s*\(\s*['"]circle['"]\s*\)/);
  });

  it("A selects arrow tool", () => {
    expect(sourceCode).toMatch(/['"]a['"]\)\s*setSelectedTool\s*\(\s*['"]arrow['"]\s*\)/);
  });

  it("T selects text tool", () => {
    expect(sourceCode).toMatch(/['"]t['"]\)\s*setSelectedTool\s*\(\s*['"]text['"]\s*\)/);
  });
});

// ---------------------------------------------------------------------------
// 14. Keyboard shortcut — K = play/pause
// ---------------------------------------------------------------------------

describe("keyboard shortcut — K play/pause", () => {
  it("listens for K key to toggle play/pause", () => {
    expect(sourceCode).toMatch(/['"]k['"]\)\s*\{?\s*\n?\s*togglePlayPause/);
  });

  it("togglePlayPause calls videoEl.play() and videoEl.pause()", () => {
    expect(sourceCode).toMatch(/videoEl\.paused/);
    expect(sourceCode).toMatch(/videoEl\.play\s*\(\s*\)/);
    expect(sourceCode).toMatch(/videoEl\.pause\s*\(\s*\)/);
  });
});

// ---------------------------------------------------------------------------
// 15. Keyboard shortcut — Space = annotation workflow
// ---------------------------------------------------------------------------

describe("keyboard shortcut — Space annotation workflow", () => {
  it("listens for Space key using event.code", () => {
    expect(sourceCode).toMatch(/event\.code\s*===\s*['"]Space['"]/);
  });

  it("prevents default on space press", () => {
    expect(sourceCode).toMatch(/event\.preventDefault\s*\(\s*\)/);
  });

  it("first space press enters recording mode when not recording", () => {
    expect(sourceCode).toMatch(/if\s*\(\s*!isRecording\s*\)\s*\{?\s*\n?\s*startRecordingMode\s*\(\s*\)/);
  });

  it("second space press stops recording mode when recording", () => {
    expect(sourceCode).toMatch(/\}\s*else\s*\{?\s*\n?\s*stopRecordingMode\s*\(\s*\)/);
  });

  it("startRecordingMode pauses video", () => {
    expect(sourceCode).toMatch(/const\s+startRecordingMode\s*=\s*useCallback\s*\(\s*\(\)\s*=>\s*\{[\s\S]*?videoEl\)?\s*videoEl\.pause\(\)/);
  });
});

// ---------------------------------------------------------------------------
// 16. Keyboard shortcut — Arrow keys seek ±5 seconds
// ---------------------------------------------------------------------------

describe("keyboard shortcuts — arrow keys", () => {
  it("ArrowLeft seeks -5 seconds", () => {
    expect(sourceCode).toMatch(/['"]ArrowLeft['"]\)\s*seekBy\s*\(\s*-5\s*\)/);
  });

  it("ArrowRight seeks +5 seconds", () => {
    expect(sourceCode).toMatch(/['"]ArrowRight['"]\)\s*seekBy\s*\(\s*5\s*\)/);
  });

  it("seekBy modifies videoEl.currentTime", () => {
    expect(sourceCode).toMatch(/videoEl\.currentTime\s*=\s*clamp/);
  });
});

// ---------------------------------------------------------------------------
// 17. Keyboard shortcut — F = fullscreen
// ---------------------------------------------------------------------------

describe("keyboard shortcut — F fullscreen", () => {
  it("F key calls toggleFullscreen", () => {
    expect(sourceCode).toMatch(/['"]f['"]\)\s*toggleFullscreen\s*\(\s*\)/);
  });

  it("toggleFullscreen uses requestFullscreen", () => {
    expect(sourceCode).toMatch(/requestFullscreen\s*\(\s*\)/);
  });

  it("toggleFullscreen uses exitFullscreen", () => {
    expect(sourceCode).toMatch(/exitFullscreen\s*\(\s*\)/);
  });

  it("checks document.fullscreenElement", () => {
    expect(sourceCode).toMatch(/document\.fullscreenElement/);
  });
});

// ---------------------------------------------------------------------------
// 18. Keyboard shortcut — Ctrl+Z undo last stroke
// ---------------------------------------------------------------------------

describe("keyboard shortcut — Ctrl+Z undo", () => {
  it("checks for ctrlKey or metaKey with Z", () => {
    expect(sourceCode).toMatch(/event\.ctrlKey\s*\|\|\s*event\.metaKey/);
    expect(sourceCode).toMatch(/['"]z['"]/);
  });

  it("only undoes when in recording mode", () => {
    expect(sourceCode).toMatch(/if\s*\(\s*isRecording\s*\)\s*\{/);
  });

  it("removes last stroke using slice(0, -1)", () => {
    expect(sourceCode).toMatch(/setStrokes\s*\(\s*\(prev\)\s*=>\s*prev\.slice\s*\(\s*0\s*,\s*-1\s*\)\s*\)/);
  });
});

// ---------------------------------------------------------------------------
// 19. Keyboard shortcuts skip input/textarea
// ---------------------------------------------------------------------------

describe("keyboard shortcut input exclusion", () => {
  it("ignores keyboard events when target is input", () => {
    expect(sourceCode).toMatch(/tagName\s*===\s*['"]input['"]/);
  });

  it("ignores keyboard events when target is textarea", () => {
    expect(sourceCode).toMatch(/tagName\s*===\s*['"]textarea['"]/);
  });
});

// ---------------------------------------------------------------------------
// 19b. Keyboard shortcut guard — contenteditable
// ---------------------------------------------------------------------------

describe("Keyboard shortcut guard", () => {
  it("checks for contenteditable elements in keyboard handler", () => {
    expect(sourceCode).toMatch(/isContentEditable/);
  });

  it("prevents shortcuts from firing in input, textarea, and contenteditable", () => {
    expect(sourceCode).toMatch(/tagName === 'input'/);
    expect(sourceCode).toMatch(/tagName === 'textarea'/);
    expect(sourceCode).toMatch(/isContentEditable/);
  });
});

// ---------------------------------------------------------------------------
// 20. Web Speech API
// ---------------------------------------------------------------------------

describe("Web Speech API", () => {
  it("accesses window.SpeechRecognition with webkit fallback", () => {
    expect(sourceCode).toMatch(/window.*SpeechRecognition/);
    expect(sourceCode).toMatch(/window.*webkitSpeechRecognition/);
  });

  it("sets recognition.continuous = true", () => {
    expect(sourceCode).toMatch(/recognition\.continuous\s*=\s*true/);
  });

  it("sets recognition.interimResults = true", () => {
    expect(sourceCode).toMatch(/recognition\.interimResults\s*=\s*true/);
  });

  it("handles onresult events to accumulate transcript", () => {
    expect(sourceCode).toMatch(/recognition\.onresult/);
  });

  it("distinguishes final and interim results", () => {
    expect(sourceCode).toMatch(/result\.isFinal/);
  });

  it("starts recognition on first space press", () => {
    expect(sourceCode).toMatch(/startSpeechRecognition/);
    expect(sourceCode).toMatch(/recognitionRef\.current\.start\s*\(\s*\)/);
  });

  it("stops recognition on second space press", () => {
    expect(sourceCode).toMatch(/stopSpeechRecognition/);
    expect(sourceCode).toMatch(/recognitionRef\.current\.stop\s*\(\s*\)/);
  });
});

// ---------------------------------------------------------------------------
// 21. Frame capture — OffscreenCanvas composite
// ---------------------------------------------------------------------------

describe("OffscreenCanvas composite capture", () => {
  it("creates OffscreenCanvas with 1920x1080 dimensions", () => {
    expect(sourceCode).toMatch(/new\s+OffscreenCanvas\s*\(\s*CANVAS_WIDTH\s*,\s*CANVAS_HEIGHT\s*\)/);
  });

  it("draws video frame onto offscreen canvas", () => {
    expect(sourceCode).toMatch(/ctx\.drawImage\s*\(\s*videoEl/);
  });

  it("draws drawing canvas onto offscreen canvas", () => {
    expect(sourceCode).toMatch(/ctx\.drawImage\s*\(\s*canvasEl/);
  });

  it("converts blob to data URL using convertToBlob", () => {
    expect(sourceCode).toMatch(/convertToBlob/);
  });

  it("produces compositeDataUrl", () => {
    expect(sourceCode).toMatch(/compositeDataUrl/);
  });

  it("produces drawingDataUrl from canvas toDataURL", () => {
    expect(sourceCode).toMatch(/canvasEl\.toDataURL/);
    expect(sourceCode).toMatch(/drawingDataUrl/);
  });
});

// ---------------------------------------------------------------------------
// 22. onAnnotationCapture emission
// ---------------------------------------------------------------------------

describe("onAnnotationCapture emission", () => {
  it("calls onAnnotationCapture with AnnotationCaptureData", () => {
    expect(sourceCode).toMatch(/onAnnotationCapture\s*\(\s*data\s*\)/);
  });

  it("AnnotationCaptureData includes timestamp from videoEl.currentTime", () => {
    expect(sourceCode).toMatch(/timestamp\s*:\s*videoEl\.currentTime/);
  });

  it("AnnotationCaptureData includes transcript text", () => {
    expect(sourceCode).toMatch(/text\s*:\s*transcript\.trim\(\)/);
  });

  it("AnnotationCaptureData includes drawingDataUrl", () => {
    expect(sourceCode).toMatch(/drawingDataUrl\s*:\s*drawingDataUrl/);
  });

  it("AnnotationCaptureData includes compositeDataUrl", () => {
    expect(sourceCode).toMatch(/compositeDataUrl\s*:\s*compositeDataUrl/);
  });

  it("AnnotationCaptureData includes videoFile from src prop", () => {
    expect(sourceCode).toMatch(/videoFile\s*:\s*src/);
  });

  it("clears strokes after capture", () => {
    // handleCapture resets strokes
    expect(sourceCode).toMatch(/setStrokes\s*\(\s*\[\s*\]\s*\)/);
  });
});

// ---------------------------------------------------------------------------
// 23. Progress bar — annotation markers
// ---------------------------------------------------------------------------

describe("progress bar", () => {
  it("renders a progress bar container with bg-gray-700", () => {
    expect(sourceCode).toMatch(/relative\s+h-2\s+bg-gray-700/);
  });

  it("keeps a ref to the progress bar for mouse seek math", () => {
    expect(sourceCode).toMatch(/progressBarRef\s*=\s*useRef\s*<\s*HTMLDivElement\s*>\s*\(\s*null\s*\)/);
  });

  it("renders progress fill with bg-blue-500", () => {
    expect(sourceCode).toMatch(/bg-blue-500/);
  });

  it("maps annotations to dot markers", () => {
    expect(sourceCode).toMatch(/annotations\.map/);
  });

  it("positions dots using percentage of timestamp/duration", () => {
    expect(sourceCode).toMatch(/a\.timestamp\s*\/\s*duration/);
  });

  it("dots use bg-yellow-400 styling", () => {
    expect(sourceCode).toMatch(/bg-yellow-400/);
  });

  it("dots use rounded-full class", () => {
    expect(sourceCode).toMatch(/rounded-full/);
  });

  it("clicking a marker seeks video to that timestamp", () => {
    expect(sourceCode).toMatch(/videoEl\.currentTime\s*=\s*a\.timestamp/);
  });

  it("clicking or dragging the bar seeks using clientX and bar width", () => {
    expect(sourceCode).toMatch(/seekToClientX/);
    expect(sourceCode).toMatch(/getBoundingClientRect\s*\(\s*\)/);
    expect(sourceCode).toMatch(/clientX/);
    expect(sourceCode).toMatch(/percent\s*=\s*clamp\(\(clientX\s*-\s*rect\.left\)\s*\/\s*rect\.width/);
  });

  it("binds pointer handlers to the progress bar container", () => {
    expect(sourceCode).toMatch(/onPointerDown=\{handleProgressPointerDown\}/);
    expect(sourceCode).toMatch(/onPointerMove=\{handleProgressPointerMove\}/);
    expect(sourceCode).toMatch(/onPointerUp=\{handleProgressPointerUp\}/);
  });

  it("updates currentTime state immediately after seeking with the mouse", () => {
    expect(sourceCode).toMatch(/setCurrentTime\(nextTime\)/);
  });

  it("notifies onTimeChange immediately after seeking with the mouse", () => {
    expect(sourceCode).toMatch(/onTimeChange\?\.\(\s*nextTime\s*\)/);
  });

  it("provides aria-label for annotation markers", () => {
    expect(sourceCode).toMatch(/aria-label/);
  });
});

// ---------------------------------------------------------------------------
// 24. Recording mode state
// ---------------------------------------------------------------------------

describe("recording mode state", () => {
  it("tracks isRecording state", () => {
    expect(sourceCode).toMatch(/useState\s*<?\s*\(?\s*false\s*\)?/);
    expect(sourceCode).toMatch(/isRecording/);
  });

  it("displays Recording text when in recording mode", () => {
    expect(sourceCode).toMatch(/isRecording\s*\?\s*['"]Recording['"]\s*:\s*['"]Review['"]/);
  });

  it("shows red pulse indicator when recording", () => {
    expect(sourceCode).toMatch(/bg-red-500\s+animate-pulse/);
  });

  it("displays transcript when recording", () => {
    expect(sourceCode).toMatch(/Transcript/);
  });
});

// ---------------------------------------------------------------------------
// 25. Drawing tool buttons
// ---------------------------------------------------------------------------

describe("drawing tool buttons", () => {
  it("renders all five tool buttons", () => {
    expect(sourceCode).toMatch(/\['freehand'\s*,\s*'rectangle'\s*,\s*'circle'\s*,\s*'arrow'\s*,\s*'text'\]/);
  });

  it("highlights selected tool with bg-blue-600", () => {
    expect(sourceCode).toMatch(/bg-blue-600/);
  });

  it("non-selected tools use bg-gray-800", () => {
    expect(sourceCode).toMatch(/bg-gray-800/);
  });
});

// ---------------------------------------------------------------------------
// 26. Time display — formatTime helper
// ---------------------------------------------------------------------------

describe("formatTime helper", () => {
  it("defines formatTime function", () => {
    expect(sourceCode).toMatch(/const\s+formatTime\s*=/);
  });

  it("handles non-finite values", () => {
    expect(sourceCode).toMatch(/Number\.isFinite/);
  });

  it("formats minutes and seconds", () => {
    expect(sourceCode).toMatch(/Math\.floor\s*\(\s*seconds\s*\/\s*60\s*\)/);
    expect(sourceCode).toMatch(/Math\.floor\s*\(\s*seconds\s*%\s*60\s*\)/);
  });

  it("pads seconds to 2 digits", () => {
    expect(sourceCode).toMatch(/padStart\s*\(\s*2\s*,\s*['"]0['"]\s*\)/);
  });
});

// ---------------------------------------------------------------------------
// 27. Video time sync
// ---------------------------------------------------------------------------

describe("video time sync", () => {
  it("listens for loadedmetadata event", () => {
    expect(sourceCode).toMatch(/['"]loadedmetadata['"]/);
  });

  it("listens for timeupdate event", () => {
    expect(sourceCode).toMatch(/['"]timeupdate['"]/);
  });

  it("sets duration from video", () => {
    expect(sourceCode).toMatch(/setDuration\s*\(\s*videoEl\.duration\s*\)/);
  });

  it("sets currentTime from video", () => {
    expect(sourceCode).toMatch(/setCurrentTime\s*\(\s*videoEl\.currentTime\s*\)/);
  });

  it("notifies onTimeChange when the video time updates", () => {
    expect(sourceCode).toMatch(/onTimeChange\?\.\(\s*videoEl\.currentTime\s*\)/);
  });

  it("cleans up event listeners on unmount", () => {
    expect(sourceCode).toMatch(/removeEventListener\s*\(\s*['"]loadedmetadata['"]/);
    expect(sourceCode).toMatch(/removeEventListener\s*\(\s*['"]timeupdate['"]/);
  });
});

// ---------------------------------------------------------------------------
// 28. Progress percent calculation
// ---------------------------------------------------------------------------

describe("progress percentage", () => {
  it("computes progressPercent using useMemo", () => {
    expect(sourceCode).toMatch(/useMemo\s*\(\s*\(\)\s*=>\s*\{/);
  });

  it("returns 0 when duration is 0", () => {
    expect(sourceCode).toMatch(/if\s*\(\s*!duration\s*\)\s*return\s*0/);
  });

  it("calculates currentTime / duration * 100", () => {
    expect(sourceCode).toMatch(/currentTime\s*\/\s*duration\s*\)\s*\*\s*100/);
  });
});

// ---------------------------------------------------------------------------
// 29. Pointer event handlers
// ---------------------------------------------------------------------------

describe("pointer event handlers", () => {
  it("has onPointerDown handler", () => {
    expect(sourceCode).toMatch(/onPointerDown=\{handlePointerDown\}/);
  });

  it("has onPointerMove handler", () => {
    expect(sourceCode).toMatch(/onPointerMove=\{handlePointerMove\}/);
  });

  it("has onPointerUp handler", () => {
    expect(sourceCode).toMatch(/onPointerUp=\{handlePointerUp\}/);
  });

  it("has onPointerLeave handler", () => {
    expect(sourceCode).toMatch(/onPointerLeave=\{handlePointerUp\}/);
  });

  it("handlePointerDown returns early when not recording", () => {
    expect(sourceCode).toMatch(/if\s*\(\s*!isRecording\s*\)\s*return/);
  });

  it("text tool uses window.prompt for text input", () => {
    expect(sourceCode).toMatch(/window\.prompt\s*\(/);
  });

  it("freehand tool appends points on move", () => {
    expect(sourceCode).toMatch(/currentStroke\.tool\s*===\s*'freehand'/);
  });

  it("non-freehand tools update second point on move", () => {
    expect(sourceCode).toMatch(/\[\s*prev\.points\[\s*0\s*\]\s*,\s*point\s*\]/);
  });
});

// ---------------------------------------------------------------------------
// 30. Container and layout
// ---------------------------------------------------------------------------

describe("container and layout", () => {
  it("uses a container ref for fullscreen", () => {
    expect(sourceCode).toMatch(/ref=\{containerRef\}/);
  });

  it("video container has aspect-video class", () => {
    expect(sourceCode).toMatch(/aspect-video/);
  });

  it("video container has bg-black background", () => {
    expect(sourceCode).toMatch(/bg-black/);
  });

  it("displays current tool name in uppercase", () => {
    expect(sourceCode).toMatch(/selectedTool\.toUpperCase\s*\(\s*\)/);
  });
});

// ---------------------------------------------------------------------------
// 31. Play/Pause button
// ---------------------------------------------------------------------------

describe("play/pause button", () => {
  it("renders a Play/Pause button with K shortcut hint", () => {
    expect(sourceCode).toMatch(/Play\/Pause\s*\(K\)/);
  });

  it("button onClick calls togglePlayPause", () => {
    expect(sourceCode).toMatch(/onClick=\{togglePlayPause\}/);
  });
});

// ---------------------------------------------------------------------------
// 32. Keyboard event listener lifecycle
// ---------------------------------------------------------------------------

describe("keyboard event listener lifecycle", () => {
  it("adds keydown listener on window", () => {
    expect(sourceCode).toMatch(/window\.addEventListener\s*\(\s*['"]keydown['"]/);
  });

  it("removes keydown listener on cleanup", () => {
    expect(sourceCode).toMatch(/window\.removeEventListener\s*\(\s*['"]keydown['"]/);
  });
});

// ---------------------------------------------------------------------------
// 33. Drawing style constants
// ---------------------------------------------------------------------------

describe("drawing style", () => {
  it("sets lineWidth to 4", () => {
    expect(sourceCode).toMatch(/ctx\.lineWidth\s*=\s*4/);
  });

  it("uses orange stroke style #f97316", () => {
    expect(sourceCode).toMatch(/#f97316/);
  });

  it("uses round lineCap", () => {
    expect(sourceCode).toMatch(/ctx\.lineCap\s*=\s*['"]round['"]/);
  });

  it("uses 36px sans-serif font for text tool", () => {
    expect(sourceCode).toMatch(/['"]36px sans-serif['"]/);
  });
});

// ---------------------------------------------------------------------------
// 34. Arrow drawing specifics
// ---------------------------------------------------------------------------

describe("arrow drawing", () => {
  it("calculates arrow angle using Math.atan2", () => {
    expect(sourceCode).toMatch(/Math\.atan2/);
  });

  it("draws arrowhead with Math.cos and Math.sin", () => {
    expect(sourceCode).toMatch(/Math\.cos/);
    expect(sourceCode).toMatch(/Math\.sin/);
  });
});

// ---------------------------------------------------------------------------
// 35. Circle drawing specifics
// ---------------------------------------------------------------------------

describe("circle drawing", () => {
  it("calculates radius using Math.hypot", () => {
    expect(sourceCode).toMatch(/Math\.hypot/);
  });

  it("draws arc for circle", () => {
    expect(sourceCode).toMatch(/ctx\.arc\s*\(/);
  });
});

// ---------------------------------------------------------------------------
// 36. Rectangle drawing specifics
// ---------------------------------------------------------------------------

describe("rectangle drawing", () => {
  it("uses ctx.strokeRect for rectangles", () => {
    expect(sourceCode).toMatch(/ctx\.strokeRect/);
  });
});
