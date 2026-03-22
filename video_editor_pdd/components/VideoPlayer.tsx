'use client';

import React, { useCallback, useEffect, useMemo, useRef, useState } from 'react';
import type { Annotation, AnnotationCaptureData } from '../lib/types';

type DrawTool = 'freehand' | 'rectangle' | 'circle' | 'arrow' | 'text';

type Stroke = {
  tool: DrawTool;
  points: [number, number][];
  text?: string;
};

interface VideoPlayerProps {
  src: string;
  annotations: Annotation[];
  onAnnotationCapture: (data: AnnotationCaptureData) => void;
  onTimeChange?: (seconds: number) => void;
  onAnnotationSelect?: (annotationId: string) => void;
  seekRequest?: { annotationId: string; timestamp: number } | null;
}

const CANVAS_WIDTH = 1920;
const CANVAS_HEIGHT = 1080;
const FALLBACK_TIMELINE_DURATION = 5;

const clamp = (value: number, min: number, max: number) =>
  Math.min(Math.max(value, min), max);

const formatTime = (seconds: number) => {
  if (!Number.isFinite(seconds)) return '0:00';
  const m = Math.floor(seconds / 60);
  const s = Math.floor(seconds % 60);
  return `${m}:${s.toString().padStart(2, '0')}`;
};

export default function VideoPlayer({
  src,
  annotations,
  onAnnotationCapture,
  onTimeChange,
  onAnnotationSelect,
  seekRequest,
}: VideoPlayerProps) {
  const videoRef = useRef<HTMLVideoElement>(null);
  const canvasRef = useRef<HTMLCanvasElement>(null);
  const containerRef = useRef<HTMLDivElement>(null);
  const progressBarRef = useRef<HTMLDivElement>(null);

  // eslint-disable-next-line @typescript-eslint/no-explicit-any
  const recognitionRef = useRef<any>(null);
  const finalTranscriptRef = useRef<string>('');

  const [isRecording, setIsRecording] = useState(false);
  const [selectedTool, setSelectedTool] = useState<DrawTool>('freehand');
  const [strokes, setStrokes] = useState<Stroke[]>([]);
  const [currentStroke, setCurrentStroke] = useState<Stroke | null>(null);
  const [isDrawing, setIsDrawing] = useState(false);
  const [transcript, setTranscript] = useState('');
  const [duration, setDuration] = useState(0);
  const [currentTime, setCurrentTime] = useState(0);
  const [speechAvailable, setSpeechAvailable] = useState(false);
  const [inputMethod, setInputMethod] = useState<'typed' | 'speech'>('typed');
  const [isScrubbing, setIsScrubbing] = useState(false);

  // Setup Web Speech API
  useEffect(() => {
    if (typeof window === 'undefined') return;
    const SpeechRecognitionImpl =
      (window as any).SpeechRecognition ||
      (window as any).webkitSpeechRecognition;

    if (!SpeechRecognitionImpl) return;

    // eslint-disable-next-line @typescript-eslint/no-explicit-any
    const recognition: any = new SpeechRecognitionImpl();
    recognition.continuous = true;
    recognition.interimResults = true;

    // eslint-disable-next-line @typescript-eslint/no-explicit-any
    recognition.onresult = (event: any) => {
      let interim = '';
      for (let i = event.resultIndex; i < event.results.length; i++) {
        const result = event.results[i];
        if (result.isFinal) {
          finalTranscriptRef.current += `${result[0].transcript} `;
        } else {
          interim += result[0].transcript;
        }
      }
      setTranscript(`${finalTranscriptRef.current}${interim}`.trim());
    };

    recognitionRef.current = recognition;
    setSpeechAvailable(true);
  }, []);

  const startSpeechRecognition = useCallback(() => {
    if (!recognitionRef.current) return;
    finalTranscriptRef.current = '';
    setTranscript('');
    try {
      recognitionRef.current.start();
    } catch {
      // Avoid throwing if already started
    }
  }, []);

  const stopSpeechRecognition = useCallback(() => {
    if (!recognitionRef.current) return;
    try {
      recognitionRef.current.stop();
    } catch {
      // ignore
    }
  }, []);

  // Draw stroke on canvas
  const drawStroke = useCallback(
    (ctx: CanvasRenderingContext2D, stroke: Stroke) => {
      ctx.lineWidth = 4;
      ctx.strokeStyle = '#f97316';
      ctx.fillStyle = '#f97316';
      ctx.lineCap = 'round';
      ctx.lineJoin = 'round';

      if (stroke.tool === 'freehand') {
        ctx.beginPath();
        stroke.points.forEach(([x, y], idx) => {
          if (idx === 0) ctx.moveTo(x, y);
          else ctx.lineTo(x, y);
        });
        ctx.stroke();
        return;
      }

      if (stroke.tool === 'rectangle') {
        const [start, end] = stroke.points;
        if (!start || !end) return;
        const x = Math.min(start[0], end[0]);
        const y = Math.min(start[1], end[1]);
        const w = Math.abs(end[0] - start[0]);
        const h = Math.abs(end[1] - start[1]);
        ctx.strokeRect(x, y, w, h);
        return;
      }

      if (stroke.tool === 'circle') {
        const [start, end] = stroke.points;
        if (!start || !end) return;
        const radius = Math.hypot(end[0] - start[0], end[1] - start[1]);
        ctx.beginPath();
        ctx.arc(start[0], start[1], radius, 0, Math.PI * 2);
        ctx.stroke();
        return;
      }

      if (stroke.tool === 'arrow') {
        const [start, end] = stroke.points;
        if (!start || !end) return;
        const headLength = 16;
        const angle = Math.atan2(end[1] - start[1], end[0] - start[0]);

        ctx.beginPath();
        ctx.moveTo(start[0], start[1]);
        ctx.lineTo(end[0], end[1]);
        ctx.stroke();

        ctx.beginPath();
        ctx.moveTo(end[0], end[1]);
        ctx.lineTo(
          end[0] - headLength * Math.cos(angle - Math.PI / 6),
          end[1] - headLength * Math.sin(angle - Math.PI / 6)
        );
        ctx.lineTo(
          end[0] - headLength * Math.cos(angle + Math.PI / 6),
          end[1] - headLength * Math.sin(angle + Math.PI / 6)
        );
        ctx.lineTo(end[0], end[1]);
        ctx.fill();
        return;
      }

      if (stroke.tool === 'text') {
        const [point] = stroke.points;
        if (!point) return;
        ctx.font = '36px sans-serif';
        ctx.fillText(stroke.text || '', point[0], point[1]);
      }
    },
    []
  );

  // Redraw canvas on every stroke change
  useEffect(() => {
    const canvas = canvasRef.current;
    if (!canvas) return;
    const ctx = canvas.getContext('2d');
    if (!ctx) return;
    ctx.clearRect(0, 0, canvas.width, canvas.height);

    const allStrokes = currentStroke ? [...strokes, currentStroke] : strokes;
    allStrokes.forEach((stroke) => drawStroke(ctx, stroke));
  }, [strokes, currentStroke, drawStroke]);

  // Coordinate mapping
  const mapPointerToCanvas = useCallback(
    (event: React.PointerEvent<HTMLCanvasElement>) => {
      const canvas = canvasRef.current;
      if (!canvas) return [0, 0] as [number, number];
      const rect = canvas.getBoundingClientRect();
      const x = ((event.clientX - rect.left) / rect.width) * CANVAS_WIDTH;
      const y = ((event.clientY - rect.top) / rect.height) * CANVAS_HEIGHT;
      return [clamp(x, 0, CANVAS_WIDTH), clamp(y, 0, CANVAS_HEIGHT)] as [
        number,
        number
      ];
    },
    []
  );

  const handlePointerDown = (event: React.PointerEvent<HTMLCanvasElement>) => {
    if (!isRecording) return;
    const point = mapPointerToCanvas(event);

    if (selectedTool === 'text') {
      const text = window.prompt('Enter annotation text', '') || '';
      if (text.trim().length === 0) return;
      setStrokes((prev) => [
        ...prev,
        { tool: 'text', points: [point], text },
      ]);
      return;
    }

    setIsDrawing(true);
    setCurrentStroke({
      tool: selectedTool,
      points: [point],
    });
  };

  const handlePointerMove = (event: React.PointerEvent<HTMLCanvasElement>) => {
    if (!isDrawing || !currentStroke || !isRecording) return;
    const point = mapPointerToCanvas(event);

    if (currentStroke.tool === 'freehand') {
      setCurrentStroke((prev) =>
        prev
          ? { ...prev, points: [...prev.points, point] }
          : prev
      );
    } else {
      setCurrentStroke((prev) =>
        prev ? { ...prev, points: [prev.points[0], point] } : prev
      );
    }
  };

  const handlePointerUp = () => {
    if (!isDrawing || !currentStroke) return;
    setStrokes((prev) => [...prev, currentStroke]);
    setCurrentStroke(null);
    setIsDrawing(false);
  };

  const captureComposite = useCallback(async () => {
    const videoEl = videoRef.current;
    const canvasEl = canvasRef.current;
    if (!videoEl || !canvasEl) return null;

    try {
      const offscreen = new OffscreenCanvas(CANVAS_WIDTH, CANVAS_HEIGHT);
      const ctx = offscreen.getContext('2d');
      if (!ctx) return null;

      ctx.drawImage(videoEl, 0, 0, CANVAS_WIDTH, CANVAS_HEIGHT);
      ctx.drawImage(canvasEl, 0, 0, CANVAS_WIDTH, CANVAS_HEIGHT);

      const blob = await offscreen.convertToBlob({ type: 'image/png' });
      return await new Promise<string>((resolve) => {
        const reader = new FileReader();
        reader.onloadend = () => resolve(reader.result as string);
        reader.readAsDataURL(blob);
      });
    } catch (error) {
      console.warn('Failed to capture composite frame:', error);
      return null;
    }
  }, []);

  const captureDrawing = useCallback(() => {
    const canvasEl = canvasRef.current;
    if (!canvasEl || strokes.length === 0) return null;
    return canvasEl.toDataURL('image/png');
  }, [strokes]);

  const handleCapture = useCallback(async () => {
    const videoEl = videoRef.current;
    if (!videoEl) return;

    const compositeDataUrl = await captureComposite();
    const drawingDataUrl = captureDrawing();

    const data: AnnotationCaptureData = {
      timestamp: videoEl.currentTime,
      text: transcript.trim(),
      drawingDataUrl: drawingDataUrl ?? null,
      compositeDataUrl: compositeDataUrl ?? null,
      videoFile: src,
      inputMethod,
    };

    onAnnotationCapture(data);
    setStrokes([]);
    setCurrentStroke(null);
  }, [captureComposite, captureDrawing, transcript, src, onAnnotationCapture, inputMethod]);

  const startRecordingMode = useCallback(() => {
    const videoEl = videoRef.current;
    if (videoEl) videoEl.pause();
    setIsRecording(true);
    setStrokes([]);
    setCurrentStroke(null);
    startSpeechRecognition();
  }, [startSpeechRecognition]);

  const stopRecordingMode = useCallback(async () => {
    setIsRecording(false);
    stopSpeechRecognition();
    await handleCapture();
    const videoEl = videoRef.current;
    if (videoEl) {
      void videoEl.play().catch(() => {});
    }
  }, [stopSpeechRecognition, handleCapture]);

  const togglePlayPause = useCallback(() => {
    const videoEl = videoRef.current;
    if (!videoEl) return;
    if (videoEl.paused) {
      void videoEl.play().catch(() => {});
    } else {
      videoEl.pause();
    }
  }, []);

  const seekBy = useCallback((delta: number) => {
    const videoEl = videoRef.current;
    if (!videoEl) return;
    videoEl.currentTime = clamp(
      videoEl.currentTime + delta,
      0,
      duration || videoEl.duration || 0
    );
    onTimeChange?.(videoEl.currentTime);
  }, [duration, onTimeChange]);

  const markerTimelineDuration = useMemo(() => {
    if (duration > 0) {
      return duration;
    }

    const maxAnnotationTimestamp = annotations.reduce((max, annotation) => {
      return Math.max(max, annotation.timestamp ?? 0);
    }, 0);

    return Math.max(
      currentTime,
      maxAnnotationTimestamp,
      FALLBACK_TIMELINE_DURATION
    );
  }, [annotations, currentTime, duration]);

  const seekToClientX = useCallback((clientX: number) => {
    const videoEl = videoRef.current;
    const progressEl = progressBarRef.current;
    if (!videoEl || !progressEl) return;

    const effectiveDuration = duration || videoEl.duration || markerTimelineDuration || 0;
    if (!Number.isFinite(effectiveDuration) || effectiveDuration <= 0) return;

    const rect = progressEl.getBoundingClientRect();
    if (rect.width <= 0) return;

    const percent = clamp((clientX - rect.left) / rect.width, 0, 1);
    const nextTime = percent * effectiveDuration;
    videoEl.currentTime = nextTime;
    setCurrentTime(nextTime);
    onTimeChange?.(nextTime);
  }, [duration, markerTimelineDuration, onTimeChange]);

  const handleProgressPointerDown = useCallback(
    (event: React.PointerEvent<HTMLDivElement>) => {
      setIsScrubbing(true);
      event.currentTarget.setPointerCapture(event.pointerId);
      seekToClientX(event.clientX);
    },
    [seekToClientX]
  );

  const handleProgressPointerMove = useCallback(
    (event: React.PointerEvent<HTMLDivElement>) => {
      if (!isScrubbing) return;
      seekToClientX(event.clientX);
    },
    [isScrubbing, seekToClientX]
  );

  const handleProgressPointerUp = useCallback(
    (event: React.PointerEvent<HTMLDivElement>) => {
      if (event.currentTarget.hasPointerCapture(event.pointerId)) {
        event.currentTarget.releasePointerCapture(event.pointerId);
      }
      seekToClientX(event.clientX);
      setIsScrubbing(false);
    },
    [seekToClientX]
  );

  const toggleFullscreen = useCallback(() => {
    const container = containerRef.current;
    if (!container) return;
    if (document.fullscreenElement) {
      document.exitFullscreen();
    } else {
      container.requestFullscreen();
    }
  }, []);

  // Keyboard shortcuts
  useEffect(() => {
    const handler = (event: KeyboardEvent) => {
      const target = event.target as HTMLElement | null;
      const tagName = target?.tagName?.toLowerCase();
      if (tagName === 'input' || tagName === 'textarea' || target?.isContentEditable) return;

      if (event.code === 'Space') {
        event.preventDefault();
        if (!isRecording) {
          startRecordingMode();
        } else {
          stopRecordingMode();
        }
      }

      if (event.key.toLowerCase() === 'k') {
        togglePlayPause();
      }

      if (event.key.toLowerCase() === 'd') setSelectedTool('freehand');
      if (event.key.toLowerCase() === 'r') setSelectedTool('rectangle');
      if (event.key.toLowerCase() === 'c') setSelectedTool('circle');
      if (event.key.toLowerCase() === 'a') setSelectedTool('arrow');
      if (event.key.toLowerCase() === 't') setSelectedTool('text');

      if (event.key === 'ArrowLeft') seekBy(-5);
      if (event.key === 'ArrowRight') seekBy(5);

      if (event.key.toLowerCase() === 'f') toggleFullscreen();

      if (event.key.toLowerCase() === 'm') {
        if (speechAvailable) {
          setInputMethod((prev) => (prev === 'typed' ? 'speech' : 'typed'));
        }
      }

      if ((event.ctrlKey || event.metaKey) && event.key.toLowerCase() === 'z') {
        if (isRecording) {
          setStrokes((prev) => prev.slice(0, -1));
        }
      }
    };

    window.addEventListener('keydown', handler);
    return () => window.removeEventListener('keydown', handler);
  }, [
    isRecording,
    startRecordingMode,
    stopRecordingMode,
    togglePlayPause,
    seekBy,
    toggleFullscreen,
    speechAvailable,
  ]);

  // Sync time/duration
  useEffect(() => {
    const videoEl = videoRef.current;
    if (!videoEl) return;

    const onLoaded = () => setDuration(videoEl.duration);
    const onTime = () => {
      setCurrentTime(videoEl.currentTime);
      onTimeChange?.(videoEl.currentTime);
    };

    // If metadata is already loaded (e.g. cached video), set duration immediately
    if (videoEl.readyState >= 1 && videoEl.duration > 0) {
      setDuration(videoEl.duration);
    }

    videoEl.addEventListener('loadedmetadata', onLoaded);
    videoEl.addEventListener('timeupdate', onTime);
    return () => {
      videoEl.removeEventListener('loadedmetadata', onLoaded);
      videoEl.removeEventListener('timeupdate', onTime);
    };
  }, [onTimeChange, src]);

  useEffect(() => {
    if (!seekRequest) return;
    const videoEl = videoRef.current;
    if (!videoEl) return;
    if (Math.abs(videoEl.currentTime - seekRequest.timestamp) < 0.01) return;
    videoEl.currentTime = seekRequest.timestamp;
    setCurrentTime(seekRequest.timestamp);
    onTimeChange?.(seekRequest.timestamp);
  }, [onTimeChange, seekRequest]);

  const progressPercent = useMemo(() => {
    if (!duration) return 0;
    return (currentTime / duration) * 100;
  }, [currentTime, duration]);

  return (
    <div className="w-full max-w-5xl mx-auto space-y-3">
      <div
        ref={containerRef}
        className="relative aspect-video w-full bg-black rounded-lg overflow-hidden shadow-lg"
      >
        <video
          ref={videoRef}
          src={src}
          crossOrigin="anonymous"
          className="absolute inset-0 w-full h-full object-contain"
          controls={false}
        />
        <canvas
          ref={canvasRef}
          width={CANVAS_WIDTH}
          height={CANVAS_HEIGHT}
          className="absolute inset-0 w-full h-full object-contain"
          style={{ pointerEvents: isRecording ? 'auto' : 'none' }}
          onPointerDown={handlePointerDown}
          onPointerMove={handlePointerMove}
          onPointerUp={handlePointerUp}
          onPointerLeave={handlePointerUp}
        />
        <div className="absolute top-3 left-3 bg-black/60 text-white px-3 py-1 rounded-full text-sm flex items-center gap-2">
          <span>{isRecording ? 'Recording' : 'Review'}</span>
          {isRecording && (
            <span className="inline-flex h-2 w-2 rounded-full bg-red-500 animate-pulse" />
          )}
          <span className="ml-2 text-xs opacity-80">
            Tool: {selectedTool.toUpperCase()}
          </span>
          {speechAvailable && (
            <span className={`ml-2 text-xs ${inputMethod === 'speech' ? 'text-green-400' : 'text-white/40'}`}>
              {'\u{1F3A4}'} {inputMethod === 'speech' ? 'ON' : 'off'}
            </span>
          )}
        </div>
        {isRecording && (
          <div className="absolute bottom-3 left-3 right-3 bg-black/60 text-white px-3 py-2 rounded text-xs">
            Transcript: {transcript || '...'}
          </div>
        )}
      </div>

      <div className="flex items-center justify-between text-sm text-gray-200">
        <div className="flex items-center gap-3">
          <button
            onClick={togglePlayPause}
            className="px-3 py-1 rounded bg-gray-800 hover:bg-gray-700"
          >
            Play/Pause (K)
          </button>
          <span>
            {formatTime(currentTime)} / {formatTime(duration)}
          </span>
        </div>
        <div className="flex items-center gap-2 text-xs">
          <span>Tools:</span>
          <span>D</span>
          <span>R</span>
          <span>C</span>
          <span>A</span>
          <span>T</span>
          <span>•</span>
          <span>Space = Annotate</span>
          <span>M = Mic</span>
        </div>
      </div>

      <div
        ref={progressBarRef}
        className="relative h-2 bg-gray-700 rounded cursor-pointer touch-none"
        onPointerDown={handleProgressPointerDown}
        onPointerMove={handleProgressPointerMove}
        onPointerUp={handleProgressPointerUp}
        onPointerCancel={() => setIsScrubbing(false)}
        aria-label="Seek timeline"
      >
        <div
          className="absolute left-0 top-0 h-2 bg-blue-500 rounded"
          style={{ width: `${progressPercent}%` }}
        />
        {annotations.map((a) => (
          <button
            key={a.id}
            type="button"
            onPointerDown={(event) => event.stopPropagation()}
            onClick={() => {
              const videoEl = videoRef.current;
              if (videoEl && a.timestamp != null) {
                videoEl.currentTime = a.timestamp;
                setCurrentTime(a.timestamp);
                onTimeChange?.(a.timestamp);
                onAnnotationSelect?.(a.id);
              }
            }}
            className="absolute w-1.5 h-1.5 rounded-full bg-yellow-400 top-0 -translate-y-1"
            style={{
              left: `${a.timestamp != null ? (a.timestamp / markerTimelineDuration) * 100 : 0}%`,
            }}
            aria-label={`annotation at ${(a.timestamp ?? 0).toFixed(2)} seconds`}
          />
        ))}
      </div>

      <div className="grid grid-cols-2 md:grid-cols-5 gap-2 text-xs text-gray-100">
        {(['freehand', 'rectangle', 'circle', 'arrow', 'text'] as DrawTool[]).map(
          (tool) => (
            <button
              key={tool}
              onClick={() => setSelectedTool(tool)}
              className={`px-3 py-2 rounded ${
                selectedTool === tool
                  ? 'bg-blue-600'
                  : 'bg-gray-800 hover:bg-gray-700'
              }`}
            >
              {tool.toUpperCase()}
            </button>
          )
        )}
      </div>
    </div>
  );
}
