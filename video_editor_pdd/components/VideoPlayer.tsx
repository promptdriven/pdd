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
}

const CANVAS_WIDTH = 1920;
const CANVAS_HEIGHT = 1080;

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
}: VideoPlayerProps) {
  const videoRef = useRef<HTMLVideoElement>(null);
  const canvasRef = useRef<HTMLCanvasElement>(null);
  const containerRef = useRef<HTMLDivElement>(null);

  const recognitionRef = useRef<SpeechRecognition | null>(null);
  const finalTranscriptRef = useRef<string>('');

  const [isRecording, setIsRecording] = useState(false);
  const [selectedTool, setSelectedTool] = useState<DrawTool>('freehand');
  const [strokes, setStrokes] = useState<Stroke[]>([]);
  const [currentStroke, setCurrentStroke] = useState<Stroke | null>(null);
  const [isDrawing, setIsDrawing] = useState(false);
  const [transcript, setTranscript] = useState('');
  const [duration, setDuration] = useState(0);
  const [currentTime, setCurrentTime] = useState(0);

  // Setup Web Speech API
  useEffect(() => {
    if (typeof window === 'undefined') return;
    const SpeechRecognitionImpl =
      (window as any).SpeechRecognition ||
      (window as any).webkitSpeechRecognition;

    if (!SpeechRecognitionImpl) return;

    const recognition: SpeechRecognition = new SpeechRecognitionImpl();
    recognition.continuous = true;
    recognition.interimResults = true;

    recognition.onresult = (event: SpeechRecognitionEvent) => {
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
    };

    onAnnotationCapture(data);
    setStrokes([]);
    setCurrentStroke(null);
  }, [captureComposite, captureDrawing, transcript, src, onAnnotationCapture]);

  const startRecordingMode = useCallback(() => {
    const videoEl = videoRef.current;
    if (videoEl) videoEl.pause();
    setIsRecording(true);
    setStrokes([]);
    setCurrentStroke(null);
    startSpeechRecognition();
  }, [startSpeechRecognition]);

  const stopRecordingMode = useCallback(() => {
    setIsRecording(false);
    stopSpeechRecognition();
    handleCapture();
  }, [stopSpeechRecognition, handleCapture]);

  const togglePlayPause = useCallback(() => {
    const videoEl = videoRef.current;
    if (!videoEl) return;
    if (videoEl.paused) videoEl.play();
    else videoEl.pause();
  }, []);

  const seekBy = useCallback((delta: number) => {
    const videoEl = videoRef.current;
    if (!videoEl) return;
    videoEl.currentTime = clamp(
      videoEl.currentTime + delta,
      0,
      duration || videoEl.duration || 0
    );
  }, [duration]);

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
      if (tagName === 'input' || tagName === 'textarea') return;

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
  ]);

  // Sync time/duration
  useEffect(() => {
    const videoEl = videoRef.current;
    if (!videoEl) return;

    const onLoaded = () => setDuration(videoEl.duration);
    const onTime = () => setCurrentTime(videoEl.currentTime);

    videoEl.addEventListener('loadedmetadata', onLoaded);
    videoEl.addEventListener('timeupdate', onTime);
    return () => {
      videoEl.removeEventListener('loadedmetadata', onLoaded);
      videoEl.removeEventListener('timeupdate', onTime);
    };
  }, [src]);

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
        </div>
      </div>

      <div className="relative h-2 bg-gray-700 rounded cursor-pointer">
        <div
          className="absolute left-0 top-0 h-2 bg-blue-500 rounded"
          style={{ width: `${progressPercent}%` }}
        />
        {annotations.map((a) => (
          <button
            key={a.id}
            onClick={() => {
              const videoEl = videoRef.current;
              if (videoEl) videoEl.currentTime = a.timestamp;
            }}
            className="absolute w-1.5 h-1.5 rounded-full bg-yellow-400 top-0 -translate-y-1"
            style={{ left: `${(a.timestamp / duration) * 100}%` }}
            aria-label={`annotation at ${a.timestamp.toFixed(2)} seconds`}
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