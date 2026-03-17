// Canvas
export const CANVAS_WIDTH = 1920;
export const CANVAS_HEIGHT = 1080;
export const TOTAL_FRAMES = 360;
export const FPS = 30;

// Split layout
export const SPLIT_X = 960;
export const LEFT_PANEL_WIDTH = 958;
export const RIGHT_PANEL_START = 962;
export const RIGHT_PANEL_WIDTH = 958;
export const DIVIDER_WIDTH = 2;

// Background colors
export const BG_COLOR = "#000000";
export const LEFT_BG = "#0F172A";
export const RIGHT_BG = "#0A0F1A";
export const DIVIDER_COLOR = "#334155";
export const DIVIDER_OPACITY = 0.25;

// Panel colors
export const PANEL_BG = "#1E293B";

// Left panel colors (red/danger)
export const RED_ACCENT = "#EF4444";

// Right panel colors (green/success)
export const GREEN_ACCENT = "#5AAA6E";
export const AMBER_ACCENT = "#D9944A";
export const TEXT_LIGHT = "#E2E8F0";
export const CODE_MUTED = "#94A3B8";

// Animation timing (frames at 30fps)
export const SPLIT_LINE_START = 0;
export const SPLIT_LINE_END = 15;
export const HEADER_FADE_START = 0;
export const HEADER_FADE_END = 20;

export const CODE_DIFF_FADE_START = 20;
export const CODE_DIFF_FADE_END = 40;
export const PROMPT_FADE_START = 20;
export const PROMPT_FADE_END = 40;

export const QUESTION_MARK_START = 60;
export const QUESTION_MARK_FADE_END = 80;
export const PULSE_PERIOD = 30;

export const HIGHLIGHT_START = 80;
export const HIGHLIGHT_END = 120;

export const TEST_SUITE_START = 120;
export const CHECKMARK_INTERVAL = 15;

export const METERS_START = 220;
export const METER_FILL_DURATION = 30;
export const STATUS_LABEL_START = 250;
export const STATUS_LABEL_FADE_DURATION = 15;

// Cognitive load meter
export const METER_WIDTH = 300;
export const METER_HEIGHT = 16;
export const METER_Y = 950;

// Question mark
export const QUESTION_MARK_SIZE = 200;
export const QUESTION_MARK_X = 480;
export const QUESTION_MARK_Y = 450;
export const QUESTION_MARK_BASE_OPACITY = 0.15;
export const QUESTION_MARK_PEAK_OPACITY = 0.3;
export const QUESTION_MARK_GLOW_BLUR = 30;
export const QUESTION_MARK_GLOW_OPACITY = 0.06;

// Document panel positions
export const PROMPT_PANEL_X = 480;
export const PROMPT_PANEL_Y = 280;
export const PROMPT_PANEL_WIDTH = 400;
export const PROMPT_PANEL_HEIGHT = 250;

export const TEST_PANEL_X = 480;
export const TEST_PANEL_Y = 650;
export const TEST_PANEL_WIDTH = 400;
export const TEST_PANEL_HEIGHT = 250;

// Code diff content (fake diff lines)
export const DIFF_LINES: string[] = [
  "+ import { useState, useEffect, useCallback, useMemo } from 'react';",
  "- import { Component } from 'react';",
  "+ import { validateInput, sanitizeOutput, transformData } from './utils';",
  "  ",
  "+ export const processPayload = async (data: PayloadInput): Promise<Result> => {",
  "+   const validated = await validateInput(data);",
  "+   if (!validated.success) {",
  "+     throw new ValidationError(validated.errors);",
  "+   }",
  "-   return processLegacy(data);",
  "+   const transformed = transformData(validated.data, {",
  "+     normalize: true,",
  "+     stripNull: true,",
  "+     maxDepth: 10,",
  "+   });",
  "+   return sanitizeOutput(transformed);",
  "+ };",
  "  ",
  "+ interface ProcessorConfig {",
  "+   readonly mode: 'strict' | 'lenient';",
  "+   readonly retries: number;",
  "+   readonly timeout: number;",
  "+   readonly fallback?: () => Promise<Result>;",
  "+ }",
  "  ",
  "- class LegacyProcessor {",
  "-   private cache: Map<string, any>;",
  "-   constructor() { this.cache = new Map(); }",
  "-   process(input: any) { return this.cache.get(input); }",
  "- }",
  "  ",
  "+ export function createProcessor(config: ProcessorConfig) {",
  "+   const cache = new WeakMap<object, Result>();",
  "+   return {",
  "+     async process(input: PayloadInput): Promise<Result> {",
  "+       const cached = cache.get(input);",
  "+       if (cached) return cached;",
  "+       const result = await processPayload(input);",
  "+       cache.set(input, result);",
  "+       return result;",
  "+     },",
  "+     invalidate(key: object) { cache.delete(key); },",
  "+   };",
  "+ }",
  "  ",
  "+ // Error boundary for async operations",
  "+ export const withRetry = async <T>(fn: () => Promise<T>, retries = 3): Promise<T> => {",
  "+   for (let i = 0; i < retries; i++) {",
  "+     try { return await fn(); }",
  "+     catch (e) { if (i === retries - 1) throw e; }",
  "+   }",
  "+   throw new Error('Unreachable');",
  "+ };",
];

// Prompt document content
export const PROMPT_LINES: Array<{ text: string; highlight?: boolean }> = [
  { text: "# Payment Processor Refactor" },
  { text: "" },
  { text: "Convert the legacy class-based payment", highlight: true },
  { text: "processor to a functional architecture." },
  { text: "" },
  { text: "## Requirements" },
  { text: "- Input validation with typed errors", highlight: true },
  { text: "- WeakMap caching (not Map<string,any>)" },
  { text: "- Retry logic with configurable attempts" },
  { text: "- Null stripping + normalization", highlight: true },
  { text: "- Strict/lenient processing modes" },
  { text: "" },
  { text: "## Constraints" },
  { text: "- Must be tree-shakeable" },
  { text: "- No runtime type assertions" },
];

// Test results
export const TEST_ITEMS: string[] = [
  "test_handles_null_input",
  "test_returns_correct_format",
  "test_unicode_support",
  "test_edge_case_empty",
  "test_performance_under_100ms",
  "test_idempotent_behavior",
];
