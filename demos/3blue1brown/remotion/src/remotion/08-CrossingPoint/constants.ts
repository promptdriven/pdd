import { z } from "zod";

// Video specs from the animation doc
export const CROSSING_POINT_FPS = 30;
export const CROSSING_POINT_DURATION_SECONDS = 10;
export const CROSSING_POINT_DURATION_FRAMES = CROSSING_POINT_FPS * CROSSING_POINT_DURATION_SECONDS;
export const CROSSING_POINT_WIDTH = 1920;
export const CROSSING_POINT_HEIGHT = 1080;

// Beat timings (in frames at 30fps)
export const BEATS = {
  // Zoom out from milestone view
  ZOOM_OUT_START: 0,
  ZOOM_OUT_END: 60,              // 0-2s: Zoom out animation
  // Crossing point marker appears
  MARKER_APPEAR_START: 60,
  MARKER_APPEAR_END: 90,         // 2-3s: Radial burst appearance
  // First strong pulse
  PULSE_1_START: 90,
  PULSE_1_END: 150,              // 3-5s: First pulse wave
  // Label "We are here." fades in
  LABEL_FADE_START: 150,
  LABEL_FADE_END: 210,           // 5-7s: Label appears
  // Hold with continued pulsing
  HOLD_START: 210,
  HOLD_END: 300,                 // 7-10s: Hold with pulses
};

// Color palette
export const COLORS = {
  BACKGROUND: "#1a1a2e",
  BACKGROUND_GRADIENT_END: "#0f0f1a",
  GRID: "#333344",
  AXIS: "#666677",
  AXIS_LABEL: "rgba(255, 255, 255, 0.8)",
  TITLE: "#ffffff",
  LINE_GENERATE: "#4A90D9",      // Blue - cost to generate
  LINE_PATCH: "#D9944A",          // Amber - cost to patch
  MARKER: "#FFFFFF",              // White circle
  MARKER_GLOW: "#4A90D9",         // Blue glow for the marker
  PULSE_GLOW: "#4A90D9",          // Blue pulse rings
};

// The crossing point (where cost to generate crosses below cost to patch)
// This happens around 2023-2024 based on the spec
export const CROSSING_POINT = {
  year: 2023.5,
  hours: 0.8,  // Approximate intersection point
};

// Chart margins
export const CHART_MARGINS = {
  top: 100,
  right: 250,
  bottom: 120,
  left: 180,
};

// Year range for code cost chart (modern era)
export const YEAR_RANGE = { min: 2015, max: 2030 };
export const HOURS_RANGE = { min: 0, max: 3 };

// Chart data for code costs
export const CHART_DATA = {
  // Cost to generate code - exponentially decreasing as AI improves
  costToGenerate: [
    { year: 2015, hours: 2.5 },
    { year: 2018, hours: 2.0 },
    { year: 2020, hours: 1.5 },
    { year: 2022, hours: 1.0 },
    { year: 2023, hours: 0.8 },
    { year: 2024, hours: 0.5 },
    { year: 2026, hours: 0.2 },
    { year: 2028, hours: 0.1 },
    { year: 2030, hours: 0.05 },
  ],
  // Cost to patch code - relatively flat (human cognitive cost)
  costToPatch: [
    { year: 2015, hours: 0.8 },
    { year: 2030, hours: 0.8 },
  ],
};

// Pulse effect configuration - more dramatic than sock threshold
export const PULSE_CONFIG = {
  NUM_RINGS: 5,           // 4-5 concentric rings
  RING_STAGGER: 15,       // Frames between ring starts
  MAX_SCALE: 5,           // Rings expand more
  MARKER_RADIUS: 25,      // 25px radius as specified
};

// Props schema
export const CrossingPointProps = z.object({
  showTitle: z.boolean().default(true),
});

export const defaultCrossingPointProps: z.infer<typeof CrossingPointProps> = {
  showTitle: true,
};

export type CrossingPointPropsType = z.infer<typeof CrossingPointProps>;
