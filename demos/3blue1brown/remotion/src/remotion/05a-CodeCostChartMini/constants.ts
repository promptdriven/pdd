import { z } from "zod";

// ── Audio-synced timing ────────────────────────────────────────────
// All beat timings derived from Whisper word-level timestamps on the
// concatenated narration audio (codecostchart_narration.wav, 67s).
//
// Narration breakdown (seconds → frames at 30fps):
//
//  SECTION 1: "The old economics" (0s - 14.8s)
//   0.00s  "Now look at code."                    → frame 0    (title + axes)
//   1.94s  "For fifty years..."                   → frame 58   (blue "Cost to Generate" line draws)
//   5.44s  "Writing from scratch took hours..."   → frame 163  (blue line still drawing)
//   8.44s  "weeks."                               → frame 253  (blue line reaches 2020)
//   9.00s  "So when something broke, you patched" → frame 270  (amber "Patch Cost" line draws)
//  13.12s  "It was rational."                     → frame 394  (Phase 1 done: blue + amber to 2020)
//
//  SECTION 2: "AI enters" (14.8s - 37.66s)
//  14.80s  "Now here's where it gets interesting" → frame 444  (transition beat)
//  17.50s  "AI made patching faster too"          → frame 525  (Phase 2: blue plunges, amber forks)
//  31.26s  "each patch is getting faster"         → frame 938  (highlight small-CB line dropping)
//  34.12s  "That's real."                         → frame 1024 (hold highlight)
//  37.66s  "these tools."                         → frame 1130 (Phase 2 drawing done)
//
//  SECTION 3: "The reveal" (39.24s - 54.84s)
//  39.24s  "But watch the dashed line"            → frame 1177 (REVEAL: dashed line draws for first time!)
//  43.52s  "barely moving."                       → frame 1306 (dashed line fully visible)
//  47.10s  "every patch still leaves residue"     → frame 1413 (PULSE debt area)
//  49.36s  "Technical debt"                       → frame 1481 (debt area highlight intensifies)
//  54.84s  "you're patching faster."              → frame 1645 (hold)
//
//  SECTION 4: "The data" (56.52s - 67s)
//  56.52s  "AI gave you a 60% speed up..."        → frame 1696 (data annotations appear)
//  64.88s  "the debt ate the rest"                → frame 1946 (crossing point)
//  67.00s   end of audio                          → frame 2010

export const MINI_FPS = 30;
export const MINI_DURATION_SECONDS = 68;
export const MINI_DURATION_FRAMES = MINI_FPS * MINI_DURATION_SECONDS;
export const MINI_WIDTH = 1920;
export const MINI_HEIGHT = 1080;

// Helper: seconds to frames
const s2f = (seconds: number) => Math.round(seconds * MINI_FPS);

export const BEATS = {
  // ── Section 1: The old economics ──
  AXES_VISIBLE_START: 0,
  AXES_VISIBLE_END: s2f(0.86),           // 26 - "code." lands

  // Blue "Cost to Generate" draws during "expensive... hours, days, weeks"
  BLUE_LINE_START: s2f(1.94),            // 58  - "For fifty years"
  BLUE_LINE_END: s2f(8.44),             // 253 - "weeks." (blue reaches 2020)

  // Amber "Patch Cost" draws during "you patched... rational"
  AMBER_LINE_START: s2f(9.0),            // 270 - "So when something broke"
  AMBER_LINE_END: s2f(13.12),            // 394 - "rational." Phase 1 complete

  // NOTE: No dashed line in Phase 1! It's revealed later in Section 3.

  // ── Section 2: AI enters ──
  PHASE2_START: s2f(17.5),               // 525 - "AI made patching faster"
  PHASE2_END: s2f(37.66),                // 1130 - "these tools." Phase 2 done

  // Highlight the dropping small-codebase line
  HIGHLIGHT_PATCH_START: s2f(31.26),     // 938 - "each patch is getting faster"
  HIGHLIGHT_PATCH_END: s2f(37.66),       // 1130 - "these tools."

  // ── Section 3: The reveal ──
  // Dashed line draws for the FIRST TIME here (the big reveal!)
  REVEAL_DASHED_START: s2f(39.24),       // 1177 - "But watch the dashed line"
  REVEAL_DASHED_END: s2f(43.52),         // 1306 - "barely moving." (fully drawn)

  // Pulse/highlight the debt area
  DEBT_HIGHLIGHT_START: s2f(47.10),      // 1413 - "every patch still leaves residue"
  DEBT_HIGHLIGHT_END: s2f(54.84),        // 1645 - "you're patching faster."

  // ── Section 4: The data ──
  // First annotation beat (VISUAL 9): Individual task vs Overall throughput
  EMPHASIS_START: s2f(56.52),            // 1696 - "AI gave you a 60% speed up"
  EMPHASIS_MID: s2f(60.70),             // 1821 - transition to second annotation beat

  // Second annotation beat (VISUAL 10): Code churn and refactoring
  EMPHASIS2_START: s2f(60.70),          // 1821
  EMPHASIS_END: s2f(64.88),              // 1946 - "the debt ate the rest"

  CROSSING_START: s2f(64.88),            // 1946
  CROSSING_END: s2f(68),                 // 2040
};

// Props schema
export const CodeCostChartMiniProps = z.object({
  showTitle: z.boolean().default(true),
  showAudio: z.boolean().default(true),
});

export const defaultCodeCostChartMiniProps: z.infer<typeof CodeCostChartMiniProps> = {
  showTitle: true,
  showAudio: true,
};

export type CodeCostChartMiniPropsType = z.infer<typeof CodeCostChartMiniProps>;
