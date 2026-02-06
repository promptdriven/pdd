import { z } from "zod";

// ── Audio-synced timing ────────────────────────────────────────────
// Section: Part 1: Economics of Darning
// Audio: part1_economics_narration.wav (212.4s)
// Generated from word_timestamps.json — Whisper segment boundaries
//
// Narration segments:
//     0.0s [ 0] "Eh, this isn't nostalgia. It's economics."
//     3.9s [ 1] "In 1950, a wool sock cost real money relative to an hou..."
//     9.5s [ 2] "Darning made sense. You'd spend 30 minutes to save a do..."
//    14.7s [ 3] "By 1990, the math flipped."
//    17.5s [ 4] "A new sock cost less than the time to repair the old on..."
//    21.2s [ 5] "Darning became irrational."
//    24.7s [ 6] "Now look at code."
//    27.1s [ 7] "For 50 years, generating new code was expensive."
//    31.1s [ 8] "Writing from scratch took hours, days, weeks."
//    34.6s [ 9] "So when something broke, you patched. Of course you pat..."
//    40.5s [10] "Now, here's where it gets interesting."
//    43.2s [11] "AI made patching faster too."
//    45.7s [12] "Cursor."
//    46.6s [13] "Claude."
//    47.6s [14] "Copilot."
//    48.7s [15] "They're incredible tools."
//    50.8s [16] "They understand your code base."
//    52.2s [17] "Suggest fixes. Catch bugs before you make them."
//    56.9s [18] "Look. Each patch is getting faster."
//    59.8s [19] "That's real. That's what you feel when you use these to..."
//    64.9s [20] "But watch the dashed line. The total cost. It's barely ..."
//    69.9s [21] "Because even though each patch is faster, every patch s..."
//    75.1s [22] "Technical debt. And that debt accumulates."
//    77.3s [23] "Faster now because you're patching faster."
//    81.8s [24] "AI gave you a 60% speed up on individual patches."
//    86.2s [25] "But your total cost. Down 4%, the debt ate the rest."
//    91.9s [26] "And there's something else hiding in that debt."
//    95.1s [27] "Something specific to AI assisted development."
//    99.4s [28] "When your code base is small, AI tools are brilliant."
//   103.3s [29] "The context window."
//   104.2s [30] "What the model can actually see."
//   106.7s [31] "Covers almost everything."
//   108.5s [32] "It understands how the pieces connect."
//   111.9s [33] "But code bases grow. And that window."
//   115.1s [34] "It stays the same size."
//   118.2s [35] "Now, the AI is looking through a keyhole."
//   121.2s [36] "It has to guess what's relevant."
//   123.3s [37] "And increasingly, it guesses wrong."
//   127.4s [38] "The code it needs is outside the window."
//   130.4s [39] "The code inside. Something else entirely."
//   133.9s [40] "This is why AI assisted patching feels great at first."
//   138.6s [41] "And frustrating later."
//   140.3s [42] "It's not the model getting dumber."
//   142.1s [43] "It's the ratio getting worse."
//   144.5s [44] "Every patch makes the code base bigger."
//   147.3s [45] "Every patch shrinks what the AI can see."
//   151.5s [46] "Regeneration doesn't have this problem."
//   154.0s [47] "A single module with a clear prompt."
//   156.6s [48] "That fits in the window every time."
//   160.4s [49] "Meanwhile, generation just crossed below both lines."
//   165.0s [50] "And it comes with no debt."
//   167.1s [51] "No rot."
//   168.4s [52] "Tools like cursor and clawed code are the best darning ..."
//   173.7s [53] "I use them. They're fantastic."
//   176.9s [54] "But they're still darning needles."
//   179.5s [55] "And the fundamental problem with darning isn't speed."
//   182.8s [56] "It's accumulation."
//   184.8s [57] "This is the part of software economics nobody talks abo..."
//   188.3s [58] "80-90% of software cost isn't building the initial syst..."
//   194.4s [59] "It's maintaining it, navigating around all the previous..."
//   199.8s [60] "Understanding what the last ten developers did and why."
//   204.9s [61] "And those costs compound."
//   209.0s [62] "Unless you regenerate, then they reset to zero."

export const PART1_FPS = 30;
export const PART1_DURATION_SECONDS = 215;
export const PART1_DURATION_FRAMES = PART1_FPS * PART1_DURATION_SECONDS;
export const PART1_WIDTH = 1920;
export const PART1_HEIGHT = 1080;

// Helper: seconds to frames
const s2f = (seconds: number) => Math.round(seconds * PART1_FPS);

export const BEATS = {
  // Visual 0: SockPriceChart — "Eh, this isn't nostalgia. It's economics...."
  VISUAL_00_START: s2f(0.0),  // 0 frames
  VISUAL_00_END: s2f(23.28),  // 698 frames

  // Visual 1: CodeCostChart — "Now look at code...."
  VISUAL_01_START: s2f(24.7),  // 741 frames
  VISUAL_01_END: s2f(38.82),  // 1165 frames

  // Visual 2: CodeCostChart — "Now, here's where it gets interesting...."
  VISUAL_02_START: s2f(40.48),  // 1214 frames
  VISUAL_02_END: s2f(63.34),  // 1900 frames

  // Visual 3: CrossingPoint — "But watch the dashed line. The total cost. It's ba..."
  VISUAL_03_START: s2f(64.94),  // 1948 frames
  VISUAL_03_END: s2f(90.64),  // 2719 frames

  // Visual 4: ContextRot — "And there's something else hiding in that debt...."
  VISUAL_04_START: s2f(91.9),  // 2757 frames
  VISUAL_04_END: s2f(149.76),  // 4493 frames

  // Visual 5: DeveloperEditZoomout — "Regeneration doesn't have this problem...."
  VISUAL_05_START: s2f(151.54),  // 4546 frames
  VISUAL_05_END: s2f(167.48),  // 5024 frames

  // Visual 6: veo:07_split_screen_sepia — "Tools like cursor and clawed code are the best dar..."
  VISUAL_06_START: s2f(168.36),  // 5051 frames
  VISUAL_06_END: s2f(183.44),  // 5503 frames

  // Visual 7: PieChart — "This is the part of software economics nobody talk..."
  VISUAL_07_START: s2f(184.78),  // 5543 frames
  VISUAL_07_END: s2f(203.52),  // 6106 frames

  // Visual 8: PieToCurve — "And those costs compound...."
  VISUAL_08_START: s2f(204.94),  // 6148 frames
  VISUAL_08_END: s2f(212.2),  // 6366 frames
};

// Visual sequence: maps BEATS ranges to composition IDs
export const VISUAL_SEQUENCE = [
  { start: BEATS.VISUAL_00_START, end: BEATS.VISUAL_00_END, id: "SockPriceChart", desc: "Sock economics: cost, labor, darning, flipped, irrational" },
  { start: BEATS.VISUAL_01_START, end: BEATS.VISUAL_01_END, id: "CodeCostChart", desc: "Code cost: expensive, scratch, patched, rational" },
  { start: BEATS.VISUAL_02_START, end: BEATS.VISUAL_02_END, id: "CodeCostChart", desc: "AI enters: patching faster, tools, feel it" },
  { start: BEATS.VISUAL_03_START, end: BEATS.VISUAL_03_END, id: "CrossingPoint", desc: "Dashed line, debt accumulates, 60% speedup" },
  { start: BEATS.VISUAL_04_START, end: BEATS.VISUAL_04_END, id: "ContextRot", desc: "Context rot: AI debt, keyhole, guesses wrong" },
  { start: BEATS.VISUAL_05_START, end: BEATS.VISUAL_05_END, id: "DeveloperEditZoomout", desc: "Regeneration: no debt, no rot, crossed lines" },
  { start: BEATS.VISUAL_06_START, end: BEATS.VISUAL_06_END, id: "veo:07_split_screen_sepia", desc: "Best darning needles, still accumulation" },
  { start: BEATS.VISUAL_07_START, end: BEATS.VISUAL_07_END, id: "PieChart", desc: "80-90% maintenance costs" },
  { start: BEATS.VISUAL_08_START, end: BEATS.VISUAL_08_END, id: "PieToCurve", desc: "Costs compound, regenerate resets to zero" },
];

// Props schema
export const Part1EconomicsProps = z.object({
  showTitle: z.boolean().default(true),
});

export const defaultPart1EconomicsProps: z.infer<typeof Part1EconomicsProps> = {
  showTitle: true,
};

export type Part1EconomicsPropsType = z.infer<typeof Part1EconomicsProps>;
