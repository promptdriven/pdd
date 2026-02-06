import { z } from "zod";

// ── Audio-synced timing ────────────────────────────────────────────
// Section: Part 1: Economics of Darning
// Audio: part1_economics_narration.wav (256.5s)
// Generated from word_timestamps.json — Whisper segment boundaries
//
// Narration segments:
//     0.0s [ 0] "Eh, this isn't nostalgia. It's economics."
//     3.9s [ 1] "In 1950, a wool sock cost real money relative to an hou..."
//     9.5s [ 2] "Darning made sense. You'd spend 30 minutes to save a do..."
//    14.6s [ 3] "By 1990, the math flipped, and new sock cost less than ..."
//    21.2s [ 4] "Darning became irrational."
//    24.7s [ 5] "Now look at code."
//    27.1s [ 6] "For 50 years, generating new code was expensive."
//    31.2s [ 7] "Writing from scratch took hours, days, weeks."
//    34.7s [ 8] "So when something broke, you patched. Of course you pat..."
//    40.5s [ 9] "Now, here's where it gets interesting."
//    43.2s [10] "AI made patching faster too."
//    45.7s [11] "Cursor."
//    46.6s [12] "Claude code."
//    47.8s [13] "Copilot."
//    48.7s [14] "They're incredible tools."
//    50.8s [15] "They understand your code base."
//    52.2s [16] "Suggest fixes. Catch bugs before you make them."
//    56.9s [17] "Look. Each patch is getting faster."
//    59.8s [18] "That's real. That's what you feel when you use these to..."
//    65.0s [19] "But watch the dashed line. The total cost. It's barely ..."
//    69.9s [20] "Because even though each patch is faster, every patch s..."
//    75.0s [21] "Technical debt. And that debt accumulates."
//    77.3s [22] "Faster now. Because you're patching faster."
//    82.3s [23] "AI gave you a 60% speed up on individual patches."
//    86.2s [24] "But your total cost. Down 4%, the debt ate the rest."
//    91.8s [25] "And there's something else hiding in that debt."
//    95.0s [26] "Something specific to AI assisted development."
//    99.5s [27] "When your code base is small, AI tools are brilliant."
//   103.3s [28] "The context window."
//   104.2s [29] "What the model can actually see."
//   106.7s [30] "Covers almost everything."
//   108.5s [31] "It understands how the pieces connect."
//   112.1s [32] "But code bases grow. And that window."
//   115.1s [33] "It stays the same size."
//   118.2s [34] "Now, the AI is looking through a keyhole."
//   121.2s [35] "It has to guess what's relevant."
//   123.3s [36] "And increasingly, it guesses wrong."
//   127.8s [37] "The code it needs is outside the window."
//   129.9s [38] "The code inside. Something else entirely."
//   134.1s [39] "This is why AI assisted patching feels great at first."
//   138.6s [40] "And frustrating later."
//   140.3s [41] "It's not the model getting dumber."
//   142.2s [42] "It's the ratio getting worse."
//   144.5s [43] "Every patch makes the code base bigger."
//   147.3s [44] "Every patch shrinks what the AI can see."
//   151.5s [45] "Regeneration doesn't have this problem."
//   154.0s [46] "A single module with a clear prompt."
//   156.5s [47] "That fits in the window."
//   157.6s [48] "Every time."
//   160.4s [49] "Meanwhile, generation just crossed below both lines."
//   164.8s [50] "And it comes with no debt."
//   167.1s [51] "No rot."
//   168.5s [52] "Tools like cursor and clawed code are the best darning ..."
//   173.7s [53] "I use them. They're fantastic."
//   176.9s [54] "But they're still darning needles."
//   179.5s [55] "And the fundamental problem with darning isn't speed."
//   182.8s [56] "It's accumulation."
//   184.8s [57] "This is the part of software economics nobody talks abo..."
//   188.9s [58] "80-90% of software cost isn't building the initial syst..."
//   194.4s [59] "It's maintaining it."
//   196.5s [60] "Navigating around all the previous patches."
//   199.7s [61] "Understanding what the last ten developers did."
//   203.1s [62] "And why?"
//   204.8s [63] "And those costs compound."
//   208.9s [64] "Unless you regenerate, then they reset to zero."
//   213.3s [65] "Ugh."
//   215.0s [66] "So what actually changed with clothes?"
//   218.4s [67] "It wasn't just that fabric got cheaper."
//   222.3s [68] "It was a paradigm shift in manufacturing."
//   225.2s [69] "From crafting individual objects."
//   227.8s [70] "To designing molds."
//   230.1s [71] "Make the mold once."
//   231.5s [72] "Produce unlimited identical parts."
//   234.1s [73] "Refine the mold once."
//   235.9s [74] "Every future part improves automatically."
//   239.3s [75] "And when there's a defect?"
//   242.0s [76] "You don't patch individual parts."
//   244.3s [77] "You fix the mold."
//   245.7s [78] "And that fix applies to every part you'll ever make aga..."
//   250.3s [79] "This is the real shift."
//   252.4s [80] "Not cheaper material."
//   254.4s [81] "A migration of where value lives."

export const PART1_FPS = 30;
export const PART1_DURATION_SECONDS = 259;
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
  VISUAL_01_START: s2f(24.68),  // 740 frames
  VISUAL_01_END: s2f(38.82),  // 1165 frames

  // Visual 2: CodeCostChart — "Now, here's where it gets interesting...."
  VISUAL_02_START: s2f(40.48),  // 1214 frames
  VISUAL_02_END: s2f(63.36),  // 1901 frames

  // Visual 3: CrossingPoint — "But watch the dashed line. The total cost. It's ba..."
  VISUAL_03_START: s2f(64.96),  // 1949 frames
  VISUAL_03_END: s2f(90.62),  // 2719 frames

  // Visual 4: ContextRot — "And there's something else hiding in that debt...."
  VISUAL_04_START: s2f(91.84),  // 2755 frames
  VISUAL_04_END: s2f(149.76),  // 4493 frames

  // Visual 5: DeveloperEditZoomout — "Regeneration doesn't have this problem...."
  VISUAL_05_START: s2f(151.54),  // 4546 frames
  VISUAL_05_END: s2f(167.52),  // 5026 frames

  // Visual 6: veo:07_split_screen_sepia — "Tools like cursor and clawed code are the best dar..."
  VISUAL_06_START: s2f(168.52),  // 5056 frames
  VISUAL_06_END: s2f(183.46),  // 5504 frames

  // Visual 7: PieChart — "This is the part of software economics nobody talk..."
  VISUAL_07_START: s2f(184.76),  // 5543 frames
  VISUAL_07_END: s2f(212.26),  // 6368 frames

  // Visual 8: PartsEject — "Ugh...."
  VISUAL_08_START: s2f(213.26),  // 6398 frames
  VISUAL_08_END: s2f(240.98),  // 7229 frames

  // Visual 9: ValueAura — "You don't patch individual parts...."
  VISUAL_09_START: s2f(242.04),  // 7261 frames
  VISUAL_09_END: s2f(256.26),  // 7688 frames
};

// Visual sequence: maps BEATS ranges to composition IDs
export const VISUAL_SEQUENCE = [
  { start: BEATS.VISUAL_00_START, end: BEATS.VISUAL_00_END, id: "SockPriceChart", desc: "Sock economics: nostalgia → economics → 1950 → flipped → irr" },
  { start: BEATS.VISUAL_01_START, end: BEATS.VISUAL_01_END, id: "CodeCostChart", desc: "Code economics: look at code → expensive → patched → rationa" },
  { start: BEATS.VISUAL_02_START, end: BEATS.VISUAL_02_END, id: "CodeCostChart", desc: "AI enters: interesting → faster → cursor/claude → real → fee" },
  { start: BEATS.VISUAL_03_START, end: BEATS.VISUAL_03_END, id: "CrossingPoint", desc: "Reveal: dashed line → debt → accumulates → 60% speedup → deb" },
  { start: BEATS.VISUAL_04_START, end: BEATS.VISUAL_04_END, id: "ContextRot", desc: "Context rot: something else → small=brilliant → window → gro" },
  { start: BEATS.VISUAL_05_START, end: BEATS.VISUAL_05_END, id: "DeveloperEditZoomout", desc: "Regeneration: doesn't have problem → fits window → crossed b" },
  { start: BEATS.VISUAL_06_START, end: BEATS.VISUAL_06_END, id: "veo:07_split_screen_sepia", desc: "Best darning needles: cursor/claude → fantastic → still darn" },
  { start: BEATS.VISUAL_07_START, end: BEATS.VISUAL_07_END, id: "PieChart", desc: "Maintenance costs: 80-90% → maintaining → compound → reset" },
  { start: BEATS.VISUAL_08_START, end: BEATS.VISUAL_08_END, id: "PartsEject", desc: "Paradigm shift: what changed → mold once → unlimited parts →" },
  { start: BEATS.VISUAL_09_START, end: BEATS.VISUAL_09_END, id: "ValueAura", desc: "Fix the mold → every part → real shift → where value lives" },
];

// Props schema
export const Part1EconomicsProps = z.object({
  showTitle: z.boolean().default(true),
});

export const defaultPart1EconomicsProps: z.infer<typeof Part1EconomicsProps> = {
  showTitle: true,
};

export type Part1EconomicsPropsType = z.infer<typeof Part1EconomicsProps>;
