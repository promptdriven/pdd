// ColdOpen05CrossfadeTransition constants

// Animation timing (frames at 30fps)
export const CROSSFADE_DURATION = 20; // 20 frames = ~0.67s
export const TOTAL_FRAMES = 20;

// The crossfade starts at the beginning of this component's local timeline.
// In the parent composition, this component is placed at frame 240.
export const CROSSFADE_START = 0;
export const CROSSFADE_END = 20;

// Video sources
export const LAYER_A_SRC = "veo/cold_open.mp4"; // outgoing wide shot
export const LAYER_B_SRC = "veo/cold_open.mp4"; // incoming close-up

// Layer A plays from the start of cold_open.mp4 (wide desk shot)
// Layer B plays from 8s in (close-up glasses shot)
export const LAYER_A_START_FROM = 0; // frames — start of video
export const LAYER_B_START_FROM = 240; // frames — 8s at 30fps

// Background
export const BG_COLOR = "#0A1628";
