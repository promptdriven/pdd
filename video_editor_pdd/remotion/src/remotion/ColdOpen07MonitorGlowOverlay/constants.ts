/** Total duration of the overlay in frames (~15.68s at 30fps) */
export const TOTAL_FRAMES = 470;

/** Canvas dimensions */
export const WIDTH = 1920;
export const HEIGHT = 1080;

/**
 * Glow A — left-edge blue monitor glow
 * Oscillates 15%→25%→15% over ~6s cycle
 */
export const GLOW_A_CENTER: [number, number] = [-200, 540];
export const GLOW_A_RADIUS = 600;
export const GLOW_A_COLOR = "#3B82F6";
export const GLOW_A_OPACITY_MIN = 0.15;
export const GLOW_A_OPACITY_MAX = 0.25;
export const GLOW_A_SPEED = 0.035; // ~6s period at 30fps

/**
 * Glow B — right-edge cool blue monitor glow
 * Oscillates 20%→10%→20% over ~8s cycle, counter-phased to Glow A
 */
export const GLOW_B_CENTER: [number, number] = [2120, 400];
export const GLOW_B_RADIUS = 500;
export const GLOW_B_COLOR = "#60A5FA";
export const GLOW_B_OPACITY_MIN = 0.10;
export const GLOW_B_OPACITY_MAX = 0.20;
export const GLOW_B_SPEED = 0.026; // ~8s period at 30fps
export const GLOW_B_PHASE_OFFSET = Math.PI;

/**
 * Glow C — top-right amber accent (static, no animation)
 */
export const GLOW_C_CENTER: [number, number] = [1600, -100];
export const GLOW_C_RADIUS = 400;
export const GLOW_C_COLOR = "#F59E0B";
export const GLOW_C_OPACITY = 0.08;
