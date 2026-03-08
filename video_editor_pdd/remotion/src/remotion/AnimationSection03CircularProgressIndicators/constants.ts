/**
 * Constants for AnimationSection03CircularProgressIndicators
 */

export const CANVAS = {
  width: 1920,
  height: 1080,
  background: '#f8fafc', // slate-50
};

export const INDICATORS = [
  {
    position: [480, 540] as [number, number],
    radius: 100,
    thickness: 12,
    progress: 87,
    color: '#3b82f6', // blue-500
    bgColor: '#e0e7ff', // blue-100
    label: 'Performance',
  },
  {
    position: [960, 540] as [number, number],
    radius: 100,
    thickness: 12,
    progress: 94,
    color: '#8b5cf6', // violet-500
    bgColor: '#ede9fe', // violet-100
    label: 'Reliability',
  },
  {
    position: [1440, 540] as [number, number],
    radius: 100,
    thickness: 12,
    progress: 76,
    color: '#ec4899', // pink-500
    bgColor: '#fce7f3', // pink-100
    label: 'Efficiency',
  },
];

export const ANIMATION_TIMING = {
  backgroundRingsFadeIn: { start: 0, duration: 10 },
  circle1: { start: 10, duration: 30 },
  circle2: { start: 20, duration: 30 },
  circle3: { start: 30, duration: 30 },
  labelsFadeIn: { start: 5, duration: 20 },
  staggerDelay: 10,
};

export const TYPOGRAPHY = {
  percentage: {
    fontFamily: 'Inter',
    fontWeight: 'bold',
    fontSize: 48,
  },
  label: {
    fontFamily: 'Inter',
    fontWeight: '500',
    fontSize: 18,
    color: '#475569', // slate-600
  },
};
