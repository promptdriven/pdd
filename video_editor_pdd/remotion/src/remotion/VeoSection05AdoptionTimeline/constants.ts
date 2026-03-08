// Color palette and dimensions for VeoSection05AdoptionTimeline

export const COLORS = {
  // Background
  background: {
    center: '#1A1F3A',
    edge: '#0A0E27',
  },
  // Timeline
  timelineBase: '#2A3F5F',
  timelineProgress: '#00D9FF',
  timelineGlow: '#FFFFFF',
  // Nodes
  nodeFill: '#00D9FF',
  nodeBorder: '#FFFFFF',
  // Cards
  cardBackground: 'rgba(30, 41, 56, 0.2)',
  cardBorder: '#3A4A5F',
  // Text
  textWhite: '#FFFFFF',
  textCyan: '#00D9FF',
  textGray: '#E0E6ED',
  textMuted: '#9CA3AF',
};

export const DIMENSIONS = {
  // Canvas
  width: 1920,
  height: 1080,
  // Timeline
  timeline: {
    y: 540,
    x1: 200,
    x2: 1720,
    baseHeight: 6,
    progressHeight: 8,
    glowBlur: 20,
  },
  // Nodes
  node: {
    radius: 20,
    borderWidth: 3,
    positions: [200, 580, 960, 1340, 1720],
  },
  // Cards
  card: {
    width: 280,
    height: 120,
    borderRadius: 12,
    borderWidth: 1,
    offsetAbove: 350,
    offsetBelow: 680,
  },
};

export const MILESTONES = [
  {
    year: 2020,
    title: 'Traditional Video Tools',
    adoption: 12,
    x: 200,
    y: 350,
  },
  {
    year: 2021,
    title: 'Early AI Experiments',
    adoption: 18,
    x: 580,
    y: 680,
  },
  {
    year: 2022,
    title: 'First Commercial AI Video',
    adoption: 31,
    x: 960,
    y: 350,
  },
  {
    year: 2024,
    title: 'AI Video Goes Mainstream',
    adoption: 58,
    x: 1340,
    y: 680,
  },
  {
    year: 2025,
    title: 'VEO 2 Launch',
    adoption: 82,
    x: 1720,
    y: 350,
    highlight: true,
  },
];

export const TYPOGRAPHY = {
  title: {
    fontFamily: 'Inter',
    fontWeight: 'bold',
    fontSize: 52,
    color: COLORS.textWhite,
  },
  year: {
    fontFamily: 'Inter',
    fontWeight: '600',
    fontSize: 32,
    color: COLORS.textCyan,
  },
  milestoneTitle: {
    fontFamily: 'Inter',
    fontWeight: '600',
    fontSize: 24,
    color: COLORS.textGray,
  },
  stat: {
    fontFamily: 'Inter',
    fontWeight: '500',
    fontSize: 36,
    color: COLORS.textCyan,
  },
  descriptor: {
    fontFamily: 'Inter',
    fontWeight: '400',
    fontSize: 18,
    color: COLORS.textMuted,
  },
};
