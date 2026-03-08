// Component-level constants for ROI Calculator Animation

export const CANVAS = {
  width: 1920,
  height: 1080,
} as const;

export const COLORS = {
  background: {
    top: '#0F1419',
    bottom: '#1A1F3A',
  },
  grid: '#2A2E35',
  columnHeader: {
    background: '#1E2938',
    border: '#3A4A5F',
    text: '#FFFFFF',
  },
  traditional: '#EF4444',
  aiPlatformB: '#F59E0B',
  veo2: '#10B981',
  label: '#9CA3AF',
  savingsGradient: {
    start: '#10B981',
    end: '#059669',
  },
  white: '#FFFFFF',
  descriptor: '#E0E6ED',
} as const;

export const TYPOGRAPHY = {
  columnHeader: {
    family: 'Inter',
    weight: 700,
    size: 32,
  },
  metricLabel: {
    family: 'Inter',
    weight: 600,
    size: 24,
  },
  numberValue: {
    family: 'JetBrains Mono, monospace',
    weight: 500,
    size: 48,
  },
  savings: {
    family: 'Inter',
    weight: 900,
    size: 64,
  },
  descriptor: {
    family: 'Inter',
    weight: 400,
    size: 20,
  },
} as const;

export const LAYOUT = {
  columnHeader: {
    width: 500,
    height: 80,
    positions: [110, 710, 1310],
    y: 200,
    borderRadius: 12,
    borderWidth: 2,
  },
  metricRow: {
    height: 100,
    spacing: 20,
    startY: 320,
  },
  savingsCallout: {
    width: 600,
    height: 120,
    x: 960,
    y: 900,
    borderWidth: 3,
  },
} as const;

export const PLATFORM_DATA = [
  {
    name: 'Traditional Video',
    productionTime: 180,
    equipmentCost: 25000,
    teamSize: 8,
    monthlyCost: 18900,
    color: COLORS.traditional,
  },
  {
    name: 'AI Platform B',
    productionTime: 60,
    equipmentCost: 8000,
    teamSize: 3,
    monthlyCost: 9200,
    color: COLORS.aiPlatformB,
  },
  {
    name: 'VEO 2',
    productionTime: 12,
    equipmentCost: 1200,
    teamSize: 1,
    monthlyCost: 6500,
    color: COLORS.veo2,
  },
] as const;

export const SAVINGS = {
  vsTraditional: 12400,
  vsAIPlatformB: 2700,
  timeReduction: 93,
  teamReduction: 87,
} as const;

export const ANIMATION_TIMING = {
  headerSlideStart: 0,
  headerSlideDuration: 20,
  row1Start: 20,
  row1Duration: 30,
  row2Start: 50,
  row2Duration: 30,
  row3Start: 80,
  row3Duration: 30,
  row4Start: 110,
  row4Duration: 40,
  savingsStart: 150,
  savingsSpringDuration: 30,
  pulseStart: 180,
  totalDuration: 240,
} as const;
