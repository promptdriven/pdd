import {healthyDoctorPorts} from './doctor-fixture.mjs';
// Controlled machine and account ports: no live host/account reads in launcher tests.
export const healthyMachine = {
  doctorPorts: healthyDoctorPorts,
  machineHealth: async () => ({ healthy: true, causes: [], resources: null }),
  codexLimits: async () => ({ state: 'healthy', resetAt: null, usedPercent: 25 }),
  cleanupWorktrees: async () => ({ removed: [], kept: [] }),
};
