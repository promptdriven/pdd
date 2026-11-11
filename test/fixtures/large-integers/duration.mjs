// Synthetic native module for the large-integer replay fixture. It takes a Number of seconds.
export function formatDuration(seconds) {
  if (typeof seconds !== 'number' || !Number.isInteger(seconds) || seconds < 0) throw Object.assign(new RangeError('invalid-duration'), { code: 'invalid-duration' });
  if (seconds < 3600) return `${Math.floor(seconds / 60)}m`;
  const exact = BigInt(seconds);
  return `${exact / 3600n}h ${(exact % 3600n) / 60n}m`;
}
// The defect of the issue: hour arithmetic in Number loses digits above 2^53.
export function formatDurationWithNumberHours(seconds) {
  if (seconds < 3600) return `${Math.floor(seconds / 60)}m`;
  return `${Math.floor(seconds / 3600)}h ${Math.floor((seconds % 3600) / 60)}m`;
}
