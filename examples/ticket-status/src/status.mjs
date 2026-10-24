export function statusLabel(status) {
  if (status === null) return 'Unknown';
  if (typeof status !== 'string') {
    throw new TypeError('status must be a string or null');
  }

  switch (status) {
    case 'open':
      return 'Open';
    case 'blocked':
      return 'Blocked';
    case 'done':
      return 'Done';
    default:
      return 'Unknown';
  }
}
