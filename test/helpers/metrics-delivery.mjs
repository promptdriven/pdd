export function metricsDelivery() {
  return {
    metricsAppendEvents() {
      return Promise.resolve({ ok: true });
    },
    async settle() {
      await new Promise(resolve => setImmediate(resolve));
    },
  };
}
