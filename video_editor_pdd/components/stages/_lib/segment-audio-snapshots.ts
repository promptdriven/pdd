function bytesToBase64(bytes: Uint8Array): string {
  if (typeof Buffer !== "undefined") {
    return Buffer.from(bytes).toString("base64");
  }

  let binary = "";
  for (const byte of bytes) {
    binary += String.fromCharCode(byte);
  }
  return btoa(binary);
}

async function parseJsonError(response: Response): Promise<string | null> {
  try {
    const data = await response.json();
    return typeof data?.error === "string" ? data.error : null;
  } catch {
    return null;
  }
}

export async function captureSegmentAudioSnapshots({
  segmentIds,
  fetchImpl = fetch,
  now = () => Date.now(),
}: {
  segmentIds: string[];
  fetchImpl?: typeof fetch;
  now?: () => number;
}): Promise<Record<string, string>> {
  const snapshots: Record<string, string> = {};
  const uniqueSegmentIds = Array.from(new Set(segmentIds));

  for (const segmentId of uniqueSegmentIds) {
    const response = await fetchImpl(
      `/api/audio/tts/${encodeURIComponent(segmentId)}.wav?v=${now()}`,
      { cache: "no-store" },
    );
    if (!response.ok) {
      const errorMessage = await parseJsonError(response);
      throw new Error(
        errorMessage ?? `Failed to capture segment audio for ${segmentId}.`,
      );
    }

    const buffer = await response.arrayBuffer();
    snapshots[segmentId] = bytesToBase64(new Uint8Array(buffer));
  }

  return snapshots;
}

export async function restoreSegmentAudioSnapshots({
  snapshots,
  fetchImpl = fetch,
}: {
  snapshots: Record<string, string>;
  fetchImpl?: typeof fetch;
}): Promise<void> {
  const segments = Object.entries(snapshots).map(([segmentId, audioBase64]) => ({
    segmentId,
    audioBase64,
  }));

  if (segments.length === 0) {
    return;
  }

  const response = await fetchImpl("/api/pipeline/tts-render/audio", {
    method: "POST",
    headers: { "Content-Type": "application/json" },
    body: JSON.stringify({ segments }),
  });

  if (!response.ok) {
    const errorMessage = await parseJsonError(response);
    throw new Error(errorMessage ?? "Failed to restore segment audio.");
  }
}
