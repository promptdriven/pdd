type SseStartResult = {
  jobId: string | null;
  errorMessage?: string;
};

type WaitForJobCompletionOptions = {
  fetchImpl?: typeof fetch;
  sleepImpl?: (ms: number) => Promise<void>;
  pollIntervalMs?: number;
  timeoutMs?: number;
};

const parseSsePayload = async (response: Response): Promise<SseStartResult> => {
  const body = await response.text();
  const events = body.split("\n\n").filter(Boolean);

  for (const event of events) {
    const lines = event.split("\n").filter(Boolean);
    const eventName = lines.find((line) => line.startsWith("event:"))?.slice(6).trim() ?? null;
    const dataLine = lines.find((line) => line.startsWith("data:"));
    if (!dataLine) {
      continue;
    }

    try {
      const payload = JSON.parse(dataLine.slice(5).trim()) as {
        jobId?: string | null;
        message?: string;
      };

      if (eventName === "error") {
        return {
          jobId: null,
          errorMessage: payload.message ?? "Unknown SSE error",
        };
      }

      if (payload.jobId) {
        return { jobId: payload.jobId };
      }
    } catch {
      // Ignore malformed event payloads.
    }
  }

  return { jobId: null };
};

export async function readSseStartResult(response: Response): Promise<SseStartResult> {
  const contentType = response.headers.get("content-type") ?? "";
  if (contentType.includes("application/json")) {
    const payload = (await response.json()) as { jobId?: string | null; error?: string };
    return {
      jobId: payload.jobId ?? null,
      errorMessage: payload.error,
    };
  }

  return parseSsePayload(response);
}

export async function extractJobIdFromSse(response: Response): Promise<string | null> {
  const result = await readSseStartResult(response);
  return result.jobId;
}

const defaultSleep = (ms: number) =>
  new Promise<void>((resolve) => setTimeout(resolve, ms));

export async function waitForJobCompletion(
  jobId: string,
  options: WaitForJobCompletionOptions = {},
): Promise<void> {
  const fetchImpl = options.fetchImpl ?? fetch;
  const sleepImpl = options.sleepImpl ?? defaultSleep;
  const pollIntervalMs = options.pollIntervalMs ?? 1000;
  const timeoutMs = options.timeoutMs ?? 5 * 60 * 1000;
  const startMs = Date.now();

  while (true) {
    const response = await fetchImpl(`/api/jobs/${jobId}`);
    if (response.status === 404) {
      throw new Error(`Job not found: ${jobId}`);
    }
    if (!response.ok) {
      throw new Error(`Failed to poll job ${jobId}: ${response.status}`);
    }

    const payload = (await response.json()) as {
      status?: string;
      error?: string | null;
    };

    if (payload.status === "done") {
      return;
    }

    if (payload.status === "error") {
      throw new Error(payload.error ?? `Job failed: ${jobId}`);
    }

    if (Date.now() - startMs >= timeoutMs) {
      throw new Error(`Timed out waiting for job ${jobId}`);
    }

    await sleepImpl(pollIntervalMs);
  }
}
