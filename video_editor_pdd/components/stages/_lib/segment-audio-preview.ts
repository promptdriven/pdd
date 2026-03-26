export interface PreviewAudioElement {
  currentTime: number;
  src: string;
  pause: () => void;
  load: () => void;
  play: () => Promise<void>;
  removeAttribute: (name: string) => void;
}

interface LoadSegmentPreviewAudioParams {
  audio: PreviewAudioElement;
  segmentId: string;
  previousObjectUrl: string | null;
  fetchImpl?: typeof fetch;
  createObjectURL?: (blob: Blob) => string;
  revokeObjectURL?: (url: string) => void;
  now?: () => number;
}

export async function loadSegmentPreviewAudio({
  audio,
  segmentId,
  previousObjectUrl,
  fetchImpl = fetch,
  createObjectURL = (blob) => URL.createObjectURL(blob),
  revokeObjectURL = (url) => URL.revokeObjectURL(url),
  now = () => Date.now(),
}: LoadSegmentPreviewAudioParams): Promise<string> {
  const response = await fetchImpl(`/api/audio/tts/${segmentId}.wav?v=${now()}`, {
    cache: "no-store",
  });
  if (!response.ok) {
    throw new Error("Failed to load segment audio");
  }

  const blob = await response.blob();
  const objectUrl = createObjectURL(blob);

  try {
    audio.pause();
    audio.currentTime = 0;
    if (previousObjectUrl) {
      revokeObjectURL(previousObjectUrl);
    }
    audio.src = objectUrl;
    audio.load();
    await audio.play();
    return objectUrl;
  } catch (error) {
    revokeObjectURL(objectUrl);
    audio.removeAttribute("src");
    audio.load();
    throw error;
  }
}

export function resetSegmentPreviewAudio(
  audio: PreviewAudioElement,
  objectUrl: string | null,
  revokeObjectURL: (url: string) => void = (url) => URL.revokeObjectURL(url)
): null {
  audio.pause();
  audio.currentTime = 0;
  audio.removeAttribute("src");
  audio.load();
  if (objectUrl) {
    revokeObjectURL(objectUrl);
  }
  return null;
}
