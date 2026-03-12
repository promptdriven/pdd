try {
  require("server-only");
} catch {
  // Tests import this in Node directly.
}

if (typeof window !== "undefined") {
  throw new Error("lib/veo.ts must not be imported in the browser");
}

import fs from "fs";
import path from "path";
import { exec } from "child_process";
import { promisify } from "util";
import { GoogleGenAI, type GenerateVideosParameters } from "@google/genai";

const execAsync = promisify(exec);
const POLL_INTERVAL_MS = 5000;
const OPERATION_TIMEOUT_MS = 10 * 60 * 1000;
const DEFAULT_VEO_MODEL = "veo-3.1-generate-001";

const truthyEnv = (value: string | undefined): boolean =>
  /^(1|true|yes)$/i.test((value ?? "").trim());

const getVertexProject = (): string | null =>
  process.env.GOOGLE_CLOUD_PROJECT ||
  process.env.VERTEXAI_PROJECT ||
  process.env.VERTEX_PROJECT ||
  null;

const getVertexLocation = (): string =>
  process.env.GOOGLE_CLOUD_LOCATION ||
  process.env.VERTEXAI_LOCATION ||
  process.env.VERTEX_LOCATION ||
  "global";

const getRequestHttpOptions = (): { timeout: number; apiVersion?: "v1" } =>
  shouldUseVertex()
    ? {
        timeout: OPERATION_TIMEOUT_MS,
        apiVersion: "v1",
      }
    : {
        timeout: OPERATION_TIMEOUT_MS,
      };

const shouldUseVertex = (): boolean => {
  if (truthyEnv(process.env.GOOGLE_GENAI_USE_VERTEXAI)) {
    return true;
  }

  return !process.env.GOOGLE_API_KEY && Boolean(getVertexProject());
};

const createClient = (): GoogleGenAI => {
  if (shouldUseVertex()) {
    const project = getVertexProject();
    if (!project) {
      throw new Error(
        "Vertex AI is enabled but no project was configured. Set GOOGLE_CLOUD_PROJECT, VERTEXAI_PROJECT, or VERTEX_PROJECT.",
      );
    }

    return new GoogleGenAI({
      vertexai: true,
      project,
      location: getVertexLocation(),
      apiVersion: "v1",
    });
  }

  const apiKey = process.env.GOOGLE_API_KEY;
  if (apiKey) {
    return new GoogleGenAI({ apiKey });
  }

  throw new Error(
    "Veo authentication is not configured. Set GOOGLE_API_KEY for Gemini API access or configure Vertex AI with GOOGLE_GENAI_USE_VERTEXAI=true and GOOGLE_CLOUD_PROJECT (or VERTEXAI_PROJECT / VERTEX_PROJECT).",
  );
};

const ensureOutputDir = (outputPath: string) => {
  fs.mkdirSync(path.dirname(outputPath), { recursive: true });
};

const sleep = (ms: number): Promise<void> =>
  new Promise((resolve) =>
    setTimeout(resolve, process.env.JEST_WORKER_ID ? 0 : ms),
  );

const writeInlineVideoBytes = (outputPath: string, videoBytes: string): void => {
  fs.writeFileSync(outputPath, Buffer.from(videoBytes, "base64"));
};

export async function generateReferenceImage(prompt: string, outputPath: string): Promise<void> {
  try {
    ensureOutputDir(outputPath);
    const genai = createClient();
    const response = await genai.models.generateImages({
      model: "imagen-4.0-generate-001",
      prompt,
      config: {
        numberOfImages: 1,
        aspectRatio: "1:1",
        outputMimeType: "image/png",
      },
    });

    const imageBytes = response.generatedImages?.[0]?.image?.imageBytes;
    if (!imageBytes) {
      throw new Error("Imagen returned no image data");
    }

    fs.writeFileSync(outputPath, Buffer.from(imageBytes, "base64"));
  } catch (error) {
    throw new Error(
      `Failed to generate reference image via Imagen: ${error instanceof Error ? error.message : String(error)}`,
    );
  }
}

export async function generateVeoClip(
  prompt: string,
  referenceImagePath: string | null,
  aspectRatio: string,
  outputPath: string,
  model = DEFAULT_VEO_MODEL,
): Promise<void> {
  try {
    ensureOutputDir(outputPath);
    const genai = createClient();
    const httpOptions = getRequestHttpOptions();
    const request: GenerateVideosParameters & {
      httpOptions: { timeout: number; apiVersion?: "v1" };
      image?: { imageBytes: string; mimeType: string };
    } = {
      model,
      prompt,
      config: {
        numberOfVideos: 1,
        aspectRatio,
        durationSeconds: 8,
      },
      httpOptions,
    };

    if (referenceImagePath) {
      const imageBytes = fs.readFileSync(referenceImagePath);
      request.image = {
        imageBytes: imageBytes.toString("base64"),
        mimeType: "image/png",
      };
    }

    const operation = await genai.models.generateVideos(request);
    const startTime = Date.now();
    let currentOperation = operation;

    while (!currentOperation.done) {
      if (Date.now() - startTime > OPERATION_TIMEOUT_MS) {
        throw new Error("Timed out after 600s waiting for Veo operation");
      }

      await sleep(POLL_INTERVAL_MS);
      currentOperation = await genai.operations.getVideosOperation({
        operation: currentOperation,
        httpOptions,
      } as Parameters<typeof genai.operations.getVideosOperation>[0] & {
        httpOptions: { timeout: number; apiVersion?: "v1" };
      });
    }

    if (currentOperation.error) {
      throw new Error(`Veo operation failed: ${JSON.stringify(currentOperation.error)}`);
    }

    const generatedVideo = currentOperation.response?.generatedVideos?.[0];
    const video = generatedVideo?.video;
    if (!video) {
      throw new Error("Veo operation completed with no video");
    }

    if (video.videoBytes) {
      writeInlineVideoBytes(outputPath, video.videoBytes);
      return;
    }

    await genai.files.download({
      file: video,
      downloadPath: outputPath,
      httpOptions,
    } as Parameters<typeof genai.files.download>[0] & {
      httpOptions: { timeout: number; apiVersion?: "v1" };
    });
  } catch (error) {
    throw new Error(
      `Failed to generate Veo clip: ${error instanceof Error ? error.message : String(error)}`,
    );
  }
}

export async function extractLastFrame(clipPath: string, outputPath: string): Promise<void> {
  try {
    ensureOutputDir(outputPath);
    await execAsync(
      `ffprobe -v error -show_entries format=duration -of default=noprint_wrappers=1:nokey=1 "${clipPath}"`,
    );
    await execAsync(
      `ffmpeg -y -sseof -0.1 -i "${clipPath}" -vframes 1 -q:v 2 "${outputPath}"`,
    );
  } catch (error) {
    throw new Error(
      `Failed to extract last frame: ${error instanceof Error ? error.message : String(error)}`,
    );
  }
}
