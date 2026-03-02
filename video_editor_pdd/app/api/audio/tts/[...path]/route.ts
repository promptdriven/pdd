import { NextResponse } from "next/server";
import fs from "fs";
import path from "path";
import { Readable } from "stream";

/**
 * GET /api/audio/tts/[...path]
 * Serves WAV audio files from the outputs/tts directory.
 * Supports HTTP Range requests for streaming playback.
 */
export async function GET(
  request: Request,
  { params }: { params: Promise<{ path: string[] }> }
): Promise<NextResponse | Response> {
  try {
    const { path: pathSegments } = await params;

    if (pathSegments.some((s) => s === ".." || s.includes(".."))) {
      return NextResponse.json(
        { error: "Forbidden: path traversal detected" },
        { status: 403 }
      );
    }

    const filePath = path.join(process.cwd(), "outputs", "tts", ...pathSegments);
    const resolved = path.resolve(filePath);
    const allowedRoot = path.resolve("outputs", "tts");

    if (!resolved.startsWith(allowedRoot + path.sep) && resolved !== allowedRoot) {
      return NextResponse.json(
        { error: "Forbidden: path outside allowed directory" },
        { status: 403 }
      );
    }

    if (!fs.existsSync(resolved)) {
      return NextResponse.json({ error: "File not found" }, { status: 404 });
    }

    const stat = fs.statSync(resolved);
    const total = stat.size;
    const ext = path.extname(resolved).toLowerCase();
    const contentType = ext === ".wav" ? "audio/wav" : "application/octet-stream";

    const range = request.headers.get("range");

    if (range) {
      const match = range.match(/bytes=(\d*)-(\d*)/);
      if (!match) {
        return NextResponse.json({ error: "Invalid Range header" }, { status: 400 });
      }

      const startStr = match[1];
      const endStr = match[2];
      let start: number;
      let end: number;

      if (startStr === "" && endStr !== "") {
        start = Math.max(0, total - parseInt(endStr, 10));
        end = total - 1;
      } else if (startStr !== "" && endStr === "") {
        start = parseInt(startStr, 10);
        end = total - 1;
      } else {
        start = parseInt(startStr, 10);
        end = parseInt(endStr, 10);
      }

      if (end >= total) end = total - 1;
      if (start > end || start >= total) {
        return new NextResponse(null, {
          status: 416,
          headers: { "Content-Range": `bytes */${total}` },
        });
      }

      const nodeStream = fs.createReadStream(resolved, { start, end });
      const webStream = Readable.toWeb(nodeStream) as ReadableStream;

      return new Response(webStream, {
        status: 206,
        headers: {
          "Content-Type": contentType,
          "Accept-Ranges": "bytes",
          "Content-Range": `bytes ${start}-${end}/${total}`,
          "Content-Length": String(end - start + 1),
        },
      });
    }

    const nodeStream = fs.createReadStream(resolved);
    const webStream = Readable.toWeb(nodeStream) as ReadableStream;

    return new Response(webStream, {
      status: 200,
      headers: {
        "Content-Type": contentType,
        "Accept-Ranges": "bytes",
        "Content-Length": String(total),
      },
    });
  } catch (error) {
    console.error("Error serving audio file:", error);
    return NextResponse.json({ error: "Internal Server Error" }, { status: 500 });
  }
}
