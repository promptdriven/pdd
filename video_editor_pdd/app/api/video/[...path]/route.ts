import { NextResponse } from "next/server";
import fs from "fs";
import path from "path";
import { Readable } from "stream";

/**
 * GET handler for /api/video/[...path]
 * Serves MP4 video files from allowed directories with HTTP range request support.
 *
 * Allowed root directories:
 *   - outputs/
 *   - remotion/public/
 *
 * Supports:
 *   - 206 Partial Content with Range header
 *   - 200 OK for full file requests (no Range header)
 *   - 404 Not Found if file does not exist
 *   - 403 Forbidden if path traversal is detected
 */
export async function GET(
  request: Request,
  { params }: { params: { path: string[] } }
): Promise<NextResponse> {
  try {
    const pathSegments = params.path;

    // Security check: reject any segment containing ".."
    if (pathSegments.some((segment) => segment === ".." || segment.includes(".."))) {
      return NextResponse.json(
        { error: "Forbidden: path traversal detected" },
        { status: 403 }
      );
    }

    // Reconstruct the file path from the catch-all segments
    const filePath = path.join(process.cwd(), ...pathSegments);
    const resolved = path.resolve(filePath);

    // Define allowed root directories
    const allowed = [
      path.resolve("outputs"),
      path.resolve("remotion/public"),
    ];

    // Verify the resolved path is within an allowed directory
    if (!allowed.some((d) => resolved.startsWith(d + path.sep) || resolved === d)) {
      return NextResponse.json(
        { error: "Forbidden: path outside allowed directories" },
        { status: 403 }
      );
    }

    // Check if the file exists
    if (!fs.existsSync(resolved)) {
      return NextResponse.json(
        { error: "File not found" },
        { status: 404 }
      );
    }

    // Get file stats for total size
    const stat = fs.statSync(resolved);
    const total = stat.size;

    // Common headers for all responses
    const commonHeaders: Record<string, string> = {
      "Content-Type": "video/mp4",
      "Accept-Ranges": "bytes",
    };

    // Parse the Range header
    const range = request.headers.get("range");

    if (range) {
      // Parse "bytes=start-end" format
      const match = range.match(/bytes=(\d*)-(\d*)/);

      if (!match) {
        return NextResponse.json(
          { error: "Invalid Range header" },
          { status: 400 }
        );
      }

      const startStr = match[1];
      const endStr = match[2];

      let start: number;
      let end: number;

      if (startStr === "" && endStr !== "") {
        // Suffix range: bytes=-500 (last 500 bytes)
        const suffixLength = parseInt(endStr, 10);
        start = Math.max(0, total - suffixLength);
        end = total - 1;
      } else if (startStr !== "" && endStr === "") {
        // Open-ended range: bytes=500-
        start = parseInt(startStr, 10);
        end = total - 1;
      } else {
        // Explicit range: bytes=500-999
        start = parseInt(startStr, 10);
        end = parseInt(endStr, 10);
      }

      // Clamp end to file size
      if (end >= total) {
        end = total - 1;
      }

      // Validate range
      if (start > end || start >= total) {
        return new NextResponse(null, {
          status: 416,
          headers: {
            "Content-Range": `bytes */${total}`,
            ...commonHeaders,
          },
        });
      }

      const contentLength = end - start + 1;

      // Create a readable stream for the byte range
      const nodeStream = fs.createReadStream(resolved, { start, end });
      const webStream = Readable.toWeb(nodeStream) as ReadableStream;

      return new NextResponse(webStream, {
        status: 206,
        headers: {
          ...commonHeaders,
          "Content-Range": `bytes ${start}-${end}/${total}`,
          "Content-Length": String(contentLength),
        },
      });
    }

    // No Range header — serve the full file with 200
    const nodeStream = fs.createReadStream(resolved);
    const webStream = Readable.toWeb(nodeStream) as ReadableStream;

    return new NextResponse(webStream, {
      status: 200,
      headers: {
        ...commonHeaders,
        "Content-Length": String(total),
      },
    });
  } catch (error) {
    console.error("Error serving video file:", error);
    return NextResponse.json(
      { error: "Internal Server Error" },
      { status: 500 }
    );
  }
}