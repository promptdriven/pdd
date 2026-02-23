// api_video_route_example.ts
// Runnable example that exercises the GET handler from
// app/api/video/[...path]/route.ts
//
// Verifies all prompt requirements:
//   1. 200 full file with correct headers (no Range header)
//   2. 206 partial content with Range header + Content-Range
//   3. 404 for missing files
//   4. 403 for path traversal (.. segments)
//   5. 403 for paths outside allowed directories
//   6. Content-Type: video/mp4 on all responses
//   7. Accept-Ranges: bytes on all responses

import fs from "fs";
import path from "path";
import { GET } from "../app/api/video/[...path]/route";

// ---------------------------------------------------------------------------
// Setup: create a small test MP4 file in outputs/
// ---------------------------------------------------------------------------
const outputsDir = path.join(process.cwd(), "outputs");
const testFile = path.join(outputsDir, "test-video.mp4");
const FILE_SIZE = 2048; // 2KB dummy file

fs.mkdirSync(outputsDir, { recursive: true });
fs.writeFileSync(testFile, Buffer.alloc(FILE_SIZE, 0xab));

// Also create a file under remotion/public/
const remotionDir = path.join(process.cwd(), "remotion", "public");
const remotionFile = path.join(remotionDir, "preview.mp4");
fs.mkdirSync(remotionDir, { recursive: true });
fs.writeFileSync(remotionFile, Buffer.alloc(512, 0xcd));

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

function makeRequest(urlPath: string, headers?: Record<string, string>): Request {
  return new Request(`http://localhost${urlPath}`, { headers });
}

let passed = 0;
let failed = 0;

function assert(condition: boolean, label: string) {
  if (condition) {
    passed++;
    console.log(`  ✓ ${label}`);
  } else {
    failed++;
    console.error(`  ✗ ${label}`);
  }
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

async function main() {
  console.log("=== Video API Route Example ===\n");

  // --- 1. Full file request (200) ---
  console.log("1. GET full file (no Range header) → 200");
  {
    const req = makeRequest("/api/video/outputs/test-video.mp4");
    const res = await GET(req, { params: { path: ["outputs", "test-video.mp4"] } });
    assert(res.status === 200, `status is 200 (got ${res.status})`);
    assert(res.headers.get("content-type") === "video/mp4", "Content-Type: video/mp4");
    assert(res.headers.get("accept-ranges") === "bytes", "Accept-Ranges: bytes");
    assert(res.headers.get("content-length") === String(FILE_SIZE), `Content-Length: ${FILE_SIZE}`);
  }

  // --- 2. Range request (206) ---
  console.log("\n2. GET with Range header → 206 Partial Content");
  {
    const req = makeRequest("/api/video/outputs/test-video.mp4", {
      Range: "bytes=0-511",
    });
    const res = await GET(req, { params: { path: ["outputs", "test-video.mp4"] } });
    assert(res.status === 206, `status is 206 (got ${res.status})`);
    assert(
      res.headers.get("content-range") === `bytes 0-511/${FILE_SIZE}`,
      `Content-Range: bytes 0-511/${FILE_SIZE}`
    );
    assert(res.headers.get("content-length") === "512", "Content-Length: 512");
    assert(res.headers.get("content-type") === "video/mp4", "Content-Type: video/mp4");
    assert(res.headers.get("accept-ranges") === "bytes", "Accept-Ranges: bytes");
  }

  // --- 3. Open-ended range (206) ---
  console.log("\n3. GET with open-ended Range → 206");
  {
    const req = makeRequest("/api/video/outputs/test-video.mp4", {
      Range: "bytes=1024-",
    });
    const res = await GET(req, { params: { path: ["outputs", "test-video.mp4"] } });
    assert(res.status === 206, `status is 206 (got ${res.status})`);
    assert(
      res.headers.get("content-range") === `bytes 1024-${FILE_SIZE - 1}/${FILE_SIZE}`,
      `Content-Range: bytes 1024-${FILE_SIZE - 1}/${FILE_SIZE}`
    );
  }

  // --- 4. 404 for missing file ---
  console.log("\n4. GET missing file → 404");
  {
    const req = makeRequest("/api/video/outputs/nonexistent.mp4");
    const res = await GET(req, { params: { path: ["outputs", "nonexistent.mp4"] } });
    assert(res.status === 404, `status is 404 (got ${res.status})`);
  }

  // --- 5. 403 for path traversal ---
  console.log("\n5. GET with path traversal → 403");
  {
    const req = makeRequest("/api/video/outputs/../../../etc/passwd");
    const res = await GET(req, { params: { path: ["outputs", "..", "..", "..", "etc", "passwd"] } });
    assert(res.status === 403, `status is 403 (got ${res.status})`);
  }

  // --- 6. 403 for path outside allowed directories ---
  console.log("\n6. GET outside allowed dirs → 403");
  {
    const req = makeRequest("/api/video/src/secret.mp4");
    const res = await GET(req, { params: { path: ["src", "secret.mp4"] } });
    assert(res.status === 403, `status is 403 (got ${res.status})`);
  }

  // --- 7. File from remotion/public/ (200) ---
  console.log("\n7. GET from remotion/public/ → 200");
  {
    const req = makeRequest("/api/video/remotion/public/preview.mp4");
    const res = await GET(req, { params: { path: ["remotion", "public", "preview.mp4"] } });
    assert(res.status === 200, `status is 200 (got ${res.status})`);
    assert(res.headers.get("content-type") === "video/mp4", "Content-Type: video/mp4");
    assert(res.headers.get("accept-ranges") === "bytes", "Accept-Ranges: bytes");
  }

  // --- Cleanup ---
  fs.unlinkSync(testFile);
  fs.unlinkSync(remotionFile);
  // Remove dirs only if empty
  try { fs.rmdirSync(outputsDir); } catch {}
  try { fs.rmdirSync(remotionDir); } catch {}
  try { fs.rmdirSync(path.join(process.cwd(), "remotion")); } catch {}

  // --- Summary ---
  console.log(`\n=== Results: ${passed} passed, ${failed} failed ===`);
  if (failed > 0) {
    process.exit(1);
  }
}

main().catch((err) => {
  console.error("Fatal error:", err);
  process.exit(1);
});
