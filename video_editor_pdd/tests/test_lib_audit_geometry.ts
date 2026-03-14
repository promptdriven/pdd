import fs from "fs";
import os from "os";
import path from "path";
import zlib from "zlib";

import { evaluateDeterministicGeometryAudit } from "../lib/audit-geometry";

const PNG_SIGNATURE = Buffer.from([
  0x89, 0x50, 0x4e, 0x47, 0x0d, 0x0a, 0x1a, 0x0a,
]);

const makeChunk = (type: string, data: Buffer): Buffer => {
  const length = Buffer.alloc(4);
  length.writeUInt32BE(data.length, 0);
  const chunkType = Buffer.from(type, "ascii");
  const crc = Buffer.alloc(4);
  return Buffer.concat([length, chunkType, data, crc]);
};

const hexToRgb = (hex: string) => {
  const normalized = hex.replace(/^#/, "");
  return {
    r: Number.parseInt(normalized.slice(0, 2), 16),
    g: Number.parseInt(normalized.slice(2, 4), 16),
    b: Number.parseInt(normalized.slice(4, 6), 16),
  };
};

const writeSolidShapePng = (
  filePath: string,
  width: number,
  height: number,
  shapes: Array<{
    left: number;
    top: number;
    width: number;
    height: number;
    color: string;
  }>
) => {
  const rgba = Buffer.alloc(width * height * 4, 0);

  for (const shape of shapes) {
    const color = hexToRgb(shape.color);
    for (let y = shape.top; y < shape.top + shape.height; y += 1) {
      for (let x = shape.left; x < shape.left + shape.width; x += 1) {
        const offset = (y * width + x) * 4;
        rgba[offset] = color.r;
        rgba[offset + 1] = color.g;
        rgba[offset + 2] = color.b;
        rgba[offset + 3] = 255;
      }
    }
  }

  const rows: Buffer[] = [];
  for (let y = 0; y < height; y += 1) {
    const row = rgba.subarray(y * width * 4, (y + 1) * width * 4);
    rows.push(Buffer.concat([Buffer.from([0]), row]));
  }

  const ihdr = Buffer.alloc(13);
  ihdr.writeUInt32BE(width, 0);
  ihdr.writeUInt32BE(height, 4);
  ihdr.writeUInt8(8, 8);
  ihdr.writeUInt8(6, 9);
  ihdr.writeUInt8(0, 10);
  ihdr.writeUInt8(0, 11);
  ihdr.writeUInt8(0, 12);

  const png = Buffer.concat([
    PNG_SIGNATURE,
    makeChunk("IHDR", ihdr),
    makeChunk("IDAT", zlib.deflateSync(Buffer.concat(rows))),
    makeChunk("IEND", Buffer.alloc(0)),
  ]);

  fs.writeFileSync(filePath, png);
};

describe("lib/audit-geometry", () => {
  let tmpDir: string;

  beforeEach(() => {
    tmpDir = fs.mkdtempSync(path.join(os.tmpdir(), "audit-geometry-"));
  });

  afterEach(() => {
    fs.rmSync(tmpDir, { recursive: true, force: true });
  });

  it("passes a horizontal slide visual when the rendered shape is at the expected endpoint", () => {
    const pngPath = path.join(tmpDir, "slide.png");
    writeSolidShapePng(pngPath, 200, 120, [
      { left: 132, top: 40, width: 24, height: 24, color: "#6366F1" },
    ]);

    const result = evaluateDeterministicGeometryAudit(
      [
        "## Data Points",
        "```json",
        '{ "endX": 144, "squareSize": 24, "color": "#6366F1" }',
        "```",
      ].join("\n"),
      pngPath
    );

    expect(result).toEqual(
      expect.objectContaining({
        verdict: "pass",
        check: "horizontal-slide",
      })
    );
  });

  it("passes a horizontal slide visual when the contract uses nested slide data and the shape color is only present in spec prose", () => {
    const pngPath = path.join(tmpDir, "nested-slide.png");
    writeSolidShapePng(pngPath, 200, 120, [
      { left: 132, top: 40, width: 24, height: 24, color: "#6366F1" },
    ]);

    const result = evaluateDeterministicGeometryAudit(
      [
        "### Chart/Visual Elements",
        "- Square: 24x24px, fill #6366F1",
        "",
        "## Data Points",
        "```json",
        '{ "slide": { "toX": 144, "y": 60 } }',
        "```",
      ].join("\n"),
      pngPath
    );

    expect(result).toEqual(
      expect.objectContaining({
        verdict: "pass",
        check: "horizontal-slide",
      })
    );
  });

  it("passes a split-panel visual when both shape centroids are in the expected halves", () => {
    const pngPath = path.join(tmpDir, "split.png");
    writeSolidShapePng(pngPath, 200, 120, [
      { left: 40, top: 48, width: 20, height: 20, color: "#3B82F6" },
      { left: 140, top: 42, width: 24, height: 24, color: "#6366F1" },
    ]);

    const result = evaluateDeterministicGeometryAudit(
      [
        "## Data Points",
        "```json",
        [
          "{",
          '  "leftPanel": { "color": "#3B82F6", "shape": "circle" },',
          '  "rightPanel": { "color": "#6366F1", "shape": "roundedSquare" }',
          "}",
        ].join("\n"),
        "```",
      ].join("\n"),
      pngPath
    );

    expect(result).toEqual(
      expect.objectContaining({
        verdict: "pass",
        check: "split-panels",
      })
    );
  });

  it("returns null when the rendered geometry does not satisfy the structured contract", () => {
    const pngPath = path.join(tmpDir, "mismatch.png");
    writeSolidShapePng(pngPath, 200, 120, [
      { left: 12, top: 10, width: 20, height: 20, color: "#3B82F6" },
    ]);

    const result = evaluateDeterministicGeometryAudit(
      [
        "## Data Points",
        "```json",
        '{ "endX": 144, "squareSize": 24, "color": "#6366F1" }',
        "```",
      ].join("\n"),
      pngPath
    );

    expect(result).toBeNull();
  });
});
