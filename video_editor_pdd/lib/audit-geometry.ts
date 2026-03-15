import fs from "fs";
import zlib from "zlib";

type Rgb = {
  r: number;
  g: number;
  b: number;
};

type DecodedPng = {
  width: number;
  height: number;
  rgba: Uint8Array;
};

export type DeterministicGeometryAuditResult = {
  verdict: "pass";
  summary: string;
  check:
    | "horizontal-slide"
    | "split-panels"
    | "centered-shape"
    | "vertical-divider"
    | "pipeline-nodes";
};

const PNG_SIGNATURE = Buffer.from([
  0x89, 0x50, 0x4e, 0x47, 0x0d, 0x0a, 0x1a, 0x0a,
]);

const DATA_POINTS_RE = /##\s*Data Points\s*```json\s*([\s\S]+?)\s*```/i;
const COLOR_IN_SPEC_RE =
  /\b(?:fill|stroke|color)\s*(?:=|:)?\s*["']?(#(?:[0-9a-f]{6}))["']?/gi;
const CENTER_COORDINATE_RE =
  /centered\s+at\s*\(\s*(\d+(?:\.\d+)?)\s*,\s*(\d+(?:\.\d+)?)\s*\)/i;
const PIPELINE_NODE_CENTER_RE =
  /\*\*Node\s+\d+[^:]*:\*\*[\s\S]*?centered\s+at\s+x=(\d+(?:\.\d+)?),\s*y=(\d+(?:\.\d+)?)/gi;

const extractDataPoints = (specContent: string): unknown | null => {
  const match = specContent.match(DATA_POINTS_RE);
  if (!match) {
    return null;
  }

  try {
    return JSON.parse(match[1]);
  } catch {
    return null;
  }
};

const parseHexColor = (value: string | undefined): Rgb | null => {
  if (!value) {
    return null;
  }

  const normalized = value.trim().replace(/^#/, "");
  if (!/^[0-9a-f]{6}$/i.test(normalized)) {
    return null;
  }

  return {
    r: Number.parseInt(normalized.slice(0, 2), 16),
    g: Number.parseInt(normalized.slice(2, 4), 16),
    b: Number.parseInt(normalized.slice(4, 6), 16),
  };
};

const resolveShapeColor = (
  specContent: string,
  dataPoints: Record<string, unknown>
): Rgb | null => {
  const shape =
    dataPoints.shape && typeof dataPoints.shape === "object"
      ? (dataPoints.shape as Record<string, unknown>)
      : null;
  const circle =
    dataPoints.circle && typeof dataPoints.circle === "object"
      ? (dataPoints.circle as Record<string, unknown>)
      : null;
  const shapeColor =
    shape && typeof shape.color === "string"
      ? parseHexColor(shape.color)
      : shape && typeof shape.colorEnd === "string"
        ? parseHexColor(shape.colorEnd)
        : shape && typeof shape.colorStart === "string"
          ? parseHexColor(shape.colorStart)
          : null;
  if (shapeColor) {
    return shapeColor;
  }

  const circleColor =
    circle && typeof circle.color === "string"
      ? parseHexColor(circle.color)
      : circle && typeof circle.colorEnd === "string"
        ? parseHexColor(circle.colorEnd)
        : circle && typeof circle.colorStart === "string"
          ? parseHexColor(circle.colorStart)
          : null;
  if (circleColor) {
    return circleColor;
  }

  const topLevelColor =
    typeof dataPoints.color === "string" ? parseHexColor(dataPoints.color) : null;
  if (topLevelColor) {
    return topLevelColor;
  }

  const slide =
    dataPoints.slide && typeof dataPoints.slide === "object"
      ? (dataPoints.slide as Record<string, unknown>)
      : null;
  const slideColor =
    slide && typeof slide.color === "string"
      ? parseHexColor(slide.color)
      : null;
  if (slideColor) {
    return slideColor;
  }

  const proseMatch = [...specContent.matchAll(COLOR_IN_SPEC_RE)].pop();
  return proseMatch?.[1] ? parseHexColor(proseMatch[1]) : null;
};

const paethPredictor = (a: number, b: number, c: number): number => {
  const p = a + b - c;
  const pa = Math.abs(p - a);
  const pb = Math.abs(p - b);
  const pc = Math.abs(p - c);

  if (pa <= pb && pa <= pc) {
    return a;
  }
  if (pb <= pc) {
    return b;
  }
  return c;
};

const decodePng = (filePath: string): DecodedPng | null => {
  const buffer = fs.readFileSync(filePath);
  if (buffer.length < PNG_SIGNATURE.length || !buffer.subarray(0, 8).equals(PNG_SIGNATURE)) {
    return null;
  }

  let width = 0;
  let height = 0;
  let bitDepth = 0;
  let colorType = 0;
  const idatChunks: Buffer[] = [];

  let offset = PNG_SIGNATURE.length;
  while (offset + 12 <= buffer.length) {
    const chunkLength = buffer.readUInt32BE(offset);
    const type = buffer.subarray(offset + 4, offset + 8).toString("ascii");
    const dataStart = offset + 8;
    const dataEnd = dataStart + chunkLength;
    if (dataEnd + 4 > buffer.length) {
      return null;
    }
    const data = buffer.subarray(dataStart, dataEnd);
    offset = dataEnd + 4;

    if (type === "IHDR") {
      width = data.readUInt32BE(0);
      height = data.readUInt32BE(4);
      bitDepth = data.readUInt8(8);
      colorType = data.readUInt8(9);
    } else if (type === "IDAT") {
      idatChunks.push(data);
    } else if (type === "IEND") {
      break;
    }
  }

  if (!width || !height || bitDepth !== 8 || idatChunks.length === 0) {
    return null;
  }

  const bytesPerPixel = colorType === 6 ? 4 : colorType === 2 ? 3 : null;
  if (!bytesPerPixel) {
    return null;
  }

  const stride = width * bytesPerPixel;
  const inflated = zlib.inflateSync(Buffer.concat(idatChunks));
  const expectedLength = height * (stride + 1);
  if (inflated.length < expectedLength) {
    return null;
  }

  const rgba = new Uint8Array(width * height * 4);
  let readOffset = 0;
  const priorRow = new Uint8Array(stride);

  for (let y = 0; y < height; y += 1) {
    const filterType = inflated.readUInt8(readOffset);
    readOffset += 1;
    const row = inflated.subarray(readOffset, readOffset + stride);
    readOffset += stride;
    const unfiltered = new Uint8Array(stride);

    for (let x = 0; x < stride; x += 1) {
      const left = x >= bytesPerPixel ? unfiltered[x - bytesPerPixel] : 0;
      const up = priorRow[x] ?? 0;
      const upLeft = x >= bytesPerPixel ? priorRow[x - bytesPerPixel] ?? 0 : 0;

      switch (filterType) {
        case 0:
          unfiltered[x] = row[x];
          break;
        case 1:
          unfiltered[x] = (row[x] + left) & 0xff;
          break;
        case 2:
          unfiltered[x] = (row[x] + up) & 0xff;
          break;
        case 3:
          unfiltered[x] = (row[x] + Math.floor((left + up) / 2)) & 0xff;
          break;
        case 4:
          unfiltered[x] = (row[x] + paethPredictor(left, up, upLeft)) & 0xff;
          break;
        default:
          return null;
      }
    }

    priorRow.set(unfiltered);

    for (let x = 0; x < width; x += 1) {
      const srcOffset = x * bytesPerPixel;
      const destOffset = (y * width + x) * 4;
      rgba[destOffset] = unfiltered[srcOffset];
      rgba[destOffset + 1] = unfiltered[srcOffset + 1];
      rgba[destOffset + 2] = unfiltered[srcOffset + 2];
      rgba[destOffset + 3] = bytesPerPixel === 4 ? unfiltered[srcOffset + 3] : 255;
    }
  }

  return { width, height, rgba };
};

const findColorCentroid = (
  decoded: DecodedPng,
  color: Rgb,
  tolerance = 56
): { x: number; y: number; count: number } | null => {
  let weightedX = 0;
  let weightedY = 0;
  let count = 0;

  for (let y = 0; y < decoded.height; y += 1) {
    for (let x = 0; x < decoded.width; x += 1) {
      const offset = (y * decoded.width + x) * 4;
      const alpha = decoded.rgba[offset + 3] ?? 0;
      if (alpha < 32) {
        continue;
      }

      const dr = Math.abs((decoded.rgba[offset] ?? 0) - color.r);
      const dg = Math.abs((decoded.rgba[offset + 1] ?? 0) - color.g);
      const db = Math.abs((decoded.rgba[offset + 2] ?? 0) - color.b);
      if (dr + dg + db > tolerance) {
        continue;
      }

      weightedX += x;
      weightedY += y;
      count += 1;
    }
  }

  if (!count) {
    return null;
  }

  return {
    x: weightedX / count,
    y: weightedY / count,
    count,
  };
};

const luminance = (r: number, g: number, b: number): number =>
  0.2126 * r + 0.7152 * g + 0.0722 * b;

const estimateCornerBackgroundLuminance = (decoded: DecodedPng): number => {
  const sampleSize = Math.max(2, Math.min(12, Math.floor(Math.min(decoded.width, decoded.height) * 0.05)));
  const corners = [
    { startX: 0, startY: 0 },
    { startX: Math.max(0, decoded.width - sampleSize), startY: 0 },
    { startX: 0, startY: Math.max(0, decoded.height - sampleSize) },
    {
      startX: Math.max(0, decoded.width - sampleSize),
      startY: Math.max(0, decoded.height - sampleSize),
    },
  ];

  let total = 0;
  let count = 0;
  for (const corner of corners) {
    for (let y = corner.startY; y < corner.startY + sampleSize; y += 1) {
      for (let x = corner.startX; x < corner.startX + sampleSize; x += 1) {
        const offset = (y * decoded.width + x) * 4;
        total += luminance(
          decoded.rgba[offset] ?? 0,
          decoded.rgba[offset + 1] ?? 0,
          decoded.rgba[offset + 2] ?? 0
        );
        count += 1;
      }
    }
  }

  return count > 0 ? total / count : 0;
};

const findLuminousClusterInBox = (
  decoded: DecodedPng,
  bounds: { left: number; right: number; top: number; bottom: number }
): { x: number; y: number; count: number } | null => {
  const backgroundLuminance = estimateCornerBackgroundLuminance(decoded);
  const threshold = backgroundLuminance + 28;
  let weightedX = 0;
  let weightedY = 0;
  let count = 0;

  for (let y = Math.max(0, bounds.top); y < Math.min(decoded.height, bounds.bottom); y += 1) {
    for (let x = Math.max(0, bounds.left); x < Math.min(decoded.width, bounds.right); x += 1) {
      const offset = (y * decoded.width + x) * 4;
      const alpha = decoded.rgba[offset + 3] ?? 0;
      if (alpha < 32) {
        continue;
      }

      const lum = luminance(
        decoded.rgba[offset] ?? 0,
        decoded.rgba[offset + 1] ?? 0,
        decoded.rgba[offset + 2] ?? 0
      );
      if (lum < threshold) {
        continue;
      }

      const weight = Math.max(1, lum - backgroundLuminance);
      weightedX += x * weight;
      weightedY += y * weight;
      count += weight;
    }
  }

  if (count < 20) {
    return null;
  }

  return {
    x: weightedX / count,
    y: weightedY / count,
    count,
  };
};

const resolveExpectedCenter = (
  specContent: string,
  dataPoints: Record<string, unknown>,
  decoded: DecodedPng
): { x: number; y: number } | null => {
  const shape =
    dataPoints.shape && typeof dataPoints.shape === "object"
      ? (dataPoints.shape as Record<string, unknown>)
      : null;
  const circle =
    dataPoints.circle && typeof dataPoints.circle === "object"
      ? (dataPoints.circle as Record<string, unknown>)
      : null;
  const centerX =
    typeof dataPoints.centerX === "number"
      ? dataPoints.centerX
      : shape && typeof shape.centerX === "number"
        ? shape.centerX
        : circle && typeof circle.centerX === "number"
          ? circle.centerX
        : null;
  const centerY =
    typeof dataPoints.centerY === "number"
      ? dataPoints.centerY
      : shape && typeof shape.centerY === "number"
        ? shape.centerY
        : circle && typeof circle.centerY === "number"
          ? circle.centerY
        : null;

  if (centerX != null && centerY != null) {
    return { x: centerX, y: centerY };
  }

  const coordinateMatch = specContent.match(CENTER_COORDINATE_RE);
  if (coordinateMatch) {
    return {
      x: Number(coordinateMatch[1]),
      y: Number(coordinateMatch[2]),
    };
  }

  if (!/\bcentered\b/i.test(specContent)) {
    return null;
  }

  return {
    x: decoded.width / 2,
    y: decoded.height / 2,
  };
};

const evaluateHorizontalSlide = (
  specContent: string,
  dataPoints: Record<string, unknown>,
  decoded: DecodedPng
): DeterministicGeometryAuditResult | null => {
  const slide =
    dataPoints.slide && typeof dataPoints.slide === "object"
      ? (dataPoints.slide as Record<string, unknown>)
      : null;
  const endX =
    typeof dataPoints.endX === "number"
      ? dataPoints.endX
      : slide && typeof slide.toX === "number"
        ? slide.toX
        : null;
  const expectedY =
    slide && typeof slide.y === "number" ? slide.y : decoded.height / 2;
  const color = resolveShapeColor(specContent, dataPoints);

  if (!endX || !color) {
    return null;
  }

  const centroid = findColorCentroid(decoded, color);
  if (!centroid) {
    return null;
  }

  const toleranceX = Math.max(decoded.width * 0.03, 24);
  const toleranceY = Math.max(decoded.height * 0.03, 24);
  if (
    Math.abs(centroid.x - endX) <= toleranceX &&
    Math.abs(centroid.y - expectedY) <= toleranceY
  ) {
    return {
      verdict: "pass",
      check: "horizontal-slide",
      summary: `Deterministic geometry check confirmed the primary shape is centered near (${endX.toFixed(
        0
      )}, ${expectedY.toFixed(0)}).`,
    };
  }

  return null;
};

const evaluateSplitPanels = (
  dataPoints: Record<string, unknown>,
  decoded: DecodedPng
): DeterministicGeometryAuditResult | null => {
  const leftPanel =
    dataPoints.leftPanel && typeof dataPoints.leftPanel === "object"
      ? (dataPoints.leftPanel as Record<string, unknown>)
      : null;
  const rightPanel =
    dataPoints.rightPanel && typeof dataPoints.rightPanel === "object"
      ? (dataPoints.rightPanel as Record<string, unknown>)
      : null;
  const leftColor =
    leftPanel && typeof leftPanel.color === "string"
      ? parseHexColor(leftPanel.color)
      : null;
  const rightColor =
    rightPanel && typeof rightPanel.color === "string"
      ? parseHexColor(rightPanel.color)
      : null;

  if (!leftColor || !rightColor) {
    return null;
  }

  const leftCentroid = findColorCentroid(decoded, leftColor);
  const rightCentroid = findColorCentroid(decoded, rightColor);
  if (!leftCentroid || !rightCentroid) {
    return null;
  }

  const expectedLeftX = decoded.width * 0.25;
  const expectedRightX = decoded.width * 0.75;
  const expectedY = decoded.height * 0.5;
  const toleranceX = Math.max(decoded.width * 0.08, 32);
  const toleranceY = Math.max(decoded.height * 0.08, 32);

  const leftOk =
    Math.abs(leftCentroid.x - expectedLeftX) <= toleranceX &&
    Math.abs(leftCentroid.y - expectedY) <= toleranceY;
  const rightOk =
    Math.abs(rightCentroid.x - expectedRightX) <= toleranceX &&
    Math.abs(rightCentroid.y - expectedY) <= toleranceY;

  if (leftOk && rightOk) {
    return {
      verdict: "pass",
      check: "split-panels",
      summary:
        "Deterministic geometry check confirmed both split-panel shapes are centered in their expected left/right halves.",
    };
  }

  return null;
};

const evaluateCenteredShape = (
  specContent: string,
  dataPoints: Record<string, unknown>,
  decoded: DecodedPng
): DeterministicGeometryAuditResult | null => {
  const shape =
    dataPoints.shape && typeof dataPoints.shape === "object"
      ? (dataPoints.shape as Record<string, unknown>)
      : null;
  const circle =
    dataPoints.circle && typeof dataPoints.circle === "object"
      ? (dataPoints.circle as Record<string, unknown>)
      : null;
  if (!shape && !circle) {
    return null;
  }

  const color = resolveShapeColor(specContent, dataPoints);
  const expectedCenter = resolveExpectedCenter(specContent, dataPoints, decoded);
  if (!color || !expectedCenter) {
    return null;
  }

  const centroid = findColorCentroid(decoded, color);
  if (!centroid) {
    return null;
  }

  const toleranceX = Math.max(decoded.width * 0.03, 24);
  const toleranceY = Math.max(decoded.height * 0.03, 24);
  if (
    Math.abs(centroid.x - expectedCenter.x) <= toleranceX &&
    Math.abs(centroid.y - expectedCenter.y) <= toleranceY
  ) {
    return {
      verdict: "pass",
      check: "centered-shape",
      summary: `Deterministic geometry check confirmed the primary shape is centered near (${expectedCenter.x.toFixed(
        0
      )}, ${expectedCenter.y.toFixed(0)}).`,
    };
  }

  return null;
};

const evaluateVerticalDivider = (
  dataPoints: Record<string, unknown>,
  decoded: DecodedPng
): DeterministicGeometryAuditResult | null => {
  const divider =
    dataPoints.divider && typeof dataPoints.divider === "object"
      ? (dataPoints.divider as Record<string, unknown>)
      : null;
  const endX =
    divider && typeof divider.endX === "number" ? divider.endX : null;
  const color =
    divider && typeof divider.color === "string"
      ? parseHexColor(divider.color)
      : null;

  if (!endX || !color) {
    return null;
  }

  const centroid = findColorCentroid(decoded, color);
  if (!centroid) {
    return null;
  }

  const toleranceX = Math.max(decoded.width * 0.03, 24);
  if (Math.abs(centroid.x - endX) <= toleranceX) {
    return {
      verdict: "pass",
      check: "vertical-divider",
      summary: `Deterministic geometry check confirmed the divider is resting near x=${endX.toFixed(
        0
      )}.`,
    };
  }

  return null;
};

const resolvePipelineAnchors = (
  specContent: string,
  dataPoints: Record<string, unknown>,
  decoded: DecodedPng
): Array<{ x: number; y: number }> => {
  const steps = Array.isArray(dataPoints.pipeline_steps) ? dataPoints.pipeline_steps : [];
  const proseCenters = [...specContent.matchAll(PIPELINE_NODE_CENTER_RE)].map((match) => ({
    x: Number(match[1]),
    y: Number(match[2]),
  }));

  return steps
    .map((step, index) => {
      if (!step || typeof step !== "object" || Array.isArray(step)) {
        return null;
      }
      const record = step as Record<string, unknown>;
      const x = typeof record.x === "number" ? record.x : null;
      const y =
        typeof record.y === "number"
          ? record.y
          : proseCenters[index]?.y ?? decoded.height * 0.45;
      if (x == null) {
        return null;
      }
      return { x, y };
    })
    .filter((anchor): anchor is { x: number; y: number } => anchor !== null);
};

const evaluatePipelineNodes = (
  specContent: string,
  dataPoints: Record<string, unknown>,
  decoded: DecodedPng
): DeterministicGeometryAuditResult | null => {
  const anchors = resolvePipelineAnchors(specContent, dataPoints, decoded);
  if (anchors.length < 3) {
    return null;
  }

  const gaps = anchors.slice(1).map((anchor, index) => anchor.x - anchors[index].x);
  const minGap = gaps.length > 0 ? Math.min(...gaps) : decoded.width / 4;
  const halfWidth = Math.max(24, Math.round(minGap * 0.28));
  const halfHeight = Math.max(24, Math.round(decoded.height * 0.12));
  const toleranceX = Math.max(decoded.width * 0.04, 36);
  const toleranceY = Math.max(decoded.height * 0.08, 42);

  const clusters = anchors.map((anchor) =>
    findLuminousClusterInBox(decoded, {
      left: Math.round(anchor.x - halfWidth),
      right: Math.round(anchor.x + halfWidth),
      top: Math.round(anchor.y - halfHeight),
      bottom: Math.round(anchor.y + halfHeight),
    })
  );

  if (clusters.some((cluster) => cluster == null)) {
    return null;
  }

  const allClusters = clusters as Array<{ x: number; y: number; count: number }>;
  const aligned = allClusters.every((cluster, index) => {
    const anchor = anchors[index];
    return (
      Math.abs(cluster.x - anchor.x) <= toleranceX &&
      Math.abs(cluster.y - anchor.y) <= toleranceY
    );
  });

  if (!aligned) {
    return null;
  }

  return {
    verdict: "pass",
    check: "pipeline-nodes",
    summary:
      "Deterministic geometry check confirmed the infographic nodes are distributed at the expected left, center, and right anchors.",
  };
};

export function evaluateDeterministicGeometryAudit(
  specContent: string,
  pngPath: string
): DeterministicGeometryAuditResult | null {
  const dataPoints = extractDataPoints(specContent);
  if (!dataPoints || typeof dataPoints !== "object") {
    return null;
  }

  const decoded = decodePng(pngPath);
  if (!decoded) {
    return null;
  }

  return (
    evaluateSplitPanels(dataPoints as Record<string, unknown>, decoded) ??
    evaluatePipelineNodes(specContent, dataPoints as Record<string, unknown>, decoded) ??
    evaluateVerticalDivider(dataPoints as Record<string, unknown>, decoded) ??
    evaluateHorizontalSlide(specContent, dataPoints as Record<string, unknown>, decoded) ??
    evaluateCenteredShape(specContent, dataPoints as Record<string, unknown>, decoded)
  );
}
