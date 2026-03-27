import React from 'react';
import {
  AbsoluteFill,
  Sequence,
  useCurrentFrame,
  interpolate,
  Easing,
} from 'remotion';
import {
  CANVAS_WIDTH,
  CANVAS_HEIGHT,
  BACKGROUND_COLOR,
  TOTAL_FRAMES,
  WALL_LABELS,
  WALL_SEGMENT_POSITIONS,
  ZOOM_START,
  ZOOM_END,
  ZOOM_FROM,
  ZOOM_TO,
  WALL_COLOR,
  MOLD_STROKE_COLOR,
  MOLD_STROKE_WIDTH,
  MOLD_OUTER_WIDTH,
  MOLD_OUTER_HEIGHT,
  MOLD_INNER_WIDTH,
  MOLD_INNER_HEIGHT,
  NOZZLE_WIDTH,
  NOZZLE_HEIGHT,
  DIMMED_OPACITY,
  GRID_SPACING,
  GRID_COLOR,
  GRID_OPACITY,
  WALL_GLOW_MIN,
  WALL_GLOW_MAX,
  WALL_SEGMENT_WIDTH,
  LABEL_FONT_FAMILY,
  LABEL_FONT_SIZE,
  LABEL_FONT_WEIGHT,
  LABEL_TEXT_COLOR,
  LABEL_PILL_COLOR,
  LABEL_PILL_OPACITY,
  LABEL_PILL_RADIUS,
  LABEL_PILL_PADDING_H,
  CONNECTOR_COLOR,
  CONNECTOR_OPACITY,
  CONNECTOR_WIDTH,
  SEGMENT_BRIGHTEN_DURATION,
  LABEL_FADE_DURATION,
  CONNECTOR_DRAW_DURATION,
  LABEL_DELAY_AFTER_SEGMENT,
} from './constants';

// ─── Default Props ────────────────────────────────────────────────
export const defaultPart3MoldParts03MoldWallsIlluminateProps = {};

// ─── Blueprint Grid (inline) ─────────────────────────────────────
const BlueprintGridSVG: React.FC = () => {
  const lines: React.ReactNode[] = [];
  for (let x = 0; x <= CANVAS_WIDTH; x += GRID_SPACING) {
    lines.push(
      <line
        key={`v${x}`}
        x1={x} y1={0} x2={x} y2={CANVAS_HEIGHT}
        stroke={GRID_COLOR} strokeWidth={1} opacity={GRID_OPACITY}
      />
    );
  }
  for (let y = 0; y <= CANVAS_HEIGHT; y += GRID_SPACING) {
    lines.push(
      <line
        key={`h${y}`}
        x1={0} y1={y} x2={CANVAS_WIDTH} y2={y}
        stroke={GRID_COLOR} strokeWidth={1} opacity={GRID_OPACITY}
      />
    );
  }
  return <>{lines}</>;
};

// ─── Single Wall Segment + Label ─────────────────────────────────
interface WallSegmentWithLabelProps {
  label: string;
  side: 'left' | 'right';
  yOffset: number;
}

const WallSegmentWithLabel: React.FC<WallSegmentWithLabelProps> = ({
  label,
  side,
  yOffset,
}) => {
  const frame = useCurrentFrame(); // relative to enclosing <Sequence>

  const cx = CANVAS_WIDTH / 2;
  const cy = CANVAS_HEIGHT / 2;
  const innerHalfW = MOLD_INNER_WIDTH / 2;
  const segmentHalfH = 50;

  const wallX = side === 'left' ? cx - innerHalfW : cx + innerHalfW;
  const wallY = cy + yOffset;

  // Segment glow
  const glow = interpolate(frame, [0, SEGMENT_BRIGHTEN_DURATION], [WALL_GLOW_MIN, WALL_GLOW_MAX], {
    easing: Easing.out(Easing.quad),
    extrapolateLeft: 'clamp',
    extrapolateRight: 'clamp',
  });

  // Connector draw
  const connProg = interpolate(
    frame,
    [LABEL_DELAY_AFTER_SEGMENT, LABEL_DELAY_AFTER_SEGMENT + CONNECTOR_DRAW_DURATION],
    [0, 1],
    { easing: Easing.out(Easing.quad), extrapolateLeft: 'clamp', extrapolateRight: 'clamp' }
  );

  // Label fade
  const labelOp = interpolate(
    frame,
    [LABEL_DELAY_AFTER_SEGMENT, LABEL_DELAY_AFTER_SEGMENT + LABEL_FADE_DURATION],
    [0, 1],
    { easing: Easing.out(Easing.quad), extrapolateLeft: 'clamp', extrapolateRight: 'clamp' }
  );

  // Label placement
  const connLength = 100;
  const direction = side === 'left' ? -1 : 1;
  const connEndX = wallX + direction * connLength;
  const currEndX = wallX + direction * connLength * connProg;

  // Pill dimensions
  const pillW = label.length * 8.2 + LABEL_PILL_PADDING_H * 2;
  const pillH = 28;
  const pillX = side === 'left' ? connEndX - pillW - 6 : connEndX + 6;
  const pillY = wallY - pillH / 2;

  return (
    <g>
      {/* Segment glow (broad) */}
      <line
        x1={wallX} y1={wallY - segmentHalfH}
        x2={wallX} y2={wallY + segmentHalfH}
        stroke={WALL_COLOR} strokeWidth={10}
        opacity={glow * 0.25} strokeLinecap="round"
      />
      {/* Segment core */}
      <line
        x1={wallX} y1={wallY - segmentHalfH}
        x2={wallX} y2={wallY + segmentHalfH}
        stroke={WALL_COLOR} strokeWidth={WALL_SEGMENT_WIDTH}
        opacity={glow}
      />

      {/* Connector dashed line */}
      <line
        x1={wallX} y1={wallY}
        x2={currEndX} y2={wallY}
        stroke={CONNECTOR_COLOR} strokeWidth={CONNECTOR_WIDTH}
        strokeDasharray="4 3"
        opacity={CONNECTOR_OPACITY * connProg}
      />

      {/* Label pill + text */}
      <g opacity={labelOp}>
        <rect
          x={pillX} y={pillY}
          width={pillW} height={pillH}
          rx={LABEL_PILL_RADIUS}
          fill={LABEL_PILL_COLOR}
          fillOpacity={LABEL_PILL_OPACITY}
          stroke={LABEL_PILL_COLOR}
          strokeWidth={1}
          strokeOpacity={0.25}
        />
        <text
          x={pillX + LABEL_PILL_PADDING_H}
          y={wallY + 5}
          fontFamily={LABEL_FONT_FAMILY}
          fontSize={LABEL_FONT_SIZE}
          fontWeight={LABEL_FONT_WEIGHT}
          fill={LABEL_TEXT_COLOR}
        >
          {label}
        </text>
      </g>
    </g>
  );
};

// ─── Main Component ──────────────────────────────────────────────
export const Part3MoldParts03MoldWallsIlluminate: React.FC = () => {
  const frame = useCurrentFrame();

  // Zoom animation over first 30 frames
  const scale = interpolate(frame, [ZOOM_START, ZOOM_END], [ZOOM_FROM, ZOOM_TO], {
    easing: Easing.inOut(Easing.ease),
    extrapolateLeft: 'clamp',
    extrapolateRight: 'clamp',
  });

  // Walls brighten
  const wallBright = interpolate(frame, [0, 30], [0.3, 1.0], {
    easing: Easing.out(Easing.quad),
    extrapolateLeft: 'clamp',
    extrapolateRight: 'clamp',
  });

  // Nozzle + cavity dim
  const dimFactor = interpolate(frame, [0, 30], [0.4, DIMMED_OPACITY], {
    easing: Easing.inOut(Easing.ease),
    extrapolateLeft: 'clamp',
    extrapolateRight: 'clamp',
  });

  const cx = CANVAS_WIDTH / 2;
  const cy = CANVAS_HEIGHT / 2;
  const outerX = cx - MOLD_OUTER_WIDTH / 2;
  const outerY = cy - MOLD_OUTER_HEIGHT / 2;
  const innerX = cx - MOLD_INNER_WIDTH / 2;
  const innerY = cy - MOLD_INNER_HEIGHT / 2;
  const nozzleX = cx - NOZZLE_WIDTH / 2;
  const nozzleY = outerY - NOZZLE_HEIGHT;
  const leftWallX = innerX;
  const rightWallX = innerX + MOLD_INNER_WIDTH;

  return (
    <AbsoluteFill
      style={{
        backgroundColor: BACKGROUND_COLOR,
        width: CANVAS_WIDTH,
        height: CANVAS_HEIGHT,
      }}
    >
      {/* All SVG content in one layer */}
      <AbsoluteFill>
        <svg
          width={CANVAS_WIDTH}
          height={CANVAS_HEIGHT}
          viewBox={`0 0 ${CANVAS_WIDTH} ${CANVAS_HEIGHT}`}
          style={{
            position: 'absolute',
            top: 0,
            left: 0,
          }}
        >
          {/* Blueprint Grid */}
          <BlueprintGridSVG />

          {/* Mold group with zoom transform */}
          <g
            transform={`translate(${cx}, ${cy}) scale(${scale}) translate(${-cx}, ${-cy})`}
          >
            <defs>
              <filter id="wallGlowFilter" x="-50%" y="-50%" width="200%" height="200%">
                <feGaussianBlur stdDeviation="6" result="blur" />
                <feMerge>
                  <feMergeNode in="blur" />
                  <feMergeNode in="SourceGraphic" />
                </feMerge>
              </filter>
            </defs>

            {/* Outer shell */}
            <rect
              x={outerX} y={outerY}
              width={MOLD_OUTER_WIDTH} height={MOLD_OUTER_HEIGHT}
              fill="none"
              stroke={MOLD_STROKE_COLOR}
              strokeWidth={MOLD_STROKE_WIDTH}
              rx={4}
            />

            {/* Nozzle (dimmed) */}
            <g opacity={dimFactor}>
              <rect
                x={nozzleX} y={nozzleY}
                width={NOZZLE_WIDTH} height={NOZZLE_HEIGHT}
                fill="none"
                stroke={MOLD_STROKE_COLOR}
                strokeWidth={2} rx={2}
              />
              <line
                x1={cx - 15} y1={outerY}
                x2={cx + 15} y2={outerY}
                stroke={WALL_COLOR} strokeWidth={2}
              />
            </g>

            {/* Cavity interior (dimmed) */}
            <rect
              x={innerX} y={innerY}
              width={MOLD_INNER_WIDTH} height={MOLD_INNER_HEIGHT}
              fill={WALL_COLOR}
              fillOpacity={dimFactor * 0.1}
              stroke={MOLD_STROKE_COLOR}
              strokeWidth={1}
              strokeOpacity={dimFactor}
              rx={2}
            />

            {/* Left wall — full length */}
            <line
              x1={leftWallX} y1={innerY}
              x2={leftWallX} y2={innerY + MOLD_INNER_HEIGHT}
              stroke={WALL_COLOR}
              strokeWidth={MOLD_STROKE_WIDTH}
              opacity={wallBright}
              filter="url(#wallGlowFilter)"
            />

            {/* Right wall — full length */}
            <line
              x1={rightWallX} y1={innerY}
              x2={rightWallX} y2={innerY + MOLD_INNER_HEIGHT}
              stroke={WALL_COLOR}
              strokeWidth={MOLD_STROKE_WIDTH}
              opacity={wallBright}
              filter="url(#wallGlowFilter)"
            />

            {/* Horizontal walls (top + bottom) */}
            <line
              x1={innerX} y1={innerY}
              x2={innerX + MOLD_INNER_WIDTH} y2={innerY}
              stroke={WALL_COLOR} strokeWidth={2}
              opacity={wallBright * 0.6}
            />
            <line
              x1={innerX} y1={innerY + MOLD_INNER_HEIGHT}
              x2={innerX + MOLD_INNER_WIDTH} y2={innerY + MOLD_INNER_HEIGHT}
              stroke={WALL_COLOR} strokeWidth={2}
              opacity={wallBright * 0.6}
            />
          </g>
        </svg>
      </AbsoluteFill>

      {/* Wall Segment Labels — each in its own Sequence for local frame context */}
      {WALL_LABELS.map((wall, i) => (
        <Sequence key={i} from={wall.frameIn} durationInFrames={TOTAL_FRAMES - wall.frameIn}>
          <AbsoluteFill>
            <svg
              width={CANVAS_WIDTH}
              height={CANVAS_HEIGHT}
              viewBox={`0 0 ${CANVAS_WIDTH} ${CANVAS_HEIGHT}`}
              style={{
                position: 'absolute',
                top: 0,
                left: 0,
              }}
            >
              <g
                transform={`translate(${cx}, ${cy}) scale(${ZOOM_TO}) translate(${-cx}, ${-cy})`}
              >
                <WallSegmentWithLabel
                  label={wall.label}
                  side={wall.side}
                  yOffset={WALL_SEGMENT_POSITIONS[i].y}
                />
              </g>
            </svg>
          </AbsoluteFill>
        </Sequence>
      ))}
    </AbsoluteFill>
  );
};

export default Part3MoldParts03MoldWallsIlluminate;
