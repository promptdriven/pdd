import React from 'react';
import {
  AbsoluteFill,
  useCurrentFrame,
  interpolate,
  Easing,
} from 'remotion';

import { BlueprintGrid } from './BlueprintGrid';
import { ModuleBox } from './ModuleBox';
import { ConnectionArrow } from './ConnectionArrow';
import {
  BG_COLOR,
  CENTER_MODULE_FILL,
  CENTER_MODULE_BORDER,
  CENTER_MODULE_LABEL_COLOR,
  SURROUND_MODULE_FILL,
  SURROUND_MODULE_BORDER,
  SURROUND_MODULE_LABEL_COLOR,
  GLOW_COLOR,
  GLOW_BLUR,
  GLOW_OPACITY,
  BOUNDARY_COLOR,
  BOUNDARY_CIRCLE_OPACITY,
  BOUNDARY_LABEL_OPACITY,
  MAIN_LABEL_COLOR,
  SUB_LABEL_COLOR,
  CENTER_MODULE_WIDTH,
  CENTER_MODULE_HEIGHT,
  CENTER_X,
  CENTER_Y,
  SURROUND_MODULE_WIDTH,
  SURROUND_MODULE_HEIGHT,
  BOUNDARY_RADIUS,
  CANVAS_WIDTH,
  CANVAS_HEIGHT,
  CENTRAL_FADE_START,
  CENTRAL_FADE_DURATION,
  SURROUND_FADE_START,
  SURROUND_FADE_INTERVAL,
  SURROUND_FADE_DURATION,
  ARROWS_START,
  BOUNDARY_START,
  BOUNDARY_DRAW_DURATION,
  BOUNDARY_LABEL_START,
  DIM_START,
  DIM_DURATION,
  MAIN_LABEL_START,
  MAIN_LABEL_DURATION,
  SUB_LABEL_START,
  SUB_LABEL_DURATION,
  SURROUNDING_MODULES,
} from './constants';

export const defaultPart3MoldParts11ModuleBoundaryProps = {};

export const Part3MoldParts11ModuleBoundary: React.FC = () => {
  const frame = useCurrentFrame();

  // === Central module fade-in ===
  const centralOpacity = interpolate(
    frame,
    [CENTRAL_FADE_START, CENTRAL_FADE_START + CENTRAL_FADE_DURATION],
    [0, 1],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.out(Easing.quad),
    }
  );

  // === Glow pulse (60-frame cycle using sine easing) ===
  const pulsePhase = (frame % 60) / 60;
  const pulseValue =
    0.5 + 0.5 * Math.sin(pulsePhase * Math.PI * 2);
  const glowStrength = interpolate(
    frame,
    [DIM_START, DIM_START + DIM_DURATION],
    [GLOW_OPACITY, GLOW_OPACITY * 1.8],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.inOut(Easing.sin),
    }
  );
  const currentGlowOpacity =
    glowStrength * (0.7 + 0.3 * pulseValue);

  // === Surrounding modules dim ===
  const surroundDim = interpolate(
    frame,
    [DIM_START, DIM_START + DIM_DURATION],
    [1.0, 0.6],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.inOut(Easing.sin),
    }
  );

  // === Boundary circle stroke draw ===
  const boundaryCircumference = 2 * Math.PI * BOUNDARY_RADIUS;
  const boundaryProgress = interpolate(
    frame,
    [BOUNDARY_START, BOUNDARY_START + BOUNDARY_DRAW_DURATION],
    [0, 1],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.inOut(Easing.cubic),
    }
  );

  // === Boundary label fade ===
  const boundaryLabelOpacity = interpolate(
    frame,
    [BOUNDARY_LABEL_START, BOUNDARY_LABEL_START + 15],
    [0, BOUNDARY_LABEL_OPACITY],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.out(Easing.quad),
    }
  );

  // === Main label fade ===
  const mainLabelOpacity = interpolate(
    frame,
    [MAIN_LABEL_START, MAIN_LABEL_START + MAIN_LABEL_DURATION],
    [0, 1],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.out(Easing.quad),
    }
  );

  // === Sub label fade ===
  const subLabelOpacity = interpolate(
    frame,
    [SUB_LABEL_START, SUB_LABEL_START + SUB_LABEL_DURATION],
    [0, 1],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.out(Easing.quad),
    }
  );

  return (
    <AbsoluteFill style={{ backgroundColor: BG_COLOR }}>
      {/* Blueprint grid */}
      <BlueprintGrid />

      {/* SVG layer for arrows and boundary circle */}
      <AbsoluteFill>
        <svg
          width={CANVAS_WIDTH}
          height={CANVAS_HEIGHT}
          style={{ position: 'absolute', top: 0, left: 0 }}
        >
          {/* Connection arrows */}
          {SURROUNDING_MODULES.map((mod, i) => (
            <ConnectionArrow
              key={`arrow-${mod.name}`}
              fromX={CENTER_X}
              fromY={CENTER_Y}
              toX={mod.x}
              toY={mod.y}
              dashed={mod.async}
              drawStartFrame={ARROWS_START + i * 4}
              arrowOpacity={surroundDim}
            />
          ))}

          {/* PDD boundary dashed circle */}
          {boundaryProgress > 0 && (
            <circle
              cx={CENTER_X}
              cy={CENTER_Y}
              r={BOUNDARY_RADIUS}
              fill="none"
              stroke={BOUNDARY_COLOR}
              strokeWidth={2}
              strokeDasharray="8 6"
              opacity={BOUNDARY_CIRCLE_OPACITY}
              strokeDashoffset={
                boundaryCircumference * (1 - boundaryProgress)
              }
              style={{
                transition: 'none',
              }}
            />
          )}
        </svg>
      </AbsoluteFill>

      {/* Boundary label */}
      {boundaryLabelOpacity > 0 && (
        <div
          style={{
            position: 'absolute',
            left: CENTER_X - 50,
            top: CENTER_Y - BOUNDARY_RADIUS - 28,
            width: 100,
            textAlign: 'center',
            fontFamily: 'Inter, sans-serif',
            fontSize: 11,
            fontWeight: 400,
            color: BOUNDARY_COLOR,
            opacity: boundaryLabelOpacity,
            userSelect: 'none',
          }}
        >
          PDD boundary
        </div>
      )}

      {/* Central PDD-governed module */}
      <ModuleBox
        label="user_parser"
        x={CENTER_X}
        y={CENTER_Y}
        width={CENTER_MODULE_WIDTH}
        height={CENTER_MODULE_HEIGHT}
        fillColor={CENTER_MODULE_FILL}
        borderColor={CENTER_MODULE_BORDER}
        borderWidth={2}
        borderRadius={12}
        labelColor={CENTER_MODULE_LABEL_COLOR}
        labelSize={14}
        labelWeight={700}
        opacity={centralOpacity}
        glowColor={GLOW_COLOR}
        glowBlur={GLOW_BLUR}
        glowOpacity={currentGlowOpacity}
      />

      {/* Surrounding modules */}
      {SURROUNDING_MODULES.map((mod, i) => {
        const moduleStart =
          SURROUND_FADE_START + i * SURROUND_FADE_INTERVAL;
        const moduleOpacity = interpolate(
          frame,
          [moduleStart, moduleStart + SURROUND_FADE_DURATION],
          [0, 1],
          {
            extrapolateLeft: 'clamp',
            extrapolateRight: 'clamp',
            easing: Easing.out(Easing.quad),
          }
        );

        return (
          <ModuleBox
            key={mod.name}
            label={mod.name}
            x={mod.x}
            y={mod.y}
            width={SURROUND_MODULE_WIDTH}
            height={SURROUND_MODULE_HEIGHT}
            fillColor={SURROUND_MODULE_FILL}
            borderColor={SURROUND_MODULE_BORDER}
            borderWidth={1}
            borderRadius={8}
            labelColor={SURROUND_MODULE_LABEL_COLOR}
            labelSize={12}
            labelWeight={400}
            opacity={moduleOpacity * surroundDim}
          />
        );
      })}

      {/* Main label */}
      {mainLabelOpacity > 0 && (
        <div
          style={{
            position: 'absolute',
            left: 0,
            right: 0,
            top: 800,
            textAlign: 'center',
            fontFamily: 'Inter, sans-serif',
            fontSize: 22,
            fontWeight: 600,
            color: MAIN_LABEL_COLOR,
            opacity: mainLabelOpacity,
            userSelect: 'none',
          }}
        >
          PDD operates at the module level.
        </div>
      )}

      {/* Subtext label */}
      {subLabelOpacity > 0 && (
        <div
          style={{
            position: 'absolute',
            left: 0,
            right: 0,
            top: 840,
            textAlign: 'center',
            fontFamily: 'Inter, sans-serif',
            fontSize: 14,
            fontWeight: 400,
            color: SUB_LABEL_COLOR,
            opacity: subLabelOpacity,
            userSelect: 'none',
          }}
        >
          The mold makes each part precise. The assembly is still
          yours.
        </div>
      )}
    </AbsoluteFill>
  );
};

export default Part3MoldParts11ModuleBoundary;
