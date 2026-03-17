import React from "react";
import { useCurrentFrame, interpolate, Easing } from "remotion";
import {
  GRID_X,
  GRID_Y,
  GRID_W,
  GRID_H,
  TL_CENTER_X,
  TL_CENTER_Y,
  TR_CENTER_X,
  TR_CENTER_Y,
  BL_CENTER_X,
  BL_CENTER_Y,
  BR_CENTER_X,
  BR_CENTER_Y,
  GREEN,
  RED,
  AMBER,
  LABEL_MUTED,
  FONT_FAMILY,
  TL_GLOW_START,
  TL_GLOW_END,
  TL_STAT_START,
  TL_STAT_END,
  BR_GLOW_START,
  BR_GLOW_END,
  BR_STAT_START,
  BR_STAT_END,
  AMBER_START,
  AMBER_END,
} from "./constants";

interface QuadrantFillProps {
  x: number;
  y: number;
  w: number;
  h: number;
  color: string;
  glowStart: number;
  glowEnd: number;
  glowOpacity: number;
}

const QuadrantFill: React.FC<QuadrantFillProps> = ({
  x,
  y,
  w,
  h,
  color,
  glowStart,
  glowEnd,
  glowOpacity,
}) => {
  const frame = useCurrentFrame();

  const opacity = interpolate(frame, [glowStart, glowEnd], [0, glowOpacity], {
    extrapolateLeft: "clamp",
    extrapolateRight: "clamp",
    easing: Easing.out(Easing.quad),
  });

  return <rect x={x} y={y} width={w} height={h} fill={color} opacity={opacity} />;
};

interface StudyLabelProps {
  cx: number;
  cy: number;
  studyName: string;
  stat: string;
  subtext: string;
  color: string;
  statStart: number;
  statEnd: number;
}

const StudyLabel: React.FC<StudyLabelProps> = ({
  cx,
  cy,
  studyName,
  stat,
  subtext,
  color,
  statStart,
  statEnd,
}) => {
  const frame = useCurrentFrame();

  const scaleRaw = interpolate(frame, [statStart, statEnd], [0.3, 1], {
    extrapolateLeft: "clamp",
    extrapolateRight: "clamp",
    easing: Easing.out(Easing.back(1.4)),
  });

  const textOpacity = interpolate(frame, [statStart, statEnd], [0, 1], {
    extrapolateLeft: "clamp",
    extrapolateRight: "clamp",
    easing: Easing.out(Easing.quad),
  });

  return (
    <g opacity={textOpacity}>
      {/* Study name */}
      <text
        x={cx}
        y={cy - 30}
        fill={color}
        fontSize={13}
        fontFamily={FONT_FAMILY}
        fontWeight={700}
        opacity={0.7}
        textAnchor="middle"
        dominantBaseline="middle"
      >
        {studyName}
      </text>

      {/* Stat with scale-up */}
      <text
        x={cx}
        y={cy + 5}
        fill={color}
        fontSize={32}
        fontFamily={FONT_FAMILY}
        fontWeight={700}
        opacity={0.85}
        textAnchor="middle"
        dominantBaseline="middle"
        transform={`translate(${cx}, ${cy + 5}) scale(${scaleRaw}) translate(${-cx}, ${-(cy + 5)})`}
      >
        {stat}
      </text>

      {/* Subtext */}
      <text
        x={cx}
        y={cy + 38}
        fill={LABEL_MUTED}
        fontSize={9}
        fontFamily={FONT_FAMILY}
        fontWeight={400}
        opacity={0.35}
        textAnchor="middle"
        dominantBaseline="middle"
      >
        {subtext}
      </text>
    </g>
  );
};

interface MixedLabelProps {
  cx: number;
  cy: number;
  fadeStart: number;
  fadeEnd: number;
}

const MixedLabel: React.FC<MixedLabelProps> = ({
  cx,
  cy,
  fadeStart,
  fadeEnd,
}) => {
  const frame = useCurrentFrame();

  const opacity = interpolate(frame, [fadeStart, fadeEnd], [0, 0.4], {
    extrapolateLeft: "clamp",
    extrapolateRight: "clamp",
    easing: Easing.out(Easing.quad),
  });

  return (
    <text
      x={cx}
      y={cy}
      fill={AMBER}
      fontSize={11}
      fontFamily={FONT_FAMILY}
      fontWeight={400}
      opacity={opacity}
      textAnchor="middle"
      dominantBaseline="middle"
    >
      Mixed results
    </text>
  );
};

export const QuadrantContent: React.FC = () => {
  const halfW = GRID_W / 2;
  const halfH = GRID_H / 2;

  return (
    <>
      {/* Top-left quadrant fill (green) */}
      <QuadrantFill
        x={GRID_X}
        y={GRID_Y}
        w={halfW}
        h={halfH}
        color={GREEN}
        glowStart={TL_GLOW_START}
        glowEnd={TL_GLOW_END}
        glowOpacity={0.08}
      />

      {/* Bottom-right quadrant fill (red) */}
      <QuadrantFill
        x={GRID_X + halfW}
        y={GRID_Y + halfH}
        w={halfW}
        h={halfH}
        color={RED}
        glowStart={BR_GLOW_START}
        glowEnd={BR_GLOW_END}
        glowOpacity={0.08}
      />

      {/* Top-right quadrant fill (amber) */}
      <QuadrantFill
        x={GRID_X + halfW}
        y={GRID_Y}
        w={halfW}
        h={halfH}
        color={AMBER}
        glowStart={AMBER_START}
        glowEnd={AMBER_END}
        glowOpacity={0.04}
      />

      {/* Bottom-left quadrant fill (amber) */}
      <QuadrantFill
        x={GRID_X}
        y={GRID_Y + halfH}
        w={halfW}
        h={halfH}
        color={AMBER}
        glowStart={AMBER_START}
        glowEnd={AMBER_END}
        glowOpacity={0.04}
      />

      {/* GitHub study label */}
      <StudyLabel
        cx={TL_CENTER_X}
        cy={TL_CENTER_Y}
        studyName="GitHub study"
        stat="+55%"
        subtext="95 devs, greenfield"
        color={GREEN}
        statStart={TL_STAT_START}
        statEnd={TL_STAT_END}
      />

      {/* METR study label */}
      <StudyLabel
        cx={BR_CENTER_X}
        cy={BR_CENTER_Y}
        studyName="METR study"
        stat={"\u221219%"}
        subtext="experienced devs, mature repos"
        color={RED}
        statStart={BR_STAT_START}
        statEnd={BR_STAT_END}
      />

      {/* Mixed results labels */}
      <MixedLabel
        cx={TR_CENTER_X}
        cy={TR_CENTER_Y}
        fadeStart={AMBER_START}
        fadeEnd={AMBER_END}
      />
      <MixedLabel
        cx={BL_CENTER_X}
        cy={BL_CENTER_Y}
        fadeStart={AMBER_START}
        fadeEnd={AMBER_END}
      />
    </>
  );
};
