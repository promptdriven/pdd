import React from "react";
import { useCurrentFrame, interpolate, Easing } from "remotion";
import {
  CANVAS_WIDTH,
  TITLE_FONT_SIZE,
  TITLE_FONT_WEIGHT,
  TITLE_FONT_FAMILY,
  TITLE_COLOR,
  TITLE_LINE1_Y,
  TITLE_LINE2_Y,
  TITLE_LINE2_OFFSET_X,
  LINE1_START,
  LINE1_END,
  LINE2_START,
  LINE2_END,
  SLIDE_DISTANCE,
} from "./constants";

interface TitleLineProps {
  text: string;
  y: number;
  offsetX: number;
  animStart: number;
  animEnd: number;
}

const TitleLine: React.FC<TitleLineProps> = ({
  text,
  y,
  offsetX,
  animStart,
  animEnd,
}) => {
  const frame = useCurrentFrame();
  const duration = animEnd - animStart;

  const opacity = interpolate(frame, [animStart, animStart + duration], [0, 1], {
    extrapolateLeft: "clamp",
    extrapolateRight: "clamp",
    easing: Easing.out(Easing.cubic),
  });

  const translateY = interpolate(
    frame,
    [animStart, animStart + duration],
    [SLIDE_DISTANCE, 0],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.out(Easing.cubic),
    }
  );

  return (
    <div
      style={{
        position: "absolute",
        top: y,
        left: 0,
        width: CANVAS_WIDTH,
        textAlign: "center",
        opacity,
        transform: `translateY(${translateY}px) translateX(${offsetX}px)`,
        fontFamily: TITLE_FONT_FAMILY,
        fontSize: TITLE_FONT_SIZE,
        fontWeight: TITLE_FONT_WEIGHT,
        color: TITLE_COLOR,
        letterSpacing: "4px",
      }}
    >
      {text}
    </div>
  );
};

export const TitleText: React.FC = () => {
  return (
    <>
      <TitleLine
        text="PROMPT-DRIVEN"
        y={TITLE_LINE1_Y}
        offsetX={0}
        animStart={LINE1_START}
        animEnd={LINE1_END}
      />
      <TitleLine
        text="DEVELOPMENT"
        y={TITLE_LINE2_Y}
        offsetX={TITLE_LINE2_OFFSET_X}
        animStart={LINE2_START}
        animEnd={LINE2_END}
      />
    </>
  );
};

export default TitleText;
