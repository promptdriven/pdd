import React from "react";
import { interpolate, Easing } from "remotion";
import { COLORS, TODO_COMMENTS, BEATS } from "./constants";

/**
 * Floating TODO / legacy comment labels near file clusters.
 * Fade in during the zoom-out / patch phase.
 */
export const TodoComments: React.FC<{ frame: number }> = ({ frame }) => {
  if (frame < BEATS.ZOOM_START + 30) return null;

  return (
    <g>
      {TODO_COMMENTS.map((comment, i) => {
        const delay = i * 15;
        const opacity = interpolate(
          frame,
          [BEATS.ZOOM_END + delay, BEATS.ZOOM_END + delay + 20],
          [0, 0.75],
          {
            extrapolateLeft: "clamp",
            extrapolateRight: "clamp",
            easing: Easing.out(Easing.cubic),
          }
        );

        if (opacity <= 0) return null;

        // Slight floating bob
        const bob = Math.sin((frame + i * 20) * 0.06) * 4;

        return (
          <g key={i} opacity={opacity} transform={`translate(0, ${bob})`}>
            {/* Background pill */}
            <rect
              x={comment.x - 4}
              y={comment.y - 12}
              width={comment.text.length * 7.5 + 8}
              height={18}
              rx={4}
              fill={COLORS.TODO_BG}
            />
            {/* Text */}
            <text
              x={comment.x}
              y={comment.y}
              fontSize={11}
              fill={COLORS.TODO_TEXT}
              fontFamily="monospace"
              fontStyle="italic"
            >
              {comment.text}
            </text>
          </g>
        );
      })}
    </g>
  );
};
