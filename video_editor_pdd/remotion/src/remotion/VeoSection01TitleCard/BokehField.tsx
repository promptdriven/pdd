import React from 'react';
import { useCurrentFrame, random } from 'remotion';
import { BOKEH, CANVAS, COLORS } from './constants';

interface BokehCircle {
  id: number;
  startX: number;
  startY: number;
  radius: number;
  color: string;
  opacity: number;
}

const generateBokehCircles = (count: number): BokehCircle[] => {
  const circles: BokehCircle[] = [];
  const colors = [COLORS.bokehWarm1, COLORS.bokehWarm2];
  for (let i = 0; i < count; i++) {
    const radius =
      random(`bokeh-r-${i}`) * (BOKEH.maxRadius - BOKEH.minRadius) +
      BOKEH.minRadius;
    circles.push({
      id: i,
      startX: random(`bokeh-x-${i}`) * CANVAS.width,
      startY: random(`bokeh-y-${i}`) * CANVAS.height,
      radius,
      color: colors[i % colors.length],
      opacity: random(`bokeh-o-${i}`) * 0.06 + 0.04,
    });
  }
  return circles;
};

export const BokehField: React.FC = () => {
  const frame = useCurrentFrame();
  const circles = React.useMemo(
    () => generateBokehCircles(BOKEH.count),
    [],
  );

  return (
    <>
      {circles.map((circle) => {
        // Drift diagonally: right and upward
        const driftX = circle.startX + frame * BOKEH.driftSpeed * 0.7;
        const driftY = circle.startY - frame * BOKEH.driftSpeed * 0.5;

        // Wrap around canvas edges
        const x =
          ((driftX % (CANVAS.width + 40)) + (CANVAS.width + 40)) %
          (CANVAS.width + 40);
        const y =
          ((driftY % (CANVAS.height + 40)) + (CANVAS.height + 40)) %
          (CANVAS.height + 40);

        return (
          <div
            key={circle.id}
            style={{
              position: 'absolute',
              left: x - circle.radius,
              top: y - circle.radius,
              width: circle.radius * 2,
              height: circle.radius * 2,
              borderRadius: '50%',
              backgroundColor: circle.color,
              opacity: circle.opacity,
              filter: `blur(${circle.radius * 0.4}px)`,
            }}
          />
        );
      })}
    </>
  );
};
