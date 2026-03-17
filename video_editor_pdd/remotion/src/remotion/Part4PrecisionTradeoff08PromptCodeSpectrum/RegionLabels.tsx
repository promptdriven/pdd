import React from 'react';
import { useCurrentFrame, Easing, interpolate } from 'remotion';
import { REGIONS, BAR_Y, BORDER_COLOR, ANIM } from './constants';

/**
 * Region labels above the spectrum bar with staggered fade-in
 * and thin connector lines down to the bar.
 */
export const RegionLabels: React.FC = () => {
  const frame = useCurrentFrame();

  return (
    <>
      {REGIONS.map((region, i) => {
        const entryFrame = ANIM.regionStart + i * ANIM.regionStagger;
        const opacity = interpolate(
          frame,
          [entryFrame, entryFrame + ANIM.regionFadeDuration],
          [0, 1],
          {
            extrapolateLeft: 'clamp',
            extrapolateRight: 'clamp',
            easing: Easing.out(Easing.quad),
          }
        );

        const connectorTop = region.y + 16;
        const connectorBottom = BAR_Y;

        return (
          <React.Fragment key={i}>
            {/* Label text */}
            <div
              style={{
                position: 'absolute',
                left: region.x,
                top: region.y,
                transform: 'translateX(-50%)',
                fontFamily: 'Inter, sans-serif',
                fontSize: 11,
                color: region.color,
                opacity: 0.5 * opacity,
                whiteSpace: 'nowrap',
                textAlign: 'center',
              }}
            >
              {region.label}
            </div>

            {/* Connector line from label to bar */}
            <div
              style={{
                position: 'absolute',
                left: region.x,
                top: connectorTop,
                width: 1,
                height: (connectorBottom - connectorTop) * opacity,
                backgroundColor: BORDER_COLOR,
                opacity: 0.15 * opacity,
              }}
            />
          </React.Fragment>
        );
      })}
    </>
  );
};
