import React from 'react';
import { useCurrentFrame, interpolate, Easing } from 'remotion';
import { REGIONS, BAR_Y, BORDER_COLOR, TIMING } from './constants';

/**
 * Region labels above the spectrum bar with downward connector lines.
 * They fade in left-to-right with staggered timing starting at frame 30.
 */
export const RegionLabels: React.FC = () => {
  const frame = useCurrentFrame();

  return (
    <>
      {REGIONS.map((region, i) => {
        const startFrame = TIMING.regionStart + i * TIMING.regionStagger;
        const opacity = interpolate(
          frame,
          [startFrame, startFrame + TIMING.regionFadeDuration],
          [0, 1],
          {
            extrapolateLeft: 'clamp',
            extrapolateRight: 'clamp',
            easing: Easing.out(Easing.quad),
          }
        );

        // Connector line from label to spectrum bar
        const connectorTop = region.y + 16; // below text
        const connectorHeight = BAR_Y - connectorTop;

        return (
          <React.Fragment key={region.label}>
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

            {/* Connector line */}
            <div
              style={{
                position: 'absolute',
                left: region.x,
                top: connectorTop,
                width: 1,
                height: connectorHeight * opacity,
                backgroundColor: BORDER_COLOR,
                opacity: 0.15 * opacity,
                transformOrigin: 'top',
              }}
            />
          </React.Fragment>
        );
      })}
    </>
  );
};
