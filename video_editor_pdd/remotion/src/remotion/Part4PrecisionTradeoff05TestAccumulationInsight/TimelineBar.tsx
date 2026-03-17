import React from 'react';
import { interpolate, useCurrentFrame, Easing } from 'remotion';

interface TimelineBarProps {
  y: number;
  xStart: number;
  xEnd: number;
  markers: Array<{ label: string; x: number }>;
  gradientFrom: string;
  gradientTo: string;
  animationStart: number;
  fillDuration: number;
}

export const TimelineBar: React.FC<TimelineBarProps> = ({
  y,
  xStart,
  xEnd,
  markers,
  gradientFrom,
  gradientTo,
  animationStart,
  fillDuration,
}) => {
  const frame = useCurrentFrame();
  const barWidth = xEnd - xStart;
  const barHeight = 6;

  // Track draw-in
  const trackProgress = interpolate(
    frame,
    [animationStart, animationStart + 15],
    [0, 1],
    { extrapolateLeft: 'clamp', extrapolateRight: 'clamp', easing: Easing.out(Easing.quad) }
  );

  // Gradient fill
  const fillProgress = interpolate(
    frame,
    [animationStart + 10, animationStart + 10 + fillDuration],
    [0, 1],
    { extrapolateLeft: 'clamp', extrapolateRight: 'clamp', easing: Easing.inOut(Easing.cubic) }
  );

  // Marker opacity
  const markerOpacity = interpolate(
    frame,
    [animationStart + 5, animationStart + 20],
    [0, 1],
    { extrapolateLeft: 'clamp', extrapolateRight: 'clamp', easing: Easing.out(Easing.quad) }
  );

  // "safer over time" label opacity
  const saferOpacity = interpolate(
    frame,
    [animationStart + fillDuration, animationStart + fillDuration + 15],
    [0, 0.5],
    { extrapolateLeft: 'clamp', extrapolateRight: 'clamp', easing: Easing.out(Easing.quad) }
  );

  return (
    <>
      {/* Track background */}
      <div
        style={{
          position: 'absolute',
          left: xStart,
          top: y,
          width: barWidth * trackProgress,
          height: barHeight,
          backgroundColor: '#1E293B',
          borderRadius: barHeight / 2,
        }}
      />
      {/* Gradient fill */}
      <div
        style={{
          position: 'absolute',
          left: xStart,
          top: y,
          width: barWidth * fillProgress,
          height: barHeight,
          background: `linear-gradient(to right, ${gradientFrom}, ${gradientTo})`,
          borderRadius: barHeight / 2,
        }}
      />
      {/* Markers */}
      {markers.map((marker, i) => (
        <React.Fragment key={i}>
          {/* Marker dot */}
          <div
            style={{
              position: 'absolute',
              left: marker.x - 4,
              top: y - 3,
              width: 12,
              height: 12,
              borderRadius: '50%',
              backgroundColor: i === 0 ? gradientFrom : i === markers.length - 1 ? gradientTo : '#94A3B8',
              opacity: markerOpacity * 0.7,
            }}
          />
          {/* Marker label */}
          <div
            style={{
              position: 'absolute',
              left: marker.x - 30,
              top: y + 16,
              width: 70,
              textAlign: 'center',
              fontFamily: 'Inter, sans-serif',
              fontSize: 11,
              fontWeight: 500,
              color: '#94A3B8',
              opacity: markerOpacity * 0.5,
            }}
          >
            {marker.label}
          </div>
        </React.Fragment>
      ))}
      {/* Arrow and "safer over time" label */}
      <div
        style={{
          position: 'absolute',
          left: xEnd + 12,
          top: y - 5,
          fontFamily: 'Inter, sans-serif',
          fontSize: 11,
          fontWeight: 500,
          color: '#5AAA6E',
          opacity: saferOpacity,
          whiteSpace: 'nowrap',
        }}
      >
        → safer over time
      </div>
    </>
  );
};
