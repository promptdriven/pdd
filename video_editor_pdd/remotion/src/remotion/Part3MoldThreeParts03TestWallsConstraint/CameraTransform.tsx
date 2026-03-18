import React from 'react';
import { useCurrentFrame, interpolate, Easing } from 'remotion';

/**
 * CameraTransform wraps children with a CSS transform that simulates
 * camera zoom and pan, plus optional screen shake.
 */

interface CameraTransformProps {
	children: React.ReactNode;
}

const CameraTransform: React.FC<CameraTransformProps> = ({ children }) => {
	const frame = useCurrentFrame();

	// Phase 1 (frame 0-89): normal view
	// Phase 2 (frame 90-150): zoom into "null → None" wall at ~(700, 350)
	// Phase 3 (frame 150-180): pull back to normal
	// Phase 4 (frame 180+): normal view

	// Zoom scale
	const zoomIn = interpolate(frame, [90, 120], [1, 1.2], {
		extrapolateLeft: 'clamp',
		extrapolateRight: 'clamp',
		easing: Easing.inOut(Easing.cubic),
	});

	const zoomOut = interpolate(frame, [150, 180], [1.2, 1], {
		extrapolateLeft: 'clamp',
		extrapolateRight: 'clamp',
		easing: Easing.inOut(Easing.cubic),
	});

	const scale = frame < 150 ? zoomIn : zoomOut;

	// Pan offset (when zoomed, center on the focus wall)
	// Focus point: approximately x=700, y=350 (left wall "null → None")
	// We need to translate so that (700, 350) stays centered on screen
	// Transform origin is center of screen (960, 540)
	// Offset = (960 - 700) * (scale - 1), (540 - 350) * (scale - 1)
	const panX = (960 - 720) * (scale - 1);
	const panY = (540 - 380) * (scale - 1);

	// Screen shake at frame 110-114 (impact moment)
	let shakeX = 0;
	let shakeY = 0;
	if (frame >= 110 && frame < 114) {
		const shakeAge = frame - 110;
		const shakeDecay = interpolate(shakeAge, [0, 4], [1, 0], {
			extrapolateRight: 'clamp',
		});
		// Alternating shake
		shakeX =
			Math.sin(shakeAge * Math.PI * 2) * 2 * shakeDecay;
		shakeY =
			Math.cos(shakeAge * Math.PI * 1.5) * 2 * shakeDecay;
	}

	const translateX = panX + shakeX;
	const translateY = panY + shakeY;

	return (
		<div
			style={{
				width: '100%',
				height: '100%',
				transform: `translate(${translateX}px, ${translateY}px) scale(${scale})`,
				transformOrigin: '960px 540px',
			}}
		>
			{children}
		</div>
	);
};

export default CameraTransform;
