import React from 'react';
import {
	AbsoluteFill,
	useCurrentFrame,
	interpolate,
	Easing,
} from 'remotion';

// ═══════════════════════════════════════════════════════════════════
// Constants (inlined to avoid local imports)
// ═══════════════════════════════════════════════════════════════════

const BG_COLOR = '#0A0F1A';
const LIQUID_COLOR = '#4A90D9';
const WALL_STROKE = 4;
const MONO_FONT = 'JetBrains Mono, Menlo, monospace';
const TERMINAL_BG = 'rgba(15, 23, 42, 0.85)';
const TERMINAL_BORDER = '#334155';
const TERMINAL_TEXT_COLOR = '#94A3B8';
const TERMINAL_GREEN_COLOR = '#5AAA6E';

// Mold geometry
const MOLD_CENTER_X = 960;
const MOLD_CENTER_Y = 500;
const MOLD_WIDTH = 600;
const MOLD_HEIGHT = 700;

const CAVITY_LEFT = MOLD_CENTER_X - MOLD_WIDTH / 2 + 40;   // 700
const CAVITY_RIGHT = MOLD_CENTER_X + MOLD_WIDTH / 2 - 40;  // 1220
const CAVITY_TOP = MOLD_CENTER_Y - MOLD_HEIGHT / 2 + 60;   // 210
const CAVITY_BOTTOM = MOLD_CENTER_Y + MOLD_HEIGHT / 2 - 40; // 810
const NOZZLE_Y = MOLD_CENTER_Y - MOLD_HEIGHT / 2 - 20;     // 130

// Wall segment type
interface WallSegment {
	id: string;
	label: string;
	x1: number;
	y1: number;
	x2: number;
	y2: number;
	normalX: number;
	normalY: number;
}

const WALL_SEGMENTS: WallSegment[] = [
	// Left wall
	{ id: 'left-top', label: 'null → None', x1: CAVITY_LEFT, y1: CAVITY_TOP, x2: CAVITY_LEFT, y2: CAVITY_TOP + 200, normalX: 1, normalY: 0 },
	{ id: 'left-mid', label: 'int → str', x1: CAVITY_LEFT, y1: CAVITY_TOP + 200, x2: CAVITY_LEFT + 60, y2: CAVITY_TOP + 350, normalX: 0.8, normalY: 0.2 },
	{ id: 'left-bottom', label: 'empty list', x1: CAVITY_LEFT + 60, y1: CAVITY_TOP + 350, x2: CAVITY_LEFT + 60, y2: CAVITY_BOTTOM, normalX: 1, normalY: 0 },
	// Right wall
	{ id: 'right-top', label: 'max_length', x1: CAVITY_RIGHT, y1: CAVITY_TOP, x2: CAVITY_RIGHT, y2: CAVITY_TOP + 180, normalX: -1, normalY: 0 },
	{ id: 'right-mid', label: 'utf-8 edge', x1: CAVITY_RIGHT, y1: CAVITY_TOP + 180, x2: CAVITY_RIGHT - 50, y2: CAVITY_TOP + 380, normalX: -0.8, normalY: 0.2 },
	{ id: 'right-bottom', label: 'KeyError', x1: CAVITY_RIGHT - 50, y1: CAVITY_TOP + 380, x2: CAVITY_RIGHT - 50, y2: CAVITY_BOTTOM, normalX: -1, normalY: 0 },
	// Bottom wall
	{ id: 'bottom', label: 'return type', x1: CAVITY_LEFT + 60, y1: CAVITY_BOTTOM, x2: CAVITY_RIGHT - 50, y2: CAVITY_BOTTOM, normalX: 0, normalY: -1 },
	// Top wall (with nozzle gap)
	{ id: 'top-left', label: 'import check', x1: CAVITY_LEFT, y1: CAVITY_TOP, x2: MOLD_CENTER_X - 30, y2: CAVITY_TOP, normalX: 0, normalY: 1 },
	{ id: 'top-right', label: 'type hints', x1: MOLD_CENTER_X + 30, y1: CAVITY_TOP, x2: CAVITY_RIGHT, y2: CAVITY_TOP, normalX: 0, normalY: 1 },
];

// Collision events timeline
interface CollisionEvent {
	wallId: string;
	frame: number;
	intensity: number;
}

const COLLISION_EVENTS: CollisionEvent[] = [
	{ wallId: 'right-top', frame: 50, intensity: 0.8 },
	{ wallId: 'left-top', frame: 70, intensity: 0.9 },
	{ wallId: 'left-top', frame: 110, intensity: 1.0 },  // Focus collision
	{ wallId: 'right-mid', frame: 170, intensity: 0.7 },
	{ wallId: 'left-mid', frame: 200, intensity: 0.6 },
	{ wallId: 'left-bottom', frame: 230, intensity: 0.5 },
	{ wallId: 'right-bottom', frame: 250, intensity: 0.5 },
	{ wallId: 'bottom', frame: 270, intensity: 0.6 },
];

// Terminal commands
const TERMINAL_COMMANDS = [
	{ text: '$ pdd generate user_parser', color: TERMINAL_TEXT_COLOR, delay: 0 },
	{ text: '  Generating...', color: TERMINAL_TEXT_COLOR, delay: 30 },
	{ text: '  ✓ Parser skeleton created', color: TERMINAL_GREEN_COLOR, delay: 60 },
	{ text: '  ✓ Running test suite...', color: TERMINAL_GREEN_COLOR, delay: 80 },
	{ text: '  ✓ All 12 tests passing', color: TERMINAL_GREEN_COLOR, delay: 110 },
];

// ═══════════════════════════════════════════════════════════════════
// Helpers
// ═══════════════════════════════════════════════════════════════════

function seededRandom(seed: number): number {
	const x = Math.sin(seed * 12.9898 + seed * 78.233) * 43758.5453;
	return x - Math.floor(x);
}

function noise2D(x: number, y: number, seed: number): number {
	return (
		Math.sin(x * 1.7 + y * 2.3 + seed * 0.7) * 0.3 +
		Math.sin(x * 3.1 - y * 1.9 + seed * 1.3) * 0.2 +
		Math.sin(x * 0.8 + y * 4.1 + seed * 2.1) * 0.15 +
		Math.cos(x * 2.5 + y * 0.6 + seed * 0.4) * 0.2
	);
}

function getLabelOffset(seg: WallSegment): { dx: number; dy: number } {
	if (seg.normalX > 0) return { dx: -85, dy: 0 };
	if (seg.normalX < 0) return { dx: 14, dy: 0 };
	if (seg.normalY > 0) return { dx: 0, dy: 16 };
	return { dx: 0, dy: -14 };
}

// ═══════════════════════════════════════════════════════════════════
// Particle system (deterministic, pre-generated)
// ═══════════════════════════════════════════════════════════════════

interface Particle {
	id: number;
	startFrame: number;
	startX: number;
	speed: number;
	lateralBias: number;
	size: number;
	noiseSeed: number;
}

const PARTICLE_COUNT = 200;
const NOZZLE_WIDTH = 50;

function generateParticles(): Particle[] {
	const result: Particle[] = [];
	for (let i = 0; i < PARTICLE_COUNT; i++) {
		const r1 = seededRandom(i * 7 + 1);
		const r2 = seededRandom(i * 13 + 2);
		const r3 = seededRandom(i * 19 + 3);
		const r4 = seededRandom(i * 23 + 4);
		const r5 = seededRandom(i * 31 + 5);
		result.push({
			id: i,
			startFrame: Math.floor(r1 * 160),
			startX: MOLD_CENTER_X + (r2 - 0.5) * NOZZLE_WIDTH,
			speed: 1.8 + r3 * 2.5,
			lateralBias: (r4 - 0.5) * 1.2,
			size: 2 + r5 * 4,
			noiseSeed: r1 * 100,
		});
	}
	return result;
}

const PARTICLES = generateParticles();

// ═══════════════════════════════════════════════════════════════════
// Wall flash computation
// ═══════════════════════════════════════════════════════════════════

const FLASH_DURATION = 8;
const RIPPLE_DURATION = 15;
const RIPPLE_COUNT = 3;

function computeWallFlashStates(frame: number): Record<string, number> {
	const states: Record<string, number> = {};
	COLLISION_EVENTS.forEach((evt) => {
		const age = frame - evt.frame;
		if (age >= 0 && age <= FLASH_DURATION) {
			const progress = interpolate(age, [0, FLASH_DURATION], [1, 0], {
				extrapolateRight: 'clamp',
			});
			const intensity = progress * progress * progress * evt.intensity;
			states[evt.wallId] = Math.max(states[evt.wallId] || 0, intensity);
		}
	});
	// Sustained soft glow at the end (frame 300+)
	if (frame >= 300) {
		const glow = interpolate(frame, [300, 360], [0, 0.35], {
			extrapolateRight: 'clamp',
		});
		WALL_SEGMENTS.forEach((seg) => {
			states[seg.id] = Math.max(states[seg.id] || 0, glow);
		});
	}
	return states;
}

// ═══════════════════════════════════════════════════════════════════
// Effective wall boundary for particles (follows the wall contour)
// ═══════════════════════════════════════════════════════════════════

function getEffectiveBounds(y: number) {
	let effectiveLeft = CAVITY_LEFT + 6;
	if (y > CAVITY_TOP + 200 && y < CAVITY_TOP + 350) {
		effectiveLeft = CAVITY_LEFT + 6 + ((y - (CAVITY_TOP + 200)) / 150) * 60;
	} else if (y >= CAVITY_TOP + 350) {
		effectiveLeft = CAVITY_LEFT + 66;
	}

	let effectiveRight = CAVITY_RIGHT - 6;
	if (y > CAVITY_TOP + 180 && y < CAVITY_TOP + 380) {
		effectiveRight = CAVITY_RIGHT - 6 - ((y - (CAVITY_TOP + 180)) / 200) * 50;
	} else if (y >= CAVITY_TOP + 380) {
		effectiveRight = CAVITY_RIGHT - 56;
	}

	return { effectiveLeft, effectiveRight };
}

// ═══════════════════════════════════════════════════════════════════
// Main Component
// ═══════════════════════════════════════════════════════════════════

export const defaultPart3MoldThreeParts03TestWallsConstraintProps = {};

export const Part3MoldThreeParts03TestWallsConstraint: React.FC = () => {
	const frame = useCurrentFrame();

	// ── Dynamic states ──
	const wallFlashStates = computeWallFlashStates(frame);

	// Focus phase on "null → None" wall (frame 90-150)
	const isFocusPhase = frame >= 90 && frame <= 150;
	const focusProgress = interpolate(frame, [90, 120], [0, 1], {
		extrapolateLeft: 'clamp',
		extrapolateRight: 'clamp',
		easing: Easing.inOut(Easing.cubic),
	});

	// ── Camera zoom ──
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

	// Pan to focus on "null → None" wall (~720, 380)
	const panX = (960 - 720) * (scale - 1);
	const panY = (540 - 380) * (scale - 1);

	// ── Screen shake at frame 110-114 ──
	let shakeX = 0;
	let shakeY = 0;
	if (frame >= 110 && frame < 114) {
		const shakeAge = frame - 110;
		const shakeDecay = interpolate(shakeAge, [0, 4], [1, 0], {
			extrapolateRight: 'clamp',
		});
		shakeX = Math.sin(shakeAge * Math.PI * 2) * 2 * shakeDecay;
		shakeY = Math.cos(shakeAge * Math.PI * 1.5) * 2 * shakeDecay;
	}

	const translateX = panX + shakeX;
	const translateY = panY + shakeY;

	// ── Fill level ──
	const fillLevel = interpolate(frame, [30, 290], [0, 0.85], {
		extrapolateLeft: 'clamp',
		extrapolateRight: 'clamp',
	});
	const fillHeight = (CAVITY_BOTTOM - CAVITY_TOP) * fillLevel;
	const fillY = CAVITY_BOTTOM - fillHeight;

	// Solidification glow at end
	const solidifyOpacity = interpolate(frame, [300, 340], [0, 0.3], {
		extrapolateLeft: 'clamp',
		extrapolateRight: 'clamp',
	});

	// ── Terminal overlay ──
	const termLocalFrame = frame - 150;
	const termSlideY =
		termLocalFrame >= 0
			? interpolate(termLocalFrame, [0, 15], [20, 0], {
					extrapolateRight: 'clamp',
					easing: Easing.out(Easing.cubic),
				})
			: 20;
	const termFadeIn =
		termLocalFrame >= 0
			? interpolate(termLocalFrame, [0, 15], [0, 1], {
					extrapolateRight: 'clamp',
					easing: Easing.out(Easing.cubic),
				})
			: 0;

	return (
		<AbsoluteFill style={{ backgroundColor: BG_COLOR }}>
			{/* Camera transform wrapper */}
			<div
				style={{
					position: 'absolute',
					width: 1920,
					height: 1080,
					transform: `translate(${translateX}px, ${translateY}px) scale(${scale})`,
					transformOrigin: '960px 540px',
				}}
			>
				<svg
					width={1920}
					height={1080}
					viewBox="0 0 1920 1080"
					style={{ position: 'absolute', top: 0, left: 0 }}
				>
					<defs>
						<filter id="wallGlow" x="-50%" y="-50%" width="200%" height="200%">
							<feGaussianBlur stdDeviation="4" />
						</filter>
						<filter id="liquidGlow" x="-100%" y="-100%" width="300%" height="300%">
							<feGaussianBlur stdDeviation="3" result="blur" />
							<feMerge>
								<feMergeNode in="blur" />
								<feMergeNode in="SourceGraphic" />
							</feMerge>
						</filter>
						<radialGradient id="particleGrad" cx="50%" cy="50%" r="50%">
							<stop offset="0%" stopColor={LIQUID_COLOR} stopOpacity={0.7} />
							<stop offset="70%" stopColor={LIQUID_COLOR} stopOpacity={0.3} />
							<stop offset="100%" stopColor={LIQUID_COLOR} stopOpacity={0} />
						</radialGradient>
						<filter id="solidGlow" x="-20%" y="-20%" width="140%" height="140%">
							<feGaussianBlur stdDeviation="8" />
						</filter>
					</defs>

					{/* ── Nozzle ── */}
					<line
						x1={MOLD_CENTER_X}
						y1={NOZZLE_Y - 40}
						x2={MOLD_CENTER_X}
						y2={CAVITY_TOP}
						stroke="rgba(217, 148, 74, 0.4)"
						strokeWidth={2}
						opacity={0.5}
					/>
					<rect
						x={MOLD_CENTER_X - 15}
						y={NOZZLE_Y - 50}
						width={30}
						height={20}
						fill="rgba(217, 148, 74, 0.4)"
						rx={3}
						opacity={0.6}
					/>
					{/* Nozzle drip indicator */}
					{frame < 200 && (
						<circle
							cx={MOLD_CENTER_X}
							cy={CAVITY_TOP - 5 + ((frame * 2) % 20)}
							r={3}
							fill={LIQUID_COLOR}
							opacity={0.4}
						/>
					)}

					{/* ── Cavity background ── */}
					<rect
						x={CAVITY_LEFT}
						y={CAVITY_TOP}
						width={CAVITY_RIGHT - CAVITY_LEFT}
						height={CAVITY_BOTTOM - CAVITY_TOP}
						fill="rgba(30, 41, 59, 0.15)"
						stroke="none"
						rx={4}
					/>

					{/* ── Liquid fill level ── */}
					{fillLevel > 0.01 && (
						<rect
							x={CAVITY_LEFT + 2}
							y={fillY}
							width={CAVITY_RIGHT - CAVITY_LEFT - 4}
							height={fillHeight}
							fill={LIQUID_COLOR}
							opacity={0.08 + solidifyOpacity}
							rx={2}
						/>
					)}

					{/* ── Solidified shape glow ── */}
					{solidifyOpacity > 0 && (
						<rect
							x={CAVITY_LEFT + 2}
							y={fillY}
							width={CAVITY_RIGHT - CAVITY_LEFT - 4}
							height={fillHeight}
							fill={LIQUID_COLOR}
							opacity={solidifyOpacity * 0.4}
							rx={2}
							filter="url(#solidGlow)"
						/>
					)}

					{/* ── Liquid particles ── */}
					{PARTICLES.map((p) => {
						const age = frame - p.startFrame;
						if (age < 0) return null;

						const fadeIn = Math.min(1, age / 5);
						const t = age * 0.03;
						const baseY = CAVITY_TOP + age * p.speed;
						const nx = noise2D(p.startX * 0.04, t, p.noiseSeed);
						const ny = noise2D(t, p.startX * 0.04 + 50, p.noiseSeed + 10);

						let x = p.startX + nx * 40 + p.lateralBias * age * 0.5;
						let y = baseY + ny * 15;

						const { effectiveLeft, effectiveRight } = getEffectiveBounds(y);

						// Clamp to cavity
						x = Math.max(effectiveLeft, Math.min(effectiveRight, x));
						y = Math.max(CAVITY_TOP + 4, Math.min(CAVITY_BOTTOM - 4, y));

						// Settle at fill line
						if (y > fillY && age > 40) {
							y = fillY + seededRandom(p.id * 41) * 8;
							const bounds = getEffectiveBounds(y);
							x = bounds.effectiveLeft + seededRandom(p.id * 53) * (bounds.effectiveRight - bounds.effectiveLeft);
						}

						return (
							<circle
								key={p.id}
								cx={x}
								cy={y}
								r={p.size}
								fill="url(#particleGrad)"
								opacity={fadeIn * 0.5}
								filter="url(#liquidGlow)"
							/>
						);
					})}

					{/* ── Wall segments ── */}
					{WALL_SEGMENTS.map((seg) => {
						const flashIntensity = wallFlashStates[seg.id] || 0;
						const isFocused = isFocusPhase && seg.id === 'left-top';
						const baseOpacity = 0.4;
						const opacity = Math.min(1, baseOpacity + flashIntensity * 0.6);
						const strokeExpand = flashIntensity * 2;

						const midX = (seg.x1 + seg.x2) / 2;
						const midY = (seg.y1 + seg.y2) / 2;
						const offset = getLabelOffset(seg);

						const labelOpacity = isFocused
							? interpolate(focusProgress, [0, 1], [0.3, 1.0])
							: 0.3 + flashIntensity * 0.5;

						return (
							<g key={seg.id}>
								{/* Glow behind wall on flash */}
								{flashIntensity > 0.05 && (
									<line
										x1={seg.x1}
										y1={seg.y1}
										x2={seg.x2}
										y2={seg.y2}
										stroke="#D9944A"
										strokeWidth={WALL_STROKE + strokeExpand + 8}
										opacity={flashIntensity * 0.25}
										strokeLinecap="round"
										filter="url(#wallGlow)"
									/>
								)}
								{/* Wall line */}
								<line
									x1={seg.x1}
									y1={seg.y1}
									x2={seg.x2}
									y2={seg.y2}
									stroke="#D9944A"
									strokeWidth={WALL_STROKE + strokeExpand}
									opacity={opacity}
									strokeLinecap="round"
								/>
								{/* Label */}
								<text
									x={midX + offset.dx}
									y={midY + offset.dy}
									fill="#D9944A"
									opacity={labelOpacity}
									fontFamily={MONO_FONT}
									fontSize={9}
									textAnchor={seg.normalX > 0 ? 'end' : 'start'}
									dominantBaseline="middle"
								>
									{seg.label}
								</text>
							</g>
						);
					})}

					{/* ── Collision ripples ── */}
					{COLLISION_EVENTS.map((evt, idx) => {
						const seg = WALL_SEGMENTS.find((w) => w.id === evt.wallId);
						if (!seg) return null;
						const age = frame - evt.frame;
						if (age < 0 || age > RIPPLE_DURATION) return null;

						const midX = (seg.x1 + seg.x2) / 2;
						const midY = (seg.y1 + seg.y2) / 2;

						return (
							<g key={`ripple-${idx}`}>
								{Array.from({ length: RIPPLE_COUNT }).map((_, i) => {
									const delay = i * 3;
									const rippleAge = age - delay;
									if (rippleAge < 0) return null;

									const progress = interpolate(
										rippleAge,
										[0, RIPPLE_DURATION - delay],
										[0, 1],
										{ extrapolateRight: 'clamp' },
									);
									const radius = interpolate(
										progress,
										[0, 1],
										[4, 40 * (0.7 + i * 0.15)],
										{ extrapolateRight: 'clamp' },
									);
									const rippleOpacity = interpolate(
										progress,
										[0, 0.3, 1],
										[0.3, 0.2, 0],
										{ extrapolateRight: 'clamp' },
									);

									return (
										<circle
											key={i}
											cx={midX}
											cy={midY}
											r={radius}
											fill="none"
											stroke="#D9944A"
											strokeWidth={1.5}
											opacity={rippleOpacity * evt.intensity}
										/>
									);
								})}
							</g>
						);
					})}
				</svg>
			</div>

			{/* ── Terminal Overlay (outside camera transform) ── */}
			{termLocalFrame >= 0 && (
				<div
					style={{
						position: 'absolute',
						left: 1520,
						top: 880 + termSlideY,
						width: 320,
						height: 140,
						backgroundColor: TERMINAL_BG,
						border: `1px solid ${TERMINAL_BORDER}`,
						borderRadius: 6,
						padding: '10px 12px',
						opacity: termFadeIn,
						overflow: 'hidden',
						boxSizing: 'border-box',
					}}
				>
					{/* Title bar dots */}
					<div style={{ display: 'flex', gap: 5, marginBottom: 8 }}>
						<div style={{ width: 6, height: 6, borderRadius: '50%', backgroundColor: '#EF4444', opacity: 0.6 }} />
						<div style={{ width: 6, height: 6, borderRadius: '50%', backgroundColor: '#F59E0B', opacity: 0.6 }} />
						<div style={{ width: 6, height: 6, borderRadius: '50%', backgroundColor: '#22C55E', opacity: 0.6 }} />
					</div>
					{/* Terminal lines */}
					{TERMINAL_COMMANDS.map((cmd, idx) => {
						const lineFrame = termLocalFrame - cmd.delay;
						if (lineFrame < 0) return null;
						const lineFade = interpolate(lineFrame, [0, 8], [0, 1], {
							extrapolateRight: 'clamp',
						});
						return (
							<div
								key={idx}
								style={{
									fontFamily: MONO_FONT,
									fontSize: 10,
									color: cmd.color,
									opacity: lineFade * 0.85,
									lineHeight: '16px',
									whiteSpace: 'nowrap',
									overflow: 'hidden',
								}}
							>
								{cmd.text}
							</div>
						);
					})}
				</div>
			)}
		</AbsoluteFill>
	);
};

export default Part3MoldThreeParts03TestWallsConstraint;
