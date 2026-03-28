import React from 'react';
import { AbsoluteFill, useCurrentFrame, interpolate, Easing } from 'remotion';
import DocumentContainer from './DocumentContainer';
import AnnotationArrow from './AnnotationArrow';
import {
  BG_CANVAS,
  DOC_X,
  DOC_Y,
  DOC_PADDING,
  BOTTOM_LABEL_COLOR,
  BOTTOM_LABEL_SIZE,
  BOTTOM_LABEL_TEXT,
  ANNOTATION_PROSE_COLOR,
  ANNOTATION_CODE_COLOR,
  ANNOTATIONS_START,
  BOTTOM_LABEL_START,
  BOTTOM_LABEL_FADE_DURATION,
  FADE_OUT_START,
  FADE_OUT_DURATION,
} from './constants';

export const defaultPart4PrecisionTradeoff08EmbeddedCodeDocumentProps = {};

export const Part4PrecisionTradeoff08EmbeddedCodeDocument: React.FC = () => {
  const frame = useCurrentFrame();

  // Global fade out
  const fadeOutOpacity = interpolate(
    frame,
    [FADE_OUT_START, FADE_OUT_START + FADE_OUT_DURATION],
    [1, 0],
    { extrapolateLeft: 'clamp', extrapolateRight: 'clamp', easing: Easing.in(Easing.quad) }
  );

  // Bottom label fade-in
  const bottomLabelOpacity = interpolate(
    frame,
    [BOTTOM_LABEL_START, BOTTOM_LABEL_START + BOTTOM_LABEL_FADE_DURATION],
    [0, 1],
    { extrapolateLeft: 'clamp', extrapolateRight: 'clamp', easing: Easing.out(Easing.quad) }
  );

  // Annotation positions — relative to document
  // The prose section is roughly at Y=350 (within the document area)
  // The code block is roughly at Y=530 (within the document area)
  const proseArrowY = DOC_Y + DOC_PADDING + 100; // ~288 — points at prose area
  const codeArrowY = DOC_Y + DOC_PADDING + 310; // ~498 — points at code block area
  const arrowFromX = DOC_X - 70; // left of document
  const arrowToX = DOC_X - 4; // just outside document border

  return (
    <AbsoluteFill
      style={{
        backgroundColor: BG_CANVAS,
        opacity: fadeOutOpacity,
      }}
    >
      {/* Document container with text and code */}
      <DocumentContainer />

      {/* Annotation arrows */}
      <AnnotationArrow
        fromX={arrowFromX}
        fromY={proseArrowY}
        toX={arrowToX}
        toY={proseArrowY}
        label="Natural language"
        color={ANNOTATION_PROSE_COLOR}
        labelOpacity={0.5}
        startFrame={ANNOTATIONS_START}
      />
      <AnnotationArrow
        fromX={arrowFromX}
        fromY={codeArrowY}
        toX={arrowToX}
        toY={codeArrowY}
        label="Embedded code"
        color={ANNOTATION_CODE_COLOR}
        labelOpacity={0.5}
        startFrame={ANNOTATIONS_START + 20}
      />

      {/* Bottom label */}
      <div
        style={{
          position: 'absolute',
          bottom: 60,
          left: 0,
          right: 0,
          textAlign: 'center',
          fontFamily: 'Inter, sans-serif',
          fontSize: BOTTOM_LABEL_SIZE,
          fontWeight: 400,
          color: BOTTOM_LABEL_COLOR,
          opacity: bottomLabelOpacity,
        }}
      >
        {BOTTOM_LABEL_TEXT}
      </div>
    </AbsoluteFill>
  );
};

export default Part4PrecisionTradeoff08EmbeddedCodeDocument;
