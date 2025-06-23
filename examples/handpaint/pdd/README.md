# Handpaint with Prompt-Driven Development (PDD)

This is a basic implementation of a handpaint application using PDD. Note that this implementation represents a naive usage of PDD and does not utilize its full capabilities.

## Overview

This project demonstrates a simple approach to creating a handpaint application using PDD principles. While PDD offers powerful features for program synthesis and development, this implementation focuses on basic functionality to illustrate the concept.

## Features

- Basic canvas for drawing
- Drawing with your finger
- Erasing with your palm

## Test this application out

- Download/clone the PDD repository
- Copy the path to handpaint_pdd.html
- Paste this into your browser search bar
- Allow the site to use your camera
- Start drawing!

## Usage

1. To draw:
   - Extend your index finger
   - Keep other fingers curled
   - Move your finger to draw
2. To erase:
   - Extend all fingers to show your palm
   - Move your hand over the area you want to erase

## Limitations

This is a learning example that shows a basic implementation of PDD concepts. For production use, consider exploring PDD's full capabilities including but not limited to:

- A more robust prompt that handles edge cases and errors
- Using `pdd test` to generate comprehensive unit tests
- Using `pdd fix` and `pdd crash` to debug and resolve issues automatically
- Using `pdd update` to keep the prompt synchronized with any manual code changes

## PDD Prompt Evolution

The final iteration of the prompt can be found in [`handpaint_html.prompt`](./handpaint_html.prompt). This prompt was used to generate the code in [`handpaint_pdd.html`](./handpaint_pdd.html).

To replicate this generation process:
1.  Install PDD by following the instructions in the main [README.md](https://github.com/gltanaka/pdd/blob/main/README.md).
2.  Create a new file named `handpaint_html.prompt`.
3.  Paste the desired iteration of the prompt into that file.
4.  Run `pdd generate --output handpaint_pdd.html handpaint_html.prompt` to generate the code.

The evolution of the prompt through various iterations demonstrates how PDD can be refined to achieve better results.

```
% You are an expert in JavaScript, HTML, and CSS. You will write a single HTML file that will use the camera to capture images from the user's webcam and allow them to draw on the screen with their finger by using mediapipe hand tracking and using the three.js library for the display. Show the mediapipe skeleton of my hand.

% Determine whether the user's hand is pointing or open palm.
    a) If open palm, allow user to erase the lines by tracking their open hand with mediapipe.
    b) If pointing, draw a line tracking their index finger.
```
```
% You are an expert in JavaScript, HTML, and CSS. You will write a single HTML file that does the following:
% 1. Accesses the user’s webcam via getUserMedia and displays the live camera feed as the background of the page (not a black screen).
% 2. Uses MediaPipe Hands to detect and draw the hand skeleton on top of the live video.
% 3. Uses Three.js to overlay interactive drawing:
    a) When the user’s hand is an open palm, enter “erase” mode: track the open hand position and erase any existing lines that intersect the hand.
    b) When the user’s index finger is pointed (other fingers down), enter “draw” mode: draw a continuous line following the tip of the index finger.
% 4. Ensure the camera feed is visible at all times, with the MediaPipe skeleton and drawing layer composited over it.
% 5. Provide proper initialization so the Three.js renderer uses the video feed texture and renders the drawing and skeleton in real time.
% 6. Include comments to show where the camera feed is set up, where MediaPipe is initialized, and where drawing/erasing logic is implemented.
```
```
% You are an expert in JavaScript, HTML, and CSS. You will write a single HTML file that does the following:
% 1. Accesses the user’s webcam via getUserMedia and displays the live camera feed as the background of the page, unmirrored (true camera orientation, not flipped).
% 2. Uses MediaPipe Hands to detect the user’s hand and draw the hand skeleton on top of the live video.
% 3. Uses Three.js to overlay interactive drawing:
% a) When the user’s hand is an open palm, display a small dot at the center of the palm (based on MediaPipe’s palm landmark). This dot is the erase “brush.”
% – Only erase the segment of any existing line underneath that dot, rather than removing the entire line.
% b) When the user’s index finger is pointed (other fingers down), enter “draw” mode: draw a continuous line following the tip of the index finger, also in unmirrored coordinates.
% 4. Ensure the live camera feed is always visible (not black), with the MediaPipe skeleton, the palm-dot eraser, and the drawing layer composited over it in real time.
% 5. Initialize Three.js so that:
% – The video feed is used as a texture/background.
% – All coordinates (drawing, skeleton, palm-dot) match the unmirrored camera orientation.
% 6. Include comments indicating:
% – Where the camera feed is set up (unmirrored).
% – Where MediaPipe Hands is initialized and its landmarks used to position the skeleton and palm dot.
% – Where the Three.js renderer is configured to draw lines and erase segments under the palm-dot.
% – Where the logic distinguishes “draw” vs. “erase” modes based on hand gestures.
```
```
% You are an expert in JavaScript, HTML, and CSS. You will write a single HTML file that does the following:
% 1. Immediately request webcam access via navigator.mediaDevices.getUserMedia and attach the live video stream to a <video> element set to play unmirrored (no CSS flip)—ensuring the camera feed is visible on the page.
% 2. Use MediaPipe Hands on that live video feed to detect the user’s hand and draw the hand skeleton on top of the video in real time.
% 3. Use Three.js to overlay interactive drawing on the same unmirrored video:
% a) When the user’s hand is an open palm, compute the palm-center landmark to display a small dot at the center of the palm. That dot acts as an erase “brush.” Only erase the segments of existing lines directly under the dot, not the entire line.
% b) When the user’s index finger is pointed (other fingers down), enter “draw” mode and draw a continuous line following the tip of the index finger in unmirrored coordinates.
% 4. Ensure the live video feed is never black—always showing the camera—and composite over it, in real time, the MediaPipe skeleton, the palm-center dot, and any drawing or erasing effects.
% 5. Initialize Three.js so that:
% – The video feed is used as a texture or background for the scene.
% – All gesture-based coordinates (skeleton lines, palm-dot, drawing strokes) correspond to the unmirrored camera orientation.
% 6. Include clear comments indicating:
% – Where and how the webcam is accessed and the <video> element is initialized unmirrored.
% – Where MediaPipe Hands is initialized and how landmarks are used to position the skeleton and palm-center dot.
% – Where the Three.js renderer is configured to draw and erase line segments under the palm dot.
% – Where the code decides between “draw” (index finger) vs. “erase” (open palm) modes based on hand landmarks.
```
```
% You are an expert in JavaScript, HTML, and CSS. You will write a single HTML file that does the following:
% 1. Accesses the user’s webcam via getUserMedia and displays the live camera feed as the background of the page (not a black screen). Mirror the video feed, so if the user's hand goes right in real life, the hand should also go right on the camera feed.
% 2. Uses MediaPipe Hands to detect and draw the hand skeleton on top of the live video.
% 3. Uses Three.js to overlay interactive drawing:
% a) When the user’s hand is an open palm, enter “erase” mode: track the middle of open hand position and erase any previous markings at the middle of the open palm. Add a dot at the middle of the palm to show where it is erasing. 
% b) When the user’s index finger is extended (index fingertip landmark significantly above its PIP joint) and all other fingertips are below their respective PIP joints, enter “draw” mode: draw a smooth, continuous line by sampling the index fingertip position each frame to ensure consistent tracking.
% 4. Ensure the camera feed is visible at all times, with the MediaPipe skeleton and drawing layer composited over it.
% 5. Provide proper initialization so the Three.js renderer uses the video feed texture and renders the drawing and skeleton in real time.
% 6. Include comments to show where the camera feed is set up, where MediaPipe is initialized, and where drawing/erasing logic is implemented.
```
```
% You are an expert in JavaScript, HTML, and CSS. You will write a single HTML file that does the following:
% 1. Accesses the user’s webcam via getUserMedia and displays the live camera feed as the background of the page (not a black screen). Mirror the video feed, so if the user's hand goes right in real life, the hand should also go right on the camera feed.
% 2. Uses MediaPipe Hands to detect and draw the hand skeleton on top of the live video. Add a dot at the middle of the palm as well. 
% 3. Uses Three.js to overlay interactive drawing:
% a) When the user’s hand is an open palm, enter “erase” mode: Treat the dot at the middle of the palm as an eraser. This should erase any previous drawings that are under the dot. 
% b) When the user’s index finger is extended (index fingertip landmark significantly above its PIP joint) and all other fingertips are below their respective PIP joints, enter “draw” mode: draw a smooth, continuous line by sampling the index fingertip position each frame to ensure consistent tracking.
% 4. Ensure the camera feed is visible at all times, with the MediaPipe skeleton and drawing layer composited over it.
% 5. Provide proper initialization so the Three.js renderer uses the video feed texture and renders the drawing and skeleton in real time.
```
```
% 1. Accesses the user’s webcam via getUserMedia and displays the live camera feed as the background of the page (not a black screen). Mirror the video feed, so if the user's hand goes right in real life, the hand should also go right on the camera feed.
% 2. Uses MediaPipe Hands to detect and draw the hand skeleton on top of the live video. Add a dot at the middle of the palm as well. 
% 3. Uses Three.js to overlay interactive drawing:
% a) When the user’s hand is an open palm, enter “erase” mode: Treat the dot at the middle of the palm as an eraser. This should erase any previous drawings that are under the dot. The eraser should use a partial erase. 
% b) When the user is pointing their index finger, and the finger is extended at any angle, enter “draw” mode:draw a line following the index fingertip position. 
% 4. Ensure the camera feed is visible at all times, with the MediaPipe skeleton and drawing layer composited over it.
% 5. Provide proper initialization so the Three.js renderer uses the video feed texture and renders the drawing and skeleton in real time.
% 6. Include comments to show where the camera feed is set up, where MediaPipe is initialized, and where drawing/erasing logic is implemented.
```

Below is the final iteration of the prompt.
```
% You are an expert in JavaScript, HTML, and CSS. You will write a single HTML file that does the following:
% 1. Accesses the user’s webcam via getUserMedia and displays the live camera feed as the background of the page (not a black screen). The live feed should mirror the user.
% 2. Uses MediaPipe Hands to detect and draw the hand skeleton on top of the live video. Add a dot at the middle of the palm as well. 
% 3. Uses Three.js to overlay interactive drawing:
% a) When the user’s hand is an open palm, enter “erase” mode: Treat the dot at the middle of the palm as a pixel eraser. 
% b) When the user is pointing their index finger, enter “draw” mode: draw one line that follows the tip of the index finger when it is extended at any angle.
% 4. Ensure the camera feed is visible at all times, with the MediaPipe skeleton and drawing layer composited over it.
% 5. Provide proper initialization so the Three.js renderer uses the video feed texture and renders the drawing and skeleton in real time.
% 6. Include comments to show where the camera feed is set up, where MediaPipe is initialized, and where drawing/erasing logic is implemented.
```