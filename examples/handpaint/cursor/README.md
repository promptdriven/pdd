# Hand Paint Application

This is a hand-tracking drawing application implemented using Cursor IDE. The application uses your computer's camera to track your hand movements and allows you to draw by pointing your index finger and erase by showing your palm.

## Features

- Basic canvas for drawing
- Drawing with your finger
- Erasing with your palm

## Test this application out

- Download/clone the PDD repository
- Copy the path to handpaint.html
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

## Development Process

This application was developed through an interactive conversation with Cursor's AI assistant. To replicate this demo, first install Cursor IDE from [Cursor's website](https://cursor.sh) and log in. Once installed, and open a new .html file, and link add it as context to the Cursor agent. You can then begin to replicate the development process by using the same prompts listed in the conversation below. Please be aware that AI model responses can vary, so you may need to slightly adjust your follow-up prompts to achieve the desired outcome. Below is the conversation was used to build and refine the current application in handpaint.html:

```
User: Write code for the following application:

Using the user's camera, track the user's hand that is in frame.
Treat the user's finger as a pen, and draw where the user's finger is pointing.
If the user's palm is detected, treat it as an eraser that erases previous drawings.

[Assistant implemented initial version with basic hand tracking and drawing]

User: The drawings are not exactly where the finger is, and the left to right actions are mirrored.

[Assistant fixed coordinate calculations and mirroring issues]

User: Add dots along the hand to show what is being recognized as a finger and what is being recognized as a hand.

[Assistant added visual indicators for hand landmarks]

User: The lines that were previously drawn no longer stay on the canvas. 

[Assistant fixed the canvas clearing issue by implementing a two-canvas system]

User: I only want the app to draw the lines when the finger is pointing out on its own. If the hand is in any other configuration, don't draw anything.

[Assistant implemented finger extension detection]

User: The camera is mirrored. While the positioning of the drawing and the hand visualization is correct, the input from my camera is mirrored. Change it so that it is not mirrored.

[Assistant mirrored the display]

User: Now, the camera feed is fine, but the drawing is mirrored. I want the camera input and the drawing to be matching.

[Assistant mirrored the drawing coordinates]

User: Adjust the threshold for the finger being out to be larger. It is drawing too often as I am extending the finger.

[Assistant adjusted drawing thresholds]

User: The palm is not erasing. It should erase when the palm of the hand is visible (all 5 fingers are extended), and it should erase in the middle of the palm.

[Assistant implemented palm detection and center calculation for erasing]

User: Right now, there are two issues with the eraser:

It always erases (doesn't matter if the fingers are extended or not, leads to erasing when not intended).
The eraser is not in the middle of the palm. Rather, it is at the base of the palm.

[Assistant adjusted palm detection and moved eraser to middle]

User: It seems that the palm detection is now too strict, and barely erases.

[Assistant adjusted palm detection thresholds to be more lenient]
```

## Technical Details

The application uses:
- MediaPipe Hands for hand tracking
- HTML5 Canvas for drawing
- Two-layer canvas system for persistent drawing and landmark visualization
- Custom palm center calculation for accurate erasing
- Configurable thresholds for finger extension and palm detection

## Dependencies

- MediaPipe Hands
- MediaPipe Camera Utils
- MediaPipe Drawing Utils
