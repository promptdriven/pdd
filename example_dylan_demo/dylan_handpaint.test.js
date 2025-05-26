const puppeteer = require('puppeteer');
const path = require('path');

describe('Hand Paint Application Tests', () => {
    let browser;
    let page;

    beforeAll(async () => {
        browser = await puppeteer.launch({
            headless: false, // We need to see the browser for visual testing
            args: ['--use-fake-ui-for-media-stream'] // This allows us to mock the camera
        });
        page = await browser.newPage();
    });

    afterAll(async () => {
        await browser.close();
    });

    beforeEach(async () => {
        // Load the application before each test
        await page.goto(`file:${path.join(__dirname, 'dylan_handpaint.html')}`);
        
        // Mock the camera
        await page.evaluateOnNewDocument(() => {
            // Mock getUserMedia
            navigator.mediaDevices.getUserMedia = async () => {
                return new MediaStream();
            };
        });
    });

    test('Application loads successfully', async () => {
        // Check if canvas and video elements exist
        const canvas = await page.$('#canvas');
        const video = await page.$('#video');
        
        expect(canvas).not.toBeNull();
        expect(video).not.toBeNull();
    });

    test('Canvas dimensions are correct', async () => {
        const dimensions = await page.evaluate(() => {
            const canvas = document.getElementById('canvas');
            return {
                width: canvas.width,
                height: canvas.height
            };
        });

        expect(dimensions.width).toBe(640);
        expect(dimensions.height).toBe(480);
    });

    test('Drawing functionality works', async () => {
        // Mock hand landmarks for drawing
        await page.evaluate(() => {
            const mockLandmarks = {
                multiHandLandmarks: [[
                    { x: 0.5, y: 0.5 }, // Palm
                    { x: 0.5, y: 0.5 }, // Wrist
                    { x: 0.5, y: 0.5 }, // Thumb
                    { x: 0.5, y: 0.5 }, // Index finger base
                    { x: 0.5, y: 0.5 }, // Index finger middle
                    { x: 0.5, y: 0.5 }, // Index finger tip
                    { x: 0.5, y: 0.5 }, // Middle finger base
                    { x: 0.5, y: 0.5 }, // Middle finger middle
                    { x: 0.6, y: 0.6 }, // Index finger tip (drawing point)
                    { x: 0.5, y: 0.5 }, // Ring finger base
                    { x: 0.5, y: 0.5 }, // Ring finger middle
                    { x: 0.5, y: 0.5 }, // Ring finger tip
                    { x: 0.5, y: 0.5 }, // Pinky base
                    { x: 0.5, y: 0.5 }, // Pinky middle
                    { x: 0.5, y: 0.5 }, // Pinky tip
                    { x: 0.5, y: 0.5 }, // Index finger base
                    { x: 0.5, y: 0.5 }, // Index finger middle
                    { x: 0.5, y: 0.5 }, // Index finger tip
                    { x: 0.5, y: 0.5 }, // Middle finger base
                    { x: 0.5, y: 0.5 }, // Middle finger middle
                    { x: 0.5, y: 0.5 }  // Middle finger tip
                ]]
            };

            // Trigger the hands.onResults callback
            window.hands.onResults(mockLandmarks);
        });

        // Check if drawing occurred
        const hasDrawing = await page.evaluate(() => {
            const canvas = document.getElementById('canvas');
            const ctx = canvas.getContext('2d');
            const imageData = ctx.getImageData(0, 0, canvas.width, canvas.height);
            return imageData.data.some(pixel => pixel !== 0);
        });

        expect(hasDrawing).toBe(true);
    });

    test('Eraser functionality works', async () => {
        // First draw something
        await page.evaluate(() => {
            const canvas = document.getElementById('canvas');
            const ctx = canvas.getContext('2d');
            ctx.beginPath();
            ctx.moveTo(100, 100);
            ctx.lineTo(200, 200);
            ctx.strokeStyle = '#00ff00';
            ctx.lineWidth = 5;
            ctx.stroke();
        });

        // Mock hand landmarks for erasing (palm close to index finger)
        await page.evaluate(() => {
            const mockLandmarks = {
                multiHandLandmarks: [[
                    { x: 0.4, y: 0.4 }, // Palm (close to index finger)
                    { x: 0.5, y: 0.5 }, // Wrist
                    { x: 0.5, y: 0.5 }, // Thumb
                    { x: 0.5, y: 0.5 }, // Index finger base
                    { x: 0.5, y: 0.5 }, // Index finger middle
                    { x: 0.5, y: 0.5 }, // Index finger tip
                    { x: 0.5, y: 0.5 }, // Middle finger base
                    { x: 0.5, y: 0.5 }, // Middle finger middle
                    { x: 0.41, y: 0.41 }, // Index finger tip (close to palm)
                    { x: 0.5, y: 0.5 }, // Ring finger base
                    { x: 0.5, y: 0.5 }, // Ring finger middle
                    { x: 0.5, y: 0.5 }, // Ring finger tip
                    { x: 0.5, y: 0.5 }, // Pinky base
                    { x: 0.5, y: 0.5 }, // Pinky middle
                    { x: 0.5, y: 0.5 }, // Pinky tip
                    { x: 0.5, y: 0.5 }, // Index finger base
                    { x: 0.5, y: 0.5 }, // Index finger middle
                    { x: 0.5, y: 0.5 }, // Index finger tip
                    { x: 0.5, y: 0.5 }, // Middle finger base
                    { x: 0.5, y: 0.5 }, // Middle finger middle
                    { x: 0.5, y: 0.5 }  // Middle finger tip
                ]]
            };

            // Trigger the hands.onResults callback
            window.hands.onResults(mockLandmarks);
        });

        // Check if erasing occurred
        const hasErased = await page.evaluate(() => {
            const canvas = document.getElementById('canvas');
            const ctx = canvas.getContext('2d');
            const imageData = ctx.getImageData(150, 150, 50, 50); // Check area where eraser should have worked
            return !imageData.data.some(pixel => pixel !== 0);
        });

        expect(hasErased).toBe(true);
    });

    test('MediaPipe Hands initialization', async () => {
        const handsInitialized = await page.evaluate(() => {
            return window.hands !== undefined;
        });

        expect(handsInitialized).toBe(true);
    });

    test('Camera initialization', async () => {
        const cameraInitialized = await page.evaluate(() => {
            return window.camera !== undefined;
        });

        expect(cameraInitialized).toBe(true);
    });
}); 