// example_usage.ts
// Comprehensive usage example for lib/sse.ts
// Demonstrates the SSE stream factory: createSseStream, send, done, error.
//
// This file exercises the module directly — no Next.js runtime needed.
// It reads back the ReadableStream to verify the SSE wire format.

import { createSseStream } from '../lib/sse';

// ============================================================================
// Helper: consume a ReadableStream and return the decoded text
// ============================================================================

async function consumeStream(stream: ReadableStream<Uint8Array>): Promise<string> {
  const reader = stream.getReader();
  const decoder = new TextDecoder();
  let result = '';

  while (true) {
    const { done, value } = await reader.read();
    if (done) break;
    result += decoder.decode(value, { stream: true });
  }
  result += decoder.decode(); // flush
  return result;
}

// ============================================================================
// Example 1: Basic send + done — happy-path pipeline progress
// ============================================================================

async function example1_sendAndDone(): Promise<void> {
  console.log('=== Example 1: send() + done() ===');

  const { stream, send, done } = createSseStream();

  // Simulate pipeline progress updates
  send({ step: 'ingest', progress: 25 });
  send({ step: 'transcode', progress: 50 });
  send({ step: 'render', progress: 75 });
  send({ step: 'export', progress: 100 });

  // Signal successful completion
  done();

  // Read back and verify the SSE wire format
  const output = await consumeStream(stream);
  console.log(output);

  // Verify each message follows SSE data format: "data: {...}\n\n"
  const lines = output.split('\n\n').filter(Boolean);
  console.log(`Message count: ${lines.length}`);

  // First four are data messages
  for (let i = 0; i < 4; i++) {
    const parsed = JSON.parse(lines[i].replace('data: ', ''));
    console.log(`  Message ${i + 1}: step=${parsed.step}, progress=${parsed.progress}`);
  }

  // Last one is the done event
  console.log(`  Done event: ${lines[4]}`);
  console.log('');
}

// ============================================================================
// Example 2: send + error — pipeline failure
// ============================================================================

async function example2_sendAndError(): Promise<void> {
  console.log('=== Example 2: send() + error() ===');

  const { stream, send, error } = createSseStream();

  // Simulate partial progress then failure
  send({ step: 'ingest', progress: 25 });
  send({ step: 'transcode', progress: 50 });

  // Signal an error
  error('Transcode failed: unsupported codec');

  // Read back the stream
  const output = await consumeStream(stream);
  console.log(output);

  // Verify the error event format
  const lines = output.split('\n\n').filter(Boolean);
  console.log(`Message count: ${lines.length}`);

  // Last message is the error event with both event: and data: lines
  const errorEvent = lines[lines.length - 1];
  const errorLines = errorEvent.split('\n');
  console.log(`  Error event line: ${errorLines[0]}`);
  console.log(`  Error data line: ${errorLines[1]}`);

  const errorData = JSON.parse(errorLines[1].replace('data: ', ''));
  console.log(`  Error message: ${errorData.message}`);
  console.log('');
}

// ============================================================================
// Example 3: Stream is closed after done() — subsequent calls are no-ops
// ============================================================================

async function example3_closedAfterDone(): Promise<void> {
  console.log('=== Example 3: Stream closed after done() ===');

  const { stream, send, done } = createSseStream();

  send({ step: 'ingest', progress: 100 });
  done();

  // These should be silently ignored (stream already closed)
  send({ step: 'ghost', progress: 999 });
  send({ step: 'phantom', progress: 0 });

  const output = await consumeStream(stream);
  const lines = output.split('\n\n').filter(Boolean);

  console.log(`Messages after done(): ${lines.length} (expected 2: 1 data + 1 done event)`);
  console.log(output);
}

// ============================================================================
// Example 4: Stream is closed after error() — subsequent calls are no-ops
// ============================================================================

async function example4_closedAfterError(): Promise<void> {
  console.log('=== Example 4: Stream closed after error() ===');

  const { stream, send, done, error } = createSseStream();

  error('Immediate failure');

  // These should be silently ignored
  send({ step: 'never', progress: 0 });
  done();

  const output = await consumeStream(stream);
  const lines = output.split('\n\n').filter(Boolean);

  console.log(`Messages after error(): ${lines.length} (expected 1: error event only)`);
  console.log(output);
}

// ============================================================================
// Example 5: Using with Response (simulated Next.js route handler pattern)
// ============================================================================

async function example5_responsePattern(): Promise<void> {
  console.log('=== Example 5: Next.js Response pattern ===');

  const { stream, send, done } = createSseStream();

  // Build a Response exactly as a Next.js route handler would
  const response = new Response(stream, {
    headers: {
      'Content-Type': 'text/event-stream',
      'Cache-Control': 'no-cache',
      'Connection': 'keep-alive',
    },
  });

  // Fire-and-forget async work (typical pattern)
  send({ status: 'started' });
  send({ status: 'processing', detail: 'Generating frames...' });
  done();

  // Verify the Response is correctly formed
  console.log(`Content-Type: ${response.headers.get('Content-Type')}`);
  console.log(`Cache-Control: ${response.headers.get('Cache-Control')}`);
  console.log(`Connection: ${response.headers.get('Connection')}`);

  // Read the body
  const body = await response.text();
  console.log(`\nResponse body:\n${body}`);
}

// ============================================================================
// Run all examples
// ============================================================================

async function main(): Promise<void> {
  await example1_sendAndDone();
  await example2_sendAndError();
  await example3_closedAfterDone();
  await example4_closedAfterError();
  await example5_responsePattern();

  console.log('All examples completed successfully');
}

main().catch(console.error);
