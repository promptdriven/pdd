# User Story 22: Video Streaming with Range Requests

**As a** director reviewing a long video,
**I want** the video player to support HTTP range requests for seeking,
**So that** I can jump to any point without downloading the entire file first.

## Acceptance Criteria

- [ ] `GET /video/full` streams the full stitched video with HTTP range request support (206 Partial Content)
- [ ] `GET /video/sections/:file` streams individual section videos with range request support
- [ ] The `<video>` element can seek to any point without buffering the entire file
- [ ] Proper `Content-Range`, `Accept-Ranges`, and `Content-Length` headers are set on responses
- [ ] 416 Range Not Satisfiable returned for invalid range requests
- [ ] Video player displays total duration from metadata without downloading the full file
- [ ] Section videos are playable inline from Stage 9's [Preview] buttons

## Mapping to PRD

- Appendix A (Video API — `GET /video/full`, `GET /video/sections/:file`)
- Section 7 (Current State Assessment — range request support)

## Technical Notes

- Implement using `fs.createReadStream` with `start` and `end` options based on the `Range` header
- Video files are local (no CDN needed for V1)
- MIME type: `video/mp4` for all section and full videos
- No adaptive bitrate or transcoding — serve the rendered MP4 directly
