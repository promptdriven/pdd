import { writeFileSync } from 'node:fs'
import { Resvg } from '@resvg/resvg-js'

const videoId = '5lBxpTSnjqo'
const srcUrl = `https://img.youtube.com/vi/${videoId}/maxresdefault.jpg`

// Fetch 16:9 thumbnail and embed into SVG with a play button overlay
const resp = await fetch(srcUrl)
if (!resp.ok) {
  throw new Error(`Failed to fetch thumbnail: ${resp.status} ${resp.statusText}`)
}
const buf = Buffer.from(await resp.arrayBuffer())
const base64 = buf.toString('base64')

// Build an SVG with the thumbnail as background and a centered play button
const width = 1280
const height = 720

const svg = `<?xml version="1.0" encoding="UTF-8"?>
<svg xmlns="http://www.w3.org/2000/svg" width="${width}" height="${height}" viewBox="0 0 ${width} ${height}">
  <defs>
    <filter id="softShadow" x="-50%" y="-50%" width="200%" height="200%">
      <feGaussianBlur in="SourceAlpha" stdDeviation="6" result="blur"/>
      <feOffset in="blur" dx="0" dy="2" result="shadow"/>
      <feMerge>
        <feMergeNode in="shadow"/>
        <feMergeNode in="SourceGraphic"/>
      </feMerge>
    </filter>
  </defs>
  <image href="data:image/jpeg;base64,${base64}" x="0" y="0" width="${width}" height="${height}" preserveAspectRatio="xMidYMid slice"/>
  <g filter="url(#softShadow)">
    <circle cx="${width/2}" cy="${height/2}" r="92" fill="rgba(0,0,0,0.55)"/>
    <polygon points="${width/2 - 28},${height/2 - 48} ${width/2 - 28},${height/2 + 48} ${width/2 + 56},${height/2}"
             fill="#ffffff"/>
  </g>
</svg>`

const resvg = new Resvg(svg, { fitTo: { mode: 'width', value: 960 } })
const png = resvg.render().asPng()
writeFileSync('images/video-thumb.png', png)
console.log('Generated images/video-thumb.png')

