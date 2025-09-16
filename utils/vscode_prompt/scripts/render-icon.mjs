import { readFileSync, writeFileSync } from 'node:fs'
import { Resvg } from '@resvg/resvg-js'

const input = 'images/icon.svg'
const output = 'images/icon.png'

const svg = readFileSync(input)

const resvg = new Resvg(svg, {
  fitTo: { mode: 'width', value: 256 },
  background: 'transparent'
})

const png = resvg.render().asPng()
writeFileSync(output, png)
console.log(`Rendered ${output} (${png.byteLength} bytes)`) 

