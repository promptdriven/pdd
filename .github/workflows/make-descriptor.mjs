import { readFile, writeFile } from 'node:fs/promises';

const [,, releaseId, pddVersion, alphaUrl, alphaSha256, alphaIntegrity, ...values] = process.argv;
if (!releaseId || !pddVersion || !alphaUrl || !/^[a-f0-9]{64}$/.test(alphaSha256 ?? '') || !alphaIntegrity)
  throw new Error('invalid alpha asset');
if (values.length % 5 !== 0) throw new Error('invalid node asset list');
const nodes = {};
for (let i = 0; i < values.length; i += 5) {
  const [platformArch, version, url, sha256, integrity] = values.slice(i, i + 5);
  if (!/^(linux|darwin)-(x64|arm64)$/.test(platformArch) || !/^\d+\.\d+\.\d+$/.test(version)
    || !url.startsWith('https://') || !/^[a-f0-9]{64}$/.test(sha256) || !integrity.startsWith('sha512-')) throw new Error('invalid node asset');
  nodes[platformArch] = { version, url, sha256, integrity, provenance: 'nodejs.org SHASUMS256.txt' };
}
if (Object.keys(nodes).length !== 4) throw new Error('all four runtime assets are required');
const descriptor = {
  releaseId,
  pddVersion,
  manifestSeq: 0,
  alpha: { url: alphaUrl, sha256: alphaSha256, integrity: alphaIntegrity, provenance: 'GitHub Actions npm pack artifact' },
  nodes,
};
await writeFile('dist/release.json', JSON.stringify(descriptor));
await writeFile('dist/release-table.txt', Object.entries(nodes).map(([platformArch, node]) => {
  const [platform, arch] = platformArch.split('-');
  return [platform, arch, node.version, node.url, node.sha256, alphaUrl, alphaSha256, JSON.stringify(descriptor)].join('|');
}).join('\n') + '\n');
