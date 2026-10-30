import assert from 'node:assert/strict';

// Warning wording is advisory. The approved vectors own its structured facts.
export function checkWarnings(actual,expected,text = null) {
  assert.ok(Array.isArray(actual),'warnings array');
  assert.equal(actual.length,expected.length,'warning count');
  for (let i=0;i<actual.length;i++) {
    const warning=actual[i], wanted=expected[i];
    assert.equal(typeof warning.message,'string');
    assert.ok(warning.message.trim() && warning.message.length<=8000 && !/[\x00-\x1f\x7f]/.test(warning.message),'finite warning message');
    assert.deepEqual(Object.fromEntries(Object.keys(wanted).map(key=>[key,warning[key]])),wanted);
    assert.deepEqual(Object.keys(warning).sort(),[...Object.keys(wanted),'message'].sort(),'warning fields');
    if (text!==null) {
      const lines=text.split('\n').filter(line=>line.startsWith('Warning:'));
      assert.equal(lines.length,expected.length,'one text line per warning');
      if (warning.kind==='world-schema-missing') assert.ok(lines.some(line=>new RegExp(`\\b${wanted.world_keys.length}\\b`).test(line)&&/schema/i.test(line)),'missing schema count');
      else for (const record of wanted.records) assert.ok(lines.some(line=>line.includes(record)),'warning record identity');
    }
  }
  if (text!==null && !expected.length) assert.equal(text.split('\n').filter(line=>line.startsWith('Warning:')).length,0);
}
