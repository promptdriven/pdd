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
    if (warning.kind==='world-schema-missing' || warning.kind==='world-writer-missing') {
      const count=wanted.world_keys.length;
      const noun=new RegExp(`\\b${count} world ${count===1?'key\\b':'keys\\b'}`);
      assert.match(warning.message,noun,'warning quantity and noun');
      if (warning.kind==='world-writer-missing') for (const path of wanted.world_keys) assert.ok(warning.message.includes(path),'warning path');
    }
    if (warning.kind==='world-writer-initial-only') for (const path of wanted.world_keys) assert.ok(warning.message.includes(path),'initial-only warning path');
    if (text!==null) {
      const lines=text.split('\n').filter(line=>line.startsWith('Warning:'));
      assert.equal(lines.length,expected.length,'one text line per warning');
      if (warning.kind==='world-schema-missing') {
        const count=wanted.world_keys.length;
        const noun=new RegExp(`\\b${count} world ${count===1?'key\\b':'keys\\b'}`);
        assert.ok(lines.some(line=>noun.test(line)&&/schema/i.test(line)),'missing schema count');
      }
      else if (warning.kind==='world-writer-missing') {
        const count=wanted.world_keys.length;
        const noun=new RegExp(`\\b${count} world ${count===1?'key\\b':'keys\\b'}`);
        assert.ok(lines.some(line=>noun.test(line)&&wanted.world_keys.every(path=>line.includes(path))),'missing writer count and paths');
      }
      else if (warning.kind==='world-writer-initial-only') assert.ok(lines.some(line=>wanted.world_keys.every(path=>line.includes(path))),'initial-only text path');
      else for (const record of wanted.records) assert.ok(lines.some(line=>line.includes(record)),'warning record identity');
    }
  }
  if (text!==null && !expected.length) assert.equal(text.split('\n').filter(line=>line.startsWith('Warning:')).length,0);
}
