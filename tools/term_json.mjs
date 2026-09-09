import assert from 'node:assert/strict';

// Canonicalize transport JSON for comparisons, not Erlang term ordering.
// Exact bit patterns remain unchanged. Duplicate output map keys are errors.
export function normalizeTermJson(value) {
  if (Array.isArray(value)) return value.map(normalizeTermJson);
  if (!value || typeof value !== 'object') return value;
  if (value.tag === 'map') {
    assert.ok(Array.isArray(value.entries), 'Map entries must be an array');
    const keyed = value.entries.map(entry => {
      assert.ok(Array.isArray(entry) && entry.length === 2, 'Map entries must be key/value pairs');
      const pair = entry.map(normalizeTermJson);
      return [JSON.stringify(pair[0]), pair];
    });
    assert.equal(new Set(keyed.map(([key]) => key)).size, keyed.length,
      'Output maps must have unique exact keys');
    keyed.sort(([left], [right]) => left < right ? -1 : left > right ? 1 : 0);
    return { entries: keyed.map(([, entry]) => entry), tag: 'map' };
  }
  if (value.tag === 'list') {
    return value.items.reduceRight((tail, head) =>
      ({ head: normalizeTermJson(head), tag: 'cons', tail }), normalizeTermJson(value.tail));
  }
  return Object.fromEntries(Object.keys(value).sort().map(key => [key, normalizeTermJson(value[key])]));
}
