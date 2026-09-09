// Run serially from the repository root. --skip-export reuses the retained
// artifact while still checking its pinned provenance and emitted Lean AST.
import assert from 'node:assert/strict';
import { spawnSync } from 'node:child_process';
import { createHash } from 'node:crypto';
import { mkdtempSync, readFileSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { join } from 'node:path';

const flags = new Set(process.argv.slice(2));
assert.ok([...flags].every(flag => flag === '--skip-export'), 'Unknown check_dijkstra option');
const source = 'tests/fixtures/erlang/dijkstra.erl';
const directory = 'tests/fixtures/erlang/dijkstra';
const artifact = join(directory, 'core.json');
const exporter = 'tools/export_core.escript';
const executable = '.lake/build/bin/erlean';
const env = { ...process.env, ERL_FLAGS: '+S 2:2 +SDcpu 1 +SDio 1', LEAN_NUM_THREADS: '1' };
function run(command, args) {
  const result = spawnSync(command, args, { encoding: 'utf8', env, timeout: 30000, maxBuffer: 16 * 1024 * 1024 });
  if (result.error) throw result.error;
  assert.equal(result.status, 0, `${command} ${args.slice(0, 3).join(' ')}: ${result.stderr}`);
  return result.stdout;
}
const digest = bytes => createHash('sha256').update(bytes).digest('hex');
const manifest = JSON.parse(readFileSync(join(directory, 'manifest.json'), 'utf8'));
assert.equal(manifest.otp_version, '29.0.6');
assert.deepEqual(manifest.compiler_options,
  ['to_core', 'binary', 'no_copt', 'deterministic', 'return_errors', 'return_warnings']);
assert.equal(manifest.source_sha256, digest(readFileSync(source)));
assert.equal(manifest.core_sha256, digest(readFileSync(artifact)));
assert.equal(manifest.exporter_sha256, digest(readFileSync(exporter)));
if (!flags.has('--skip-export')) {
  const temporary = mkdtempSync(join(tmpdir(), 'erlean-dijkstra-'));
  for (const attempt of ['first', 'second']) {
    const destination = join(temporary, attempt);
    run('asdf', ['exec', 'escript', exporter, source, destination]);
    for (const name of ['core.json', 'manifest.json', 'inventory.json']) {
      assert.deepEqual(readFileSync(join(destination, name)), readFileSync(join(directory, name)),
        `Reproducible Dijkstra ${name}`);
    }
  }
}
assert.equal(run(executable, ['emit', artifact, 'importedDijkstraModule']),
  readFileSync('Erlean/Examples/Dijkstra/Imported.lean', 'utf8'),
  'Dijkstra proofs must use the exact AST emitted from the retained artifact');

const integer = value => ({ tag: 'integer', value: String(value) });
const nil = { tag: 'nil' };
const list = items => ({ tag: 'list', items, tail: nil });
const tuple = items => ({ tag: 'tuple', items });
const graphValue = edges => list(edges.map(edge => tuple(edge.map(integer))));
function decodeDistances(value) {
  const result = [];
  while (value.tag === 'cons') {
    assert.equal(value.head.tag, 'tuple');
    assert.equal(value.head.items.length, 2);
    assert.ok(value.head.items.every(item => item.tag === 'integer'));
    result.push(value.head.items.map(item => BigInt(item.value)));
    value = value.tail;
  }
  assert.deepEqual(value, nil, 'The distances result must be a proper list');
  return result;
}

// Independent Bellman-Ford relaxation computes distances without any priority
// queue or settlement order. BigInt preserves integers beyond Number precision.
function shortestDistances(sourceVertex, edges) {
  const vertices = new Set([sourceVertex, ...edges.flatMap(([from, to]) => [from, to])]);
  const distance = new Map([[sourceVertex, 0n]]);
  for (let pass = 1; pass < vertices.size; pass++) {
    let changed = false;
    for (const [from, to, weight] of edges) {
      if (!distance.has(from)) continue;
      const candidate = distance.get(from) + weight;
      if (!distance.has(to) || candidate < distance.get(to)) {
        distance.set(to, candidate);
        changed = true;
      }
    }
    if (!changed) break;
  }
  return distance;
}
const big = 9007199254740993n;
const cases = [
  ['empty', 0, []],
  ['isolated source', 9, [[0, 1, 4], [1, 2, 5]]],
  ['single directed edge', 0, [[0, 1, 7]]],
  ['reverse direction unreachable', 1, [[0, 1, 7]]],
  ['improved queued distance', 0, [[0, 1, 10], [0, 2, 1], [2, 1, 2]]],
  ['certificate triangle', 0, [[0, 1, 9], [0, 2, 2], [2, 1, 3]]],
  ['certificate zero cycle and disconnected edge', 0, [[0, 1, 0], [1, 0, 0], [1, 2, 4], [3, 4, 1]]],
  ['proof graph', 0, [[0, 1, 4], [0, 2, 1], [2, 1, 2], [1, 3, 1], [2, 3, 5], [3, 4, 3], [0, 4, 20], [8, 9, 1]]],
  ['nonzero source', 2, [[0, 1, 4], [0, 2, 1], [2, 1, 2], [1, 3, 1], [2, 3, 5], [3, 4, 3], [0, 4, 20]]],
  ['zero cycle', 0, [[0, 1, 0], [1, 2, 0], [2, 0, 0], [2, 3, 2]]],
  ['self loops', 0, [[0, 0, 0], [0, 0, 8], [0, 1, 3], [1, 1, 0]]],
  ['parallel edges', 0, [[0, 1, 9], [0, 1, 2], [0, 1, 2], [1, 2, 4]]],
  ['equal-distance branches', 0, [[0, 1, 1], [0, 2, 1], [1, 3, 1], [2, 3, 1]]],
  ['disconnected zero cycle', 0, [[0, 1, 2], [8, 9, 0], [9, 8, 0]]],
  ['large distances', 0, [[0, 1, big], [1, 2, big], [0, 2, 2n * big + 1n]]],
  ['large vertex identities', big, [[big, big + 1n, 3], [big + 1n, big + 2n, 4], [0, 1, 0]]],
  ['dense graph', 0, Array.from({ length: 5 }, (_, from) =>
    Array.from({ length: 5 }, (_, to) => [from, to, (from * 7 + to * 3) % 6])).flat()],
];
for (const [label, rawSource, rawEdges] of cases) {
  const sourceVertex = BigInt(rawSource);
  const edges = rawEdges.map(edge => edge.map(BigInt));
  const argumentsJson = JSON.stringify([integer(sourceVertex), graphValue(edges)]);
  const lean = JSON.parse(run(executable, ['run', artifact, 'distances', argumentsJson, '500000']));
  const otp = JSON.parse(run('asdf', ['exec', 'escript', 'tools/otp_oracle.escript',
    source, 'distances', argumentsJson]));
  assert.deepEqual(lean, otp, `OTP differential: ${label}`);
  assert.equal(lean.status, 'returned', label);
  assert.equal(lean.values.length, 1, label);
  const actual = decodeDistances(lean.values[0]);
  const expected = shortestDistances(sourceVertex, edges);
  assert.equal(actual.length, expected.size, `Reachable vertex count: ${label}`);
  assert.equal(new Set(actual.map(([vertex]) => vertex)).size, actual.length, `No duplicate settlements: ${label}`);
  assert.deepEqual(actual[0], [sourceVertex, 0n], `Source distance: ${label}`);
  for (const [index, [vertex, distance]] of actual.entries()) {
    assert.ok(expected.has(vertex), `Reachability: ${label}`);
    assert.equal(distance, expected.get(vertex), `Bellman-Ford distance: ${label}, vertex ${vertex}`);
    if (index) assert.ok(actual[index - 1][1] <= distance, `Settlement ordering: ${label}`);
  }
}
const invalidCases = [
  [integer(0), graphValue([[0, 1, -1]])],
  [integer(0), graphValue([[8, 9, -1]])],
  [integer(-1), nil],
  [integer(0), graphValue([[0, -1, 3]])],
  [integer(0), list([tuple([integer(0), integer(1)])])],
  [integer(0), { tag: 'atom', value: 'not_a_graph' }],
  [{ tag: 'atom', value: 'not_a_source' }, nil],
  [integer(0), list([tuple([integer(0), integer(1), { tag: 'atom', value: 'not_a_weight' }])])],
  [integer(0), list([tuple([{ tag: 'atom', value: 'not_a_vertex' }, integer(1), integer(2)])])],
  [integer(0), list([tuple([integer(0), { tag: 'atom', value: 'not_a_vertex' }, integer(2)])])],
  [integer(0), { tag: 'list', items: [tuple([integer(0), integer(1), integer(2)])],
    tail: { tag: 'atom', value: 'improper_tail' } }],
];
for (const values of invalidCases) {
  const argumentsJson = JSON.stringify(values);
  const lean = JSON.parse(run(executable, ['run', artifact, 'distances', argumentsJson]));
  const otp = JSON.parse(run('asdf', ['exec', 'escript', 'tools/otp_oracle.escript',
    source, 'distances', argumentsJson]));
  assert.deepEqual(lean, otp, 'Invalid Dijkstra input differential');
  assert.deepEqual(lean, { status: 'raised', class: 'error', reason: { tag: 'atom', value: 'badarg' } });
}
console.log(`Dijkstra checks passed: ${cases.length} graphs against OTP 29.0.6 and independent BigInt Bellman-Ford; ${invalidCases.length} rejected inputs; exact emitted AST and provenance. Testing is not a universal correctness proof.`);
