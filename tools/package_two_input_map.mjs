import assert from 'node:assert/strict';
import { mkdir, readFile, writeFile } from 'node:fs/promises';
import { join } from 'node:path';
import { runInNewContext } from 'node:vm';

const [site, generatedMap] = process.argv.slice(2);
if (!site || !generatedMap) {
  throw new Error('Usage: node tools/package_two_input_map.mjs SITE_DIRECTORY GENERATED_MAP_DIRECTORY');
}

const reportPath = new URL(
  '../archive/2026-11-20-hurwitz-speed-mean-square-v001/two-inputs.json', import.meta.url,
);
const mapBasename = 'two-input-dottie-map';
const pairField = 'determinant_pair_at_real_part_1';
const rootPage = join(site, 'index.html');
const rootNav = '<nav aria-label="Graph navigation"><a href="./two-input/">Two-input spectral map</a></nav>';
const [root, map, png, reportJSON] = await Promise.all([
  readFile(rootPage, 'utf8'),
  readFile(join(generatedMap, mapBasename + '.html'), 'utf8'),
  readFile(join(generatedMap, mapBasename + '.png')),
  readFile(reportPath, 'utf8'),
]);
const { indexed_products: products } = JSON.parse(reportJSON);

assert(root.includes('<body><main>'), 'Expected the sixth-zero page to contain its main element');
assert(map.includes('<nav aria-label="Research links">'), 'Expected the interactive map to contain its research links');
const interactivePage = map.replace(
  '<nav aria-label="Research links">',
  '<nav aria-label="Graph and research links">' +
  '<a href="../">Sixth-zero graph</a>' +
  '<a href="./two-input-dottie-map.png" download>Download map PNG</a>',
);

const embeddedImage = interactivePage.match(/src="data:image\/png;base64,([^"]+)"/);
assert(embeddedImage, 'Expected the standalone page to embed its map PNG');
assert(Buffer.from(embeddedImage[1], 'base64').equals(png), 'Download differs from the embedded PNG');

const elements = new Map();
function makeElement() {
  const listeners = new Map();
  const attributes = new Map();
  return {
    style: {},
    textContent: '',
    addEventListener(event, listener) { listeners.set(event, listener); },
    setAttribute(name, value) { attributes.set(name, value); },
    getAttribute(name) { return attributes.get(name); },
    click() { listeners.get('click')(); },
  };
}

const presets = [...interactivePage.matchAll(
  /<button\b[^>]*\bdata-h="(-?1)"\s+data-k="(-?1)"[^>]*>([^<]+)<\/button>/g,
)].map(([, h, k, textContent]) => ({ ...makeElement(), dataset: { h, k }, textContent }));
const document = {
  querySelectorAll(selector) {
    assert.equal(selector, 'button[data-h]');
    return presets;
  },
  getElementById(id) {
    assert(interactivePage.includes('id="' + id + '"'), 'Expected element #' + id);
    if (!elements.has(id)) elements.set(id, makeElement());
    return elements.get(id);
  },
};
const script = interactivePage.match(/<script>([\s\S]+?)<\/script>/);
assert(script, 'Expected interactive map JavaScript');
runInNewContext(script[1], {
  document,
  setTimeout: callback => callback(),
  clearTimeout() {},
}, { timeout: 2_000, filename: 'two-input/index.html' });

// The page prints six decimals. Check that the displayed rounding cell intersects
// each deposited enclosure for the corresponding full-series quantity.
function checkReading(value, [lower, upper], label) {
  const rounding = 0.5e-6 + 1e-14;
  assert(Number.isFinite(value) && value + rounding >= +lower && value - rounding <= +upper,
    `${label}: displayed ${value} disagrees with [${lower}, ${upper}]`);
}

function magnitudeBounds({ real, imag }) {
  const minAbs = ([lower, upper]) => lower <= 0 && upper >= 0
    ? 0 : Math.min(Math.abs(lower), Math.abs(upper));
  const maxAbs = range => Math.max(...range.map(value => Math.abs(value)));
  return [Math.hypot(minAbs(real), minAbs(imag)), Math.hypot(maxAbs(real), maxAbs(imag))];
}

assert.deepEqual(presets.map(button => button.textContent.trim()), ['+ +', '+ −', '− +', '− −']);
for (const button of presets) {
  button.click();
  assert.equal(button.getAttribute('aria-pressed'), 'true');
  const sign = button.textContent.replaceAll(' ', '').replaceAll('−', '-');
  const read = id => document.getElementById(id).textContent;
  assert.equal(read('h-value'), sign[0] === '+' ? 'π/6' : '−π/6');
  assert.equal(read('k-value'), sign[1] === '+' ? 'π/6' : '−π/6');
  const complex = read('full').match(/^(-?\d+\.\d{6}) ([+−]) (\d+\.\d{6})i$/);
  assert(complex, `${sign}: invalid complex readout`);
  const [, real, imaginarySign, imaginaryMagnitude] = complex;
  const pair = products[sign][pairField];
  checkReading(+real, pair.real, `${sign} real component`);
  checkReading((imaginarySign === '−' ? -1 : 1) * +imaginaryMagnitude, pair.imag, `${sign} imaginary component`);
  const change = read('angular');
  assert.match(change, /^\d+\.\d{6}$/);
  if (sign[0] === sign[1]) {
    // At equal shifts h-k=0, so setting h+k=0 takes the map to the deposited origin.
    const origin = products.origin[pairField];
    const subtract = ([lo, hi], [baseLo, baseHi]) => [lo - baseHi, hi - baseLo];
    const contrast = { real: subtract(pair.real, origin.real), imag: subtract(pair.imag, origin.imag) };
    checkReading(+change, magnitudeBounds(contrast), `${sign} angular change magnitude`);
  } else {
    // Opposite shifts already have h+k=0, so they are their own baseline.
    assert.equal(change, '0.000000', `${sign} angular change on the opposite-shift diagonal`);
  }
  console.log(`${sign}  ${read('full')}  Angular change: ${change}`);
}

const mapDirectory = join(site, 'two-input');
await mkdir(mapDirectory, { recursive: true });
await Promise.all([
  writeFile(join(mapDirectory, 'index.html'), interactivePage),
  writeFile(join(mapDirectory, mapBasename + '.png'), png),
  writeFile(rootPage, root.includes(rootNav) ? root : root.replace('<body><main>', '<body><main>\n' + rootNav + '\n')),
]);
