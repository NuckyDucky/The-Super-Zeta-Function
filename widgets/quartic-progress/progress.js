const elements = Object.fromEntries(
  [...document.querySelectorAll("[id]")].map((element) => [element.id, element]),
);
const motion = matchMedia("(prefers-reduced-motion: reduce)");
const numbers = new Intl.NumberFormat();
const rangeNumber = new Intl.NumberFormat(undefined, { maximumFractionDigits: 6 });
const clock = new Intl.DateTimeFormat(undefined, { timeStyle: "medium" });
const snapshotDate = new Intl.DateTimeFormat(undefined, {
  dateStyle: "medium", timeStyle: "short", timeZone: "UTC",
});
const theme = getComputedStyle(document.documentElement);
const bulbColor = (name) => theme.getPropertyValue(`--bulb-${name}`).trim();
const colors = ["cyan", "blue", "ruby", "gold", "green", "violet"].map(bulbColor);
const pendingColor = bulbColor("off");
const stageTwo = createStageTwo();
const galaxy = createGalaxy();
const gpuCanvas = elements.grid.cloneNode();
const gpu = createLightField(gpuCanvas);
if (gpu) elements.grid.replaceWith(gpuCanvas);
const canvas = gpu ? gpuCanvas : elements.grid;
const context = gpu ? null : canvas.getContext("2d");
const field = gpu ? null : document.createElement("canvas");
const fieldContext = field?.getContext("2d");
const TWINKLE_PERIOD = 4300;
const states = {
  checking: "Kernel checking",
  assembly: "Assembling prefix",
  enclosures: "Checking enclosures",
  ready: "Ready for full replay",
  replay: "Replaying proof",
  complete: "Stage 1 verified",
  interrupted: "Run interrupted",
  waiting: "Waiting for checks",
  offline: "Connection lost",
};
const fresh = new Map();
const enclosureLights = [];
const enclosureBandCounts = [];
let snapshot;
let geometry;
let paintRequest;
let celebrationStart;
let celebrated = false;
let nextDrawAt = -Infinity;
const duty = { from: 0, to: 0, started: 0 };
let updatedAt = -Infinity;
let finishedIndices = [];

function status(state) {
  if (elements.state.dataset.state !== state || elements.state.textContent !== states[state]) {
    elements.state.dataset.state = state;
    elements.state.textContent = states[state];
  }
}

function lamp(id, checked, active) {
  elements[id].classList.toggle("passed", checked);
  elements[id].classList.toggle("active", active && !checked);
}

function layout() {
  if (!snapshot || !elements["stage-one-history"].open) return;
  const width = canvas.clientWidth;
  const cols = Math.min(140, Math.max(42, Math.floor(width / (width < 480 ? 5 : 8))));
  const xStep = width / cols;
  const yStep = Math.min(5.7, Math.max(3.8, xStep * .75));
  const height = Math.ceil(Math.ceil(snapshot.total / cols) * yStep);
  const ratio = Math.min(devicePixelRatio || 1, 1.5);
  geometry = { width, height, cols, xStep, yStep, ratio };
  canvas.style.height = `${height}px`;
  canvas.width = Math.round(width * ratio);
  canvas.height = Math.round(height * ratio);
  if (gpu) gpu.resize(geometry);
  else {
    field.width = canvas.width;
    field.height = canvas.height;
    drawField();
  }
  scheduleDraw();
}

function cell(index) {
  const { cols, xStep, yStep } = geometry;
  const gap = xStep < 5 ? .95 : 1.45;
  return [index % cols * xStep, Math.floor(index / cols) * yStep, xStep - gap, yStep - gap];
}

function cellSeed(index) {
  const mixed = Math.imul(index + 1, 0x9e3779b1) ^ Math.imul(snapshot.groups[index] + 1, 0x85ebca77);
  return (mixed ^ (mixed >>> 16)) >>> 0;
}

function lampColor(index) { return colors[cellSeed(index) % colors.length]; }

function drawField() {
  const { width, height, ratio } = geometry;
  fieldContext.setTransform(ratio, 0, 0, ratio, 0, 0);
  fieldContext.clearRect(0, 0, width, height);
  for (let index = 0; index < snapshot.total; index++) {
    const [x, y, cellWidth, cellHeight] = cell(index);
    const state = snapshot.bits[index];
    const lit = state === "1";
    fieldContext.fillStyle = lit ? lampColor(index) : state === "2" ? "#000" : pendingColor;
    if (lit) {
      fieldContext.globalAlpha = .15;
      fieldContext.fillRect(x - .4, y - .4, cellWidth + .8, cellHeight + .8);
      fieldContext.globalAlpha = 1;
    }
    fieldContext.fillRect(x, y, cellWidth, cellHeight);
  }
}

function draw(time) {
  paintRequest = undefined;
  const animated = !motion.matches && !document.hidden;
  const frameTime = 1000 / (gpu ? 144 : 24);
  if (animated && time < nextDrawAt - .4) {
    scheduleDraw();
    return;
  }
  nextDrawAt = time - nextDrawAt < frameTime ? nextDrawAt + frameTime : time + frameTime;
  const clockPosition = time / TWINKLE_PERIOD;
  const cycle = {
    phase: clockPosition % 1,
    round: Math.floor(clockPosition),
    duty: animated ? dutyAt(time) : 0,
  };
  const finish = celebrationStart === undefined ? -1 : (time - celebrationStart) / 1000;
  if (gpu) {
    gpu.draw(cycle, animated ? (time - updatedAt) / 1000 : -1, finish);
  } else {
    drawCanvas(time, cycle);
  }
  if (finish >= 7 || !animated) celebrationStart = undefined;
  if (animated && (snapshot.count || celebrationStart !== undefined)) scheduleDraw();
}

function drawCanvas(time, cycle) {
  const { width, height, ratio } = geometry;
  context.setTransform(ratio, 0, 0, ratio, 0, 0);
  context.clearRect(0, 0, width, height);
  context.drawImage(field, 0, 0, width, height);
  context.globalCompositeOperation = "screen";
  if (cycle.duty) {
    for (const index of finishedIndices) {
      const localPhase = (cellSeed(index) & 65535) / 65536;
      const phase = (cycle.phase + localPhase) % 1;
      if (phase >= cycle.duty) continue;
      const light = Math.sin(Math.PI * phase / cycle.duty) ** 2;
      if (light < .06) continue;
      const [x, y, w, h] = cell(index);
      context.globalAlpha = light * .38;
      context.fillStyle = lampColor(index);
      context.fillRect(x - 1, y - 1, w + 2, h + 2);
      context.globalAlpha = light * .72;
      context.fillStyle = lampColor(index);
      context.fillRect(x, y, w, h);
    }
  }
  if (motion.matches) fresh.clear();
  for (const [index, started] of fresh) {
    const age = (time - started) / 1500;
    if (age >= 1) {
      fresh.delete(index);
      continue;
    }
    const glow = (1 - age) ** 2;
    context.globalAlpha = glow;
    context.shadowColor = lampColor(index);
    context.shadowBlur = 9;
    context.fillStyle = lampColor(index);
    context.fillRect(...cell(index));
    context.shadowBlur = 0;
    context.globalAlpha = glow * .65;
    context.fillStyle = lampColor(index);
    context.fillRect(...cell(index));
  }
  context.globalAlpha = 1;
  context.shadowBlur = 0;
  if (celebrationStart !== undefined) drawCelebration(time);
  context.globalCompositeOperation = "source-over";
}

function twinkleRate({ count, total }) {
  const base = 10 + Math.floor(100 * count / (15 * total));
  return count === total ? 4 * base : base;
}

function dutyAt(time) {
  const t = Math.min(1, Math.max(0, (time - duty.started) / 800));
  return duty.from + (duty.to - duty.from) * t * t * (3 - 2 * t);
}

function drawCelebration(time) {
  const elapsed = time - celebrationStart;
  if (elapsed >= 7000 || motion.matches) {
    celebrationStart = undefined;
    return;
  }
  const { cols } = geometry;
  const rows = Math.ceil(snapshot.total / cols);
  const wave = elapsed / 2600 - .2;
  for (let index = 0; index < snapshot.total; index++) {
    if (snapshot.bits[index] !== "1") continue;
    const [x, y, width, height] = cell(index);
    const position = .55 * (index % cols) / cols + .45 * Math.floor(index / cols) / rows;
    const ripple = Math.max(0, 1 - Math.abs((wave % 1.15) - position) * 8);
    const sparkleAt = (cellSeed(index) % 3200) + position * 2500;
    const sparkle = Math.max(0, 1 - Math.abs(sparkleAt - elapsed) / 190);
    const fade = Math.min(1, (7000 - elapsed) / 1000);
    const brightness = Math.max(.54 * ripple ** 2, .88 * sparkle ** 2) * fade;
    if (brightness <= .02) continue;
    context.globalAlpha = brightness;
    context.fillStyle = lampColor(index);
    context.fillRect(x, y, width, height);
    if (sparkle > .86 && index % 7 === 0) {
      context.shadowColor = lampColor(index);
      context.shadowBlur = 12;
      context.fillRect(x - 1, y - 1, width + 2, height + 2);
      context.shadowBlur = 0;
    }
  }
  context.globalAlpha = 1;
}

function celebrateWhenReady() {
  if (celebrated || !snapshot?.replayPass || document.hidden || !elements["stage-one-history"].open) return;
  celebrated = true;
  if (!motion.matches) {
    celebrationStart = performance.now();
    scheduleDraw();
  }
}

function scheduleDraw() {
  if (paintRequest === undefined && !document.hidden && elements["stage-one-history"].open) {
    paintRequest = requestAnimationFrame(draw);
  }
}

function apply(next) {
  const previous = snapshot;
  snapshot = next;
  const nextDuty = twinkleRate(next) / 100;
  if (nextDuty !== duty.to) {
    const now = performance.now();
    duty.from = previous ? dutyAt(now) : nextDuty;
    duty.to = nextDuty;
    duty.started = now;
  }
  const changed = previous?.bits !== next.bits;
  if (changed) {
    updatedAt = performance.now();
    if (gpu) {
      gpu.update(next, previous);
    } else {
      finishedIndices = [];
      for (let index = 0; index < next.total; index++) {
        if (next.bits[index] === "1") finishedIndices.push(index);
        if (previous && previous.bits[index] !== "1" && next.bits[index] === "1" && !motion.matches) {
          fresh.set(index, updatedAt);
        }
        if (previous?.bits[index] === "1" && next.bits[index] === "0") fresh.delete(index);
      }
    }
  }
  if (!previous || previous.total !== next.total) layout();
  else if (changed && elements["stage-one-history"].open) {
    if (!gpu) drawField();
    scheduleDraw();
  }

  status(next.state);
  const isArchive = next.mode === "archive";
  elements["view-mode"].textContent = isArchive ? "Archived snapshot" : "Live localhost";
  document.body.classList.toggle("proof-passed", next.replayPass);
  celebrateWhenReady();
  elements.percent.textContent = (100 * next.count / next.total).toFixed(1);
  elements["batch-count"].textContent = numbers.format(next.count);
  elements["batch-total"].textContent = `/ ${numbers.format(next.total)}`;
  showTwinkleRate();
  elements.rate.textContent = next.recent && next.state === "checking"
    ? `${(next.recent / 15).toFixed(1)} batches per minute · last 15 min`
    : "Saved kernel checks";
  elements["block-count"].textContent = `${next.blocks} / ${next.blockTotal}`;
  showEnclosures(next);
  stageTwo.update(next);
  galaxy.update(next);
  elements["kernel-status"].textContent = next.kernelPass ? "Passed" : next.state === "enclosures"
    ? "Checking enclosures" : "Pending";
  elements["replay-status"].textContent = next.replayPass ? "Passed" : next.replayCount
    ? `${next.replayCount} rebuilt` : next.state === "replay" ? "Building" : "Queued";
  lamp("block-lamp", next.blocks === next.blockTotal, next.state === "checking" || next.state === "assembly");
  lamp("kernel-lamp", next.kernelPass, next.state === "enclosures");
  lamp("replay-lamp", next.replayPass, next.state === "replay");
  elements.axioms.hidden = next.axioms.length === 0;
  elements.axioms.textContent = next.axioms.length ? `Axioms · ${next.axioms.join(", ")}` : "";
  const updated = new Date(next.time * 1000);
  elements.updated.dateTime = updated.toISOString();
  elements.updated.textContent = isArchive
    ? `Snapshot recorded ${snapshotDate.format(updated)} UTC`
    : `Last checked at ${clock.format(updated)}`;
  canvas.setAttribute("aria-label",
    `${numbers.format(next.count)} of ${numbers.format(next.total)} numerical batches passed. Illuminated cells represent saved checks.`);
}

function showEnclosures(next) {
  const total = next.enclosureTotal || 0;
  if (!total || !next.enclosureBands || (next.count < next.total && !next.enclosures)) return;
  elements["enclosure-strip"].hidden = false;
  elements["enclosure-count"].textContent = numbers.format(next.enclosures);
  elements["enclosure-total"].textContent = `/ ${numbers.format(total)} modules`;
  elements["enclosure-lights"].setAttribute("aria-label",
    `${next.enclosures} of ${total} enclosure modules passed`);
  if (enclosureLights.length !== total) {
    enclosureLights.length = 0;
    enclosureBandCounts.length = 0;
    const fragment = document.createDocumentFragment();
    for (const band of next.enclosureBands) {
      const section = document.createElement("div");
      const heading = document.createElement("p");
      heading.className = "enclosure-band-head";
      const range = document.createElement("span");
      range.textContent = `x ${rangeNumber.format(band.lo)}–${rangeNumber.format(band.hi)}`;
      const count = document.createElement("strong");
      heading.append(range, count);
      const row = document.createElement("div");
      row.className = "enclosure-band-lights";
      for (let index = band.start; index < band.stop; index++) {
        const bulb = document.createElement("span");
        bulb.className = "enclosure-bulb";
        bulb.style.setProperty("--module-bulb", colors[index % colors.length]);
        row.append(bulb);
        enclosureLights.push(bulb);
      }
      section.append(heading, row);
      fragment.append(section);
      enclosureBandCounts.push(count);
    }
    elements["enclosure-lights"].replaceChildren(fragment);
  }
  for (const [index, band] of next.enclosureBands.entries()) {
    let passed = 0;
    for (let cell = band.start; cell < band.stop; cell++) passed += Number(next.enclosureBits[cell] === "1");
    enclosureBandCounts[index].textContent = `${passed}/${band.stop - band.start}`;
  }
  for (const [index, bulb] of enclosureLights.entries()) {
    const bit = next.enclosureBits[index];
    const state = bit === "1" ? "passed" : bit === "2" ? "failed" : "processing";
    bulb.dataset.status = state;
    bulb.title = `Enclosure module ${index + 1} · ${state}`;
  }
  updateEnclosureReadout(next);
}

function updateEnclosureReadout(next) {
  const live = next.enclosureLive;
  let event = "Preparing the interval checker";
  let detail = "Lean is building the lemmas that the enclosure modules import.";
  if (live) {
    const active = live.active === 1 ? "1 module in progress" : `${live.active} modules in progress`;
    event = `Checking ${live.module}`;
    detail = `Cells ${live.first}–${live.first + live.count - 1} · x ∈ [${rangeNumber.format(live.lo)}, ${rangeNumber.format(live.hi)}] · ${active}`;
  } else if (next.enclosures === next.enclosureTotal) {
    event = "All interval modules accepted";
    detail = next.kernelPass
      ? "Lean assembled the bounds into the quartic kernel certificate."
      : "Lean is assembling the bounds into the quartic kernel certificate.";
  } else if (next.state === "interrupted") {
    event = "Replay interrupted";
    detail = "The saved enclosure checks are still available.";
  }
  if (elements["enclosure-event"].textContent !== event) elements["enclosure-event"].textContent = event;
  if (elements["enclosure-detail"].textContent !== detail) elements["enclosure-detail"].textContent = detail;
}

function showTwinkleRate() {
  if (!snapshot) return;
  elements["twinkle-rate"].textContent = motion.matches
    ? "Twinkle paused"
    : `${twinkleRate(snapshot)}% twinkle`;
}

async function refresh() {
  try {
    const response = await fetch("./progress.json", { cache: "no-store", signal: AbortSignal.timeout(5000) });
    if (!response.ok) throw new Error("Progress endpoint unavailable");
    const next = await response.json();
    apply(next);
    if (next.mode === "archive") return;
  } catch {
    status("offline");
  }
  setTimeout(refresh, snapshot?.replayPass ? 30000 : document.hidden ? 15000 : 5000);
}

canvas.addEventListener("pointermove", (event) => {
  if (!geometry) return;
  const row = Math.floor(event.offsetY / geometry.yStep);
  const col = Math.floor(event.offsetX / geometry.xStep);
  const index = row * geometry.cols + col;
  if (index < 0 || index >= snapshot.total) return;
  const state = snapshot.bits[index] === "1" ? "Passed" : snapshot.bits[index] === "2" ? "Failed" : "Processing";
  elements["cell-detail"].textContent = `Block ${snapshot.groups[index]} · Batch ${index + 1} · ${state}`;
});
canvas.addEventListener("pointerleave", () => { elements["cell-detail"].textContent = ""; });
window.addEventListener("resize", layout);
elements["stage-one-history"].addEventListener("toggle", () => {
  if (elements["stage-one-history"].open) {
    layout();
    celebrateWhenReady();
  } else if (paintRequest !== undefined) {
    cancelAnimationFrame(paintRequest);
    paintRequest = undefined;
  }
});
document.addEventListener("visibilitychange", () => {
  celebrateWhenReady();
  if (snapshot) scheduleDraw();
});
motion.addEventListener("change", () => {
  showTwinkleRate();
  if (snapshot) scheduleDraw();
});
refresh();

function bulletinFor(next) {
  if (next.replayPass) {
    const status = next.mode === "archive" ? "At this snapshot, Lean was idle." : "Lean is idle.";
    return `${status} In the last recorded check the imaginary part was negative, zero, and positive at three low-height points, with opposite values at the reflected pair. The next check is to bound j² + k² away from zero throughout the right ring.`;
  }
  if (next.state === "interrupted") return "The replay stopped. Lean’s saved checks are still available.";
  if (next.state === "waiting") return "No recent Lean activity. The page is waiting for the next saved check.";
  if (next.state === "ready") return "The quartic certificate passed. The full-proof replay is ready to start.";
  if (next.state === "enclosures") {
    const active = next.enclosureLive;
    if (active) {
      const lo = rangeNumber.format(active.lo);
      const hi = rangeNumber.format(active.hi);
      return `Lean is checking ${active.module}. It bounds the theta sum and the quartic kernel on the intervals between x = ${lo} and x = ${hi}.`;
    }
    return "This phase checks rational lower and upper bounds for the quartic kernel over each grid interval.";
  }
  if (next.state === "replay") {
    return `Lean is rebuilding the proof against the checked quartic certificate. It has rebuilt ${next.replayCount} of ${next.replayTotal} proof modules.`;
  }
  if (next.state === "assembly") {
    return "Lean is joining the checked coefficient batches into prefix blocks and validating positivity of the running sums.";
  }
  return "Lean is checking the coefficient batches that supply the signed running sums for the quartic certificate.";
}

function updateSegment(next) {
  const publication = next.publicationReplay;
  const stopped = next.state === "interrupted" || publication?.failed;
  let label, count, total, units, passed;
  if (publication) {
    ({ count, total, passed } = publication);
    label = "Publication replay";
    units = "modules";
  } else if (next.kernelPass) {
    label = "Full-proof replay";
    count = next.replayCount;
    total = next.replayTotal ?? 95;
    passed = next.replayPass;
    units = "modules";
  } else if (next.state === "enclosures" || next.enclosures) {
    label = "Theta enclosures";
    count = next.enclosures;
    total = next.enclosureTotal;
    units = "modules";
  } else if (next.state === "assembly" || next.count === next.total) {
    label = "Signed prefix assembly";
    count = next.blocks;
    total = next.blockTotal;
    units = "blocks";
  } else {
    label = "Numerical certificate";
    count = next.count;
    total = next.total;
    units = "batches";
  }
  if (!total) return;
  const bar = elements["segment-bar"];
  bar.max = total;
  bar.value = count;
  elements["segment-label"].textContent = label;
  const percent = Math.floor(100 * count / total);
  const suffix = stopped ? " · Paused" : passed ? " · Audit passed"
    : count === total ? " · Assembling and auditing" : count === 0 && next.state === "ready" ? " · Queued" : "";
  elements["segment-readout"].textContent =
    `${percent}% · ${numbers.format(count)} / ${numbers.format(total)} ${units} checked${suffix}`;
}

function createStageTwo() {
  const milestones = [
    { label: "Quartic handoff", x: 200, y: 31, color: "gold", status: "waiting",
      evidence: "Stage 1", detail: "Replay the full proof with the kernel-checked quartic certificate." },
    { label: "Height and box", x: 316, y: 113, color: "cyan", status: "kernel",
      evidence: "Kernel magic", detail: "For any reference T ≥ 203, place the right disk at 33/64 + i(T − 1/512), then recover the input and its Super Zeta address w/2." },
    { label: "Mirror the rings", x: 272, y: 247, color: "blue", status: "kernel",
      evidence: "Kernel magic", detail: "Murphy’s specialization gives theta reflection. At the same height the mirror keeps the j-axis reading and reverses the k-axis reading." },
    { label: "Test both axes", x: 128, y: 247, color: "ruby", status: "next",
      evidence: "Current focus", detail: "At a chosen height, bound j² + k² away from zero across the right ring. The reflected reading then gives the matching result on the left." },
    { label: "Cover candidates", x: 84, y: 113, color: "violet", status: "queued",
      evidence: "Next proof target", detail: "Prove that any off-line candidate in the target domain falls in a ring covered by the axis test or its mirror, using the original Super Zeta address." },
  ];
  let selected = 3;
  const arms = [...elements["stage-arms"].children];
  const buttons = milestones.map((milestone, index) => {
    const button = document.createElement("button");
    button.type = "button";
    button.className = "stage-point";
    const color = bulbColor(milestone.color);
    button.style.setProperty("--point-color", color);
    arms[index].style.setProperty("--point-color", color);
    button.style.setProperty("--point-delay", `-${.83 * index}s`);
    button.style.left = `${milestone.x / 4}%`;
    button.style.top = `${milestone.y / 3}%`;
    const light = document.createElement("i");
    light.setAttribute("aria-hidden", "true");
    const label = document.createElement("span");
    const percent = document.createElement("strong");
    percent.className = "stage-point-percent";
    label.append(milestone.label, percent);
    button.append(light, label);
    button.addEventListener("click", () => {
      selected = index;
      render();
    });
    elements["stage-star"].append(button);
    return { button, percent };
  });

  function setText(element, text) {
    if (element.textContent !== text) element.textContent = text;
  }

  function render() {
    const verified = milestones.filter(({ status }) => status === "kernel").length;
    setText(elements["stage-progress-percent"], `${Math.round(100 * verified / milestones.length)}%`);
    setText(elements["stage-progress-count"], `${verified} of ${milestones.length} milestones verified`);
    for (const [index, { button, percent }] of buttons.entries()) {
      const { label, status, evidence } = milestones[index];
      if (button.dataset.status !== status) {
        button.dataset.status = status;
        arms[index].dataset.status = status;
      }
      const value = status === "kernel" ? "100%" : status === "queued" ? "0%" : "—";
      const readable = value === "—" ? "Progress unmeasured" : `${value} verified`;
      setText(percent, value);
      button.setAttribute("aria-pressed", String(index === selected));
      button.setAttribute("aria-label", `${label} · ${evidence} · ${readable}`);
    }
    const { label, evidence, detail } = milestones[selected];
    setText(elements["star-evidence"], evidence);
    setText(elements["star-milestone"], label);
    setText(elements["star-description"], detail);
  }

  render();
  return {
    update(next) {
      updateSegment(next);
      const handoff = milestones[0];
      handoff.status = next.replayPass ? "kernel" : next.state === "interrupted" ? "failed" : "waiting";
      handoff.evidence = next.replayPass ? "Kernel magic" : next.state === "interrupted" ? "Interrupted" :
        next.kernelPass ? "Full replay" : "Quartic build";
      handoff.detail = next.replayPass
        ? `The audit passed with ${numbers.format(next.replayCount)} fresh modules and ${numbers.format(next.replayCertificateCount)} verified certificate modules.`
        : next.kernelPass ? `${next.replayCount} of ${next.replayTotal} fresh modules compiled against the certificate.`
          : `${next.enclosures} of ${next.enclosureTotal} enclosure modules checked.`;
      setText(elements["stage-one-status"], next.replayPass ? "Audit passed" :
        next.kernelPass ? `${next.replayCount} / ${next.replayTotal} replay modules` : states[next.state]);
      setText(elements["broadcast-message"], bulletinFor(next));
      render();
    },
  };
}

function createGalaxy() {
  const sky = elements["galaxy-sky"].getContext("2d");
  if (sky) {
    let seed = 2381;
    const random = () => {
      seed = (Math.imul(seed, 1664525) + 1013904223) >>> 0;
      return seed / 2 ** 32;
    };
    for (let index = 0; index < 620; index++) {
      const x = random() * 512;
      const band = 98 - 34 * Math.sin(x / 126);
      const y = index < 400 ? band + (random() + random() - 1) * 86 : random() * 180;
      const size = index % 23 === 0 ? 1.5 : .55 + random() * .6;
      sky.fillStyle = colors[index % colors.length];
      sky.globalAlpha = .09 + random() * (size > 1.3 ? .34 : .17);
      sky.fillRect(x, y, size, size);
    }
  }

  const tracks = [
    {
      title: "Gaussian quartic", color: "gold", wire: "M0,46 Q25,50 50,30 T100,6",
      curve: [47, 41, 30, 17, 9],
      entries: [
        ["Numerical batches", (p) => `Lean checked ${numbers.format(p.count)} of ${numbers.format(p.total)} numerical batches.`, (p) => check(p.count, p.total, p.state === "checking")],
        ["Prefix assembly", (p) => `Lean assembled ${p.blocks} of ${p.blockTotal} prefix blocks for the range through coefficient 2²⁵.`, (p) => check(p.blocks, p.blockTotal, p.state === "assembly")],
        ["Interval enclosures", (p) => `Lean checked ${p.enclosures} of ${p.enclosureTotal} modules bounding the theta kernel over real intervals.`, (p) => check(p.enclosures, p.enclosureTotal, p.state === "enclosures")],
        ["Quartic certificate", (p) => p.kernelPass ? "The finished certificate passed its transitive axiom audit." : "The finished certificate combines the prefix and enclosure proofs with the sign theorem.", (p) => p.kernelPass ? "kernel" : p.enclosures === p.enclosureTotal ? "active" : "queued"],
        ["Full proof replay", (p) => p.replayPass ? `All ${p.replayTotal} fresh proof modules compiled against the kernel-checked certificate.` : `${p.replayCount} of ${p.replayTotal} fresh proof modules rebuilt against the certificate.`, (p) => p.replayPass ? "kernel" : p.state === "replay" ? "active" : "queued"],
      ],
      readout: (p) => p.replayPass ? "Full proof audited" : p.kernelPass ? `${p.replayCount} / 95 replay modules` : p.enclosures ? `${p.enclosures} / ${p.enclosureTotal} enclosures` : `${numbers.format(p.count)} / ${numbers.format(p.total)} batches`,
    },
    {
      title: "Dottie spire", color: "cyan", wire: "M0,40 Q25,1 50,8 T100,42",
      curve: [29, 12, 8, 14, 29],
      entries: [
        ["Reciprocal maps", "Lean rebuilt the ordered two-step return and Dottie multiplier lemmas.", "kernel"],
        ["Trapping-disk theorem", "Lean checked the general criterion that turns disk containment, contraction, and divisor exclusions into a period certificate.", "kernel"],
        ["Period-320 witnesses", "A 384-bit interval replay checked both phase origins at three marked parameters, including primitive-period exclusions.", "interval"],
        ["Concrete disk data", "The phase-Q case has 640 directed exponential stages recorded for a certificate replay.", "prepared"],
        ["Concrete Lean replay", "Feed the phase-Q disk data into the trapping-disk theorem and audit the resulting theorem.", "queued"],
      ],
      readout: () => "6 interval-checked witnesses",
    },
    {
      title: "Super Zeta", color: "violet", wire: "M0,13 Q25,54 50,43 T100,8",
      curve: [24, 39, 43, 33, 18],
      entries: [
        ["Quartet spectrum", "Lean rebuilt the spectrum and reference-spectrum modules.", "kernel"],
        ["Mellin components", "Lean rebuilt the kernel and Mellin-step modules and printed their axiom dependencies.", "kernel"],
        ["Dottie-height contour", "The archived directed contour counted two critical-line zeros in the Dottie window.", "interval"],
        ["CUDA phase reduction", "The warm GPU reduced the benchmark in 16.5 ms versus 147.0 ms on CPU. Directed phase anchors ran on CPU.", "measured"],
        ["Next anchored replay", "Exercise the GPU scheduler in a fresh forecast and retain the directed verifier for the result.", "queued"],
      ],
      readout: () => "4 Lean modules rebuilt",
    },
  ];
  const evidence = {
    kernel: "Kernel magic", interval: "Interval replay", measured: "Benchmark",
    prepared: "Data ready", active: "Running", queued: "Queued", failed: "Interrupted",
  };
  let current;
  let selected;
  const quartic = tracks[0].entries;

  function check(count, total, active) {
    return total > 0 && count === total ? "kernel" : active ? "active" : "queued";
  }

  function stage(entry, autoFocus) {
    if (typeof entry[2] !== "function") return entry[2];
    if (!current) return "queued";
    const state = entry[2](current);
    return current.state === "interrupted" && entry === autoFocus && state !== "kernel" ? "failed" : state;
  }

  function setText(element, value) {
    if (element.textContent !== value) element.textContent = value;
  }

  const routes = tracks.map((track) => {
    const route = document.createElement("section");
    route.className = "galaxy-route";
    route.style.color = bulbColor(track.color);
    const heading = document.createElement("h3");
    heading.textContent = track.title;
    const readout = document.createElement("p");
    readout.className = "galaxy-readout";
    const lamps = document.createElement("div");
    lamps.className = "galaxy-string";
    const ns = "http://www.w3.org/2000/svg";
    const wire = document.createElementNS(ns, "svg");
    wire.setAttribute("viewBox", "0 0 100 56");
    wire.setAttribute("preserveAspectRatio", "none");
    wire.setAttribute("aria-hidden", "true");
    const curve = document.createElementNS(ns, "path");
    curve.setAttribute("d", track.wire);
    wire.append(curve);
    lamps.append(wire);
    const buttons = track.entries.map((entry, index) => {
      const button = document.createElement("button");
      button.type = "button";
      button.className = "galaxy-bulb";
      button.style.left = `${12 + 19 * index}%`;
      button.style.top = `${track.curve[index] / 56 * 100}%`;
      button.style.animationDelay = `-${index * 1.13 + track.curve[index] * .06}s`;
      const flare = document.createElement("i");
      flare.setAttribute("aria-hidden", "true");
      button.append(flare);
      button.addEventListener("click", () => {
        selected = entry;
        render();
      });
      button.addEventListener("animationend", (event) => {
        if (event.animationName === "galaxy-arrival") button.classList.remove("new-light");
      });
      lamps.append(button);
      return button;
    });
    route.append(lamps, heading, readout);
    elements["galaxy-routes"].append(route);
    return { readout, buttons };
  });

  function render(animateArrival = false) {
    const autoFocus = quartic.find((entry) => stage(entry) !== "kernel") ?? quartic[4];
    const focus = selected ?? autoFocus;
    tracks.forEach((track, i) => {
      if (current || i > 0) setText(routes[i].readout, track.readout(current));
      track.entries.forEach((entry, j) => {
        const button = routes[i].buttons[j];
        const state = stage(entry, autoFocus);
        if (button.dataset.status !== state) {
          button.dataset.status = state;
          if (animateArrival && state === "kernel" && !motion.matches) button.classList.add("new-light");
        }
        const pressed = String(entry === focus);
        const label = `${track.title} · ${entry[0]} · ${evidence[state]}`;
        if (button.getAttribute("aria-pressed") !== pressed) button.setAttribute("aria-pressed", pressed);
        if (button.getAttribute("aria-label") !== label) {
          button.setAttribute("aria-label", label);
          button.title = `${entry[0]} · ${evidence[state]}`;
        }
      });
    });
    setText(elements["galaxy-evidence"], evidence[stage(focus, autoFocus)]);
    setText(elements["galaxy-milestone"], focus[0]);
    const description = focus[1];
    setText(elements["galaxy-description"], typeof description === "function"
      ? current ? description(current) : "Waiting for the live Lean snapshot." : description);
  }

  render();
  return {
    update(next) {
      const animateArrival = Boolean(current);
      current = next;
      render(animateArrival);
    },
  };
}

function createLightField(target) {
  const gl = target.getContext("webgl2", {
    alpha: true, antialias: false, depth: false, stencil: false, premultipliedAlpha: false,
    powerPreference: "low-power",
  });
  if (!gl) return null;

  const pulseModel = `
    uint scramble(uint bits) {
      bits ^= bits >> 16;
      bits *= 0x7feb352du;
      bits ^= bits >> 15;
      bits *= 0x846ca68bu;
      return bits ^ (bits >> 16);
    }

    float offsetFor(int index) {
      return float(scramble(uint(index)) & 65535u) / 65536.0;
    }

    float pulseFor(float phase, float duty) {
      if (phase >= duty) return 0.0;
      float pulse = sin(3.14159265 * phase / duty);
      return pulse * pulse;
    }

    float arrivalFor(uint mark, float age) {
      if ((mark & 128u) == 0u || age < 0.0 || age >= 1.9) return -1.0;
      return age / 1.9;
    }

    float finalShimmer(int index, vec2 cell, ivec2 grid, float age) {
      if (age < 0.0 || age >= 7.0) return 0.0;
      float rows = ceil(float(grid.y) / float(grid.x));
      float position = 0.55 * cell.x / float(grid.x) + 0.45 * cell.y / rows;
      float wave = mod(age / 2.6 - 0.2, 1.15);
      float ripple = max(0.0, 1.0 - abs(wave - position) * 7.0);
      float sparkleAt = float(scramble(uint(index)) & 4095u) / 1280.0 + position * 2.5;
      float sparkle = max(0.0, 1.0 - abs(sparkleAt - age) / 0.23);
      return max(0.78 * ripple * ripple, sparkle * sparkle) * clamp(7.0 - age, 0.0, 1.0);
    }`;

  const vertex = `#version 300 es
    void main() {
      vec2 position = vec2(float((gl_VertexID << 1) & 2), float(gl_VertexID & 2));
      gl_Position = vec4(position * 2.0 - 1.0, 0.0, 1.0);
    }`;
  const fragment = `#version 300 es
    precision highp float;
    precision highp int;
    uniform highp usampler2D cells;
    uniform vec3 palette[${colors.length}];
    uniform vec3 offColor;
    uniform ivec2 grid;
    uniform vec4 geometry;
    uniform float pixelHeight;
    uniform vec4 timing;
    out vec4 pixel;
    ${pulseModel}

    void main() {
      vec2 screen = vec2(gl_FragCoord.x, pixelHeight - gl_FragCoord.y) / geometry.w;
      vec2 cell = floor(screen / geometry.xy);
      int index = int(cell.y) * grid.x + int(cell.x);
      if (int(cell.x) >= grid.x || index >= grid.y) {
        pixel = vec4(0.0);
        return;
      }

      vec2 center = (geometry.xy - geometry.z) * 0.5;
      vec2 delta = abs(screen - cell * geometry.xy - center);
      float edge = max(delta.x - center.x + 0.25, delta.y - center.y + 0.25);
      float face = 1.0 - smoothstep(-0.22, 0.28, edge);
      uint mark = texelFetch(cells, ivec2(index & 255, index >> 8), 0).r;
      uint colorCode = mark & 63u;
      if (colorCode == 0u) {
        pixel = vec4((mark & 64u) != 0u ? vec3(0.0) : offColor, face);
        return;
      }

      vec3 bulb = palette[int(colorCode) - 1];
      float glow = pulseFor(fract(timing.x + offsetFor(index)), timing.y);
      float arrival = arrivalFor(mark, timing.z);
      if (arrival >= 0.0) glow = max(glow, (1.0 - arrival) * (1.0 - arrival));
      glow = max(glow, finalShimmer(index, cell, grid, timing.w));

      vec2 radius = max(vec2(1.0), center * vec2(0.82, 0.93));
      float ellipse = length(delta / radius);
      float filament = exp(-3.8 * ellipse * ellipse);
      float glass = 1.0 - smoothstep(0.58, 1.14, ellipse);
      float aura = (0.27 + 0.72 * glow) * exp(-1.55 * ellipse * ellipse);
      vec3 light = bulb * (0.73 + 0.38 * filament + (0.31 + 0.19 * filament) * glow);
      pixel = vec4(light, max(glass, aura));
    }`;

  const flareVertex = `#version 300 es
    precision highp float;
    precision highp int;
    uniform highp usampler2D cells;
    uniform vec3 palette[${colors.length}];
    uniform ivec2 grid;
    uniform vec4 geometry;
    uniform vec2 viewportSize;
    uniform vec4 timing;
    uniform uint cycleIndex;
    flat out vec3 tint;
    flat out float power;
    flat out float arrival;
    out vec2 lens;
    ${pulseModel}

    void main() {
      int index = gl_InstanceID;
      uint mark = texelFetch(cells, ivec2(index & 255, index >> 8), 0).r;
      uint code = mark & 63u;
      gl_Position = vec4(2.0, 2.0, 0.0, 1.0);
      if (code == 0u || timing.y <= 0.0) return;

      vec2 cell = vec2(float(index % grid.x), float(index / grid.x));
      float clock = timing.x + offsetFor(index);
      uint lap = cycleIndex + uint(floor(clock));
      bool spark = (scramble(uint(index) ^ (lap * 0x9e3779b1u)) & 31u) < 4u;
      float twinkle = spark ? pow(pulseFor(fract(clock), timing.y), 5.0) : 0.0;
      float closing = finalShimmer(index, cell, grid, timing.w);
      arrival = arrivalFor(mark, timing.z);
      float nova = arrival >= 0.0 ? pow(1.0 - arrival, 1.45) : 0.0;
      power = max(nova, max(0.82 * twinkle, 0.82 * closing * closing * closing));
      if (power < 0.08) return;

      lens = 2.0 * vec2(float(gl_VertexID & 1), float(gl_VertexID >> 1)) - 1.0;
      float drift = arrival >= 0.0 ? (1.0 - exp(-5.0 * arrival)) : 0.0;
      float extent = 9.0 + 4.0 * power + 13.0 * drift;
      vec2 center = (cell * geometry.xy + (geometry.xy - geometry.z) * 0.5 + extent * lens) * geometry.w;
      vec2 clip = 2.0 * center / viewportSize - 1.0;
      gl_Position = vec4(clip.x, -clip.y, 0.0, 1.0);
      tint = palette[int(code) - 1];
    }`;

  const flareFragment = `#version 300 es
    precision highp float;
    precision highp int;
    uniform highp usampler2D cells;
    uniform ivec2 grid;
    uniform vec4 geometry;
    uniform vec2 viewportSize;
    flat in vec3 tint;
    flat in float power;
    flat in float arrival;
    in vec2 lens;
    out vec4 pixel;

    void main() {
      vec2 physical = vec2(gl_FragCoord.x, viewportSize.y - gl_FragCoord.y) / geometry.w;
      ivec2 tile = ivec2(physical / geometry.xy);
      int index = tile.y * grid.x + tile.x;
      if (tile.x >= grid.x || index >= grid.y) discard;
      if ((texelFetch(cells, ivec2(index & 255, index >> 8), 0).r & 63u) == 0u) discard;

      vec2 axial = abs(lens);
      float radius = length(lens);
      float armX = exp(-52.0 * axial.y) * pow(max(0.0, 1.0 - axial.x), 2.2);
      float armY = exp(-52.0 * axial.x) * pow(max(0.0, 1.0 - axial.y), 2.2);
      float diagonals = exp(-37.0 * abs(axial.x - axial.y)) * pow(max(0.0, 1.0 - 1.5 * radius), 2.7);
      float bloom = exp(-14.0 * radius * radius);
      float ring = 0.0;
      if (arrival >= 0.0) {
        float radiusOfFront = 0.08 + 0.84 * arrival;
        float front = (radius - radiusOfFront) / 0.046;
        ring = 0.65 * exp(-front * front);
      }
      float opacity = power * (0.63 * max(armX, armY) + 0.25 * diagonals + 0.31 * bloom + ring);
      if (opacity < 0.008) discard;
      pixel = vec4(tint * (1.03 + 0.1 * bloom), min(0.93, opacity));
    }`;

  function shader(kind, source) {
    const stage = gl.createShader(kind);
    gl.shaderSource(stage, source);
    gl.compileShader(stage);
    if (!gl.getShaderParameter(stage, gl.COMPILE_STATUS)) {
      throw new Error(gl.getShaderInfoLog(stage));
    }
    return stage;
  }

  function link(vertexSource, fragmentSource) {
    const program = gl.createProgram();
    const stages = [shader(gl.VERTEX_SHADER, vertexSource), shader(gl.FRAGMENT_SHADER, fragmentSource)];
    for (const stage of stages) gl.attachShader(program, stage);
    gl.linkProgram(program);
    for (const stage of stages) gl.deleteShader(stage);
    if (!gl.getProgramParameter(program, gl.LINK_STATUS)) {
      throw new Error(gl.getProgramInfoLog(program));
    }
    return program;
  }

  let bulbProgram;
  let flareProgram;
  try {
    bulbProgram = link(vertex, fragment);
    flareProgram = link(flareVertex, flareFragment);
  } catch (error) {
    console.warn("WebGL lights unavailable", error);
    gl.getExtension("WEBGL_lose_context")?.loseContext();
    return null;
  }

  function rgb(hex) {
    return [1, 3, 5].map((offset) => parseInt(hex.slice(offset, offset + 2), 16) / 255);
  }
  function bind(program, names) {
    const uniforms = Object.fromEntries(
      ["cells", "palette[0]", "grid", "geometry", "timing", ...names]
        .map((name) => [name, gl.getUniformLocation(program, name)]),
    );
    gl.useProgram(program);
    gl.uniform3fv(uniforms["palette[0]"], colors.flatMap(rgb));
    gl.uniform1i(uniforms.cells, 0);
    return uniforms;
  }
  const bulbs = bind(bulbProgram, ["offColor", "pixelHeight"]);
  gl.uniform3fv(bulbs.offColor, rgb(pendingColor));
  const flares = bind(flareProgram, ["viewportSize", "cycleIndex"]);
  gl.blendFuncSeparate(gl.SRC_ALPHA, gl.ONE_MINUS_SRC_ALPHA, gl.ONE, gl.ONE_MINUS_SRC_ALPHA);
  const texture = gl.createTexture();
  gl.bindTexture(gl.TEXTURE_2D, texture);
  gl.texParameteri(gl.TEXTURE_2D, gl.TEXTURE_MIN_FILTER, gl.NEAREST);
  gl.texParameteri(gl.TEXTURE_2D, gl.TEXTURE_MAG_FILTER, gl.NEAREST);
  let texels;
  let cols = 1;

  target.dataset.renderer = "webgl2";
  return {
    resize({ cols: columns, xStep, yStep, ratio }) {
      cols = columns;
      gl.viewport(0, 0, target.width, target.height);
      const gap = xStep < 5 ? 0.95 : 1.45;
      gl.useProgram(bulbProgram);
      gl.uniform4f(bulbs.geometry, xStep, yStep, gap, ratio);
      gl.uniform1f(bulbs.pixelHeight, target.height);
      gl.useProgram(flareProgram);
      gl.uniform4f(flares.geometry, xStep, yStep, gap, ratio);
      gl.uniform2f(flares.viewportSize, target.width, target.height);
    },
    update(next, previous) {
      const rows = Math.ceil(next.total / 256);
      const resized = texels?.length !== 256 * rows;
      if (resized) texels = new Uint8Array(256 * rows);
      for (let index = 0; index < next.total; index++) {
        const lit = next.bits[index] === "1";
        const recent = lit && previous && previous.bits[index] !== "1" ? 128 : 0;
        const failed = next.bits[index] === "2" ? 64 : 0;
        const colorCode = lit ? 1 + cellSeed(index) % colors.length : 0;
        texels[index] = colorCode | recent | failed;
      }
      if (resized) gl.texImage2D(gl.TEXTURE_2D, 0, gl.R8UI, 256, rows, 0, gl.RED_INTEGER, gl.UNSIGNED_BYTE, texels);
      else gl.texSubImage2D(gl.TEXTURE_2D, 0, 0, 0, 256, rows, gl.RED_INTEGER, gl.UNSIGNED_BYTE, texels);
    },
    draw({ phase, round = 0, duty: twinkleDuty }, recent, final) {
      gl.useProgram(bulbProgram);
      gl.uniform2i(bulbs.grid, cols, snapshot.total);
      gl.uniform4f(bulbs.timing, phase, twinkleDuty, recent, final);
      gl.drawArrays(gl.TRIANGLES, 0, 3);
      if (twinkleDuty > 0) {
        gl.useProgram(flareProgram);
        gl.uniform2i(flares.grid, cols, snapshot.total);
        gl.uniform4f(flares.timing, phase, twinkleDuty, recent, final);
        gl.uniform1ui(flares.cycleIndex, round);
        gl.enable(gl.BLEND);
        gl.drawArraysInstanced(gl.TRIANGLE_STRIP, 0, 4, snapshot.total);
        gl.disable(gl.BLEND);
      }
    },
  };
}
