"use strict";
const ids = ["speed", "speed-error", "position-error", "delay", "acceleration", "brake", "wall"];
function admissionLabel(threshold, clearance) {
  const roundingBand = 16 * Number.EPSILON * Math.max(1, threshold, clearance);
  if (Math.abs(threshold - clearance) <= roundingBand) return "at numerical boundary (check exactly)";
  return threshold < clearance ? "admits" : "rejects";
}
function updateMargin() {
  const values = {};
  for (const id of ids) {
    values[id] = Number(document.getElementById(id).value);
    document.getElementById(`${id}-value`).value = values[id].toFixed(id === "position-error" ? 3 : 2);
  }
  const u = values.speed + values["speed-error"];
  const tau = values.delay, a = values.acceleration, b = values.brake;
  const nominal = values.speed ** 2 / (2 * b);
  const bounded = values["position-error"] + u * tau + a * tau ** 2 / 2 + (u + a * tau) ** 2 / (2 * b);
  const wall = values.wall, scale = 720 / (1.15 * Math.max(bounded, wall, 0.1));
  document.getElementById("nominal-bar").setAttribute("width", nominal * scale);
  document.getElementById("bounded-bar").setAttribute("width", bounded * scale);
  const wallLine = document.getElementById("wall-line");
  wallLine.setAttribute("x1", 20 + wall * scale);
  wallLine.setAttribute("x2", 20 + wall * scale);
  document.getElementById("nominal-label").textContent = `Nominal: ${nominal.toFixed(4)} m`;
  document.getElementById("bounded-label").textContent = `Bounded: ${bounded.toFixed(4)} m`;
  document.getElementById("wall-label").textContent = `Available: ${wall.toFixed(4)} m (axis rescales)`;
  document.getElementById("diagram-desc").textContent = `Nominal threshold ${nominal.toFixed(4)} metres; bounded threshold ${bounded.toFixed(4)} metres; available clearance ${wall.toFixed(4)} metres.`;
  document.getElementById("verdict").textContent = `Nominal: ${admissionLabel(nominal, wall)}. Bounded: ${admissionLabel(bounded, wall)}. Model admission only.`;
}
ids.forEach(id => document.getElementById(id).addEventListener("input", updateMargin));
updateMargin();
