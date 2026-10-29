---
title: <A plain claim, as a sentence. What the theorem guarantees, no symbols.>
subtitle: <One or two sentences: the theorem's name, the setting, and what this page covers.>
eyebrow: Explainer NN · <Area> · <topic>
area: <Controls | Estimation | Vision | Robotics | Applied math>
slug: <folder-name>
lean: ControlsLean/<Area>/<File>.lean
theorems:
  - <headline_theorem>
  - <supporting_theorem>
updated: YYYY-MM-DD
---

## The idea in one picture {#idea}

<The problem in engineering terms: what you want to know and why checking it directly is hard.>

<The idea in one or two sentences, with the key object named ($V$, the witness, the bound).>

<figure class="ex-figure">
<!-- include: diagram.svg -->
<figcaption><What the diagram shows, with the one number that makes the point.></figcaption>
</figure>

## What the theorem says {#statement}

<Setting: the objects and their types, in one short paragraph.>

<div class="theorem-box">
<span class="label">Theorem · <name></span>

If <hypotheses in words>,

$$<the precise statement>$$

then <conclusion in words>.

</div>

<Each hypothesis read plainly, as a short bullet list. Note anything the Lean version does
NOT require that a textbook would.>

Here is the Lean statement, with a translation:

```lean
<paste the exact signature>
```

| Lean | Math |
| --- | --- |
| `<lean expr>` | $<math>$ |

## Why it holds {#why}

<One sentence on the shape of the proof.>

<ol class="steps">
<li><strong><Step claim.></strong> <Detail with math.> (<code>lemma_name</code>)</li>
<li><strong><Step claim.></strong> <Detail.> (<code>lemma_name</code>)</li>
<li><strong><Step claim.></strong> <Detail.> (<code>lemma_name</code>)</li>
</ol>

<Which step carries the real content, and which are bookkeeping.>

## A simple example {#simple}

<Smallest instance. Every number checkable by hand. Include the failing-hypothesis case if
it teaches something, and say whether the conclusion fails too.>

<figure class="ex-figure">
<video controls preload="metadata" playsinline width="1280" height="720" poster="media/<Simple>.png" aria-label="<what the animation shows>"><source src="media/<Simple>.mp4" type="video/mp4"></video>
<figcaption><What to watch for. Rough length.></figcaption>
</figure>

## A harder example {#harder}

<An instance where the naive approach fails and the theorem's object still works.>

| step | <quantity> | <naive> | <certified> |
| --- | --- | --- | --- |

<figure class="ex-figure">
<video controls preload="metadata" playsinline width="1280" height="720" poster="media/<Harder>.png" aria-label="<what the animation shows>"><source src="media/<Harder>.mp4" type="video/mp4"></video>
<figcaption><Left panel / right panel. Rough length.></figcaption>
</figure>

## Where it might apply {#applies}

<One sentence on what kind of tool this is (a check, a construction, a bound).>

<div class="applies">
<div><h3><Setting></h3><p><What maps onto the hypotheses there, and what the theorem then certifies. Name a repo theorem that uses it, if one does.></p></div>
<div><h3><Setting></h3><p>...</p></div>
</div>

## What it does not say {#limits}

<ul class="limits">
<li><strong>Model scope.</strong> ...</li>
<li><strong>What it does not compute.</strong> ...</li>
<li><strong>Floating point.</strong> ...</li>
<li><strong>When the hypothesis fails.</strong> ...</li>
</ul>

## Check it yourself {#check}

```sh
scripts/check.sh ControlsLean/<Area>/<File>.lean
cd site/explainers/<slug> && uv run --no-project --with numpy example.py
```
