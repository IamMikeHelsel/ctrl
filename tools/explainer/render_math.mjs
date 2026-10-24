// Build-time TeX -> MathML. Reads [{tex, display}] JSON on stdin, writes
// {ok: [html...], errors: [{i, tex, message}]} on stdout. No runtime JS ships to the page;
// browsers render MathML natively.
import katex from "katex";

let input = "";
for await (const chunk of process.stdin) input += chunk;
const items = JSON.parse(input);

const macros = {
  "\\R": "\\mathbb{R}",
  "\\N": "\\mathbb{N}",
  "\\T": "^{\\top}",
  "\\norm": "\\lVert #1 \\rVert",
};

const ok = [];
const errors = [];
items.forEach(({ tex, display }, i) => {
  try {
    ok.push(
      katex.renderToString(tex, {
        displayMode: display,
        output: "mathml",
        throwOnError: true,
        strict: "error",
        macros: { ...macros },
      }),
    );
  } catch (e) {
    ok.push("");
    errors.push({ i, tex, message: String(e.message || e) });
  }
});
process.stdout.write(JSON.stringify({ ok, errors }));
