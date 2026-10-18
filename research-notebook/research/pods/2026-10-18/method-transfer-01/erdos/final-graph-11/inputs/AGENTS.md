# Writing guidance

Mike requests that writing here and in later work follow ASD-STE100 at about 80%.
Use this as a strong style preference, not a measured compliance score.

- Use short sentences, active voice, and familiar words.
- Use one term for each technical concept. Define necessary technical terms.
- Give each paragraph one main topic. Put the main point first.
- Give instructions in a clear sequence. State conditions before their actions.
- Preserve mathematical meaning, assumptions, units, notation, and source claims.
- Keep exact theorem statements and quotations when a rewrite would change them.
- Avoid word substitutions that make the text less natural or less precise.
- Do not claim full STE compliance without checking the full standard and dictionary.

Source: https://www.asd-ste100.org/about_STE.html
The official overview describes writing rules, a controlled dictionary, and permitted
technical nouns and verbs. The full standard has not been checked for this project.

Keep reports concise and candid. Separate proved results, numerical evidence, and
open questions. Do not give invented confidence percentages or publication odds.

# Repository storage

The repository for this research is `IamMikeHelsel/ctrl` (private).
This workspace is the working research folder. Its source, reports, proof evidence,
and final animations are preserved under `research-notebook/` in that repository.
The current isolated checkout is `/Users/mike/Dev/ctrl-research-notebook`.

Before handing off new research, update and check the notebook from that checkout:

```sh
python3 tools/sync_research_notebook.py --source /Users/mike/Documents/Codex/2026-10-16/okay-spend-30-or-40-minutes
python3 tools/sync_research_notebook.py --source /Users/mike/Documents/Codex/2026-10-16/okay-spend-30-or-40-minutes --check
```

Review and commit the updated notebook and its manifest on the research branch.
Keep proof sources and recorded evidence byte-for-byte. Do not change toolchain pins
to fit the main library. Check hashes before reporting preservation as complete.
Build caches are excluded. External repository revisions and local patches are
recorded separately. Read `research-notebook/README.md` for the full storage scope.
Report local commits, remote pushes, and merges as separate states.
