# Solcore semantics and proven guarantees

An accessible guide to what Solcore programs mean and what the model proves.
Read it without following proof scripts: each chapter explains behavior,
examples, theorem assumptions, and the limits of the conclusion.

## Reading path

1. [The model in one picture](Guide/Orientation.lean)
2. [Reading a theorem](Guide/Theorems.lean)
3. [Values, bindings, and expressions](Guide/Language.lean)
4. [What checking guarantees](Guide/Checking.lean)
5. [Evaluation, safety, and fuel](Guide/Execution.lean)
6. [Three kinds of state](Guide/State.lean)
7. [Contracts, rollback, and effects](Guide/Contracts.lean)
8. [From source names to Core positions](Guide/Frontend.lean)
9. [Source types and specialization](Guide/SourceTypes.lean)
10. [Proven source fragments](Guide/SourceSemantics.lean)
11. [Reproducible Oracle experiments](Guide/Oracle.lean)
12. [Map of proven guarantees](Guide/Guarantees.lean)
13. [Using and maintaining the documentation](Guide/Maintenance.lean)

These links open the checked chapter sources. Build the rendered site below
for navigation, search, examples, and declaration signature hovers. The guide
covers the major semantic and verification boundaries; the detailed revision
inventory and exact wire catalogs remain linked reference documents.

## Build and preview

From the repository root, with Git and the pinned Lean toolchain available:

```sh
./manual/build.sh
```

The script checks that the manual and library toolchain files agree and that
Lake is using the expected Lean version. If a system Lean shadows elan, select
the toolchain explicitly:

```sh
lean_bin=$(dirname "$(elan which lake)")
PATH="$lean_bin:$PATH" ./manual/build.sh
```

The first build downloads and compiles documentation dependencies. The script
checks the chapters, then renders through Lean to avoid a native executable
relink during editing. The chapters import the semantic modules they explain rather than the
whole public library umbrella. Root library builds do not download or depend on Verso.

Serve the generated pages locally with Python:

```sh
python3 -m http.server 8000 --bind 127.0.0.1 --directory manual/_out/html-multi
```

Open <http://127.0.0.1:8000>. Rebuild and refresh after editing. The single-page
edition is at `manual/_out/html-single/index.html`. The multi-page edition uses
one page per chapter with stable URLs. Rendering completes before the previous
preview is replaced, and obsolete generated chapter pages are removed. Build output and caches are
ignored by Git. CI runs the same build script and retains HTML as an artifact.

## Keep the guide connected to the code

- Use `lean` blocks with assertions for concrete claims about the model. An
  example that merely type-checks does not assert its expected result.
- Use the `name` role for declaration references. It resolves the actual name
  and supplies signature hover information; plain backticks do not do this.
- Use `{docstring Solcore.Core.Program.checkDetailedIn}` to include an existing
  signature and source docstring. Keep API explanations in the source so the
  guide and editor documentation share the same text. Avoid enabling missing
  docstrings globally to hide gaps.
- For checked references in source documentation, scope `set_option doc.verso
  true in` to the declaration and use the native `{lean}` role in its docstring.
  Lean checks these references during library compilation without an external
  Verso dependency. The checker, its specification, and its correctness theorem
  demonstrate this pattern. Ordinary Markdown docstrings elsewhere still work.
- The pinned manual renderer imports rich source docstrings through Markdown.
  Use it for the prose and inline references demonstrated here; verify rendered
  output before adopting richer source documentation features.
- Apply the relevant theorem in an example when practical. A reference's
  continued existence alone does not check its contract or an English summary.
- Give sections stable tags and link with `ref`. Run both compilation and HTML
  generation, because unresolved section references can fail during rendering.

`Guide.lean` assembles chapters from `Guide/`; `Main.lean` generates the HTML.
Each chapter should answer a concrete reader question. Keep implementation
inventories in `docs/CURRENT_STATUS.md` and protocol details in the wire catalogs.

## Dependencies

The manual uses the library's Lean 4.32.1 toolchain and pins Verso's v4.32.0
revision. `lake-manifest.json` records resolved transitive dependencies. Keep
both toolchain files aligned when upgrading, select a compatible Verso revision,
then run `lake -d manual update` and the complete manual build before committing
the updated manifest. Do not copy a manifest from a different Lean version.
