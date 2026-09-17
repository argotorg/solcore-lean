import VersoManual

open Verso.Genre Manual

#doc (Manual) "Using and maintaining the documentation" =>
%%%
tag := "maintenance"
file := "maintenance"
%%%

The guide explains the model and the meaning of its guarantees. The surrounding
reference documents have narrower jobs:

* [Architecture](https://github.com/Y-Nak/solcore-lean/blob/main/docs/ARCHITECTURE.md)
  defines stable responsibilities and the connections between layers.
* [Current status](https://github.com/Y-Nak/solcore-lean/blob/main/docs/CURRENT_STATUS.md)
  records the revision-local implementation boundary.
* [Feature matrix](https://github.com/Y-Nak/solcore-lean/blob/main/docs/FEATURE_MATRIX.md)
  locates individual supported and deferred features.
* [Specification charter](https://github.com/Y-Nak/solcore-lean/blob/main/docs/SPEC_CHARTER.md)
  defines authority and compatibility obligations.
* [Core v3](https://github.com/Y-Nak/solcore-lean/blob/main/docs/CORE_WIRE_V3.md)
  and [Oracle v5](https://github.com/Y-Nak/solcore-lean/blob/main/docs/ORACLE_V5_WIRE.md)
  specify exact public wire contracts.
* [Development](https://github.com/Y-Nak/solcore-lean/blob/main/docs/DEVELOPMENT.md)
  explains builds, tests, audits, and the semantic-feature workflow.
* [Decision records](https://github.com/Y-Nak/solcore-lean/tree/main/docs/adr)
  explain selected rules and the alternatives considered at the time.

# Keep explanations close to their guarantees

Definitions and theorem contracts belong in docstrings beside the existing
Lean declarations. Use `includeDocstring` to render that prose in a chapter;
use `docstring` when the full signature also helps the reader. Assumptions and
limits belong with the contract, so editor documentation and the guide share
the same explanation. Native rich docstrings check inline Lean references
during library compilation.

The guide owns the reading order, motivation, worked examples, and connections
between declarations. The guarantee map is a reading index, not a second
collection of theorem summaries. Avoid copying source explanations into a
chapter or adding declarations solely to hold guide prose.

A checked example should assert the behavior being explained. Merely defining
an expression does not check the claimed result. A theorem reference checks
that the declaration exists, while applying it to an example also exercises
its contract. Neither mechanism proves the surrounding English.

When a semantic feature changes, review the associated chapter, source
docstrings, examples, and guarantee-map entry together. The status ledger and
feature matrix record the precise new boundary. A historical ADR should retain
its historical meaning rather than being rewritten as a current progress log.

# Build and preview

From the repository root, run:

```
./manual/build.sh
```

This builds the checked chapters and renders both a single-page and a
multiple-page HTML edition. Rendering checks section references in addition
to the declaration and example checks performed by Lean. The separate manual
package pins its documentation dependencies; the semantic library does not
need an external Verso dependency.

The [manual build instructions](https://github.com/Y-Nak/solcore-lean/blob/main/manual/README.md)
cover local serving, toolchain selection, dependency upgrades, and authoring.
The generated site and dependency caches are ignored by Git. CI retains the
rendered site as a review artifact.

# Where to go deeper

Start from a theorem's statement and the definitions in its assumptions. Read
the proof when you want to understand the argument or extend the result. The
machine/evaluation correspondence is a useful example: saved continuations
explain how a small-step machine implements a compositional evaluation rule.
That idea is often more illuminating than a line-by-line tour of proof tactics.

For compiler comparison, record the exact supported fragment, input world,
observation policy, and implementation revision. A discrepancy is useful only
when both sides are answering the same question.
