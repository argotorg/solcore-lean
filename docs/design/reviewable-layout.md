# Reviewable layout

The repository has 10,428 Lean files and 2.16 million lines. 7,095 files have
fewer than 200 lines. Two flat directories dominate:
`Solcore/SourceSemantics/CoreLowering/` with 3,457 files and `Solcore/Test/`
with 3,299. A reviewer cannot find the specification and the main theorems
among them.

This refactor:
- gives every area a short front, made of the definitions that form the
  specification and the theorems the project claims;
- moves everything else into an `Internal/` subdirectory of that area;
- merges small files on one topic into one file, so that the file count drops
  by about an order of magnitude;
- adds a reviewer's guide that lists, for each area, what to read and in which
  order.

## Invariants

The refactor changes where declarations live, never what they say.

1. **Declarations.** Every declaration keeps its name, kind, type and
   attributes. Every definition, opaque constant, inductive type and instance
   also keeps its value. Theorems keep their statements, and their proofs move
   unchanged.
   - **Exceptions.** A lane may delete a private helper that is textually
     identical to another copy in the same merged file. It may also rename a
     private helper whose name clashes, recording the rename.
   - **Check.** The declaration snapshot checks this. Its diff between the
     base and the result must be empty, apart from the recorded renames.
2. **Namespaces.** Namespaces do not change. Most files declare a namespace
   named after their own module, such as
   `Solcore.SourceSemantics.CoreLowering.Foo`. After a merge, that namespace
   names one section of a larger file. Renaming namespaces would rename about
   100,000 declarations, so it is out of scope.
3. **Trust.** No `sorry`, `admit`, axioms or `native_decide`.
   `scripts/check-kernel.mjs` keeps checking every file it checked before, and
   its roots follow any directory that moves.
4. **Behaviour.** The gate passes unchanged:
   - `lake build` and `lake test`;
   - the kernel check;
   - the Python tests and the corpus validators;
   - offline `prepare-semantic-tools.py --prepare` and `--verify`.

   Executables keep their names and their roots in `Tests/`.
   `.github/workflows/semantic.yml` does not change.

## Layout of an area

| Place | Contents |
| --- | --- |
| `Solcore/<Area>.lean` | The umbrella. Its module doc is the area's reading guide: what to read first and the main theorems. |
| `Solcore/<Area>/<Name>.lean` | The front: the definitions that form the specification, and the main theorems. Few files, each opening with a module doc that names its main declarations. |
| `Solcore/<Area>/Internal/<Topic>.lean` | Supporting lemmas, case analyses, certificates, receipts, executable helpers and everything else, merged by topic. |

**What belongs in the front.**
- **Specification:**
  - syntax, typing rules and semantics;
  - Core and the runtime model;
  - the compiler functions that the theorems describe;
  - the public API's entry points.
- **Main theorems:** the results the project claims, starting with README's
  "Proof status":
  - Core type preservation and finite execution safety;
  - source type preservation;
  - the source-to-Core correspondence proved so far;
  - imported Hull safety and Hull meaning preservation;
  - parser correctness;
  - emitter meaning.

  Theorems that design notes cite also count. So do the roots of an area's
  theorem dependencies that state such a result.

When a front file mixes main results with many helper lemmas, the helpers move
to `Internal/` where that is practical. Everything else is internal.

**Tests.** `Solcore/Test/` is merged by subject, with one file per tested
feature group. `Tests/Main.lean` keeps calling the same entry points.

**Reviewer's guide.** Each area has a page in `docs/review/` with these parts:
- the front files and their main definitions;
- the main theorems, each with a link and a one-line reading;
- what `Internal/` holds.

`docs/review/README.md` indexes the pages.

## Tools

The tools are in `scripts/refactor/`, and each prints its usage.

- **`snapshot.py take OUT.jsonl`.** Writes one record per constant of every
  built module. A record holds:
  - the normalized name and the kind;
  - hashes of the type and, except for theorems, of the value;
  - flags: private, instance priority, simp sets, reducibility, protected,
    noncomputable, class, inline, `implemented_by`, `extern` and a docstring
    hash.

  The module is recorded too, but the comparison ignores it. So do private
  name prefixes, macro scopes and macro helper names, which depend on the
  module. Lean caches matchers, `_proof_i`, `_simp_i` and `_sparseCasesOn_i`
  per module, so these are skipped; the constants that use them still cover
  their content, up to bound names, because a file can reuse a matcher that
  differs only in those. A full snapshot takes about 70 seconds and 3 GB, and
  it refuses to run on a stale build.
- **`snapshot.py diff A B [--renames FILE]`.** Exits non-zero on any added,
  removed or changed declaration.
- **`leanmerge.py`.**
  - `graph` prints import statistics, importers and merge suggestions
    (`--chains`, `--siblings`).
  - `merge --into T --area P M1 … Mn` and `move OLD NEW --area P` do the
    merging and moving.
  - `consolidate` removes the shims at the end.
  - `clashes` estimates duplicate names.
  - `scan` shows how a file is read.
- **`PrintConst.lean`.** `lake env lean --run scripts/refactor/PrintConst.lean
  <Module> <Name>` prints a constant, which helps to investigate a diff.

`leanmerge.py merge` does the following:
- puts the bodies in import order, each wrapped in its own `section`, with the
  scopes it leaves open closed;
- keeps each source's module doc as its section's header;
- takes the union of the imports;
- rewrites importers inside the area;
- leaves a one-line shim at the old path of every module that another area
  imports.

It refuses the following:
- module-system files and `lakefile` roots;
- an import cycle;
- a name declared in two bodies. When the two copies are textually identical,
  it names the copy to delete.

## Merging

- **Grouping:**
  - Merge files of one area and one topic.
  - Aim for 1,000 to 4,000 lines per file, and at most about 6,000. Larger
    existing files stay as they are.
  - Prefer files that are imported together.
- **Clashes.** Resolve a name clash between two bodies as follows. If the
  copies are identical, delete the later copy. Otherwise, rename one copy by
  hand and record the rename in `.refactor/renames-<lane>.tsv`.
- **Downstream breakage.** A merge can show a downstream module more
  declarations, for example extra `@[simp]` lemmas or instances. When that
  breaks a proof in another area, regroup instead of editing that area.
- **Moves.** Each lane records its moves in `.refactor/moves-<lane>.tsv` and
  commits that file with its changes.

## Verification

Each lane checks its work as follows:
- **Before any change:** takes a snapshot at its base.
- **Every commit:**
  - builds `Solcore` and the executables;
  - requires an empty snapshot diff against the base, with its renames file;
  - runs the kernel check and `git diff --check`.
- **Before its final report, and before any commit that changes tests or
  executables:** also runs `lake test`, the Python tests with the corpus
  validators, and offline `--prepare` and `--verify`.

At each integration, the integrator runs the gate, the snapshot diff against
main and a short differential smoke run with frozen tools.

## Lanes

Each lane owns one set of areas. It edits files only there, plus its
`.refactor/` files and its page in `docs/review/`.

| Lane | Areas | Files |
| --- | --- | ---: |
| R1 | `Solcore/SourceSemantics/CoreLowering` | 3,457 |
| R2 | The rest of `Solcore/SourceSemantics`, `Solcore/Core`, `Solcore/ContractRuntime`, `Solcore/TypeSystem`, `Solcore/Resolved`, `Solcore/Util`, `Solcore/Abi`, `Solcore/Workspace` and the top-level files | about 910 |
| R3 | `Solcore/Syntax` | 1,697 |
| R4 | `Solcore/Frontend` and `Solcore/Synthesis` | 1,004 |
| R5 | `Solcore/Test` and `Tests` | 3,360 |

The machine has 10 cores and 32 GB, so lanes run in waves. R1 and R3 go
first. R2 starts when one of them frees capacity, and R4 and R5 follow.
Changes to the lower areas (Syntax, Core, TypeSystem) rebuild almost
everything downstream, so those lanes batch their merges and build in full
only at the end of a batch.

## Consolidation

After all lanes are on main, the integrator does the following:
1. removes the shims and rewrites imports with `leanmerge.py consolidate`;
2. updates the file paths and module names in README, the design notes and
   the scripts' guides;
3. writes `docs/review/README.md`;
4. runs the gate, the snapshot diff and the smoke run.

The moves map stays with the integration records, so older notes can still
be followed. One example is the paused integer unit's list of statements.

## Result

The five lanes and the consolidation finished on 2026-11-09. Both columns count
every tracked `.lean` file in the same way, the first at the base `c26259d6c`.

| | Before | After |
| --- | ---: | ---: |
| Lean files | 10,435 | 1,253 |
| Lines | 2,163,994 | 2,178,447 |
| Files under 200 lines | 7,099 | 153 |
| `Solcore/SourceSemantics/CoreLowering/` | 3,457 files | 13 front files, 353 in `Internal/` |
| `Solcore/Test/` | 3,301 files | 211 files |

The line count grew by about one percent, because each merged module keeps its
module doc and gains a `section` wrapper and a marker line.

| Area | Files | In `Internal/` |
| --- | ---: | ---: |
| `SourceSemantics/CoreLowering` | 366 | 353 |
| `Syntax` | 169 | 108 |
| `SourceSemantics`, without `CoreLowering` | 147 | 100 |
| `Frontend` | 135 | 73 |
| `Synthesis` | 49 | 27 |
| `Core` | 38 | 15 |
| `ContractRuntime` | 33 | 21 |
| `TypeSystem`, `Resolved`, `Workspace`, `Abi`, `Util` | 27 | 5 |
| `Test` | 211 | |
| `Tests` | 61 | |
| Umbrellas, `Solcore.lean`, `lakefile.lean` and the refactor's Lean tools | 17 | |

Two files stay far above the 6,000-line guideline, because each was one module at
the base: `SourceSemantics/Internal/Inference/Soundness` with 26,302 lines and
`SourceSemantics/Internal/Substitution/StructuralLaws` with 12,993. Some small
files stay apart because a check required it: a `@[simp]` lemma, an instance or
a matcher would reach other modules, or a test asserts what a file's imports
must not reach. Each area's page in `docs/review/` names these files and the
reason.

**Records.** These stay in `.refactor/`, so that older notes, commit messages
and the integration records can still be followed:
- `moves-<lane>.tsv`: one row per old module, `old_module new_module kind`,
  where `kind` is `merge` or `move`, 10,254 rows in all. A comment row
  `# split OLD INTERMEDIATE extract` marks a module whose definitions were
  extracted before the merge: its row points to the laws, and the definitions
  are in the area's front under the same namespace.
- `renames-<lane>.tsv`: the renamed private helpers, 30 in Syntax and 480 in
  the tests.
- `deleted-<lane>.tsv`: the identical private copies that were deleted, with
  their text.
- `plan-r4.tsv`: Frontend's and Synthesis's planned files, which the second
  phase of the SourceSemantics lane read to keep its files below Frontend's
  imports.

**Markers.** Each merged section starts with a line
`-- leanmerge: from <old module>`: 10,269 markers in 987 files. With the moves
map, a marker finds the section that an old module name refers to. Older
headings `## Consolidated module: <name>` come from an earlier consolidation and
name a section in the same way.

**Not done.** A separate layer of definitions, with the proofs of the
specification files moved to `Internal/` once marked `private`, is left for a
later change.
