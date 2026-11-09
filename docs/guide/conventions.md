# Conventions

This page covers:
- how the code is laid out;
- where a new declaration goes;
- which proof rules hold everywhere;
- how to find code that older notes name by a module path that no longer exists.

## Layout of an area

| Place | Contents |
| --- | --- |
| `Solcore/<Area>.lean` | The umbrella. It imports the area, and its module doc says what to read first. |
| `Solcore/<Area>/<Name>.lean` | The front: the definitions that make up the specification, and the main theorems. Each file opens with a module doc that names its main declarations. |
| `Solcore/<Area>/Internal/<Topic>.lean` | Everything else, by topic: supporting lemmas, case analyses, certificates, receipts and executable helpers. |

A large part of an area has its own subdirectory, laid out the same way. Examples are
`Solcore/Syntax/Parser`, `Solcore/Syntax/Grammar`, `Solcore/Frontend/RustHull` and
`Solcore/SourceSemantics/CoreLowering`.

**Sections and namespaces.**
- Most `Internal/` files, and some front files, were merged from many small modules.
- Each merged part is a `section`. It starts at a line `-- leanmerge: from <old module>` and keeps
  the namespace of that old module, such as `Solcore.SourceSemantics.CoreLowering.Foo`.
- So a namespace names a section, not a file. To find a declaration, search for its name or for the
  marker; do not derive a path from its namespace.
- Namespaces were left as they were, because renaming them would rename most declarations.

## Where a new declaration goes

- **A definition that theorems are stated over, or that the public API exposes.** Put it in the
  front file of its topic, and its laws in `Internal/`. ContractRuntime follows this split most
  closely; [its page](contract-runtime.md) lists the front files that keep laws, and why.
- **A main result.** This is a theorem that README's Proof status would name, or that a design note
  cites. Put it in the front next to the theorems of its kind, and its helper lemmas in `Internal/`.
- **Anything else.** Put it in the `Internal/` file of its topic; each area's page lists the topics.
  - Add it to the section whose namespace fits.
  - For a new topic, start a new section at the end of the file with its own namespace.
  - Do not add `-- leanmerge:` markers to new code. They record where merged code came from.
- **A new file.**
  - Create one when no topic fits, or when an existing file would grow past about 6,000 lines.
  - The target is 1,000 to 4,000 lines on one topic.
  - Two files are far larger: `SourceSemantics/Internal/Inference/Soundness` and
    `SourceSemantics/Internal/Substitution/StructuralLaws`. Each was one module before the layout,
    and they stay whole.
- **Build and import.**
  - `lake build` builds every module under `Solcore/`, imported or not: the library's glob is
    `Solcore.*`.
  - Import a new front file from the area's umbrella, directly or through another front file.
  - A few modules are left out of their umbrella on purpose. `SourceSemantics/CompiledBodies` and
    `SourceSemantics/Staging/Preservation` use Core lowering files, so the Core lowering umbrella
    imports them. `Synthesis/Source/ScalarMeaning/` and some synthesis families are reached only
    from tools and tests. Each area's page says what its umbrella leaves out.
  - A test runs only once it is registered; see [Tests](tests.md).

## What moving code can change

Moving a declaration to another file keeps its statement. It can still change what other proofs
see.

- **`@[simp]` reach.**
  - A `@[simp]` lemma is active in every module that imports its file.
  - Merging two files gives each importer the other's simp lemmas. That can change what `simp` does
    far away.
  - This is why some files on one topic stay separate. The Core primitive laws are an example (see
    [Core](core.md)).
  - When a move breaks a proof in another area, regroup the files instead of editing that area.
- **Instances.** Instances spread to importers the same way.
- **`private` is per file.**
  - A private helper is visible only in its file, so a proof that unfolds a private definition must
    stay in that file.
  - Two merged files cannot both declare a private helper of the same name.
- **Matchers and equation lemmas.** Lean reuses a structurally equal matcher within a module.
  Moving a definition can therefore change the binder names in its equation lemmas (`.eq_1`,
  `.eq_def`), which proofs that rewrite with them may notice.

[Workflow](workflow.md#refactoring-without-changing-declarations) describes the tools that check a
pure move.

## Proof rules

- **No `sorry`, `admit` or new axioms.**
  - [`scripts/check-kernel.mjs`](../../scripts/check-kernel.mjs) rejects any line that contains one
    of these as a whole word: `sorry`, `admit`, `axiom`, `partial`, `unsafe`, `noncomputable`,
    `extern`, `implemented_by`.
  - It checks every file under `Solcore/Core`, `Solcore/Util`, `Solcore/ContractRuntime`,
    `Solcore/Resolved`, `Solcore/SourceSemantics`, `Solcore/Synthesis/Source/ScalarMeaning`,
    `Solcore/TypeSystem`, `Solcore/Frontend`, `Solcore/Syntax` and `Solcore/Workspace`.
  - It also checks the umbrellas `Resolved.lean`, `SourceSemantics.lean`, `TypeSystem.lean` and
    `Frontend.lean`.
  - The check is textual, so the words also fail in comments and docstrings. Prose such as "a
    partial result" fails there too: write "an incomplete result" instead.
- **No `native_decide` outside tests.** It makes the proof trust compiled evaluation. No file in the
  checked directories uses it, although the check does not look for it. Tests may decide a fixture
  with it.
- **Warnings are errors.** The package sets `warningAsError`, so an unused variable or a deprecated
  name fails the build.
- **Front theorems state what the project claims.** Change one only deliberately. When you do,
  update README's Proof status and the area's guide page with it.

## Documentation

- Write docs in English.
- **Module docs.**
  - Each front file opens with a module doc that names its main declarations.
  - Each umbrella's module doc says what to read first.
  - Keep them current when you add or move a main declaration.
- **Guide and design notes.**
  - This guide describes the code as it is.
  - A design note describes work before and while it is done; see
    [Adding a language feature](adding-a-feature.md).
  - When the work is done, move what stays true into the guide or a module doc, and delete the
    note.
- **Links.** When you rename or move a file, update the links to it in README, this guide, the
  design notes and the scripts' guides (`scripts/*.md`).

## Following older notes

Commit messages, integration records and notes written before the layout refactor (commit
f820cc25f) name modules that no longer exist. The `.refactor/` files map them to the current
layout.

- **Moves.**
  - `.refactor/moves-<lane>.tsv` maps each old module to the module that holds it now. Its columns
    are the old module, the new module and the kind of move.
  - The marker `-- leanmerge: from <old module>` then finds the old module's section in that file.
- **Splits.**
  - A line starting `# split` marks an old module that was split: its definitions went to the front
    and its laws to `Internal/`.
  - The map points such a module at the laws. Its definitions are in the area's front, under the
    same namespace.
- **Renames and deletions.**
  - `.refactor/renames-<lane>.tsv` lists the private helpers renamed to avoid clashes.
  - `.refactor/deleted-<lane>.tsv` lists the identical private copies that were removed.
