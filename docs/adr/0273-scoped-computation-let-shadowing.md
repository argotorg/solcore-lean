# ADR-0273: Scoped shadowing in shared computation bodies

- Status: Accepted for implementation
- Decision date: 2026-09-10
- Scope: Typed/inferred local shadowing with a conservative terminal-if boundary

## Canonical evidence

Use argotorg/solcore-rs at
`18fd9f75d290df0070e21ee56e0a5691f232596f`.
A let initializer is resolved before the new local is registered
(`crates/hir/src/nameres/body_resolver.rs:40–55`).
Registration overwrites the same spelling in the current scope, and parameters
are registered before the body in that same scope
(`body_resolver.rs:936–959`, `nameres/queries.rs:140–159`).
Typing records each new let's type by its original statement identity, after
checking the initializer against its own annotation or inferred type
(`crates/hir-ty/src/infer/stmt.rs:58–99`).
The new type need not equal a shadowed binding's type.

An important reference boundary prevents simply removing both name guards.
The pinned resolver walks bare if branches sequentially, then before else,
without pushing a scope (`body_resolver.rs:94–108`).
Lowering retains those original statement lists without adding blocks
(`crates/parser/src/lower/body.rs:471–481,508–525`).
Explicit block statements and individual match arms do push/pop a scope
(`body_resolver.rs:109–127,961–964`).
Thus an unblocked then-side redefinition of an existing x can change which
source identity an else-side x denotes. The current Lean body engine checks
both branches against the same input bundle. Do not silently equate these two
name-resolution behaviors or describe every if arm as a lexical scope.

## Conservative source-only name protection

Add a small source-only analysis for names exposed by let statements without
crossing an explicit block or match-arm scope. A let contributes its original
identifier spelling; an unscoped if contributes both branches; statement tails
are traversed in order. Explicit block and match interiors contribute no names
to their surrounding scope. Other forms do not add supported computation lets.
This is a boundary for the existing computation-body profile, not a complete
name resolver for loops, assembly, global declarations or arbitrary syntax.

Specify exposed let-name occurrence independently over the original AST.
Define a source predicate saying that none of those names belongs to a given
protected list. Provide a total Boolean guard with exact correspondence to
that predicate, including rejection, and the subset law needed by old embeddings.
Neither interface assumes successful body checking or runtime evaluation.

At each terminal if, require its then body to protect all spellings in the
current input name table. Recursively inspecting both arms of nested unscoped
ifs also detects an inner else redefinition that would leak into an outer else.
Explicit nested blocks and match arms are genuine scope barriers and remain
available for branch-local shadowing.

This deliberately conservative condition preserves every already-present
name's resolution across the reference then traversal. Names first introduced
only in then can still be visible to the reference else, while the Lean child
profile rejects their absent lookup: that is retained incompleteness, not a
claim of full reference name-resolution equivalence.
An else-side shadow is allowed because every supported if is terminal; no
following source statement consumes the reference branch's resulting scope.
Do not extend this reasoning to nonterminal if/block sequencing.

## Shadowing changes static admission, not binding execution

Remove the unused-spelling requirement from the shared typed and inferred let
checker branches and their independent HasType/Elaborates constructors.
Check the original initializer in the original inputs, then prepend the new
binding with the existing owner-filtered fresh LocalId. Preserve all old rows,
values, types and positions behind it; do not overwrite a slot, reuse an old
identity, deduplicate names or evaluate the initializer under the new binding.
Existing first-match lookup then selects the new row in the tail.

Add the independent name-protection premise to the shared conditional
constructors and the corresponding guard to checking. These constructor
interfaces intentionally change; the shared twelve, recursive fourteen and
entry four theorem contracts and child-operation hypotheses remain unchanged.
Keep the raw/cost judgments and Core lowering unchanged. Their binding rules
already evaluate under the old environment and extend it with the actual
initializer value, at initializer cost plus tail cost plus two.

Reuse actual ordered-input and same-ID bridges for execution and cost proofs.
Runtime-world checking continues to inspect retained old rows and unused
closure captures; shadowing does not make those values disappear or validate
their references. No source-only call-cost bound or arbitrary-store safety
follows from a source name change.

The older TypedLetReturnBody/TypedLetReturnTree, LocalComputationReturnTree
and older function endpoints keep their unused-name restrictions. Shared
instantiation with the older child profile is distinct from that older body
endpoint. Preserve the old one-way embedding by proving that old fresh-let
evidence protects any subset of its current names, then applying that fact at
each newly guarded conditional. Duplicate runtime parameters remain rejected.

## Consumers and staged verification

Migrate old constructor arguments mechanically while retaining exact original
AST/Core, owners, type tables, actual inputs, effects, costs and checkpoints.
Move only the three now-obsolete shared/recursive rejection instances to
independent positives: two original bodies in shared-body.sol with Shared#54,
and the original function in compile-recursive.sol with CompileRecursive#4.
The old else-side shadow fixture remains admissible because its then body has
no exposed let. Keep unknown annotations and all older endpoint rejections.

New consumers cover parameter shadow, repeated same-block binding, changed
types, old-name initializer lookup, fresh identities in sparse/foreign scopes,
retained old closures and literal values, and explicit nested scope barriers.
Show that then-side exposed shadow is rejected even when a raw selected path
succeeds; nested unscoped else leakage must also be rejected. Then-only new
names remain unavailable to Lean's else rather than fabricated as inputs.
Preserve missing self-reference and duplicate-parameter failures.

Use parsed actual-effect consumers with explicit branch blocks, original
annotation/initializer/body evidence, separately written Core paths, ordered
stores, exact costs, all-fuel outcomes and genuine checkpoints/resumption.
Keep source block sequencing and lambda creation outside this extension.

Commit decision, scope definitions/proofs, shared definitions/proofs, old
consumers, new consumers and publication separately in small chunks. Keep
proof files below 300 lines. Require independent reviews, focused/aggregate/full
tests, exact public contracts/catalogs, standard-axiom audits, import/kernel/
metadata and EOF/whitespace checks. Diagnostic/parser proofs stay paused;
all working files stay inside the repository.
