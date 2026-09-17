import VersoManual
import Solcore.Resolved.EvaluationProperties
import Solcore.Resolved.TypingProperties
import Solcore.Resolved.LoweringProperties

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

#doc (Manual) "From source names to Core positions" =>
%%%
tag := "frontend"
file := "frontend"
%%%

The source frontend has several separate responsibilities. Parsing recovers
structure from text. Resolution identifies declarations. Source checking
selects types and overloads. Specialization chooses concrete instances.
Elaboration expresses the supported computation in Core. A guarantee about
one stage does not automatically cover the others.

# Parsing preserves evidence about the source

The canonical `Solcore.Syntax` lexer and parser preserve source identity,
UTF-8 byte spans, tokens, comments, syntax, and diagnostics. Ordinary malformed
source produces retained diagnostics. Getting a parser output therefore does
not mean the file is diagnostic-free, well scoped, or well typed.

The parser proof families cover provenance, progress and fuel adequacy,
public totality, and ordinary grammar correspondence at their stated
boundaries. Some exactness results identify the AST and endpoint without
asserting equality of every diagnostic trace or internal parser state.
Read those conclusions literally.

For example,
[`productionParse_exists_ok`](https://github.com/Y-Nak/solcore-lean/blob/main/Solcore/Syntax/Parser/CanonicalParserTotalityProperties.lean)
states that every source file produces an ordinary parse output. The companion
already-tokenized theorem requires a lexical carrier valid for that source.
Neither conclusion asserts that the output has no diagnostics.

The canonical syntax work is separate from the frozen Surface v1 parser behind
Oracle v4. The [canonical syntax plan](https://github.com/Y-Nak/solcore-lean/blob/main/docs/M2_PLAN.md)
and [syntax status](https://github.com/Y-Nak/solcore-lean/blob/main/docs/CURRENT_STATUS.md)
describe that distinction and the remaining diagnostic boundaries.

# Reading source syntax without assuming execution support

A file can contain imports, type and data declarations, functions, traits and
implementations, and contract-related declarations. Expressions include
literals, names, calls, operators, tuples, conditionals, lambdas, and blocks.
Patterns and statements add further structure; inline Yul has its own syntax.
The parser can retain forms whose source checking or Core lowering is still
outside a selected executable profile.

A small canonical type declaration is:

```
type Store = mapping(address => word);
```

This describes source syntax. It does not assert that a particular mapping
operation has already been lowered to Core storage operations. The
{ref "source-types"}[source type chapter] explains the additional checking,
evidence, and specialization responsibilities.

# A name is not an identity

Two variables can share a spelling while belonging to different bindings.
{name Solcore.Resolved.LocalId}`LocalId` records an owning declaration and a
binder index. A local scope orders these identities. Lowering looks up an
identity's position rather than guessing from its printed name or source span.

For a scope `[newer, older]`, the older identity lowers to position one. A let
lowers its initializer under the old scope and its body under the extended
scope. This keeps the binder out of its own initializer and handles shadowing
without capturing the wrong value.

{name Solcore.Resolved.Expr.lower?_iff}`Expr.lower?_iff`
connects the executable optional lowering result to the declarative
{name Solcore.Resolved.Lowers}`Lowers` relation. Failure retains a real boundary:
a missing reference is not assigned a default position.

The scope rule is executable even when the binder identity is left abstract:

```lean
open Solcore

example (binder : Resolved.LocalId) :
    (Resolved.Expr.letE binder (.bool true)
      (.var binder)).lower? [] =
      some (.letE (.bool true) (.var 0)) := by
  simp [Resolved.Expr.lower?, Resolved.LocalScope.index?]
```

# The semantic bridge that is proven

{name Solcore.Resolved.Lowers.evaluates_iff}`Lowers.evaluates_iff`
assumes a successful lowering under the identities of a named environment.
It relates named evaluation to Core evaluation using the environment's values.
Both sides have the same initial store, result value, and final store.

This is stronger than merely showing that lowering produces a well-typed term.
It says that the lowered computation means the same thing at this boundary.
The separate
{name Solcore.Resolved.Lowers.typing_iff}`Lowers.typing_iff`
connects the corresponding typing judgments.

The local resolved fragment contains literals, variables, pairs, selected
primitives, lets, and conditionals. It is not the whole source language.
{name Solcore.Resolved.Evaluates.store_eq}`Evaluates.store_eq`
shows that this fragment preserves the store. That fact follows from its
constructors; it should not be generalized to later source paths with effects.

# Renaming and inserting a binding

Adding a temporary at the front of a Core environment changes the positions of
existing variables. A correct transformation must lift their indices and
respect binders. Renaming and insertion theorem families make that obligation
explicit. For closures, the right comparison can be a relation between bodies
and captured environments, rather than literal equality of the closure values.

This explains why a compiler cannot rearrange syntax just because a primitive
is commutative on values. Expressions may allocate, write, fail, or consume
fuel before producing those values. Evaluation order must be preserved before
reordering already computed operands.

The {ref "source-semantics"}[proven source-fragment chapter] covers additional
independent source evaluation and compositional body guarantees beyond this
local bridge.

# The larger executable frontend

The newer whole-program path loads modules, assigns declaration identities,
resolves namespaces and imports, and checks a supported source profile. Its
type machinery includes rigid parameters, flexible variables, substitutions,
rank-1 schemes, occurs-checking unification, and evidence-producing trait and
coercion search. Search budget exhaustion is distinct from no solution.

Typed occurrences retain chosen declarations, instantiated types, local
identities, and links to obligations and coercions. Specialization builds a
finite plan keyed by declarations and concrete type arguments. A budget can
bound type-growing recursion even when repeated identical keys are recognized.
The acyclic linker accepts a narrower executable boundary than the planner.

Accepted elaborations retain equations showing their resolved lowering and
independent Core re-inference. These checked carriers are valuable guarantees
about the produced object. They are not a substitute for a general theorem
that all source-language meanings are preserved through the complete frontend.
General source execution and a public source Oracle remain separate work.

Operator spelling also needs care. Source operators may resolve to ordinary
overloaded functions with eager arguments. A Core short-circuit builder's
conditional semantics does not automatically describe every source spelling
that resembles it.

See [source elaboration](https://github.com/Y-Nak/solcore-lean/blob/main/Solcore/Frontend/SourceCoreElaboration.lean)
and the [feature matrix](https://github.com/Y-Nak/solcore-lean/blob/main/docs/FEATURE_MATRIX.md)
for the exact admitted forms and current linking restrictions.
