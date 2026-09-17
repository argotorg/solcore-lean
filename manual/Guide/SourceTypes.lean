import VersoManual
import Solcore.TypeSystem.Unification
import Solcore.TypeSystem.Scheme

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

#doc (Manual) "Source types, overloads, and specialization" =>
%%%
tag := "source-types"
file := "source-types"
%%%

Core checking answers whether a concrete expression has a concrete type. Source
checking has additional work: names may be overloaded, functions may have type
parameters, and operations may require an implementation of a trait. Keeping
these stages distinct helps explain both the available functionality and the
limits of its current proofs.

# Unknown types and generic types are different

{name Solcore.TypeSystem.Ty}`TypeSystem.Ty` distinguishes flexible inference
variables from rigid generic parameters. An inference variable is a question
the checker can solve. A generic parameter belongs to a declaration and stands
for the type supplied by a caller; the checker cannot simply redefine it to
make the function body work.

Source types additionally describe functions, products, nominal applications,
mappings, proxy types, and compile-time forms. Their presence in this datatype
does not mean every form already has a runtime Core elaboration.

# Unification solves equality constraints

Unification searches for a substitution that makes two types agree. For example,
if a function argument must be Word and its type is still unknown, the unknown
can be assigned Word. Word and Boolean are distinct concrete types and cannot
be made equal by a substitution.

```lean
open Solcore.TypeSystem

example : Unification.unifyTypes Ty.word Ty.bool =
    .error (.mismatch Ty.word Ty.bool) := by
  rfl

example : Unification.unifyTypes Ty.word Ty.word =
    .ok [] := by
  rfl
```

The occurs check prevents solving a variable by a type containing that same
variable, which would require an infinite type. The executable search also has
a budget. Its `exhausted` result must not be treated as a proof that the
constraints are inconsistent.

These examples demonstrate the executable kernel. They do not claim a broad
soundness-and-completeness metatheory for the entire source type system.

# Schemes allow repeated independent uses

A {name Solcore.TypeSystem.Scheme}`Scheme` quantifies inference variables in
a rank-1 type. Instantiation replaces its quantified variables with fresh
ones so separate uses can solve them independently. A declaration scheme
similarly instantiates rigid declaration parameters at use sites.

Freshness is necessary: using one generic function with a Word should not
accidentally constrain a separate Boolean use. Higher-rank types, higher-kinded
types, polymorphic recursion, and local let-polymorphism require boundaries
beyond the current executable profiles.

# Overloads and traits retain evidence

Source checking considers visible candidate declarations and records the chosen
identity and type instantiation at the occurrence. Trait search freshens
implementation heads, unifies them with the goal, and recursively considers
required predicates. The implementation distinguishes no solution, ambiguity,
and an inconclusive bounded search.

Coercions are explicit evidence paths between source types. Their endpoints,
adjacency, and obligation ownership matter: finding a sequence of plausible
conversions is insufficient if it belongs to the wrong occurrence or fails to
connect the expected types. The current elaborator defensively checks these
relationships before admitting its supported runtime evidence.

# Specialization is planning; linking is execution preparation

A specialization key combines a declaration with concrete type arguments. The
planner retains roots and call occurrences and discovers reachable keys. Seeing
the same recursive key can finish planning that part of the graph; a growing
sequence of distinct type instantiations instead reaches a budget frontier.

The executable linker accepts a restricted complete acyclic plan. It expands
direct calls using argument lets that preserve evaluation order and avoid
capture, then independently checks the Core result. Consequently, a plan can
be representable without being executable by this linker.

Selected trait methods and ordinary operator functions have restricted linked
execution paths. General runtime evidence, indirect or recursive linking, and
whole-source preservation remain separate work. The exact supported method and
coercion profiles are recorded in the
[feature matrix](https://github.com/Y-Nak/solcore-lean/blob/main/docs/FEATURE_MATRIX.md).
