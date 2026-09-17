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

{includeDocstring Solcore.TypeSystem.Ty}

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

{includeDocstring Solcore.TypeSystem.Unification.unify}

# Schemes allow repeated independent uses

{includeDocstring Solcore.TypeSystem.Scheme.instantiate}

{includeDocstring Solcore.TypeSystem.DeclarationScheme.instantiate}

The [feature matrix](https://github.com/Y-Nak/solcore-lean/blob/main/docs/FEATURE_MATRIX.md)
records the supported source profiles and remaining polymorphism boundaries.

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
