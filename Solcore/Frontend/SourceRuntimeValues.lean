import Solcore.Core.Primitive
import Solcore.Frontend.SourceCompilationPlan

/-! Source values and heap observations shared by compiler adapters.
The historical public namespace is retained for API compatibility. This module
contains no expression, statement, or callable evaluator. -/

set_option autoImplicit false

namespace Solcore.Frontend.SourceTypedRuntime

open SourceInference TypeSystem SourceCompilationPlan

/-- Erase staging wrappers while preserving the complete runtime type shape.
`comptime<T>` changes when a value is available, not its runtime
representation.  Erasure is recursive because staging wrappers may occur
inside products, functions, mappings, proxies, and nominal arguments. -/
@[simp] def runtimeType : Ty → Ty
  | .variable id => .variable id
  | .parameter id => .parameter id
  | .constructor id => .constructor id
  | .application function argument =>
      .application (runtimeType function) (runtimeType argument)
  | .function parameter result =>
      .function (runtimeType parameter) (runtimeType result)
  | .product left right => .product (runtimeType left) (runtimeType right)
  | .mapping key value => .mapping (runtimeType key) (runtimeType value)
  | .proxy inner => .proxy (runtimeType inner)
  | .comptime inner => runtimeType inner
  | .error => .error

@[simp] theorem runtimeType_idempotent (type : Ty) :
    runtimeType (runtimeType type) = runtimeType type := by
  induction type <;> simp_all [runtimeType]

abbrev Environment := List (Resolved.LocalId × Location)

/-- Values which deliberately retain source-level types.  Mapping entries are
ordered by first insertion; replacement preserves that order. -/
inductive Value where
  | unit
  | bool (value : Bool)
  | word (value : Core.Word)
  | integer (value : Int)
  | product (left right : Value)
  | proxy (inner : Ty)
  | constructed
      (instantiation : DataConstructorInstantiation)
      (arguments : List Value)
  | mapping
      (keyType valueType : Ty)
      (entries : List (Value × Value))
  | closure
      (parameters : List TypedBinder)
      (resultType : Ty)
      (body : List StatementId)
      (source : TypedSource)
      (owner : Key)
      (captured : Environment)
      (evidence : RuntimeEvidenceEnvironment)
  /-- A runtime-only view of a principal value at one concrete occurrence.
  The wrapper keeps the stored closure and its plan provenance unchanged;
  callable execution applies the substitution to the closure's checked source
  graph just before entering its body. -/
  | instantiated
      (substitution : Substitution)
      (requirements : List LocalRequirementWitness)
      (principal : Value)
  /-- One closed view of a source declaration.  The evidence list is stored
  in the declaration's predicate order so an indirect invocation has the same
  authenticated dictionary that was available at the reference occurrence. -/
  | global (key : Key) (evidence : RuntimeEvidenceEnvironment)
  | builtin (function : BuiltinFunctionId)
  deriving Repr

structure Cell where
  type : Ty
  value : Option Value
  deriving Repr

structure RuntimeState where
  heap : List Cell := []
  deriving Repr

namespace RuntimeState

def read? (state : RuntimeState) (location : Location) : Option Cell :=
  state.heap[location.index]?

/-- Replace one existing cell.  The explicit recursion avoids exposing an
index proof in the runtime API. -/
def replaceCell : Nat → Cell → List Cell → List Cell
  | _, _, [] => []
  | 0, replacement, _ :: rest => replacement :: rest
  | index + 1, replacement, cell :: rest =>
      cell :: replaceCell index replacement rest

def write? (state : RuntimeState) (location : Location)
    (value : Option Value) : Option RuntimeState := do
  let cell ← state.read? location
  pure { heap := replaceCell location.index { cell with value } state.heap }

def allocate (state : RuntimeState) (type : Ty) (value : Option Value) :
    Location × RuntimeState :=
  (⟨state.heap.length⟩, { heap := state.heap ++ [{ type, value }] })

end RuntimeState

end Solcore.Frontend.SourceTypedRuntime
