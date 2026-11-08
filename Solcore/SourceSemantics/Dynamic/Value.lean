import Solcore.Core.Primitive
import Solcore.Frontend.SourceInference.TypedIR
import Solcore.SourceSemantics.Context
import Solcore.SourceSemantics.Traits

/-!
# Values and runtime types

The mathematical values of the source language. Main declarations: `Dynamic.Value`,
`Dynamic.Closure`, `Dynamic.GeneralizedClosure`, `Dynamic.SemanticFault`,
`Dynamic.ExpressionOutcome`, `Dynamic.ControlOutcome`, `Dynamic.ValueRuntimeType`.
-/

section
-- leanmerge: from Solcore.SourceSemantics.Dynamic.Value
/-!
Proof-facing values for the declarative source dynamics.

These carriers are independent of the executable source runtime.  In
particular, a closure retains the typed occurrence graph and an environment of
abstract locations, while a global function retains its exact generic
instantiation.  No evaluator result is embedded in these definitions.
-/

set_option autoImplicit false

namespace Solcore.SourceSemantics.Dynamic

open Frontend
open Frontend.SourceInference
open TypeSystem

/-- Concrete dictionaries captured by first-class functions. -/
abbrev EvidenceEnvironment := List (ProgramPredicate × TraitEvidence)

/-- An abstract address in the source-level heap. -/
structure Location where
  index : Nat
  deriving Repr, BEq, DecidableEq

/-- Lexical bindings point to cells.  A closure's captured environment points
to its own snapshot cells, which only closure applications copy. -/
abbrev Environment := List (Resolved.LocalId × Location)

/-- A source closure contains code and the locations of its snapshot cells,
but no recursive value payload.  This separation keeps the value carrier
strictly positive. -/
structure Closure where
  parameters : List TypedBinder
  resultType : Ty
  body : List StatementId
  source : TypedSource
  captured : Environment
  context : Context
  evidence : EvidenceEnvironment
  deriving Repr

/-- Principal code stored for a generalized direct-lambda local.  Evidence is
supplied at each use site because distinct instantiations can require distinct
dictionaries.  The initializer identity keeps the carrier tied to the exact
source occurrence from which the direct-lambda components were recovered. -/
structure GeneralizedClosure where
  binder : TypedBinder
  initializer : ExpressionId
  parameters : List TypedBinder
  resultType : Ty
  body : List StatementId
  source : TypedSource
  captured : Environment
  definitionContext : Context
  deriving Repr

/-- A first-class top-level function at one exact generic instantiation. -/
structure GlobalFunction where
  instantiation : DeclarationInstantiation
  evidence : EvidenceEnvironment
  deriving Repr

/-- A first-class compiler-provided source function. -/
structure BuiltinFunction where
  id : BuiltinFunctionId
  deriving Repr, BEq, DecidableEq

/-- Mathematical source values.  Constructor values retain their nominal
instantiation, and mappings retain mathematical key/value entries rather than
borrowing any representation from the executable runtime. -/
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
  | closure (function : Closure)
  | global (function : GlobalFunction)
  | builtin (function : BuiltinFunction)
  deriving Repr

/-- Semantic failures are observable stuck outcomes of source evaluation.
They describe the source-level reason and do not mention an implementation's
fuel counter, call-edge cache, or specialization worklist. -/
inductive SemanticFault where
  | missingExpression (id : ExpressionId)
  | missingStatement (id : StatementId)
  | unboundLocal (id : Resolved.LocalId)
  | danglingLocation (location : Location)
  | uninitializedLocation (location : Location)
  | unsupportedPolymorphicBinder (id : Resolved.LocalId)
  | missingDeclaration (id : Resolved.DeclarationId)
  | typeMismatch (expected actual : Ty)
  /-- The requested mapping entry is absent and its value type has no
  canonical default. The typed-source runtime observes this reason as
  `RuntimeError.typeMismatch valueType none`. -/
  | missingMappingDefault (valueType : Ty)
  | notCallable
  | argumentArityMismatch (expected actual : Nat)
  | invalidUnaryOperand (operator : Syntax.UnaryOp)
  | invalidBinaryOperands (operator : Syntax.BinaryOp)
  | invalidAssignmentOperands (operator : Syntax.ValueAssignOp)
  | invalidProjection
  | invalidPattern
  | unsatisfiedRequirement (id : RequirementId)
  | stagingViolation
  | controlEscapedFunction
  deriving Repr, DecidableEq

/-- Terminal result of one expression evaluation.  Heap evolution is kept as
a parameter of the future evaluation judgment, not hidden in this outcome. -/
inductive ExpressionOutcome where
  | value (result : Value)
  | fault (reason : SemanticFault)
  deriving Repr

/-- Statement-level control transfer.  Continuing execution retains the
current lexical environment; return discards it at the function boundary. -/
inductive ControlOutcome where
  | fallthrough (environment : Environment)
  | returned (value : Value)
  | breaking (environment : Environment)
  | continuing (environment : Environment)
  | fault (reason : SemanticFault)
  deriving Repr

namespace ControlOutcome

/-- Exactly the ordinary and loop-local transfers retain an environment. -/
def environment? : ControlOutcome → Option Environment
  | .fallthrough environment
  | .breaking environment
  | .continuing environment => some environment
  | .returned _
  | .fault _ => none

@[simp] theorem environment?_fallthrough (environment : Environment) :
    (ControlOutcome.fallthrough environment).environment? = some environment :=
  rfl

@[simp] theorem environment?_returned (value : Value) :
    (ControlOutcome.returned value).environment? = none :=
  rfl

@[simp] theorem environment?_breaking (environment : Environment) :
    (ControlOutcome.breaking environment).environment? = some environment :=
  rfl

@[simp] theorem environment?_continuing (environment : Environment) :
    (ControlOutcome.continuing environment).environment? = some environment :=
  rfl

@[simp] theorem environment?_fault (reason : SemanticFault) :
    (ControlOutcome.fault reason).environment? = none :=
  rfl

end ControlOutcome

end Solcore.SourceSemantics.Dynamic
end

section
-- leanmerge: from Solcore.SourceSemantics.Dynamic.RuntimeType
/-! Source runtime type compatibility erases staging recursively. Canonical
shallow metadata remains raw; a runtime key guard compares its normalized
view with the normalized expected type. Defaults and diagnostics retain the
original expected metadata. No runtime value codec or evaluator is imported. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.Dynamic
open Frontend Frontend.SourceInference TypeSystem

/-- Erase availability annotations throughout a source type. -/
@[simp] def runtimeType : Ty → Ty
  | .variable id => .variable id
  | .parameter id => .parameter id
  | .constructor id => .constructor id
  | .application function argument => .application (runtimeType function) (runtimeType argument)
  | .function parameter result => .function (runtimeType parameter) (runtimeType result)
  | .product left right => .product (runtimeType left) (runtimeType right)
  | .mapping key value => .mapping (runtimeType key) (runtimeType value)
  | .proxy inner => .proxy (runtimeType inner)
  | .comptime inner => runtimeType inner
  | .error => .error

@[simp] theorem runtimeType_idempotent (type : Ty) : runtimeType (runtimeType type) = runtimeType type := by
  induction type <;> simp_all [runtimeType]

/-- Canonical shallow runtime type of every mathematical source value. -/
inductive ValueRuntimeType : Value → Ty → Prop where
  | unit : ValueRuntimeType .unit .unit
  | bool (value : Bool) : ValueRuntimeType (.bool value) .bool
  | word (value : Core.Word) : ValueRuntimeType (.word value) .word
  | integer (value : Int) : ValueRuntimeType (.integer value) .integer
  | product
      {left right : Value} {leftType rightType : Ty}
      (left_type : ValueRuntimeType left leftType)
      (right_type : ValueRuntimeType right rightType) :
      ValueRuntimeType (.product left right) (.product leftType rightType)
  | proxy (inner : Ty) : ValueRuntimeType (.proxy inner) (.proxy inner)
  | constructed
      (instantiation : DataConstructorInstantiation) (arguments : List Value) :
      ValueRuntimeType (.constructed instantiation arguments)
        instantiation.resultType
  | mapping (keyType valueType : Ty) (entries : List (Value × Value)) :
      ValueRuntimeType (.mapping keyType valueType entries)
        (.mapping keyType valueType)
  | closure (function : Closure) :
      ValueRuntimeType (.closure function)
        (.function
          (Ty.productMany (function.parameters.map fun binder => binder.scheme.body))
          function.resultType)
  | global (function : GlobalFunction) :
      ValueRuntimeType (.global function) function.instantiation.type
  | builtin (function : BuiltinFunction) :
      ValueRuntimeType (.builtin function) function.id.type

/-- The retained shallow metadata of a mathematical value is unique. -/
theorem ValueRuntimeType.functional {value : Value} {first second : Ty}
    (typed : ValueRuntimeType value first) (other : ValueRuntimeType value second) : first = second := by
  induction typed generalizing second with
  | unit | bool | word | integer | proxy | constructed | mapping | closure | global | builtin => cases other; rfl
  | product left right first second =>
    cases other with
    | product a b => simp only [first a, second b]

/-- A key passes its runtime type guard when its canonical shallow type
and the retained expected type have the same runtime shape. -/
inductive ValueRuntimeTypeMatches (value : Value) (expected : Ty) : Prop where
  | intro {actual : Ty} (typed : ValueRuntimeType value actual)
      (same : runtimeType actual = runtimeType expected) : ValueRuntimeTypeMatches value expected

/-- Existing exact type receipts imply the runtime guard. -/
theorem ValueRuntimeType.matches {value : Value} {type : Ty} (typed : ValueRuntimeType value type) :
    ValueRuntimeTypeMatches value type := .intro typed rfl

namespace ValueRuntimeTypeMatches

theorem of_view {value : Value} {actual expected : Ty}
    (typed : ValueRuntimeType value actual) (same : runtimeType actual = runtimeType expected) :
    ValueRuntimeTypeMatches value expected := .intro typed same

theorem agrees {value : Value} {actual expected : Ty}
    (accepted : ValueRuntimeTypeMatches value expected) (typed : ValueRuntimeType value actual) :
    runtimeType actual = runtimeType expected := by
  cases accepted with
  | intro canonical same => exact (congrArg runtimeType (typed.functional canonical)).trans same

theorem bool (value : Bool) : ValueRuntimeTypeMatches (.bool value) .bool := (ValueRuntimeType.bool value).matches
theorem word (value : Core.Word) : ValueRuntimeTypeMatches (.word value) .word := (ValueRuntimeType.word value).matches
theorem integer (value : Int) : ValueRuntimeTypeMatches (.integer value) .integer := (ValueRuntimeType.integer value).matches

end ValueRuntimeTypeMatches
end Solcore.SourceSemantics.Dynamic
end
