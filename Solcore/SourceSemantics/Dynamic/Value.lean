import Solcore.Core.Primitive
import Solcore.Frontend.SourceInference.TypedIR
import Solcore.SourceSemantics.Context
import Solcore.SourceSemantics.Traits

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

/-- Lexical bindings point to cells so closures observe later mutations. -/
abbrev Environment := List (Resolved.LocalId × Location)

/-- A source closure contains code and captured locations, but no recursive
value payload.  This separation keeps the value carrier strictly positive. -/
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
