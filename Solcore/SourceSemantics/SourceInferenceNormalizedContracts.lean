import Solcore.SourceSemantics.SourceInferenceNormalizedGeneralizationFormation
import Solcore.SourceSemantics.SourceInferenceNormalizedEntryFormation
import Solcore.SourceSemantics.SourceInferenceNormalizedApplicationFormation
import Solcore.SourceSemantics.SourceInferenceNormalizedCaptureFormation

/-! Contracts for normalized formation along the actual mutually recursive
inference calls. The outer substitution is the eventual real finalizer's
substitution. Capture checks refer only to actual returned node/header
inventories; the whole-body finalizer discharges these terminal conditions. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceNormalizedCoercionFormation
open Frontend SourceInference TypeSystem Detail SourceInferenceSoundness

structure InferenceFormationContext (semantic : SourceSemantics.Context)
    (context : SourceInference.Context) (outer : Substitution) : Prop
    extends FormationContext semantic context outer where
  scope : ProducerScope context semantic
  canonical : SignatureParametersWellFormed context.scope.genericOwner context.typeParameters
  validated : ProgramSignatureFormationValidated context.signatures
  functionShapes : ∀ signature ∈ context.signatures.functions,
    signature.scheme.body = .function (Ty.productMany signature.parameterTypes)
      (Ty.productMany signature.returnTypes)

def InferExprFuelFormation
    (semantic : SourceSemantics.Context) (outer : Substitution) (fuel : Nat) (context : SourceInference.Context) (expression : Syntax.Expr)
    (expected : Option Ty) (state : State) : Prop :=
  state.InferenceReady →
    state.NodesBelowNextOccurrence →
    NormalizedStateFormation semantic outer state →
    InferenceFormationContext semantic context outer →
    (∀ expectedType ∈ expected,
      expectedType.VariablesBelow state.inference.next) →
    (∀ expectedType ∈ expected, TypeAdmissible semantic (outer.apply expectedType)) →
    ∀ result,
      inferExprFuel fuel context expression expected state = .ok result →
      outer.SemanticallyExtends result.2.inference.substitution →
      NoCaptureNodes outer result.2.nodes →
      TypeAdmissible semantic (outer.apply result.1.type) ∧
        NormalizedStateFormation semantic outer result.2

def InferConstructorApplicationFuelFormation
    (semantic : SourceSemantics.Context) (outer : Substitution) (fuel : Nat) (context : SourceInference.Context) (source : Syntax.Expr)
    (id : ExpressionId) (instantiation : DataConstructorInstantiation)
    (arguments : List Syntax.Expr) (expected : Option Ty)
    (state : State) : Prop :=
  state.InferenceReady →
    state.NodesBelowNextOccurrence →
    NormalizedStateFormation semantic outer state →
    InferenceFormationContext semantic context outer →
    (∀ payload ∈ instantiation.payloadTypes,
      payload.VariablesBelow state.inference.next) →
    (∀ payload ∈ instantiation.payloadTypes, TypeAdmissible semantic (outer.apply payload)) →
    instantiation.resultType.VariablesBelow state.inference.next →
    TypeAdmissible semantic (outer.apply instantiation.resultType) →
    (∀ expectedType ∈ expected,
      expectedType.VariablesBelow state.inference.next) →
    (∀ expectedType ∈ expected, TypeAdmissible semantic (outer.apply expectedType)) →
    ∀ result,
      inferConstructorApplicationFuel fuel context source id instantiation
          arguments expected state = .ok result →
      outer.SemanticallyExtends result.2.inference.substitution →
      NoCaptureNodes outer result.2.nodes →
      TypeAdmissible semantic (outer.apply result.1.type) ∧
        NormalizedStateFormation semantic outer result.2

def InferConstructorArgumentsFuelFormation
    (semantic : SourceSemantics.Context) (outer : Substitution) (fuel : Nat) (context : SourceInference.Context) (sources : List Syntax.Expr)
    (expectedTypes : List Ty) (state : State) : Prop :=
  state.InferenceReady →
    state.NodesBelowNextOccurrence →
    NormalizedStateFormation semantic outer state →
    InferenceFormationContext semantic context outer →
    (∀ expectedType ∈ expectedTypes,
      expectedType.VariablesBelow state.inference.next) →
    (∀ expectedType ∈ expectedTypes, TypeAdmissible semantic (outer.apply expectedType)) →
    ∀ result,
      inferConstructorArgumentsFuel fuel context sources expectedTypes state =
          .ok result →
      outer.SemanticallyExtends result.2.inference.substitution →
      NoCaptureNodes outer result.2.nodes →
      (∀ expression ∈ result.1, TypeAdmissible semantic (outer.apply expression.type)) ∧
        NormalizedStateFormation semantic outer result.2

def InferStatementsFuelFormation
    (semantic : SourceSemantics.Context) (outer : Substitution) (fuel : Nat) (context : SourceInference.Context) (statements : List Syntax.Statement)
    (expectedReturn : Ty) (state : State) : Prop :=
  state.InferenceReady →
    state.NodesBelowNextOccurrence →
    NormalizedStateFormation semantic outer state →
    InferenceFormationContext semantic context outer →
    expectedReturn.VariablesBelow state.inference.next →
    TypeAdmissible semantic (outer.apply expectedReturn) →
    ∀ result,
      inferStatementsFuel fuel context statements expectedReturn state =
          .ok result →
      outer.SemanticallyExtends result.state.inference.substitution →
      NoCaptureNodes outer result.state.nodes →
      TypeAdmissible semantic (outer.apply result.type) ∧
        NormalizedStateFormation semantic outer result.state

def InferStatementFuelFormation
    (semantic : SourceSemantics.Context) (outer : Substitution) (fuel : Nat) (context : SourceInference.Context) (statement : Syntax.Statement)
    (expectedReturn : Ty) (state : State) : Prop :=
  state.InferenceReady →
    state.NodesBelowNextOccurrence →
    NormalizedStateFormation semantic outer state →
    InferenceFormationContext semantic context outer →
    expectedReturn.VariablesBelow state.inference.next →
    TypeAdmissible semantic (outer.apply expectedReturn) →
    ∀ result,
      inferStatementFuel fuel context statement expectedReturn state =
          .ok result →
      outer.SemanticallyExtends result.state.inference.substitution →
      NoCaptureNodes outer result.state.nodes →
      TypeAdmissible semantic (outer.apply result.type) ∧
        NormalizedStateFormation semantic outer result.state

def InferForItemsFuelFormation
    (semantic : SourceSemantics.Context) (outer : Substitution) (fuel : Nat) (context : SourceInference.Context) (items : List Syntax.ForItem)
    (state : State) : Prop :=
  state.InferenceReady →
    state.NodesBelowNextOccurrence →
    NormalizedStateFormation semantic outer state →
    InferenceFormationContext semantic context outer →
    ∀ result,
      inferForItemsFuel fuel context items state = .ok result →
      outer.SemanticallyExtends result.state.inference.substitution →
      NoCaptureNodes outer result.state.nodes →
      NoCaptureItems outer result.items →
      NormalizedStateFormation semantic outer result.state

def InferForItemFuelFormation
    (semantic : SourceSemantics.Context) (outer : Substitution) (fuel : Nat) (context : SourceInference.Context) (item : Syntax.ForItem)
    (state : State) : Prop :=
  state.InferenceReady →
    state.NodesBelowNextOccurrence →
    NormalizedStateFormation semantic outer state →
    InferenceFormationContext semantic context outer →
    ∀ result,
      inferForItemFuel fuel context item state = .ok result →
      outer.SemanticallyExtends result.2.inference.substitution →
      NoCaptureNodes outer result.2.nodes →
      NoCaptureItems outer [result.1] →
      NormalizedStateFormation semantic outer result.2

def InferPlaceFuelFormation
    (semantic : SourceSemantics.Context) (outer : Substitution) (fuel : Nat) (context : SourceInference.Context) (target : Syntax.Expr)
    (state : State) : Prop :=
  state.InferenceReady →
    state.NodesBelowNextOccurrence →
    NormalizedStateFormation semantic outer state →
    InferenceFormationContext semantic context outer →
    ∀ result,
      inferPlaceFuel fuel context target state = .ok result →
      outer.SemanticallyExtends result.2.inference.substitution →
      NoCaptureNodes outer result.2.nodes →
      TypeAdmissible semantic (outer.apply result.1.type) ∧
        NormalizedStateFormation semantic outer result.2

def InferAssignedValueFuelFormation
    (semantic : SourceSemantics.Context) (outer : Substitution) (fuel : Nat) (context : SourceInference.Context) (target : Syntax.Expr)
    (operator : Syntax.ValueAssignOp) (value : Syntax.Expr)
    (state : State) : Prop :=
  state.InferenceReady →
    state.NodesBelowNextOccurrence →
    NormalizedStateFormation semantic outer state →
    InferenceFormationContext semantic context outer →
    ∀ result,
      inferAssignedValueFuel fuel context target operator value state =
          .ok result →
      outer.SemanticallyExtends result.2.2.inference.substitution →
      NoCaptureNodes outer result.2.2.nodes →
      TypeAdmissible semantic (outer.apply result.1.target.type) ∧
        TypeAdmissible semantic (outer.apply result.2.1.type) ∧
        NormalizedStateFormation semantic outer result.2.2

def InferExprsFuelFormation
    (semantic : SourceSemantics.Context) (outer : Substitution) (fuel : Nat) (context : SourceInference.Context) (expressions : List Syntax.Expr)
    (state : State) : Prop :=
  state.InferenceReady →
    state.NodesBelowNextOccurrence →
    NormalizedStateFormation semantic outer state →
    InferenceFormationContext semantic context outer →
    ∀ result,
      inferExprsFuel fuel context expressions state = .ok result →
      outer.SemanticallyExtends result.2.inference.substitution →
      NoCaptureNodes outer result.2.nodes →
      (∀ expression ∈ result.1, TypeAdmissible semantic (outer.apply expression.type)) ∧
        NormalizedStateFormation semantic outer result.2

def InferMatchCasesFuelFormation
    (semantic : SourceSemantics.Context) (outer : Substitution) (fuel : Nat) (context : SourceInference.Context) (scrutineeType expectedReturn : Ty)
    (outerScope : LexicalScope) (cases : List Syntax.MatchCase)
    (state : State) : Prop :=
  state.InferenceReady →
    state.NodesBelowNextOccurrence →
    NormalizedStateFormation semantic outer state →
    InferenceFormationContext semantic context outer →
    scrutineeType.VariablesBelow state.inference.next →
    TypeAdmissible semantic (outer.apply scrutineeType) →
    expectedReturn.VariablesBelow state.inference.next →
    TypeAdmissible semantic (outer.apply expectedReturn) →
    state.lexicalScope = outerScope →
    ∀ result,
      inferMatchCasesFuel fuel context scrutineeType expectedReturn outerScope
          cases state = .ok result →
      outer.SemanticallyExtends result.state.inference.substitution →
      NoCaptureNodes outer result.state.nodes →
      NormalizedStateFormation semantic outer result.state

end Solcore.SourceSemantics.SourceInferenceNormalizedCoercionFormation
