import Solcore.SourceSemantics.SourceInferenceSelectedPrivacyPatterns
import Solcore.SourceSemantics.SourceInferenceSelectedPrivacyCallRecording
import Solcore.Frontend.SourceInference.DirectRequirementInference

/-! Privacy through the actual mutually recursive source inference calls. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceSoundness.ProtectedVariables
open Frontend SourceInference TypeSystem Detail

def InferExprFuelPrivacy
    (protectedVars : List TypeVarId) (fuel : Nat) (context : SourceInference.Context) (expression : Syntax.Expr)
    (expected : Option Ty) (state : State) : Prop :=
  state.InferenceReady →
    state.RequirementsWellFormed →
    (∀ metavariable ∈ protectedVars, metavariable.index < state.inference.next) →
    LiveBindersSafe protectedVars state →
    SignatureCatalogWellFormed context.signatures →
    ProgramSignatureFormationValidated context.signatures →
    (∀ signature ∈ context.signatures.functions,
      signature.scheme.body = .function (Ty.productMany signature.parameterTypes) (Ty.productMany signature.returnTypes)) →
    (∀ expectedType ∈ expected,
      expectedType.VariablesBelow state.inference.next) →
    (∀ expectedType ∈ expected, Safe protectedVars state expectedType) →
    ∀ result,
      inferExprFuel fuel context expression expected state = .ok result →
      SafeTransport protectedVars state result.2 ∧
        Safe protectedVars result.2 result.1.type ∧ LiveBindersSafe protectedVars result.2 ∧
        ∀ row ∈ result.2.requirements, row ∉ state.requirements → PredicateSafe protectedVars result.2 row.predicate

def InferConstructorApplicationFuelPrivacy
    (protectedVars : List TypeVarId) (fuel : Nat) (context : SourceInference.Context) (source : Syntax.Expr)
    (id : ExpressionId) (instantiation : DataConstructorInstantiation)
    (arguments : List Syntax.Expr) (expected : Option Ty)
    (state : State) : Prop :=
  state.InferenceReady →
    state.RequirementsWellFormed →
    (∀ metavariable ∈ protectedVars, metavariable.index < state.inference.next) →
    LiveBindersSafe protectedVars state →
    SignatureCatalogWellFormed context.signatures →
    ProgramSignatureFormationValidated context.signatures →
    (∀ signature ∈ context.signatures.functions,
      signature.scheme.body = .function (Ty.productMany signature.parameterTypes) (Ty.productMany signature.returnTypes)) →
    (∀ payload ∈ instantiation.payloadTypes,
      payload.VariablesBelow state.inference.next) →
    (∀ payload ∈ instantiation.payloadTypes, Safe protectedVars state payload) →
    instantiation.resultType.VariablesBelow state.inference.next →
    Safe protectedVars state instantiation.resultType →
    (∀ expectedType ∈ expected,
      expectedType.VariablesBelow state.inference.next) →
    (∀ expectedType ∈ expected, Safe protectedVars state expectedType) →
    ∀ result,
      inferConstructorApplicationFuel fuel context source id instantiation
          arguments expected state = .ok result →
      SafeTransport protectedVars state result.2 ∧
        Safe protectedVars result.2 result.1.type ∧ LiveBindersSafe protectedVars result.2 ∧
        ∀ row ∈ result.2.requirements, row ∉ state.requirements → PredicateSafe protectedVars result.2 row.predicate

def InferConstructorArgumentsFuelPrivacy
    (protectedVars : List TypeVarId) (fuel : Nat) (context : SourceInference.Context) (sources : List Syntax.Expr)
    (expectedTypes : List Ty) (state : State) : Prop :=
  state.InferenceReady →
    state.RequirementsWellFormed →
    (∀ metavariable ∈ protectedVars, metavariable.index < state.inference.next) →
    LiveBindersSafe protectedVars state →
    SignatureCatalogWellFormed context.signatures →
    ProgramSignatureFormationValidated context.signatures →
    (∀ signature ∈ context.signatures.functions,
      signature.scheme.body = .function (Ty.productMany signature.parameterTypes) (Ty.productMany signature.returnTypes)) →
    (∀ expectedType ∈ expectedTypes,
      expectedType.VariablesBelow state.inference.next) →
    (∀ expectedType ∈ expectedTypes, Safe protectedVars state expectedType) →
    ∀ result,
      inferConstructorArgumentsFuel fuel context sources expectedTypes state =
          .ok result →
      SafeTransport protectedVars state result.2 ∧
        (∀ expression ∈ result.1, Safe protectedVars result.2 expression.type) ∧
        LiveBindersSafe protectedVars result.2 ∧
        ∀ row ∈ result.2.requirements, row ∉ state.requirements → PredicateSafe protectedVars result.2 row.predicate

def InferStatementsFuelPrivacy
    (protectedVars : List TypeVarId) (fuel : Nat) (context : SourceInference.Context) (statements : List Syntax.Statement)
    (expectedReturn : Ty) (state : State) : Prop :=
  state.InferenceReady →
    state.RequirementsWellFormed →
    (∀ metavariable ∈ protectedVars, metavariable.index < state.inference.next) →
    LiveBindersSafe protectedVars state →
    SignatureCatalogWellFormed context.signatures →
    ProgramSignatureFormationValidated context.signatures →
    (∀ signature ∈ context.signatures.functions,
      signature.scheme.body = .function (Ty.productMany signature.parameterTypes) (Ty.productMany signature.returnTypes)) →
    expectedReturn.VariablesBelow state.inference.next →
    Safe protectedVars state expectedReturn →
    ∀ result,
      inferStatementsFuel fuel context statements expectedReturn state =
          .ok result →
      SafeTransport protectedVars state result.state ∧
        Safe protectedVars result.state result.type ∧ LiveBindersSafe protectedVars result.state ∧
        ∀ row ∈ result.state.requirements, row ∉ state.requirements → PredicateSafe protectedVars result.state row.predicate

def InferStatementFuelPrivacy
    (protectedVars : List TypeVarId) (fuel : Nat) (context : SourceInference.Context) (statement : Syntax.Statement)
    (expectedReturn : Ty) (state : State) : Prop :=
  state.InferenceReady →
    state.RequirementsWellFormed →
    (∀ metavariable ∈ protectedVars, metavariable.index < state.inference.next) →
    LiveBindersSafe protectedVars state →
    SignatureCatalogWellFormed context.signatures →
    ProgramSignatureFormationValidated context.signatures →
    (∀ signature ∈ context.signatures.functions,
      signature.scheme.body = .function (Ty.productMany signature.parameterTypes) (Ty.productMany signature.returnTypes)) →
    expectedReturn.VariablesBelow state.inference.next →
    Safe protectedVars state expectedReturn →
    ∀ result,
      inferStatementFuel fuel context statement expectedReturn state =
          .ok result →
      SafeTransport protectedVars state result.state ∧
        Safe protectedVars result.state result.type ∧ LiveBindersSafe protectedVars result.state ∧
        ∀ row ∈ result.state.requirements, row ∉ state.requirements → PredicateSafe protectedVars result.state row.predicate

def InferForItemsFuelPrivacy
    (protectedVars : List TypeVarId) (fuel : Nat) (context : SourceInference.Context) (items : List Syntax.ForItem)
    (state : State) : Prop :=
  state.InferenceReady →
    state.RequirementsWellFormed →
    (∀ metavariable ∈ protectedVars, metavariable.index < state.inference.next) →
    LiveBindersSafe protectedVars state →
    SignatureCatalogWellFormed context.signatures →
    ProgramSignatureFormationValidated context.signatures →
    (∀ signature ∈ context.signatures.functions,
      signature.scheme.body = .function (Ty.productMany signature.parameterTypes) (Ty.productMany signature.returnTypes)) →
    ∀ result,
      inferForItemsFuel fuel context items state = .ok result →
      SafeTransport protectedVars state result.state ∧ LiveBindersSafe protectedVars result.state ∧
        ∀ row ∈ result.state.requirements, row ∉ state.requirements → PredicateSafe protectedVars result.state row.predicate

def InferForItemFuelPrivacy
    (protectedVars : List TypeVarId) (fuel : Nat) (context : SourceInference.Context) (item : Syntax.ForItem)
    (state : State) : Prop :=
  state.InferenceReady →
    state.RequirementsWellFormed →
    (∀ metavariable ∈ protectedVars, metavariable.index < state.inference.next) →
    LiveBindersSafe protectedVars state →
    SignatureCatalogWellFormed context.signatures →
    ProgramSignatureFormationValidated context.signatures →
    (∀ signature ∈ context.signatures.functions,
      signature.scheme.body = .function (Ty.productMany signature.parameterTypes) (Ty.productMany signature.returnTypes)) →
    ∀ result,
      inferForItemFuel fuel context item state = .ok result →
      SafeTransport protectedVars state result.2 ∧ LiveBindersSafe protectedVars result.2 ∧
        ∀ row ∈ result.2.requirements, row ∉ state.requirements → PredicateSafe protectedVars result.2 row.predicate

def InferPlaceFuelPrivacy
    (protectedVars : List TypeVarId) (fuel : Nat) (context : SourceInference.Context) (target : Syntax.Expr)
    (state : State) : Prop :=
  state.InferenceReady →
    state.RequirementsWellFormed →
    (∀ metavariable ∈ protectedVars, metavariable.index < state.inference.next) →
    LiveBindersSafe protectedVars state →
    SignatureCatalogWellFormed context.signatures →
    ProgramSignatureFormationValidated context.signatures →
    (∀ signature ∈ context.signatures.functions,
      signature.scheme.body = .function (Ty.productMany signature.parameterTypes) (Ty.productMany signature.returnTypes)) →
    ∀ result,
      inferPlaceFuel fuel context target state = .ok result →
      SafeTransport protectedVars state result.2 ∧
        Safe protectedVars result.2 result.1.type ∧ LiveBindersSafe protectedVars result.2 ∧
        ∀ row ∈ result.2.requirements, row ∉ state.requirements → PredicateSafe protectedVars result.2 row.predicate

def InferAssignedValueFuelPrivacy
    (protectedVars : List TypeVarId) (fuel : Nat) (context : SourceInference.Context) (target : Syntax.Expr)
    (operator : Syntax.ValueAssignOp) (value : Syntax.Expr)
    (state : State) : Prop :=
  state.InferenceReady →
    state.RequirementsWellFormed →
    (∀ metavariable ∈ protectedVars, metavariable.index < state.inference.next) →
    LiveBindersSafe protectedVars state →
    SignatureCatalogWellFormed context.signatures →
    ProgramSignatureFormationValidated context.signatures →
    (∀ signature ∈ context.signatures.functions,
      signature.scheme.body = .function (Ty.productMany signature.parameterTypes) (Ty.productMany signature.returnTypes)) →
    ∀ result,
      inferAssignedValueFuel fuel context target operator value state =
          .ok result →
      SafeTransport protectedVars state result.2.2 ∧
        Safe protectedVars result.2.2 result.1.target.type ∧
        Safe protectedVars result.2.2 result.2.1.type ∧ LiveBindersSafe protectedVars result.2.2 ∧
        ∀ row ∈ result.2.2.requirements, row ∉ state.requirements → PredicateSafe protectedVars result.2.2 row.predicate

def InferExprsFuelPrivacy
    (protectedVars : List TypeVarId) (fuel : Nat) (context : SourceInference.Context) (expressions : List Syntax.Expr)
    (state : State) : Prop :=
  state.InferenceReady →
    state.RequirementsWellFormed →
    (∀ metavariable ∈ protectedVars, metavariable.index < state.inference.next) →
    LiveBindersSafe protectedVars state →
    SignatureCatalogWellFormed context.signatures →
    ProgramSignatureFormationValidated context.signatures →
    (∀ signature ∈ context.signatures.functions,
      signature.scheme.body = .function (Ty.productMany signature.parameterTypes) (Ty.productMany signature.returnTypes)) →
    ∀ result,
      inferExprsFuel fuel context expressions state = .ok result →
      SafeTransport protectedVars state result.2 ∧
        (∀ expression ∈ result.1, Safe protectedVars result.2 expression.type) ∧
        LiveBindersSafe protectedVars result.2 ∧
        ∀ row ∈ result.2.requirements, row ∉ state.requirements → PredicateSafe protectedVars result.2 row.predicate

def InferMatchCasesFuelPrivacy
    (protectedVars : List TypeVarId) (fuel : Nat) (context : SourceInference.Context) (scrutineeType expectedReturn : Ty)
    (outerScope : LexicalScope) (cases : List Syntax.MatchCase)
    (state : State) : Prop :=
  state.InferenceReady →
    state.RequirementsWellFormed →
    (∀ metavariable ∈ protectedVars, metavariable.index < state.inference.next) →
    LiveBindersSafe protectedVars state →
    SignatureCatalogWellFormed context.signatures →
    ProgramSignatureFormationValidated context.signatures →
    (∀ signature ∈ context.signatures.functions,
      signature.scheme.body = .function (Ty.productMany signature.parameterTypes) (Ty.productMany signature.returnTypes)) →
    scrutineeType.VariablesBelow state.inference.next →
    Safe protectedVars state scrutineeType →
    expectedReturn.VariablesBelow state.inference.next →
    Safe protectedVars state expectedReturn →
    state.lexicalScope = outerScope →
    ∀ result,
      inferMatchCasesFuel fuel context scrutineeType expectedReturn outerScope
          cases state = .ok result →
      SafeTransport protectedVars state result.state ∧ LiveBindersSafe protectedVars result.state ∧
        ∀ row ∈ result.state.requirements, row ∉ state.requirements → PredicateSafe protectedVars result.state row.predicate

end Solcore.SourceSemantics.SourceInferenceSoundness.ProtectedVariables
