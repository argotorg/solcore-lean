import Solcore.SourceSemantics.SourceInferenceProtectedVariableFixedness
import Solcore.SourceSemantics.SourceInferenceSelectedPrivacyInference

/-! Actual inference leaves protected, initially fixed variables unchanged. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceSoundness.ProtectedVariables
open Frontend SourceInference TypeSystem Detail

def InferExprFuelFixedness
    (protectedVars : List TypeVarId) (fuel : Nat) (context : SourceInference.Context) (expression : Syntax.Expr)
    (expected : Option Ty) (state : State) : Prop :=
  state.InferenceReady →
    state.RequirementsWellFormed →
    (∀ metavariable ∈ protectedVars, metavariable.index < state.inference.next) →
    LiveBindersSafe protectedVars state →
    FixesProtected protectedVars state →
    SignatureCatalogWellFormed context.signatures →
    ProgramSignatureFormationValidated context.signatures →
    (∀ signature ∈ context.signatures.functions,
      signature.scheme.body = .function (Ty.productMany signature.parameterTypes) (Ty.productMany signature.returnTypes)) →
    (∀ expectedType ∈ expected,
      expectedType.VariablesBelow state.inference.next) →
    (∀ expectedType ∈ expected, Safe protectedVars state expectedType) →
    ∀ result,
      inferExprFuel fuel context expression expected state = .ok result →
      FixesProtected protectedVars result.2

def InferConstructorApplicationFuelFixedness
    (protectedVars : List TypeVarId) (fuel : Nat) (context : SourceInference.Context) (source : Syntax.Expr)
    (id : ExpressionId) (instantiation : DataConstructorInstantiation)
    (arguments : List Syntax.Expr) (expected : Option Ty)
    (state : State) : Prop :=
  state.InferenceReady →
    state.RequirementsWellFormed →
    (∀ metavariable ∈ protectedVars, metavariable.index < state.inference.next) →
    LiveBindersSafe protectedVars state →
    FixesProtected protectedVars state →
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
      FixesProtected protectedVars result.2

def InferConstructorArgumentsFuelFixedness
    (protectedVars : List TypeVarId) (fuel : Nat) (context : SourceInference.Context) (sources : List Syntax.Expr)
    (expectedTypes : List Ty) (state : State) : Prop :=
  state.InferenceReady →
    state.RequirementsWellFormed →
    (∀ metavariable ∈ protectedVars, metavariable.index < state.inference.next) →
    LiveBindersSafe protectedVars state →
    FixesProtected protectedVars state →
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
      FixesProtected protectedVars result.2

def InferStatementsFuelFixedness
    (protectedVars : List TypeVarId) (fuel : Nat) (context : SourceInference.Context) (statements : List Syntax.Statement)
    (expectedReturn : Ty) (state : State) : Prop :=
  state.InferenceReady →
    state.RequirementsWellFormed →
    (∀ metavariable ∈ protectedVars, metavariable.index < state.inference.next) →
    LiveBindersSafe protectedVars state →
    FixesProtected protectedVars state →
    SignatureCatalogWellFormed context.signatures →
    ProgramSignatureFormationValidated context.signatures →
    (∀ signature ∈ context.signatures.functions,
      signature.scheme.body = .function (Ty.productMany signature.parameterTypes) (Ty.productMany signature.returnTypes)) →
    expectedReturn.VariablesBelow state.inference.next →
    Safe protectedVars state expectedReturn →
    ∀ result,
      inferStatementsFuel fuel context statements expectedReturn state =
          .ok result →
      FixesProtected protectedVars result.state

def InferStatementFuelFixedness
    (protectedVars : List TypeVarId) (fuel : Nat) (context : SourceInference.Context) (statement : Syntax.Statement)
    (expectedReturn : Ty) (state : State) : Prop :=
  state.InferenceReady →
    state.RequirementsWellFormed →
    (∀ metavariable ∈ protectedVars, metavariable.index < state.inference.next) →
    LiveBindersSafe protectedVars state →
    FixesProtected protectedVars state →
    SignatureCatalogWellFormed context.signatures →
    ProgramSignatureFormationValidated context.signatures →
    (∀ signature ∈ context.signatures.functions,
      signature.scheme.body = .function (Ty.productMany signature.parameterTypes) (Ty.productMany signature.returnTypes)) →
    expectedReturn.VariablesBelow state.inference.next →
    Safe protectedVars state expectedReturn →
    ∀ result,
      inferStatementFuel fuel context statement expectedReturn state =
          .ok result →
      FixesProtected protectedVars result.state

def InferForItemsFuelFixedness
    (protectedVars : List TypeVarId) (fuel : Nat) (context : SourceInference.Context) (items : List Syntax.ForItem)
    (state : State) : Prop :=
  state.InferenceReady →
    state.RequirementsWellFormed →
    (∀ metavariable ∈ protectedVars, metavariable.index < state.inference.next) →
    LiveBindersSafe protectedVars state →
    FixesProtected protectedVars state →
    SignatureCatalogWellFormed context.signatures →
    ProgramSignatureFormationValidated context.signatures →
    (∀ signature ∈ context.signatures.functions,
      signature.scheme.body = .function (Ty.productMany signature.parameterTypes) (Ty.productMany signature.returnTypes)) →
    ∀ result,
      inferForItemsFuel fuel context items state = .ok result →
      FixesProtected protectedVars result.state

def InferForItemFuelFixedness
    (protectedVars : List TypeVarId) (fuel : Nat) (context : SourceInference.Context) (item : Syntax.ForItem)
    (state : State) : Prop :=
  state.InferenceReady →
    state.RequirementsWellFormed →
    (∀ metavariable ∈ protectedVars, metavariable.index < state.inference.next) →
    LiveBindersSafe protectedVars state →
    FixesProtected protectedVars state →
    SignatureCatalogWellFormed context.signatures →
    ProgramSignatureFormationValidated context.signatures →
    (∀ signature ∈ context.signatures.functions,
      signature.scheme.body = .function (Ty.productMany signature.parameterTypes) (Ty.productMany signature.returnTypes)) →
    ∀ result,
      inferForItemFuel fuel context item state = .ok result →
      FixesProtected protectedVars result.2

def InferPlaceFuelFixedness
    (protectedVars : List TypeVarId) (fuel : Nat) (context : SourceInference.Context) (target : Syntax.Expr)
    (state : State) : Prop :=
  state.InferenceReady →
    state.RequirementsWellFormed →
    (∀ metavariable ∈ protectedVars, metavariable.index < state.inference.next) →
    LiveBindersSafe protectedVars state →
    FixesProtected protectedVars state →
    SignatureCatalogWellFormed context.signatures →
    ProgramSignatureFormationValidated context.signatures →
    (∀ signature ∈ context.signatures.functions,
      signature.scheme.body = .function (Ty.productMany signature.parameterTypes) (Ty.productMany signature.returnTypes)) →
    ∀ result,
      inferPlaceFuel fuel context target state = .ok result →
      FixesProtected protectedVars result.2

def InferAssignedValueFuelFixedness
    (protectedVars : List TypeVarId) (fuel : Nat) (context : SourceInference.Context) (target : Syntax.Expr)
    (operator : Syntax.ValueAssignOp) (value : Syntax.Expr)
    (state : State) : Prop :=
  state.InferenceReady →
    state.RequirementsWellFormed →
    (∀ metavariable ∈ protectedVars, metavariable.index < state.inference.next) →
    LiveBindersSafe protectedVars state →
    FixesProtected protectedVars state →
    SignatureCatalogWellFormed context.signatures →
    ProgramSignatureFormationValidated context.signatures →
    (∀ signature ∈ context.signatures.functions,
      signature.scheme.body = .function (Ty.productMany signature.parameterTypes) (Ty.productMany signature.returnTypes)) →
    ∀ result,
      inferAssignedValueFuel fuel context target operator value state =
          .ok result →
      FixesProtected protectedVars result.2.2

def InferExprsFuelFixedness
    (protectedVars : List TypeVarId) (fuel : Nat) (context : SourceInference.Context) (expressions : List Syntax.Expr)
    (state : State) : Prop :=
  state.InferenceReady →
    state.RequirementsWellFormed →
    (∀ metavariable ∈ protectedVars, metavariable.index < state.inference.next) →
    LiveBindersSafe protectedVars state →
    FixesProtected protectedVars state →
    SignatureCatalogWellFormed context.signatures →
    ProgramSignatureFormationValidated context.signatures →
    (∀ signature ∈ context.signatures.functions,
      signature.scheme.body = .function (Ty.productMany signature.parameterTypes) (Ty.productMany signature.returnTypes)) →
    ∀ result,
      inferExprsFuel fuel context expressions state = .ok result →
      FixesProtected protectedVars result.2

def InferMatchCasesFuelFixedness
    (protectedVars : List TypeVarId) (fuel : Nat) (context : SourceInference.Context) (scrutineeType expectedReturn : Ty)
    (outerScope : LexicalScope) (cases : List Syntax.MatchCase)
    (state : State) : Prop :=
  state.InferenceReady →
    state.RequirementsWellFormed →
    (∀ metavariable ∈ protectedVars, metavariable.index < state.inference.next) →
    LiveBindersSafe protectedVars state →
    FixesProtected protectedVars state →
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
      FixesProtected protectedVars result.state

end Solcore.SourceSemantics.SourceInferenceSoundness.ProtectedVariables
