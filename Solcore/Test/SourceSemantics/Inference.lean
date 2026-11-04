import Solcore.SourceSemantics.SourceInferenceSoundness
import Solcore.SourceSemantics.CoreLowering.LambdaMetadataViews
import Solcore.SourceSemantics.Dynamic.Fault
import Solcore.SourceSemantics.CoreLowering.CompatiblePathFaults
import Solcore.Frontend.SourceRuntimeValues
import Solcore.SourceSemantics.CoreLowering.LegacyClosureBoundary
import Solcore.Test.SourceCoreUnifiedCorpusSupport
import Solcore.Frontend.SourceInference.Types
import Solcore.Frontend.SourceInference.TypedIRProperties
import Solcore.Frontend.SourceSpecialization
import Solcore.SourceSemantics.Substitution
import Solcore.SourceSemantics.TraitResolutionSoundness

/-!
# Source inference tests

The source inference slice, the typed IR carrier, typed trait resolution, closure capture boundaries and
mapping defaults.
-/

section
-- leanmerge: from Solcore.Test.SourceInference
/-! Focused parsed-source regressions for the source inference slice. -/

set_option autoImplicit false

namespace Tests.SourceInference

open Solcore Solcore.Frontend

private def assertTrue (condition : Bool) (message : String) : IO Unit := do
  unless condition do
    throw (IO.userError message)

private def workspace (content : String) : Workspace.RawWorkspace := {
  entry := "main.solc"
  mainSources := [{ path := "main.solc", content }]
  externalLibraries := []
}

private def check (content : String) :
    IO (List SourceInference.CheckedFunction) := do
  match SourceInference.loadAndCheckProgram (workspace content) with
  | .ok checked => pure checked
  | .error errors =>
      throw (IO.userError s!"source inference failed: {reprStr errors}")

private def load (content : String) : IO LoadedProgram := do
  match loadProgram (workspace content) with
  | .ok loaded => pure loaded
  | .error errors =>
      throw (IO.userError s!"source inference loading failed: {reprStr errors}")

private def checkedNamed (environment : ProgramEnvironment)
    (checked : List SourceInference.CheckedFunction) (name : String) :
    IO SourceInference.CheckedFunction :=
  match checked.find? fun function =>
      (environment.declaration? function.declaration).any fun declaration =>
        declaration.name == some name with
  | some function => pure function
  | none => throw (IO.userError s!"checked function `{name}` was not found")

private def traitNameOf (environment : ProgramEnvironment)
    (predicate : ProgramPredicate) : Option String := do
  let trait ← predicate.trait.declaration?
  let declaration ← environment.declaration? trait
  declaration.name

private def hasBuiltinIntWordEvidence
    (solved : SourceInference.SolvedRequirement) : Bool :=
  solved.predicate == ProgramSignatures.builtinIntPredicate .word &&
    match solved.evidence with
    | .implementation (.byImpl goal (.builtin .intWord) premises) =>
        goal == solved.predicate && premises.isEmpty
    | _ => false

private def solverRegressionModule : Workspace.ModuleId :=
  ⟨.main, ⟨[⟨"source_inference_solver", by decide⟩], by decide⟩⟩

private def solverRegressionOwner : Resolved.DeclarationId :=
  ⟨solverRegressionModule, 0⟩

/-- A solved initial state supports reflexive progress, fresh-variable
allocation, and a following source-state-only update as one composable
inference-progress chain. -/
example :
    let initial := SourceInference.State.initial solverRegressionOwner
    let fresh := initial.fresh.2
    initial.InferenceProgress (fresh.withLocals []) := by
  dsimp only
  have initialSolved :
      (SourceInference.State.initial solverRegressionOwner).inference.Solved := by
    change (TypeSystem.InferState.initial 0).Solved
    exact TypeSystem.InferState.Solved.initial 0
  have reflexive :=
    SourceInference.State.InferenceProgress.refl initialSolved
  have freshProgress := SourceInference.State.InferenceProgress.fresh
    (SourceInference.State.initial solverRegressionOwner) reflexive.solved
  have stateOnlyProgress := SourceInference.State.InferenceProgress.withLocals
    (SourceInference.State.initial solverRegressionOwner).fresh.2 []
    freshProgress.solved
  exact reflexive.trans (freshProgress.trans stateOnlyProgress)

/-- A type bounded in the input state remains bounded after applying the
solved substitution of any later inference state. -/
example {before after : SourceInference.State} {type : TypeSystem.Ty}
    (progress : before.InferenceProgress after)
    (below : type.VariablesBelow before.inference.next) :
    (after.resolve type).VariablesBelow after.inference.next := by
  exact progress.resolve_variablesBelow below

/-- Readiness starts from the input environment, survives fresh allocation,
and admits a binder whose monomorphic body is the freshly allocated type. -/
example :
    let initial := SourceInference.State.initial solverRegressionOwner
    let allocation := initial.fresh
    let scheme := TypeSystem.Scheme.mono allocation.1
    (allocation.2.allocateBinder "fresh" scheme none false []).2
      |>.InferenceReady := by
  dsimp only
  let initial := SourceInference.State.initial solverRegressionOwner
  have initialReady : initial.InferenceReady :=
    SourceInference.State.InferenceReady.initial solverRegressionOwner [] []
  have freshReady : initial.fresh.2.InferenceReady :=
    SourceInference.State.InferenceReady.fresh initialReady
  have freshTypeBelow :
      initial.fresh.1.VariablesBelow initial.fresh.2.inference.next := by
    simp [initial, SourceInference.State.fresh,
      TypeSystem.InferState.fresh]
  exact SourceInference.State.InferenceReady.allocateBinder
    "fresh" (TypeSystem.Scheme.mono initial.fresh.1) none false []
    freshReady (by
      simpa [TypeSystem.Scheme.mono] using freshTypeBelow)

/-- Initial parameters are below the stable-local cutoff, so the next visible
binder receives an identity distinct from every retained input binder. -/
example :
    let locals : TypeSystem.Environment :=
      [("left", .mono .word), ("right", .mono .bool)]
    let state := SourceInference.State.initial solverRegressionOwner locals []
    let allocated := state.allocateBinder "fresh" (.mono .unit)
    allocated.1.id ∉ state.localBinders.map fun binder => binder.id := by
  dsimp only
  apply SourceInference.State.allocateBinder_id_fresh
  exact SourceInference.State.initial_localBindersBelowNextLocal
    solverRegressionOwner
    [("left", .mono .word), ("right", .mono .bool)] []

/-- Restoring an outer lexical scope after inner inference preserves the
inner semantic progress while re-establishing outer-binder readiness. -/
example {outer inner : SourceInference.State}
    (ready : outer.InferenceReady)
    (progress : outer.InferenceProgress inner) :
    outer.InferenceProgress
        (inner.restoreLexicalScope outer.lexicalScope) ∧
      (inner.restoreLexicalScope outer.lexicalScope).InferenceReady := by
  exact SourceInference.State.restoreLexicalScope_inferenceProperties
    ready progress

/-- Lexical restoration exposes exactly the captured scope. -/
example (state : SourceInference.State)
    (scope : SourceInference.LexicalScope) :
    (state.restoreLexicalScope scope).lexicalScope = scope := by
  simp

/-- Repeated fresh-type allocation packages progress, readiness, and exact
allocator bounds for every returned metavariable. -/
example (count : Nat) (state : SourceInference.State)
    (ready : state.InferenceReady) :
    state.InferenceProgress
        (SourceInference.Detail.freshTypes count state).2 ∧
      (SourceInference.Detail.freshTypes count state).2.InferenceReady ∧
      ∀ type ∈ (SourceInference.Detail.freshTypes count state).1,
        type.VariablesBelow
          (SourceInference.Detail.freshTypes count state).2.inference.next := by
  exact SourceInference.Detail.freshTypes_inferenceProperties count state ready

/-- Successful lambda-parameter binding packages progress and readiness while
bounding every returned parameter type at the final allocator. -/
example {context : SourceInference.Context}
    {parameters : List Syntax.LambdaParameter} {index : Nat}
    {seen : List String} {state : SourceInference.State}
    {result : List SourceInference.TypedBinder × List TypeSystem.Ty ×
      SourceInference.State}
    (ready : state.InferenceReady)
    (success : SourceInference.Detail.bindLambdaParameters context parameters
      index seen state = .ok result) :
    state.InferenceProgress result.2.2 ∧
      result.2.2.InferenceReady ∧
      ∀ type ∈ result.2.1,
        type.VariablesBelow result.2.2.inference.next := by
  exact SourceInference.Detail.bindLambdaParameters_inferenceProperties
    ready success

/-- Successful recursive source-pattern inference advances inference safely
and returns a pattern type bounded by the final allocator. -/
example {fuel : Nat} {context : SourceInference.Context}
    {pattern : Syntax.Pattern} {expected : TypeSystem.Ty}
    {state : SourceInference.State}
    {result : SourceInference.TypedMatchPattern × SourceInference.State}
    (ready : state.InferenceReady)
    (expectedBelow : expected.VariablesBelow state.inference.next)
    (validated : ProgramSignatureFormationValidated context.signatures)
    (success : SourceInference.Detail.inferMatchPatternFuel fuel context
      pattern expected state = .ok result) :
    state.InferenceProgress result.2 ∧ result.2.InferenceReady ∧
      result.1.type.VariablesBelow result.2.inference.next := by
  exact SourceInference.Detail.inferMatchPatternFuel_inferenceProperties
    ready expectedBelow validated success

private def shadowingBinderEnvironment : TypeSystem.Environment :=
  [("shadowed", TypeSystem.Scheme.mono .bool),
    ("shadowed", TypeSystem.Scheme.mono .word)]

private def shadowingBinderState : SourceInference.State :=
  SourceInference.State.initial solverRegressionOwner
    shadowingBinderEnvironment

private def shadowingSelectedBinder : SourceInference.TypedBinder := {
  id := { owner := solverRegressionOwner, binderIndex := 0 }
  name := "shadowed"
  scheme := TypeSystem.Scheme.mono .bool
}

private theorem shadowingBinderState_ready :
    shadowingBinderState.InferenceReady := by
  exact SourceInference.State.InferenceReady.initial
    solverRegressionOwner shadowingBinderEnvironment []

private theorem shadowingBinderState_lookup :
    shadowingBinderState.lookupBinder? "shadowed" =
      some shadowingSelectedBinder := by
  rfl

/-- First-match shadowing selects the innermost binder while readiness exposes
that exact selected scheme in the canonical environment and bounds both its
body and unquantified free variables. -/
example :
    ("shadowed", shadowingSelectedBinder.scheme) ∈
        shadowingBinderState.binderEnvironment ∧
      shadowingSelectedBinder.scheme.body.VariablesBelow
        shadowingBinderState.inference.next ∧
      shadowingSelectedBinder.scheme.FreeVariablesBelow
        shadowingBinderState.inference.next := by
  exact ⟨
    SourceInference.State.lookupBinder?_eq_some_mem_binderEnvironment
      shadowingBinderState_lookup,
    shadowingBinderState_ready.lookupBinder?_body_variablesBelow
      shadowingBinderState_lookup,
    shadowingBinderState_ready.lookupBinder?_freeVariablesBelow
      shadowingBinderState_lookup⟩

/-- Instantiating the selected shadowing binder advances the allocator
monotonically while preserving readiness and bounding the resolved body. -/
example :
    let instantiated :=
      shadowingSelectedBinder.scheme.instantiateWithSubstitution
        shadowingBinderState.inference.next
    let inference := {
      shadowingBinderState.inference with next := instantiated.next
    }
    let next : SourceInference.State := {
      shadowingBinderState with inference
    }
    shadowingBinderState.InferenceProgress next ∧
      next.InferenceReady ∧
      (next.resolve instantiated.body).VariablesBelow next.inference.next := by
  exact SourceInference.Detail.localBinderInstantiation_inferenceProperties
    shadowingBinderState_ready shadowingBinderState_lookup

private def unificationProgressInput : SourceInference.State :=
  (SourceInference.State.initial solverRegressionOwner).fresh.2

private def unificationProgressVariable : TypeSystem.Ty :=
  (SourceInference.State.initial solverRegressionOwner).fresh.1

private def unificationProgressResult : SourceInference.State := {
  unificationProgressInput with
  inference := {
    next := 1
    substitution := [(⟨0⟩, .word)]
  }
}

private theorem unificationProgress_success :
    SourceInference.Detail.unify unificationProgressInput
      unificationProgressVariable .word = .ok unificationProgressResult := by
  rfl

/-- Binding a freshly allocated variable to `Word` produces a genuine
semantic substitution extension while preserving inference readiness. -/
example :
    unificationProgressResult.inference.substitution.SemanticallyExtends
        unificationProgressInput.inference.substitution ∧
      unificationProgressResult.InferenceReady ∧
      unificationProgressResult.resolve unificationProgressVariable = .word := by
  have inputReady : unificationProgressInput.InferenceReady := by
    exact SourceInference.State.InferenceReady.fresh
      (SourceInference.State.InferenceReady.initial
        solverRegressionOwner [] [])
  have variableBelow : unificationProgressVariable.VariablesBelow
      unificationProgressInput.inference.next := by
    simp [unificationProgressVariable, unificationProgressInput,
      SourceInference.State.fresh, TypeSystem.InferState.fresh]
  have wordBelow : TypeSystem.Ty.word.VariablesBelow
      unificationProgressInput.inference.next := by
    simp [TypeSystem.Ty.word, TypeSystem.Ty.VariablesBelow,
      TypeSystem.Ty.freeVariables]
  have progress := SourceInference.Detail.unify_inferenceProgress
    inputReady.solved variableBelow wordBelow unificationProgress_success
  have resultReady :=
    SourceInference.Detail.unify_preserves_inferenceReady inputReady
      variableBelow wordBelow unificationProgress_success
  exact ⟨progress.substitution_extends, resultReady, rfl⟩

private def solverRegressionFirst : TypeSystem.TypeVarId := ⟨0⟩
private def solverRegressionSecond : TypeSystem.TypeVarId := ⟨1⟩

private def solverRegressionSource : ProgramPredicate :=
  ProgramSignatures.builtinIntPredicate (.variable solverRegressionFirst)

private def solverRegressionNormalized : ProgramPredicate :=
  ProgramSignatures.builtinIntPredicate (.variable solverRegressionSecond)

private def solverRegressionContext : SourceInference.Context := {
  environment := { modules := [], declarations := [] }
  signatures := {
    functions := []
    implRules := []
    traits := []
    implementations := []
  }
  scope := {
    currentModule := solverRegressionModule
    genericOwner := solverRegressionOwner
    genericParameters := []
  }
  assumptions := [solverRegressionSource]
}

private def solverRegressionSpan : Syntax.SourceSpan :=
  ⟨⟨.main, "source_inference_solver.sol"⟩, 0, 0⟩

private def residualRangeSubstitution : TypeSystem.Substitution :=
  [(⟨0⟩, .variable ⟨1⟩)]

private def residualRangeState : SourceInference.State := {
  SourceInference.State.initial solverRegressionOwner with
  inference := { next := 2, substitution := residualRangeSubstitution }
}

private def residualRangeResult : SourceInference.Result := {
  type := .unit
  substitution := residualRangeSubstitution
  solvedRequirements := []
  typedSource := residualRangeState.toTypedSource []
}

/-- Finalization accepts a structurally formed substitution range which
retains a residual flexible variable. -/
example :
    SourceInference.Detail.finalize solverRegressionContext .unit
        residualRangeState [] = .ok residualRangeResult := by
  rfl

private def recoveryRangeState : SourceInference.State := {
  SourceInference.State.initial solverRegressionOwner with
  inference := { next := 1, substitution := [(⟨0⟩, .error)] }
}

/-- Finalization rejects a recovery type stored in the final substitution
before exposing the substituted source. -/
example :
    SourceInference.Detail.finalize solverRegressionContext .unit
        recoveryRangeState [] =
      .error (.typeFormation (.recoveryType solverRegressionOwner)) := by
  rfl

private def instantiationStartScheme : TypeSystem.Scheme := {
  quantified := [⟨0⟩]
  body := .variable ⟨0⟩
}

private def instantiationStartState : SourceInference.State :=
  SourceInference.State.initial solverRegressionOwner
    [("genericStart", instantiationStartScheme)]

private def instantiationStartSource : Syntax.Expr :=
  ⟨solverRegressionSpan,
    .identifier ⟨solverRegressionSpan, "genericStart"⟩⟩

/-- A local generic reference retains the exact allocator position from
immediately before its canonical scheme instantiation. -/
example :
    (match SourceInference.Detail.inferExprFuel 1 solverRegressionContext
        instantiationStartSource none instantiationStartState with
      | .error _ => []
      | .ok (_, state) => state.nodes.filterMap fun
          | .expression node => some node.localSchemeInstantiationStart
          | .statement _ => none) =
      [some instantiationStartState.inference.next] := by
  native_decide

private def noCaptureQuantified : TypeSystem.TypeVarId := ⟨10⟩
private def noCaptureSourceVariable : TypeSystem.TypeVarId := ⟨11⟩

private def zeroRequirementGenericBinder : SourceInference.TypedBinder := {
  id := ⟨solverRegressionOwner, 0⟩
  name := "generic"
  scheme := {
    quantified := [noCaptureQuantified]
    body := .variable noCaptureSourceVariable
  }
  schemeRequirements := []
  span := some solverRegressionSpan
}

private def noCaptureInitializer : SourceInference.ExpressionNode := {
  id := ⟨⟨solverRegressionOwner, 0⟩⟩
  span := solverRegressionSpan
  type := .variable noCaptureSourceVariable
  form := .literal (.decimal "0")
  requirements := []
}

private def noCaptureStatement : SourceInference.StatementNode := {
  id := ⟨⟨solverRegressionOwner, 1⟩⟩
  span := solverRegressionSpan
  type := .unit
  form := .letDecl zeroRequirementGenericBinder
    (some noCaptureInitializer.id)
}

private def noCaptureSource : SourceInference.TypedSource := {
  owner := solverRegressionOwner
  inputs := []
  roots := [.statement noCaptureStatement.id]
  nodes := [
    .expression noCaptureInitializer,
    .statement noCaptureStatement
  ]
}

private def captureSubstitution : TypeSystem.Substitution :=
  [(noCaptureSourceVariable, .variable noCaptureQuantified)]

private def safeSubstitution : TypeSystem.Substitution :=
  [(noCaptureSourceVariable, .word)]

/-- The initialized-let inventory includes a generalized binder even when its
qualified-requirement spine is empty. -/
example : noCaptureSource.initializedLetBinders =
    [zeroRequirementGenericBinder] := by
  rfl

/-- A closed replacement cannot capture the generalized binder. -/
example :
    SourceInference.Detail.validateSourceLocalSchemeNoCapture noCaptureSource
        safeSubstitution = .ok () := by
  rfl

/-- A forged final substitution whose selected range mentions the protected
quantifier is rejected even for a zero-requirement generic scheme. -/
example :
    SourceInference.Detail.validateSourceLocalSchemeNoCapture noCaptureSource
        captureSubstitution =
      .error (.localSchemeInstantiationCapture
        zeroRequirementGenericBinder.id) := by
  rfl

/-- Successful executable validation exposes the reusable proof-facing
binder-local no-capture certificate. -/
example : SourceInference.Detail.LocalBinderInstantiationNoCapture
    safeSubstitution zeroRequirementGenericBinder := by
  exact SourceInference.Detail.validateSourceLocalSchemeNoCapture_success
    (source := noCaptureSource) (substitution := safeSubstitution) (by rfl)
    zeroRequirementGenericBinder (by
      change zeroRequirementGenericBinder ∈ [zeroRequirementGenericBinder]
      simp)

private def forgedCaptureState : SourceInference.State := {
  SourceInference.State.initial solverRegressionOwner with
  inference := { next := 12, substitution := captureSubstitution }
  nextLocal := 1
  nextOccurrence := 2
  nodes := noCaptureSource.nodes
}

/-- Finalization runs capture validation after defaulting and before exposing
the substituted source or invoking requirement solving. -/
example :
    SourceInference.Detail.finalize solverRegressionContext .unit
        forgedCaptureState noCaptureSource.roots =
      .error (.localSchemeInstantiationCapture
        zeroRequirementGenericBinder.id) := by
  rfl

private def numericPatternOrigin : SourceInference.IntegerPatternOrigin := {
  metavariable := ⟨0⟩
  span := solverRegressionSpan
  requirement := ⟨0⟩
}

private def numericPatternState : SourceInference.State := {
  unificationProgressInput with integerPatterns := [numericPatternOrigin]
}

private def numericPatternOutOfBoundsState : SourceInference.State := {
  numericPatternState with
  inference := { numericPatternState.inference with next := 0 }
}

private def numericLiteralOutOfBoundsOrigin :
    SourceInference.IntegerLiteralOrigin := {
  metavariable := ⟨1⟩
  expression := ⟨⟨solverRegressionOwner, 0⟩⟩
  requirement := ⟨0⟩
}

private def numericLiteralOutOfBoundsState : SourceInference.State := {
  unificationProgressInput with
  integerLiterals := [numericLiteralOutOfBoundsOrigin]
}

/-- The executable numeric-origin guard accepts an allocated pattern target. -/
example :
    SourceInference.Detail.validateNumericOriginsBelowNext
        numericPatternState = .ok () := by
  rfl

/-- The guard reports the exact first pattern metavariable at the allocator
boundary instead of passing malformed state to defaulting. -/
example :
    SourceInference.Detail.validateNumericOriginsBelowNext
        numericPatternOutOfBoundsState =
      .error (.numericOriginOutOfBounds numericPatternOrigin.metavariable 0) := by
  rfl

/-- Literal origins are checked after patterns by the same allocator guard. -/
example :
    SourceInference.Detail.validateNumericOriginsBelowNext
        numericLiteralOutOfBoundsState =
      .error (.numericOriginOutOfBounds
        numericLiteralOutOfBoundsOrigin.metavariable 1) := by
  rfl

private def numericPatternResult : SourceInference.State := {
  numericPatternState with inference := unificationProgressResult.inference
}

private theorem numericPatternState_ready :
    numericPatternState.InferenceReady := by
  have ready := SourceInference.State.InferenceReady.fresh
    (SourceInference.State.InferenceReady.initial solverRegressionOwner [] [])
  constructor
  · simpa [numericPatternState, unificationProgressInput] using ready.solved
  · simpa [numericPatternState, unificationProgressInput,
      SourceInference.State.binderEnvironment] using ready.bindersBelow

private theorem numericPatternState_originsBelow :
    numericPatternState.NumericOriginsBelowNext := by
  exact
    SourceInference.Detail.validateNumericOriginsBelowNext_success (by rfl)

private theorem numericPatternDefault_success :
    SourceInference.Detail.defaultIntegerPatternTarget numericPatternState
      numericPatternOrigin = .ok numericPatternResult := by
  rfl

/-- A concrete unresolved numeric origin is allocator-bounded and defaulting
it to `Word` preserves both solved inference progress and readiness. -/
example :
    numericPatternState.InferenceProgress numericPatternResult ∧
      numericPatternResult.InferenceReady := by
  exact SourceInference.Detail.defaultIntegerPatternTarget_inferenceProperties
    numericPatternState_ready
    (numericPatternState_originsBelow.1 numericPatternOrigin (by simp
      [numericPatternState]))
    numericPatternDefault_success

private def solverRegressionRecoveryType : Syntax.TypeExpr := {
  span := solverRegressionSpan
  value := .error
}

/-- Successful source annotation resolution produces an allocator-bounded
type independently of the allocator's current position. -/
example {source : Syntax.TypeExpr} {type : TypeSystem.Ty}
    (success : SourceInference.Detail.resolveSourceType
      solverRegressionContext source = .ok type)
    (next : Nat) :
    type.VariablesBelow next :=
  SourceInference.Detail.resolveSourceType_success_variablesBelow
    success next

/-- Formation validation bounds every payload of a cataloged data constructor
at any flexible-variable allocator position. -/
example {signatures : ProgramSignatures}
    (validated : ProgramSignatureFormationValidated signatures)
    {dataType : ProgramDataSignature}
    (dataMember : dataType ∈ signatures.dataTypes)
    {constructor : ProgramDataConstructorSignature}
    (constructorMember : constructor ∈ dataType.constructors)
    (next : Nat) :
    ∀ payload ∈ constructor.payloadTypes,
      payload.VariablesBelow next := by
  exact
    ProgramSignatureFormationValidated.data_constructor_payloadTypes_variablesBelow
      validated dataMember constructorMember next

/-- Explicit constructor lookup preserves the owning data declaration and
constructor's membership in the whole-program signature catalog. -/
example {context : SourceInference.Context} {qualifiers : List String}
    {name : String} {dataType : ProgramDataSignature}
    {constructor : ProgramDataConstructorSignature}
    (success : SourceInference.Detail.explicitConstructorCandidate context
      qualifiers name = .ok (dataType, constructor)) :
    dataType ∈ context.signatures.dataTypes ∧
      constructor ∈ dataType.constructors := by
  exact SourceInference.Detail.explicitConstructorCandidate_success_members
    success

/-- Contextual constructor lookup additionally records the nominal expected
type that supplied the constructor's type arguments. -/
example {context : SourceInference.Context} {state : SourceInference.State}
    {expected : Option TypeSystem.Ty} {name : String}
    {dataType : ProgramDataSignature}
    {constructor : ProgramDataConstructorSignature}
    {arguments : List TypeSystem.Ty}
    (success : SourceInference.Detail.contextualConstructorCandidate context
      state expected name = .ok (dataType, constructor, arguments)) :
    dataType ∈ context.signatures.dataTypes ∧
      constructor ∈ dataType.constructors ∧
      ∃ expectedType,
        expected = some expectedType ∧
          state.resolve expectedType =
            TypeSystem.Ty.nominal dataType.id arguments := by
  exact SourceInference.Detail.contextualConstructorCandidate_success_facts
    success

/-- A contextual constructor lookup plus validated signatures bounds its
instantiated payload and result types at the current inference allocator. -/
example {context : SourceInference.Context} {state : SourceInference.State}
    {expected : Option TypeSystem.Ty} {name : String}
    {dataType : ProgramDataSignature}
    {constructor : ProgramDataConstructorSignature}
    {arguments : List TypeSystem.Ty}
    (ready : state.InferenceReady)
    (expectedBelow : ∀ expectedType ∈ expected,
      expectedType.VariablesBelow state.inference.next)
    (validated : ProgramSignatureFormationValidated context.signatures)
    (success : SourceInference.Detail.contextualConstructorCandidate context
      state expected name = .ok (dataType, constructor, arguments)) :
    (∀ payload ∈
        (SourceInference.Detail.instantiateDataConstructor dataType constructor
          arguments).payloadTypes,
      payload.VariablesBelow state.inference.next) ∧
      (SourceInference.Detail.instantiateDataConstructor dataType constructor
        arguments).resultType.VariablesBelow state.inference.next := by
  exact SourceInference.Detail.contextualConstructorCandidate_success_instantiation_variablesBelow
    ready expectedBelow validated success

/-- Pure constructor instantiation preserves allocator bounds on substituted
payload and nominal result types. -/
example {dataType : ProgramDataSignature}
    {constructor : ProgramDataConstructorSignature}
    {arguments : List TypeSystem.Ty} {next : Nat}
    (argumentsBelow : ∀ argument ∈ arguments,
      argument.VariablesBelow next)
    (payloadTypesBelow : ∀ payload ∈ constructor.payloadTypes,
      payload.VariablesBelow next) :
    (∀ payload ∈
        (SourceInference.Detail.instantiateDataConstructor dataType constructor
          arguments).payloadTypes,
      payload.VariablesBelow next) ∧
      (SourceInference.Detail.instantiateDataConstructor dataType constructor
        arguments).resultType.VariablesBelow next := by
  exact SourceInference.Detail.instantiateDataConstructor_types_variablesBelow
    argumentsBelow payloadTypesBelow

/-- Every constructor-callee candidate retains whole-program ownership
provenance. -/
example {context : SourceInference.Context} {state : SourceInference.State}
    {callee : Syntax.Expr}
    {candidates : List
      (ProgramDataSignature × ProgramDataConstructorSignature)}
    (success : SourceInference.Detail.constructorCalleeCandidates context state
      callee = .ok candidates) :
    ∀ dataType constructor, (dataType, constructor) ∈ candidates →
      dataType ∈ context.signatures.dataTypes ∧
        constructor ∈ dataType.constructors := by
  exact SourceInference.Detail.constructorCalleeCandidates_success_members
    success

/-- Fresh constructor instantiation packages allocator progress, readiness,
bounded parameter replacements, bounded payloads, and a bounded nominal
result without relying on a concrete constructor fixture. -/
example (dataType : ProgramDataSignature)
    (constructor : ProgramDataConstructorSignature)
    (state : SourceInference.State)
    (ready : state.InferenceReady)
    (payloadTypesBelow : ∀ payload ∈ constructor.payloadTypes,
      payload.VariablesBelow state.inference.next) :
    let result := SourceInference.Detail.freshDataConstructorInstantiation
      dataType constructor state
    state.InferenceProgress result.2 ∧
      result.2.InferenceReady ∧
      (∀ parameter replacement,
        (parameter, replacement) ∈ result.1.parameterSubstitution →
          replacement.VariablesBelow result.2.inference.next) ∧
      (∀ payload ∈ result.1.payloadTypes,
        payload.VariablesBelow result.2.inference.next) ∧
      result.1.resultType.VariablesBelow result.2.inference.next := by
  exact
    SourceInference.Detail.freshDataConstructorInstantiation_inferenceProperties
      dataType constructor state ready payloadTypesBelow

/-- A complete semantic application of constructor freshening: catalog
membership and a residually open declaration context suffice to admit the
exact generic instantiation returned by the executable allocator. -/
example {semanticContext : Solcore.SourceSemantics.Context}
    {dataType : ProgramDataSignature}
    {constructor : ProgramDataConstructorSignature}
    (state : SourceInference.State)
    (catalog : Solcore.SourceSemantics.SignatureCatalogWellFormed
      semanticContext.signatures)
    (binders : Solcore.SourceSemantics.TypeParameterBindersWellFormed
      semanticContext)
    (residual : semanticContext.residualTypeVariables = true)
    (dataType_mem : dataType ∈ semanticContext.signatures.dataTypes)
    (constructor_mem : constructor ∈ dataType.constructors) :
    let result := SourceInference.Detail.freshDataConstructorInstantiation
      dataType constructor state
    Solcore.SourceSemantics.DataConstructorInstantiation.Admissible
      semanticContext result.1 := by
  dsimp only
  exact
    Solcore.SourceSemantics.SourceInferenceSoundness.freshDataConstructorInstantiation_admissible
      catalog binders residual dataType_mem constructor_mem rfl

/-- Formation validation rejects the recovery sentinel independently of how
the resolved type was produced. -/
example : validateResolvedTypeFormation solverRegressionContext.signatures
    solverRegressionOwner [] .error =
    .error (.recoveryType solverRegressionOwner) := by
  rfl

/-- Formation validation also rejects constructor application syntax whose
head is not a cataloged nominal declaration. -/
example : validateResolvedTypeFormation solverRegressionContext.signatures
    solverRegressionOwner [] (.application .word .bool) =
    .error (.invalidApplication solverRegressionOwner
      (.application .word .bool)) := by
  rfl

private def solverRegressionState : SourceInference.State := {
  SourceInference.State.initial solverRegressionOwner with
  inference := {
    next := 2
    substitution := [
      (solverRegressionFirst, .variable solverRegressionSecond),
      (solverRegressionSecond, .bool)
    ]
  }
}

/-- Expected-type fitting packages allocator progress, readiness, and the
returned expression's allocator bound for downstream inference proofs. -/
example {actual : SourceInference.InferredExpression}
    {expected : Option TypeSystem.Ty}
    {result : SourceInference.Detail.ExpectationResult}
    (ready : solverRegressionState.InferenceReady)
    (actualBelow : actual.type.VariablesBelow
      solverRegressionState.inference.next)
    (expectedBelow : ∀ expectedType ∈ expected,
      expectedType.VariablesBelow solverRegressionState.inference.next)
    (success : SourceInference.Detail.withExpected solverRegressionContext
      solverRegressionState actual expected = .ok result) :
    solverRegressionState.InferenceProgress result.state ∧
      result.state.InferenceReady ∧
      result.expression.type.VariablesBelow result.state.inference.next := by
  exact SourceInference.Detail.withExpected_inferenceProperties ready
    actualBelow expectedBelow success

/-- A candidate retained by expected-type fitting exposes the same inference
progress, readiness, and allocator-bounded result type as the underlying fit. -/
example {context : SourceInference.Context}
    {state : SourceInference.State}
    {actual : SourceInference.InferredExpression}
    {expected : Option TypeSystem.Ty}
    {result : SourceInference.Detail.ExpectationResult}
    (ready : state.InferenceReady)
    (actualBelow : actual.type.VariablesBelow state.inference.next)
    (expectedBelow : ∀ expectedType ∈ expected,
      expectedType.VariablesBelow state.inference.next)
    (success : SourceInference.Detail.candidateWithExpected context state
      actual expected = .ok (some result)) :
    state.InferenceProgress result.state ∧
      result.state.InferenceReady ∧
      result.expression.type.VariablesBelow result.state.inference.next := by
  exact
    SourceInference.Detail.candidateWithExpected_some_inferenceProperties
      ready actualBelow expectedBelow success

/-- Recognizing a bounded function type bounds both its parameter bundle and
its result type. -/
example {type parameter result : TypeSystem.Ty} {next : Nat}
    (typeBelow : type.VariablesBelow next)
    (success : SourceInference.Detail.functionParts? type =
      some (parameter, result)) :
    parameter.VariablesBelow next ∧ result.VariablesBelow next := by
  exact SourceInference.Detail.functionParts?_success_variablesBelow
    typeBelow success

/-- Recovering an arity-indexed parameter row from a bounded bundle preserves
the allocator bound for every recovered parameter. -/
example {arity next : Nat} {parameter : TypeSystem.Ty}
    {parameters : List TypeSystem.Ty}
    (parameterBelow : parameter.VariablesBelow next)
    (success : SourceInference.Detail.parameterTypesForArity? arity parameter =
      some parameters) :
    ∀ type ∈ parameters, type.VariablesBelow next := by
  exact
    SourceInference.Detail.parameterTypesForArity?_success_variablesBelow
      parameterBelow success

/-- Successfully fitting a bounded argument spine against bounded parameters
makes semantic inference progress and preserves readiness. -/
example {context : SourceInference.Context} {state : SourceInference.State}
    {arguments : List SourceInference.InferredExpression}
    {parameters : List TypeSystem.Ty}
    {result : SourceInference.Detail.ArgumentFitResult}
    (ready : state.InferenceReady)
    (argumentsBelow : ∀ argument ∈ arguments,
      argument.type.VariablesBelow state.inference.next)
    (parametersBelow : ∀ parameter ∈ parameters,
      parameter.VariablesBelow state.inference.next)
    (success : SourceInference.Detail.fitArguments context state arguments
      parameters = .ok (some result)) :
    state.InferenceProgress result.state ∧
      result.state.InferenceReady := by
  exact SourceInference.Detail.fitArguments_some_inferenceProperties
    ready argumentsBelow parametersBelow success

/-- A retained function-candidate attempt packages progress, readiness, and a
final allocator bound for its inferred result type. -/
example {context : SourceInference.Context}
    {arguments : List SourceInference.InferredExpression}
    {integerLiteralOrigins : List SourceInference.IntegerLiteralOrigin}
    {call : SourceInference.ExpressionId}
    {expected : Option TypeSystem.Ty} {state : SourceInference.State}
    {signature : ProgramFunctionSignature}
    {result : SourceInference.Detail.CandidateAttemptResult}
    (ready : state.InferenceReady)
    (argumentsBelow : ∀ argument ∈ arguments,
      argument.type.VariablesBelow state.inference.next)
    (schemeBodyBelow : signature.scheme.body.VariablesBelow
      state.inference.next)
    (expectedBelow : ∀ expectedType ∈ expected,
      expectedType.VariablesBelow state.inference.next)
    (success : SourceInference.Detail.tryFunctionCandidate context arguments
      integerLiteralOrigins call expected state signature = .ok (some result)) :
    state.InferenceProgress result.state ∧
      result.state.InferenceReady ∧
      result.result.type.VariablesBelow result.state.inference.next := by
  exact SourceInference.Detail.tryFunctionCandidate_some_inferenceProperties
    ready argumentsBelow schemeBodyBelow expectedBelow success

/-- Selecting among bounded function candidates preserves the retained
attempt's progress, readiness, and result-type allocator bound. -/
example {context : SourceInference.Context} {name : String}
    {candidates : List ProgramFunctionSignature}
    {arguments : List SourceInference.InferredExpression}
    {integerLiteralOrigins : List SourceInference.IntegerLiteralOrigin}
    {call : SourceInference.ExpressionId}
    {expected : Option TypeSystem.Ty} {state : SourceInference.State}
    {result : SourceInference.Detail.CandidateAttemptResult}
    (ready : state.InferenceReady)
    (argumentsBelow : ∀ argument ∈ arguments,
      argument.type.VariablesBelow state.inference.next)
    (candidateBodiesBelow : ∀ signature ∈ candidates,
      signature.scheme.body.VariablesBelow state.inference.next)
    (expectedBelow : ∀ expectedType ∈ expected,
      expectedType.VariablesBelow state.inference.next)
    (success : SourceInference.Detail.selectFunctionCandidateFrom context name
      candidates arguments integerLiteralOrigins call expected state =
        .ok result) :
    state.InferenceProgress result.state ∧
      result.state.InferenceReady ∧
      result.result.type.VariablesBelow result.state.inference.next := by
  exact SourceInference.Detail.selectFunctionCandidateFrom_inferenceProperties
    ready argumentsBelow candidateBodiesBelow expectedBelow success

/-- Applying a bounded indirect function type packages progress, readiness,
and a final allocator bound for the inferred application result. -/
example {context : SourceInference.Context}
    {call : SourceInference.ExpressionId} {calleeType : TypeSystem.Ty}
    {arguments : List SourceInference.InferredExpression}
    {expected : Option TypeSystem.Ty} {state : SourceInference.State}
    {result : SourceInference.Detail.IndirectApplicationResult}
    (ready : state.InferenceReady)
    (calleeBelow : calleeType.VariablesBelow state.inference.next)
    (argumentsBelow : ∀ argument ∈ arguments,
      argument.type.VariablesBelow state.inference.next)
    (expectedBelow : ∀ expectedType ∈ expected,
      expectedType.VariablesBelow state.inference.next)
    (success : SourceInference.Detail.applyFunctionType context call calleeType
      arguments expected state = .ok result) :
    state.InferenceProgress result.state ∧
      result.state.InferenceReady ∧
      result.result.type.VariablesBelow result.state.inference.next := by
  exact SourceInference.Detail.applyFunctionType_inferenceProperties ready
    calleeBelow argumentsBelow expectedBelow success

/-- Pairwise unification of bounded builtin arguments and parameters makes
inference progress and preserves readiness. -/
example {arguments : List SourceInference.InferredExpression}
    {parameters : List TypeSystem.Ty}
    {state next : SourceInference.State}
    (ready : state.InferenceReady)
    (argumentsBelow : ∀ argument ∈ arguments,
      argument.type.VariablesBelow state.inference.next)
    (parametersBelow : ∀ parameter ∈ parameters,
      parameter.VariablesBelow state.inference.next)
    (success : SourceInference.Detail.unifyBuiltinFunctionArgumentsEqual
      arguments parameters state = .ok next) :
    state.InferenceProgress next ∧ next.InferenceReady := by
  exact
    SourceInference.Detail.unifyBuiltinFunctionArgumentsEqual_inferenceProperties
      ready argumentsBelow parametersBelow success

/-- Recording a fixed builtin-function call preserves inference readiness and
returns an allocator-bounded result type. -/
example {source callee : Syntax.Expr} {name : String}
    {function : BuiltinFunctionId}
    {arguments : List SourceInference.InferredExpression}
    {call : SourceInference.ExpressionId}
    {expected : Option TypeSystem.Ty} {state : SourceInference.State}
    {result : SourceInference.InferredExpression × SourceInference.State}
    (ready : state.InferenceReady)
    (argumentsBelow : ∀ argument ∈ arguments,
      argument.type.VariablesBelow state.inference.next)
    (expectedBelow : ∀ expectedType ∈ expected,
      expectedType.VariablesBelow state.inference.next)
    (success : SourceInference.Detail.recordBuiltinFunctionCall source callee
      name function arguments call expected state = .ok result) :
    state.InferenceProgress result.2 ∧
      result.2.InferenceReady ∧
      result.1.type.VariablesBelow result.2.inference.next := by
  exact
    SourceInference.Detail.recordBuiltinFunctionCall_inferenceProperties
      ready argumentsBelow expectedBelow success

/-- Recording an already inferred indirect call changes only typed-source
metadata and preserves the result-type allocator bound. -/
example (source : Syntax.Expr) (callee : SourceInference.InferredExpression)
    (arguments : List SourceInference.InferredExpression)
    (result : SourceInference.Detail.IndirectApplicationResult)
    (ready : result.state.InferenceReady)
    (resultBelow : result.result.type.VariablesBelow
      result.state.inference.next) :
    result.state.InferenceProgress
        (SourceInference.Detail.recordIndirectCall source callee arguments
          result).2 ∧
      (SourceInference.Detail.recordIndirectCall source callee arguments
        result).2.InferenceReady ∧
      (SourceInference.Detail.recordIndirectCall source callee arguments
        result).1.type.VariablesBelow
        (SourceInference.Detail.recordIndirectCall source callee arguments
          result).2.inference.next := by
  exact SourceInference.Detail.recordIndirectCall_inferenceProperties source
    callee arguments result ready resultBelow

/-- Unary operator inference preserves progress and readiness and returns an
allocator-bounded type. -/
example {context : SourceInference.Context} {operator : Syntax.UnaryOp}
    {operandType : TypeSystem.Ty} {expected : Option TypeSystem.Ty}
    {integerLiterals : List SourceInference.IntegerLiteralOrigin}
    {state : SourceInference.State}
    {result : SourceInference.Detail.OperatorInferenceResult}
    (ready : state.InferenceReady)
    (operandBelow : operandType.VariablesBelow state.inference.next)
    (expectedBelow : ∀ expectedType ∈ expected,
      expectedType.VariablesBelow state.inference.next)
    (success : SourceInference.Detail.inferUnaryOperator context operator
      operandType expected integerLiterals state = .ok result) :
    state.InferenceProgress result.state ∧
      result.state.InferenceReady ∧
      result.type.VariablesBelow result.state.inference.next := by
  exact SourceInference.Detail.inferUnaryOperator_inferenceProperties ready
    operandBelow expectedBelow success

/-- Binary operator inference preserves progress and readiness after operand
unification and returns an allocator-bounded type. -/
example {context : SourceInference.Context} {operator : Syntax.BinaryOp}
    {left right : TypeSystem.Ty} {expected : Option TypeSystem.Ty}
    {integerLiterals : List SourceInference.IntegerLiteralOrigin}
    {state : SourceInference.State}
    {result : SourceInference.Detail.OperatorInferenceResult}
    (ready : state.InferenceReady)
    (leftBelow : left.VariablesBelow state.inference.next)
    (rightBelow : right.VariablesBelow state.inference.next)
    (expectedBelow : ∀ expectedType ∈ expected,
      expectedType.VariablesBelow state.inference.next)
    (success : SourceInference.Detail.inferBinaryOperator context operator left
      right expected integerLiterals state = .ok result) :
    state.InferenceProgress result.state ∧
      result.state.InferenceReady ∧
      result.type.VariablesBelow result.state.inference.next := by
  exact SourceInference.Detail.inferBinaryOperator_inferenceProperties ready
    leftBelow rightBelow expectedBelow success

/-- Attaching delayed argument coercions preserves semantic inference progress
and readiness. -/
example (state : SourceInference.State)
    (entries : List SourceInference.Detail.ExpressionCoercions)
    (ready : state.InferenceReady) :
    state.InferenceProgress
        (SourceInference.Detail.attachExpressionCoercions state entries) ∧
      (SourceInference.Detail.attachExpressionCoercions state entries).InferenceReady := by
  exact SourceInference.Detail.attachExpressionCoercions_inferenceProperties
    state entries ready

/-- Recording a selected call result preserves inference properties and its
caller-supplied result-type bound. -/
example (source callee : Syntax.Expr) (name : String)
    (arguments : List SourceInference.InferredExpression)
    (attempt : SourceInference.Detail.CandidateAttemptResult)
    (result : SourceInference.InferredExpression)
    (trailingCoercions : List SourceInference.CoercionStep)
    (state : SourceInference.State)
    (ready : state.InferenceReady)
    (resultBelow : result.type.VariablesBelow state.inference.next) :
    state.InferenceProgress
        (SourceInference.Detail.recordSelectedCallResult source callee name
          arguments attempt result trailingCoercions state).2 ∧
      (SourceInference.Detail.recordSelectedCallResult source callee name
        arguments attempt result trailingCoercions state).2.InferenceReady ∧
      (SourceInference.Detail.recordSelectedCallResult source callee name
        arguments attempt result trailingCoercions state).1.type.VariablesBelow
        (SourceInference.Detail.recordSelectedCallResult source callee name
          arguments attempt result trailingCoercions state).2.inference.next := by
  exact
    SourceInference.Detail.recordSelectedCallResult_inferenceProperties source
      callee name arguments attempt result trailingCoercions state ready
      resultBelow

/-- The ordinary selected-call wrapper inherits progress, readiness, and the
returned result-type bound. -/
example (source callee : Syntax.Expr) (name : String)
    (arguments : List SourceInference.InferredExpression)
    (attempt : SourceInference.Detail.CandidateAttemptResult)
    (ready : attempt.state.InferenceReady)
    (resultBelow : attempt.result.type.VariablesBelow
      attempt.state.inference.next) :
    attempt.state.InferenceProgress
        (SourceInference.Detail.recordSelectedCall source callee name arguments
          attempt).2 ∧
      (SourceInference.Detail.recordSelectedCall source callee name arguments
        attempt).2.InferenceReady ∧
      (SourceInference.Detail.recordSelectedCall source callee name arguments
        attempt).1.type.VariablesBelow
        (SourceInference.Detail.recordSelectedCall source callee name arguments
          attempt).2.inference.next := by
  exact SourceInference.Detail.recordSelectedCall_inferenceProperties source
    callee name arguments attempt ready resultBelow

/-- Recording an expected expression extends the same inference guarantees
through source-node allocation without requiring a concrete evaluator case. -/
example {source : Syntax.Expr} {id : SourceInference.ExpressionId}
    {type : TypeSystem.Ty} {form : SourceInference.ExpressionForm}
    {requirements : List SourceInference.RequirementId}
    {expected : Option TypeSystem.Ty}
    {result : SourceInference.InferredExpression × SourceInference.State}
    (ready : solverRegressionState.InferenceReady)
    (typeBelow : type.VariablesBelow
      solverRegressionState.inference.next)
    (expectedBelow : ∀ expectedType ∈ expected,
      expectedType.VariablesBelow solverRegressionState.inference.next)
    (success : SourceInference.Detail.recordExpressionWithExpected
      solverRegressionContext source id type form requirements expected
      solverRegressionState = .ok result) :
    solverRegressionState.InferenceProgress result.2 ∧
      result.2.InferenceReady ∧
      result.1.type.VariablesBelow result.2.inference.next := by
  exact SourceInference.Detail.recordExpressionWithExpected_inferenceProperties
    ready typeBelow expectedBelow success

/-- Instantiating and recording a top-level function reference packages
allocator progress, readiness, and the returned expression-type bound. -/
example {context : SourceInference.Context} {source : Syntax.Expr}
    {id : SourceInference.ExpressionId} {name : String}
    {signature : ProgramFunctionSignature}
    {expected : Option TypeSystem.Ty} {state : SourceInference.State}
    {result : SourceInference.InferredExpression × SourceInference.State}
    (ready : state.InferenceReady)
    (schemeBodyBelow : signature.scheme.body.VariablesBelow
      state.inference.next)
    (expectedBelow : ∀ expectedType ∈ expected,
      expectedType.VariablesBelow state.inference.next)
    (success :
      (let instantiated :=
          signature.scheme.instantiate state.inference.next
       let inference := {
         state.inference with next := instantiated.next
       }
       let (requirements, state) :=
         ({ state with inference }).addRequirementsWithIds
           instantiated.predicates
       SourceInference.Detail.recordExpressionWithExpected context source id
         instantiated.body
         (.reference name (.declaration
           (SourceInference.DeclarationInstantiation.ofInstantiated
             signature instantiated)))
         requirements expected state) = .ok result) :
    state.InferenceProgress result.2 ∧
      result.2.InferenceReady ∧
      result.1.type.VariablesBelow result.2.inference.next := by
  exact
    SourceInference.Detail.recordInstantiatedFunctionReference_inferenceProperties
      ready schemeBodyBelow expectedBelow success

/-- Successful recursive expression inference packages semantic progress,
readiness, and an allocator bound for the inferred expression type. -/
example {fuel : Nat} {context : SourceInference.Context}
    {expression : Syntax.Expr} {expected : Option TypeSystem.Ty}
    {state : SourceInference.State}
    (ready : state.InferenceReady)
    (validated : ProgramSignatureFormationValidated context.signatures)
    (canonical : ∀ signature ∈ context.signatures.functions,
      signature.scheme.body = .function
        (TypeSystem.Ty.productMany signature.parameterTypes)
        (TypeSystem.Ty.productMany signature.returnTypes))
    (expectedBelow : ∀ expectedType ∈ expected,
      expectedType.VariablesBelow state.inference.next)
    {result : SourceInference.InferredExpression × SourceInference.State}
    (success : SourceInference.Detail.inferExprFuel fuel context expression
      expected state = .ok result) :
    state.InferenceProgress result.2 ∧
      result.2.InferenceReady ∧
      result.1.type.VariablesBelow result.2.inference.next := by
  exact SourceInference.Detail.inferExprFuel_inferenceProperties ready
    validated canonical expectedBelow success

/-- Successful recursive statement-list inference packages semantic progress,
readiness, and an allocator bound for the inferred block type. -/
example {fuel : Nat} {context : SourceInference.Context}
    {statements : List Syntax.Statement} {expectedReturn : TypeSystem.Ty}
    {state : SourceInference.State}
    (ready : state.InferenceReady)
    (validated : ProgramSignatureFormationValidated context.signatures)
    (canonical : ∀ signature ∈ context.signatures.functions,
      signature.scheme.body = .function
        (TypeSystem.Ty.productMany signature.parameterTypes)
        (TypeSystem.Ty.productMany signature.returnTypes))
    (returnBelow : expectedReturn.VariablesBelow state.inference.next)
    {result : SourceInference.Detail.BlockResult}
    (success : SourceInference.Detail.inferStatementsFuel fuel context
      statements expectedReturn state = .ok result) :
    state.InferenceProgress result.state ∧
      result.state.InferenceReady ∧
      result.type.VariablesBelow result.state.inference.next := by
  exact SourceInference.Detail.inferStatementsFuel_inferenceProperties ready
    validated canonical returnBelow success

/-- Successful function-body checking exposes the body-inference stage and
its semantic state invariants before return fitting and finalization. -/
example {environment : ProgramEnvironment}
    {signatures : ProgramSignatures}
    {signature : ProgramFunctionSignature} {fuel : Nat}
    {checked : SourceInference.CheckedFunction}
    (validated : ProgramSignatureFormationValidated signatures)
    (member : signature ∈ signatures.functions)
    (canonical : ∀ candidate ∈ signatures.functions,
      candidate.scheme.body = .function
        (TypeSystem.Ty.productMany candidate.parameterTypes)
        (TypeSystem.Ty.productMany candidate.returnTypes))
    (success : SourceInference.checkFunctionBody environment signatures
      signature fuel = .ok checked) :
    ∃ declaration body,
      environment.declaration? signature.id = some declaration ∧
        SourceInference.Detail.inferStatementsFuel fuel
            {
              environment
              signatures
              scope := .ofDeclaration declaration
              typeParameters := signature.scheme.parameters
              assumptions := signature.scheme.predicates
            }
            signature.source.value.body.value
            (TypeSystem.Ty.productMany signature.returnTypes)
            (SourceInference.State.initial declaration.id
              ((signature.parameterNames.zip signature.parameterTypes).map
                fun parameter =>
                  (parameter.1, TypeSystem.Scheme.mono parameter.2))
              signature.parameterComptime) = .ok body ∧
          (SourceInference.State.initial declaration.id
              ((signature.parameterNames.zip signature.parameterTypes).map
                fun parameter =>
                  (parameter.1, TypeSystem.Scheme.mono parameter.2))
              signature.parameterComptime).InferenceProgress body.state ∧
            body.state.InferenceReady ∧
              body.type.VariablesBelow body.state.inference.next := by
  exact SourceInference.checkFunctionBody_success_body_inferenceProperties
    validated member canonical success

/-- Successful checking of a formation-validated catalog exposes the scoped
requirement ledger in the exact declaration context used by body typing. -/
example {environment : ProgramEnvironment}
    {signatures : ProgramSignatures}
    {signature : ProgramFunctionSignature} {fuel : Nat}
    {checked : SourceInference.CheckedFunction}
    (validated : ProgramSignatureFormationValidated signatures)
    (member : signature ∈ signatures.functions)
    (success : SourceInference.checkFunctionBody environment signatures
      signature fuel = .ok checked) :
    Solcore.SourceSemantics.ScopedRequirementLedgerWellFormed
      (Solcore.SourceSemantics.checkedBodyContext signatures signature checked)
      checked.typedBody := by
  exact
    Solcore.SourceSemantics.SourceInferenceSoundness.checkFunctionBody_success_scopedRequirementLedgerWellFormed_bodyContext
      validated member success

/-- The deep-typing entry bridge returns one lexical context carrying both
the declarative input extension and its finalized executable alignment. -/
example {environment : ProgramEnvironment}
    {signatures : ProgramSignatures}
    {signature : ProgramFunctionSignature} {fuel : Nat}
    {checked : SourceInference.CheckedFunction}
    (parameterTypes : Solcore.SourceSemantics.TypesWellFormed
      (Solcore.SourceSemantics.checkedBodyContext signatures signature checked)
      signature.parameterTypes)
    (success : SourceInference.checkFunctionBody environment signatures
      signature fuel = .ok checked) :
    ∃ lexicalContext,
      Solcore.SourceSemantics.MonoBindersExtend signature.id
          (Solcore.SourceSemantics.checkedBodyContext signatures signature
            checked)
          checked.typedBody.inputs signature.parameterTypes lexicalContext ∧
        Solcore.SourceSemantics.SourceInferenceSoundness.LocalEnvironmentAligned
          (SourceInference.State.initial signature.id
            ((signature.parameterNames.zip signature.parameterTypes).map
              fun parameter =>
                (parameter.1, TypeSystem.Scheme.mono parameter.2))
            signature.parameterComptime)
          checked.substitution lexicalContext := by
  exact
    Solcore.SourceSemantics.SourceInferenceSoundness.checkFunctionBody_success_initialLocalEnvironmentAligned
      parameterTypes success

private def solverRegressionRequirement : SourceInference.Requirement := {
  id := ⟨0⟩
  predicate := solverRegressionSource
}

private def solverRegressionExpressionId : SourceInference.ExpressionId :=
  ⟨⟨solverRegressionOwner, 0⟩⟩

private def solverRegressionRequirementNode :
    SourceInference.ExpressionNode := {
  id := solverRegressionExpressionId
  span := solverRegressionSpan
  type := .word
  form := .literal (.decimal "0")
  requirements := [solverRegressionRequirement.id]
}

private def solverRegressionRoots : List SourceInference.NodeId :=
  [.expression solverRegressionExpressionId]

private def solverRegressionSemanticContext :
    Solcore.SourceSemantics.Context :=
  (Solcore.SourceSemantics.Context.ofSignatures
    solverRegressionContext.signatures).withAssumptions
      [solverRegressionNormalized]

private def solverRegressionTemplateState : SourceInference.State := {
  solverRegressionState with
  localSchemeAssumptions := [solverRegressionRequirement.id]
}

private def solverRegressionFinalizeState : SourceInference.State := {
  solverRegressionState with
  nextOccurrence := 1
  nodes := [.expression solverRegressionRequirementNode]
  requirements := [solverRegressionRequirement]
}

private def generalizationSideConditionState : SourceInference.State := {
  SourceInference.State.initial solverRegressionOwner with
  nextRequirement := 1
  requirements := [solverRegressionRequirement]
  directCallRequirements := [solverRegressionRequirement.id]
}

private theorem generalizationSideConditionState_requirementsWellFormed :
    generalizationSideConditionState.RequirementsWellFormed := by
  rfl

private def forgedLocalSchemeRequirement :
    SourceInference.LocalSchemeRequirement := {
  templateRequirement := solverRegressionRequirement.id
  predicate := solverRegressionNormalized
}

private def forgedQualifiedBinder : SourceInference.TypedBinder := {
  id := { owner := solverRegressionOwner, binderIndex := 0 }
  name := "forged"
  scheme := .mono .word
  schemeRequirements := [forgedLocalSchemeRequirement]
}

private def forgedOuterBinder : SourceInference.TypedBinder := {
  id := { owner := solverRegressionOwner, binderIndex := 1 }
  name := "forged"
  scheme := .mono .bool
}

/-- A state assembled outside the canonical allocation API may omit the
selected inner binder's template classification even when an outer binder with
the same name is otherwise valid. -/
private def forgedUntrackedBinderState : SourceInference.State := {
  SourceInference.State.initial solverRegressionOwner with
  localBinders := [forgedQualifiedBinder, forgedOuterBinder]
  nextLocal := 2
}

/-- Guarded lookup rejects the malformed first match instead of exposing it or
silently skipping to the valid outer binder. -/
example :
    forgedUntrackedBinderState.lookupBinder? "forged" = none := by
  rfl

private def guardedBinderAllocation :=
  (SourceInference.State.initial solverRegressionOwner).allocateBinder
    "guarded" (.mono .word) none false [forgedLocalSchemeRequirement]

/-- Canonical binder allocation classifies its templates, so the lookup guard
is observationally transparent for well-formed states. -/
example :
    guardedBinderAllocation.2.lookupBinder? "guarded" =
      some guardedBinderAllocation.1 := by
  rfl

/-- Batch allocation produces consecutive, distinct identities which remain
fresh for the complete input ledger even when predicate payloads repeat. -/
example :
    let allocation := generalizationSideConditionState.addRequirementsWithIds
      [solverRegressionNormalized, solverRegressionNormalized]
    allocation.1 = [(⟨1⟩ : SourceInference.RequirementId), ⟨2⟩] ∧
      allocation.1.Nodup ∧
      ∀ id, id ∈ allocation.1 →
        id ∉ generalizationSideConditionState.requirements.map
          (fun requirement => requirement.id) := by
  dsimp only
  refine ⟨rfl, ?_, ?_⟩
  · exact SourceInference.State.addRequirementsWithIds_ids_nodup
      generalizationSideConditionState
      [solverRegressionNormalized, solverRegressionNormalized]
  · exact SourceInference.State.addRequirementsWithIds_ids_fresh
      generalizationSideConditionState
      [solverRegressionNormalized, solverRegressionNormalized]
      generalizationSideConditionState_requirementsWellFormed

private def ledgerExtensionRequirement : SourceInference.Requirement := {
  id := ⟨1⟩
  predicate := solverRegressionNormalized
}

private def generalizationSideConditionExtendedState :
    SourceInference.State := {
  generalizationSideConditionState with
  nextRequirement := 2
  requirements := [solverRegressionRequirement, ledgerExtensionRequirement]
}

private theorem
    generalizationSideConditionExtendedState_requirementsWellFormed :
    generalizationSideConditionExtendedState.RequirementsWellFormed := by
  rfl

private theorem generalizationSideCondition_requirements_subset_extended :
    generalizationSideConditionState.requirements ⊆
      generalizationSideConditionExtendedState.requirements := by
  intro requirement member
  change requirement ∈ [solverRegressionRequirement] at member
  change requirement ∈
    [solverRegressionRequirement, ledgerExtensionRequirement]
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at member ⊢
  exact Or.inl member

/-- A canonical ledger extension preserves the exact predicate payload of a
row allocated before the prior fresh-identity boundary. -/
example :
    solverRegressionRequirement ∈
        generalizationSideConditionExtendedState.requirements.take
          generalizationSideConditionState.nextRequirement ↔
      solverRegressionRequirement ∈
        generalizationSideConditionState.requirements := by
  exact SourceInference.State.mem_take_prior_requirements_iff
    generalizationSideConditionState
    generalizationSideConditionExtendedState
    generalizationSideConditionState_requirementsWellFormed
    generalizationSideConditionExtendedState_requirementsWellFormed
    generalizationSideCondition_requirements_subset_extended
    solverRegressionRequirement

/-- Canonical ledger formation synchronizes its length and bounds every
retained stable identity by the next fresh identity. -/
example :
    generalizationSideConditionState.requirements.length =
        generalizationSideConditionState.nextRequirement ∧
      solverRegressionRequirement.id.index <
        generalizationSideConditionState.nextRequirement := by
  have member : solverRegressionRequirement ∈
      generalizationSideConditionState.requirements := by
    simp [generalizationSideConditionState]
  exact ⟨
    SourceInference.State.requirements_length_eq_nextRequirement
      generalizationSideConditionState
      generalizationSideConditionState_requirementsWellFormed,
    SourceInference.State.requirement_id_lt_nextRequirement
      generalizationSideConditionState
      generalizationSideConditionState_requirementsWellFormed member⟩

/-- Canonical identity order makes take/drop cutoffs coincide exactly with
the numerical boundary on stable requirement identities. -/
example :
    solverRegressionRequirement ∈
        generalizationSideConditionState.requirements.take 1 ∧
      solverRegressionRequirement ∉
        generalizationSideConditionState.requirements.take 0 ∧
      solverRegressionRequirement ∈
        generalizationSideConditionState.requirements.drop 0 ∧
      solverRegressionRequirement ∉
        generalizationSideConditionState.requirements.drop 1 := by
  constructor
  · rw [SourceInference.State.mem_take_requirements_iff
      generalizationSideConditionState
      generalizationSideConditionState_requirementsWellFormed]
    simp [generalizationSideConditionState, solverRegressionRequirement]
  constructor
  · rw [SourceInference.State.mem_take_requirements_iff
      generalizationSideConditionState
      generalizationSideConditionState_requirementsWellFormed]
    simp [solverRegressionRequirement]
  constructor
  · rw [SourceInference.State.mem_drop_requirements_iff
      generalizationSideConditionState
      generalizationSideConditionState_requirementsWellFormed]
    simp [generalizationSideConditionState, solverRegressionRequirement]
  · rw [SourceInference.State.mem_drop_requirements_iff
      generalizationSideConditionState
      generalizationSideConditionState_requirementsWellFormed]
    simp [solverRegressionRequirement]

private def stableGeneralizationVariable : TypeSystem.TypeVarId := ⟨0⟩

private def stableGeneralizationState : SourceInference.State :=
  SourceInference.State.initial solverRegressionOwner [
    ("captured", .mono (.variable stableGeneralizationVariable))
  ]

/-- The executable blocker characterization exposes the exact lexical scheme
that prevents a captured variable from being generalized. -/
example : stableGeneralizationVariable ∈
    SourceInference.Detail.generalizeValueBlockedVariables
      stableGeneralizationState
      [("captured", .mono (.variable stableGeneralizationVariable))] 0 := by
  rw [SourceInference.Detail.mem_generalizeValueBlockedVariables_iff]
  left
  refine ⟨("captured", .mono (.variable stableGeneralizationVariable)),
    by simp, ?_⟩
  simp [TypeSystem.Scheme.mono, TypeSystem.Scheme.freeVariables,
    TypeSystem.Ty.freeVariables]

/-- A requirement predating the initializer contributes an exact blocker
witness even when its identity is otherwise classified as a direct call. -/
example :
    solverRegressionRequirement ∈
        SourceInference.Detail.generalizeValueBlockingRequirements
          generalizationSideConditionState 1 ∧
      solverRegressionRequirement ∉
        SourceInference.Detail.generalizeValueBlockingRequirements
          generalizationSideConditionState 0 := by
  constructor
  · rw [SourceInference.Detail.mem_generalizeValueBlockingRequirements_iff]
    exact Or.inl (by simp [generalizationSideConditionState])
  · rw [SourceInference.Detail.mem_generalizeValueBlockingRequirements_iff]
    simp [generalizationSideConditionState]

/-- A requirement-witness blocker exposes the variable carried by its
normalized predicate. -/
example : solverRegressionFirst ∈
    SourceInference.Detail.generalizeValueBlockedVariables
      generalizationSideConditionState [] 1 := by
  rw [SourceInference.Detail.mem_generalizeValueBlockedVariables_iff]
  right
  refine ⟨solverRegressionRequirement, ?_, ?_⟩
  · rw [SourceInference.Detail.mem_generalizeValueBlockingRequirements_iff]
    exact Or.inl (by simp [generalizationSideConditionState])
  · change solverRegressionFirst ∈
      (TypeSystem.Substitution.apply []
        (.variable solverRegressionFirst)).freeVariables
    rw [show ([] : TypeSystem.Substitution) =
      TypeSystem.Substitution.empty by rfl]
    rw [TypeSystem.Substitution.empty_apply]
    simp [TypeSystem.Ty.freeVariables]

/-- Exact quantified-variable projection excludes the requirement-blocked
variable and retains the other free variable in stable type order. -/
example :
    (SourceInference.Detail.generalizeValue generalizationSideConditionState []
      1 (.product (.variable solverRegressionFirst)
        (.variable solverRegressionSecond))).scheme.quantified =
      [solverRegressionSecond] := by
  decide

/-- Generalization derives its lexical barrier from stable binders.  Replacing
the legacy environment cache with a stale closed scheme therefore cannot make
the captured variable polymorphic; using that stale cache directly would. -/
example :
    let stale : SourceInference.State := {
      stableGeneralizationState with locals := [("captured", .mono .word)]
    }
    (SourceInference.Detail.generalizeValue stale
      (stale.binderEnvironment.apply stale.inference.substitution) 0
      (.variable stableGeneralizationVariable)).scheme.quantified = [] ∧
    (SourceInference.Detail.generalizeValue stale
      (stale.locals.apply stale.inference.substitution) 0
      (.variable stableGeneralizationVariable)).scheme.quantified =
        [stableGeneralizationVariable] := by
  decide

private theorem generalizationSideConditionIds :
    (SourceInference.Detail.generalizeValue generalizationSideConditionState []
      0 (.variable solverRegressionFirst)).requirements.map
        (fun requirement => requirement.templateRequirement) =
      [solverRegressionRequirement.id] := by
  rfl

/-- The generalization projections supply exactly the uniqueness, coverage,
and freshness side conditions needed by template-tracking allocation. -/
example :
    ((SourceInference.Detail.generalizeValue generalizationSideConditionState []
      0 (.variable solverRegressionFirst)).requirements.map
        (fun requirement => requirement.templateRequirement)).Nodup ∧
    ((SourceInference.Detail.generalizeValue generalizationSideConditionState []
      0 (.variable solverRegressionFirst)).requirements.map
        (fun requirement => requirement.templateRequirement)).Sublist
      (generalizationSideConditionState.requirements.map
        (fun requirement => requirement.id)) ∧
    solverRegressionRequirement.id ∉
      generalizationSideConditionState.localSchemeAssumptions := by
  have ledgerUnique := SourceInference.State.requirementIds_nodup
    generalizationSideConditionState (by rfl)
  have covered := SourceInference.Detail.generalizeValue_templateIds_sublist
    generalizationSideConditionState [] 0 (.variable solverRegressionFirst)
  have fresh := SourceInference.Detail.generalizeValue_templateIds_fresh
    generalizationSideConditionState [] 0 (.variable solverRegressionFirst)
      solverRegressionRequirement.id (by
        rw [generalizationSideConditionIds]
        simp)
  exact ⟨covered.nodup ledgerUnique, covered, fresh⟩

/-- Canonical generalization exposes the exact scheme and predicate facts
needed by declarative generalized-let formation. -/
example :
    (SourceInference.Detail.generalizeValue generalizationSideConditionState []
      0 (.variable solverRegressionFirst)).scheme.body =
        .variable solverRegressionFirst ∧
    (SourceInference.Detail.generalizeValue generalizationSideConditionState []
      0 (.variable solverRegressionFirst)).scheme.quantified.Nodup ∧
    ∃ requirement,
      requirement ∈
        (SourceInference.Detail.generalizeValue
          generalizationSideConditionState [] 0
            (.variable solverRegressionFirst)).requirements ∧
      (∃ metavariable,
        metavariable ∈
          (SourceInference.Detail.generalizeValue
            generalizationSideConditionState [] 0
              (.variable solverRegressionFirst)).scheme.quantified ∧
        metavariable ∈ TypedTraitResolution.predicateVariables
          requirement.predicate) ∧
      ∃ rawRequirement,
        rawRequirement ∈ generalizationSideConditionState.requirements ∧
        rawRequirement.id = requirement.templateRequirement ∧
        requirement.predicate =
          SourceInference.Detail.applyPredicate generalizationSideConditionState
            rawRequirement.predicate := by
  have idMember : solverRegressionRequirement.id ∈
      (SourceInference.Detail.generalizeValue generalizationSideConditionState []
        0 (.variable solverRegressionFirst)).requirements.map
          (fun requirement => requirement.templateRequirement) := by
    rw [generalizationSideConditionIds]
    simp
  rcases List.mem_map.mp idMember with
    ⟨requirement, requirementMember, _⟩
  refine ⟨SourceInference.Detail.generalizeValue_scheme_body _ _ _ _,
    SourceInference.Detail.generalizeValue_scheme_quantified_nodup _ _ _ _,
    requirement, requirementMember, ?_, ?_⟩
  · exact
      SourceInference.Detail.generalizeValue_requirement_depends_on_quantified
        generalizationSideConditionState [] 0 (.variable solverRegressionFirst)
        requirement requirementMember
  · exact SourceInference.Detail.generalizeValue_requirement_source
      generalizationSideConditionState [] 0 (.variable solverRegressionFirst)
      requirement requirementMember

/-- A result with no quantified variables cannot retain qualified scheme
requirements. -/
example :
    (SourceInference.Detail.generalizeValue generalizationSideConditionState []
      0 .word).requirements = [] := by
  apply SourceInference.Detail.generalizeValue_requirements_empty_of_quantified_eq_nil
  rfl

private def solverRegressionSolvedRow : SourceInference.SolvedRequirement := {
  id := solverRegressionRequirement.id
  predicate := solverRegressionNormalized
  evidence := .assumption solverRegressionNormalized
}

private def solverRegressionFinalizedResult : SourceInference.Result := {
  type := .word
  substitution := solverRegressionFinalizeState.inference.substitution
  solvedRequirements := [solverRegressionSolvedRow]
  typedSource :=
    (solverRegressionFinalizeState.toTypedSource
      solverRegressionRoots).applySubstitution
      solverRegressionFinalizeState.inference.substitution
}

/-- This equation fails if the already-normalized head is passed through
`solvePredicate` and receives the inference substitution a second time. -/
example : SourceInference.Detail.solvePredicates solverRegressionContext
    solverRegressionState [solverRegressionSource] =
    .ok ([solverRegressionNormalized],
      [.assumption solverRegressionNormalized]) := by
  rfl

example : Solcore.SourceSemantics.RetainedEvidenceValid
    [solverRegressionNormalized]
    solverRegressionContext.signatures.resolutionRules
    solverRegressionNormalized
    (.assumption solverRegressionNormalized) := by
  exact
    Solcore.SourceSemantics.SourceInferenceSoundness.solvePredicate_sound
      (context := solverRegressionContext)
      (state := solverRegressionState)
      (source := solverRegressionSource)
      (by rfl)

example : Solcore.SourceSemantics.RetainedEvidenceValid
    [solverRegressionNormalized]
    solverRegressionContext.signatures.resolutionRules
    (ProgramSignatures.builtinIntPredicate .word)
    (.implementation (.byImpl
      (ProgramSignatures.builtinIntPredicate .word)
      (.builtin .intWord) [])) := by
  exact
    Solcore.SourceSemantics.SourceInferenceSoundness.solveNormalizedPredicate_sound
      (context := solverRegressionContext)
      (state := solverRegressionState)
      (goal := ProgramSignatures.builtinIntPredicate .word)
      (by rfl)

example : Solcore.SourceSemantics.SolvedRequirementValid
    solverRegressionSemanticContext {
      id := solverRegressionRequirement.id
      predicate := solverRegressionNormalized
      evidence := .assumption solverRegressionNormalized
    } := by
  exact
    Solcore.SourceSemantics.SourceInferenceSoundness.solveRequirementEvidence_ordinary_sound
        (inferenceContext := solverRegressionContext)
        (state := solverRegressionState)
        (requirement := solverRegressionRequirement)
        (retained := .assumption solverRegressionNormalized)
        (semanticContext := solverRegressionSemanticContext)
        (by
          change solverRegressionRequirement.id ∉ []
          simp) rfl rfl (by rfl)

example {retained : SourceInference.PredicateEvidence}
    (success : SourceInference.Detail.solveRequirementEvidence
      solverRegressionContext solverRegressionTemplateState
      solverRegressionRequirement = .ok retained) :
    retained = .assumption solverRegressionNormalized := by
  exact
    Solcore.SourceSemantics.SourceInferenceSoundness.solveRequirementEvidence_template_eq
        (context := solverRegressionContext)
        (state := solverRegressionTemplateState)
        (requirement := solverRegressionRequirement)
        (by simp [solverRegressionTemplateState]) success

/-- Whole-ledger solving preserves the ordinary row and validates it after
normalizing the declaration assumptions exactly once. -/
example : Solcore.SourceSemantics.SolvedRequirementsValid
    solverRegressionSemanticContext [{
      id := solverRegressionRequirement.id
      predicate := solverRegressionNormalized
      evidence := .assumption solverRegressionNormalized
    }] := by
  apply
    Solcore.SourceSemantics.SourceInferenceSoundness.solveRequirements_ordinary_sound
      (inferenceContext := solverRegressionContext)
      (state := solverRegressionState)
      (requirements := [solverRegressionRequirement])
  · intro requirement member
    have requirement_eq : requirement = solverRegressionRequirement := by
      simpa using member
    subst requirement
    change solverRegressionRequirement.id ∉ []
    simp
  · rfl
  · rfl
  · rfl

/-- Finalizing a nonempty ordinary ledger exposes a declarative context in
which every emitted solved row has valid retained evidence. -/
example : Solcore.SourceSemantics.SolvedRequirementsValid
    (Solcore.SourceSemantics.SourceInferenceSoundness.finalizedRequirementContext
      solverRegressionContext solverRegressionFinalizedResult)
    solverRegressionFinalizedResult.solvedRequirements := by
  apply
    Solcore.SourceSemantics.SourceInferenceSoundness.finalize_solvedRequirementsValid
      (inferenceContext := solverRegressionContext)
      (type := .word)
      (state := solverRegressionFinalizeState)
      (roots := solverRegressionRoots)
  · rfl
  · rfl

private def integerLiteralRows
    (function : SourceInference.CheckedFunction) :
    List (SourceInference.ExpressionNode ×
      SourceInference.IntegerLiteralResolution) :=
  function.typedBody.nodes.filterMap fun
    | .expression node =>
        match node.form with
        | .integerLiteral _ resolution => some (node, resolution)
        | _ => none
    | .statement _ => none

private def hasExactDefaultedWordEvidence
    (function : SourceInference.CheckedFunction)
    (row : SourceInference.ExpressionNode ×
      SourceInference.IntegerLiteralResolution) : Bool :=
  let node := row.1
  let resolution := row.2
  node.type == TypeSystem.Ty.word &&
    resolution.targetType == TypeSystem.Ty.word &&
    node.requirements == [resolution.requirement] &&
    node.coercions.isEmpty &&
    function.solvedRequirements.any fun solved =>
      solved.id == resolution.requirement && hasBuiltinIntWordEvidence solved

private def testLambdaLetTupleConditional : IO Unit := do
  let checked ← check (String.intercalate "\n" [
    "function polymorphic(flag: Bool) returns (Word, Bool) {",
    "  let id = lam(value) { return value; };",
    "  return (id(((1))), id(flag ? flag : !flag));",
    "}",
    "function expected(flag: Bool) returns (function(Word) returns (Word)) {",
    "  return lam(value) { return flag ? value + 1 : value; };",
    "}",
    "function empty() { return (); }"
  ])
  assertTrue (decide (checked.length = 3))
    "lambda/let/tuple fixture lost a checked function"
  match checked with
  | first :: second :: third :: [] =>
      assertTrue (decide (first.inferredBodyType =
          TypeSystem.Ty.product .word .bool))
        "let-polymorphic tuple did not infer Word × Bool"
      let idBinders := first.typedBody.nodes.filterMap fun
        | .statement { form := .letDecl binder (some _), .. } =>
            if binder.name == "id" then some binder else none
        | _ => none
      match idBinders with
      | [binder] =>
          let schemeShape := match binder.scheme.quantified,
              binder.scheme.body with
            | [quantified], .function (.variable parameter) (.variable result) =>
                quantified == parameter && parameter == result
            | _, _ => false
          assertTrue schemeShape
            "local id did not retain its generalized α → α scheme"
          let referenceTypes := first.typedBody.nodes.filterMap fun
            | .expression node => match node.form with
                | .reference _ (.local candidate) =>
                    if candidate == binder.id then some node.rawType else none
                | _ => none
            | .statement _ => none
          assertTrue (referenceTypes.length == 2 &&
              referenceTypes.any (· == .function .word .word) &&
              referenceTypes.any (· == .function .bool .bool))
            "local id was not independently instantiated at Word and Bool"
      | _ => throw (IO.userError
          "let-polymorphic fixture did not retain exactly one local id binder")
      assertTrue (decide (second.inferredBodyType =
          TypeSystem.Ty.function .word .word))
        "expected function type did not guide an inferred lambda"
      assertTrue (decide (third.inferredBodyType = .unit))
        "empty tuple did not check as Unit"
  | _ => throw (IO.userError "checked function order changed")

/-- A discarded use of a polymorphic local has no expected type.  The
frontend therefore retains a fresh occurrence metavariable after independently
generalizing the binder; the declarative source semantics must admit it as a
body-wide residual variable. -/
private def testDiscardedPolymorphicReferenceResidual : IO Unit := do
  let checked ← check (String.intercalate "\n" [
    "function discard() {",
    "  let id = lam(value) { return value; };",
    "  id;",
    "  return ();",
    "}"
  ])
  let function ← match checked with
    | [function] => pure function
    | functions => throw (IO.userError
        s!"discarded polymorphic fixture produced {functions.length} functions")
  let binders := function.typedBody.nodes.filterMap fun
    | .statement { form := .letDecl binder (some _), .. } =>
        if binder.name == "id" then some binder else none
    | _ => none
  let binder ← match binders with
    | [binder] => pure binder
    | _ => throw (IO.userError
        "discarded polymorphic fixture lost its unique id binder")
  let referenceTypes := function.typedBody.nodes.filterMap fun
    | .expression node => match node.form with
        | .reference _ (.local candidate) =>
            if candidate == binder.id then some node.rawType else none
        | _ => none
    | .statement _ => none
  let retainedResidual := match binder.scheme.quantified, referenceTypes with
    | [quantified], [.function (.variable parameter) (.variable result)] =>
        parameter == result && parameter != quantified
    | _, _ => false
  assertTrue retainedResidual
    "discarded polymorphic reference did not retain an independent residual type"

private def testAmbiguousOverload : IO Unit := do
  let source := String.intercalate "\n" [
    "function choose(value: Word) returns (Word) { return value; }",
    "function choose(other: Word) returns (Word) { return other + 1; }",
    "function run() returns (Word) { return choose(1); }"
  ]
  match SourceInference.loadAndCheckProgram (workspace source) with
  | .error errors =>
      assertTrue (errors.any fun error => match error with
        | .body { error := .ambiguousOverload "choose" candidates, .. } =>
            candidates.length == 2
        | _ => false) "ambiguous overload was not reported explicitly"
  | .ok _ => throw (IO.userError "ambiguous overload was selected")

private def testIntegerLiteralExpectedType : IO Unit := do
  let source := "function bad() returns (Bool) { return 1; }"
  match SourceInference.loadAndCheckProgram (workspace source) with
  | .error errors =>
      assertTrue (errors.any fun error => match error with
        | .body { error := .unsupportedIntegerLiteralTarget _ type, .. } =>
            type == TypeSystem.Ty.bool
        | _ => false) "an integer literal silently checked as Bool"
  | .ok _ => throw (IO.userError "an integer literal checked as Bool")

private def testClosedUnsupportedIntegerLiteralTarget : IO Unit := do
  let metavariable : TypeSystem.TypeVarId := ⟨0⟩
  let expression : SourceInference.ExpressionId :=
    ⟨⟨solverRegressionOwner, 0⟩⟩
  let origin : SourceInference.IntegerLiteralOrigin := {
    metavariable
    expression
    requirement := ⟨0⟩
  }
  let initial := SourceInference.State.initial solverRegressionOwner
  let state : SourceInference.State := {
    initial with
    inference := {
      next := 1
      substitution := [(metavariable, .bool)]
    }
  }
  match SourceInference.Detail.validateIntegerLiteralTarget origin state with
  | .error (.unsupportedIntegerLiteralTarget rejected type) =>
      assertTrue (rejected == expression && type == TypeSystem.Ty.bool)
        "unsupported closed integer-literal target lost its exact diagnostic"
  | .error error => throw (IO.userError
      s!"unsupported closed integer-literal target produced {reprStr error}")
  | .ok _ => throw (IO.userError
      "unsupported closed integer-literal target passed final validation")

private def literalLedgerMetavariable : TypeSystem.TypeVarId := ⟨0⟩

private def literalLedgerExpression : SourceInference.ExpressionId :=
  ⟨⟨solverRegressionOwner, 0⟩⟩

private def literalLedgerRequirement : SourceInference.RequirementId := ⟨0⟩

private def literalLedgerResolution :
    SourceInference.IntegerLiteralResolution := {
  rawValue := 7
  targetType := .variable literalLedgerMetavariable
  requirement := literalLedgerRequirement
}

private def literalLedgerNode : SourceInference.ExpressionNode := {
  id := literalLedgerExpression
  span := solverRegressionSpan
  type := .variable literalLedgerMetavariable
  form := .integerLiteral (.decimal "7") literalLedgerResolution
  requirements := [literalLedgerRequirement]
}

private def literalLedgerState : SourceInference.State := {
  SourceInference.State.initial solverRegressionOwner with
  inference := { next := 1 }
  nextOccurrence := 1
  nodes := [.expression literalLedgerNode]
  integerLiterals := [{
    metavariable := literalLedgerMetavariable
    expression := literalLedgerExpression
    requirement := literalLedgerRequirement
  }]
  nextRequirement := 1
  requirements := [{
    id := literalLedgerRequirement
    predicate := literalLedgerResolution.predicate
  }]
}

private def testIntegerLiteralLedgerValidation : IO Unit := do
  match SourceInference.Detail.validateIntegerLiteralLedger literalLedgerState with
  | .ok () => pure ()
  | .error error => throw (IO.userError
      s!"a consistent integer-literal ledger produced {reprStr error}")

  let missingOrigin := { literalLedgerState with integerLiterals := [] }
  match SourceInference.Detail.validateIntegerLiteralLedger missingOrigin with
  | .error (.missingIntegerLiteralRequirement expression requirement) =>
      assertTrue (expression == literalLedgerExpression &&
          requirement == literalLedgerRequirement)
        "missing integer-literal origin lost its exact diagnostic"
  | .error error => throw (IO.userError
      s!"missing integer-literal origin produced {reprStr error}")
  | .ok () => throw (IO.userError
      "an integer-literal node without origin metadata passed validation")

  let missingRequirement := { literalLedgerState with requirements := [] }
  match SourceInference.Detail.validateIntegerLiteralLedger missingRequirement with
  | .error (.missingIntegerLiteralRequirement expression requirement) =>
      assertTrue (expression == literalLedgerExpression &&
          requirement == literalLedgerRequirement)
        "missing integer-literal requirement row lost its exact diagnostic"
  | .error error => throw (IO.userError
      s!"missing integer-literal requirement row produced {reprStr error}")
  | .ok () => throw (IO.userError
      "an integer-literal node without its requirement row passed validation")

  let wrongPredicate := ProgramSignatures.builtinIntPredicate .bool
  let mismatchedPredicate := {
    literalLedgerState with
    requirements := [{
      id := literalLedgerRequirement
      predicate := wrongPredicate
    }]
  }
  match SourceInference.Detail.validateIntegerLiteralLedger mismatchedPredicate with
  | .error (.integerLiteralRequirementPredicateMismatch expression requirement
      expected actual) =>
      assertTrue (expression == literalLedgerExpression &&
          requirement == literalLedgerRequirement &&
          expected == literalLedgerResolution.predicate &&
          actual == wrongPredicate)
        "mismatched integer-literal predicate lost its exact diagnostic"
  | .error error => throw (IO.userError
      s!"mismatched integer-literal predicate produced {reprStr error}")
  | .ok () => throw (IO.userError
      "an integer-literal node with a mismatched predicate passed validation")

  let inconsistentResolution : SourceInference.IntegerLiteralResolution := {
    literalLedgerResolution with rawValue := 8
  }
  let inconsistentNode : SourceInference.ExpressionNode := {
    literalLedgerNode with
    form := .integerLiteral (.decimal "7") inconsistentResolution
  }
  let inconsistentValue := {
    literalLedgerState with nodes := [.expression inconsistentNode]
  }
  match SourceInference.Detail.validateIntegerLiteralLedger inconsistentValue with
  | .error (.unsupportedLiteral kind) =>
      assertTrue (kind == "inconsistent integer literal metadata")
        "inconsistent integer-literal value lost its exact diagnostic"
  | .error error => throw (IO.userError
      s!"inconsistent integer-literal value produced {reprStr error}")
  | .ok () => throw (IO.userError
      "an integer-literal node with an inconsistent value passed validation")

private def graphValidationOccurrence (index : Nat) :
    SourceInference.OccurrenceId :=
  ⟨solverRegressionOwner, index⟩

private def graphValidationExpression (index : Nat) :
    SourceInference.ExpressionId :=
  ⟨graphValidationOccurrence index⟩

private def graphValidationStatement (index : Nat) :
    SourceInference.StatementId :=
  ⟨graphValidationOccurrence index⟩

private def graphValidationExpressionNode (index : Nat)
    (form : SourceInference.ExpressionForm) :
    SourceInference.ExpressionNode := {
  id := graphValidationExpression index
  span := solverRegressionSpan
  type := .word
  form
}

private def graphValidationStatementNode (index : Nat)
    (form : SourceInference.StatementForm) :
    SourceInference.StatementNode := {
  id := graphValidationStatement index
  span := solverRegressionSpan
  type := .word
  form
}

private def validSourceGraph : SourceInference.TypedSource := {
  owner := solverRegressionOwner
  inputs := []
  roots := [.expression (graphValidationExpression 1)]
  nodes := [
    .expression (graphValidationExpressionNode 0 (.literal (.decimal "0"))),
    .expression (graphValidationExpressionNode 1
      (.group (graphValidationExpression 0)))
  ]
}

/-- Require the forest validator to retain the exact repeated incoming ID. -/
private def expectDuplicateIncomingNode (label : String)
    (source : SourceInference.TypedSource)
    (expected : SourceInference.NodeId) : IO Unit := do
  match SourceInference.Detail.validateSourceGraph source with
  | .error (.duplicateIncomingNode id) =>
      assertTrue (id == expected)
        s!"{label} lost its exact duplicate-incoming diagnostic"
  | .error error => throw (IO.userError
      s!"{label} produced {reprStr error}")
  | .ok () => throw (IO.userError
      s!"{label} passed graph validation")

/-- Require root-driven coverage to identify the first unreachable table ID. -/
private def expectUnreachableNode (label : String)
    (source : SourceInference.TypedSource)
    (expected : SourceInference.NodeId) : IO Unit := do
  match SourceInference.Detail.validateSourceGraph source with
  | .error (.unreachableNode id) =>
      assertTrue (id == expected)
        s!"{label} lost its exact unreachable-node diagnostic"
  | .error error => throw (IO.userError
      s!"{label} produced {reprStr error}")
  | .ok () => throw (IO.userError
      s!"{label} passed graph validation")

/-- The finalization boundary rejects malformed occurrence graphs before
exposing them to semantic consumers.  Node-table duplicate detection erases
category, while lookup and forest validation preserve it. -/
private def testSourceGraphValidation : IO Unit := do
  match SourceInference.Detail.validateSourceGraph validSourceGraph with
  | .ok () => pure ()
  | .error error => throw (IO.userError
      s!"a valid typed-source graph produced {reprStr error}")

  let foreignOwner : Resolved.DeclarationId :=
    { solverRegressionOwner with declarationIndex := 1 }
  let foreignOccurrence : SourceInference.OccurrenceId := ⟨foreignOwner, 0⟩
  let foreignExpression : SourceInference.ExpressionId := ⟨foreignOccurrence⟩
  let foreignNode : SourceInference.ExpressionNode := {
    graphValidationExpressionNode 0 (.literal (.decimal "0")) with
    id := foreignExpression
  }
  let ownerMismatch := {
    validSourceGraph with
    roots := []
    nodes := [.expression foreignNode]
  }
  match SourceInference.Detail.validateSourceGraph ownerMismatch with
  | .error (.nodeOwnerMismatch expected actual) =>
      assertTrue (expected == solverRegressionOwner &&
          actual == foreignOccurrence)
        "node-owner mismatch lost its exact diagnostic"
  | .error error => throw (IO.userError
      s!"node-owner mismatch produced {reprStr error}")
  | .ok () => throw (IO.userError
      "a foreign-owner source node passed graph validation")

  let duplicateOccurrence := graphValidationOccurrence 0
  let crossCategoryDuplicate := {
    validSourceGraph with
    roots := []
    nodes := [
      .expression (graphValidationExpressionNode 0 (.literal (.decimal "0"))),
      .statement (graphValidationStatementNode 0 .continueStmt)
    ]
  }
  match SourceInference.Detail.validateSourceGraph crossCategoryDuplicate with
  | .error (.duplicateOccurrence occurrence) =>
      assertTrue (occurrence == duplicateOccurrence)
        "cross-category duplicate occurrence lost its exact diagnostic"
  | .error error => throw (IO.userError
      s!"cross-category duplicate occurrence produced {reprStr error}")
  | .ok () => throw (IO.userError
      "expression and statement nodes shared one occurrence")

  let wrongCategoryRoot : SourceInference.NodeId :=
    .statement (graphValidationStatement 1)
  let missingRoot := { validSourceGraph with roots := [wrongCategoryRoot] }
  match SourceInference.Detail.validateSourceGraph missingRoot with
  | .error (.missingRoot root) =>
      assertTrue (root == wrongCategoryRoot)
        "wrong-category root lost its exact diagnostic"
  | .error error => throw (IO.userError
      s!"wrong-category root produced {reprStr error}")
  | .ok () => throw (IO.userError
      "a statement root resolved to an expression at the same occurrence")

  let parentId : SourceInference.NodeId :=
    .expression (graphValidationExpression 1)
  let missingChildId : SourceInference.NodeId :=
    .expression (graphValidationExpression 0)
  let wrongCategoryChild := {
    validSourceGraph with
    nodes := [
      .statement (graphValidationStatementNode 0 .continueStmt),
      .expression (graphValidationExpressionNode 1
        (.group (graphValidationExpression 0)))
    ]
  }
  match SourceInference.Detail.validateSourceGraph wrongCategoryChild with
  | .error (.missingChild parent child) =>
      assertTrue (parent == parentId && child == missingChildId)
        "wrong-category child edge lost its exact diagnostic"
  | .error error => throw (IO.userError
      s!"wrong-category child edge produced {reprStr error}")
  | .ok () => throw (IO.userError
      "an expression edge resolved to a statement at the same occurrence")

  let rootOne : SourceInference.NodeId :=
    .expression (graphValidationExpression 1)
  let rootZero : SourceInference.NodeId :=
    .expression (graphValidationExpression 0)
  let rootTwo : SourceInference.NodeId :=
    .expression (graphValidationExpression 2)

  let duplicateRoot := {
    validSourceGraph with
    roots := [rootOne, rootOne]
  }
  expectDuplicateIncomingNode "a duplicate source root" duplicateRoot rootOne

  let duplicateChildSlot := {
    validSourceGraph with
    nodes := [
      .expression (graphValidationExpressionNode 0 (.literal (.decimal "0"))),
      .expression (graphValidationExpressionNode 1
        (.tuple [graphValidationExpression 0, graphValidationExpression 0]))
    ]
  }
  expectDuplicateIncomingNode "a duplicate child slot"
    duplicateChildSlot rootZero

  let sharedChild := {
    validSourceGraph with
    roots := [rootOne, rootTwo]
    nodes := [
      .expression (graphValidationExpressionNode 0 (.literal (.decimal "0"))),
      .expression (graphValidationExpressionNode 1
        (.group (graphValidationExpression 0))),
      .expression (graphValidationExpressionNode 2
        (.group (graphValidationExpression 0)))
    ]
  }
  expectDuplicateIncomingNode "a child shared by two parents"
    sharedChild rootZero

  let rootAsChild := {
    validSourceGraph with
    roots := [rootZero, rootOne]
  }
  expectDuplicateIncomingNode "a root retained as a child"
    rootAsChild rootZero

  let orphanCycle := {
    validSourceGraph with
    roots := [rootZero]
    nodes := [
      .expression (graphValidationExpressionNode 0 (.literal (.decimal "0"))),
      .expression (graphValidationExpressionNode 1
        (.group (graphValidationExpression 2))),
      .expression (graphValidationExpressionNode 2
        (.group (graphValidationExpression 1)))
    ]
  }
  expectUnreachableNode "an orphan cycle" orphanCycle rootOne

  let simpleCycle := {
    validSourceGraph with
    roots := [rootZero]
    nodes := [
      .expression (graphValidationExpressionNode 0
        (.group (graphValidationExpression 1))),
      .expression (graphValidationExpressionNode 1
        (.group (graphValidationExpression 0)))
    ]
  }
  expectDuplicateIncomingNode "a reachable cycle" simpleCycle rootZero

  let finalizationState : SourceInference.State := {
    SourceInference.State.initial solverRegressionOwner with
    nextOccurrence := 2
    nodes := validSourceGraph.nodes
  }
  match SourceInference.Detail.finalize solverRegressionContext .word
      finalizationState [wrongCategoryRoot] with
  | .error (.missingRoot root) =>
      assertTrue (root == wrongCategoryRoot)
        "finalization lost its graph-validation diagnostic"
  | .error error => throw (IO.userError
      s!"finalization returned the wrong graph error: {reprStr error}")
  | .ok _ => throw (IO.userError
      "finalization accepted a wrong-category root")

private def testClosedUnsupportedIntegerPatternTarget : IO Unit := do
  let metavariable : TypeSystem.TypeVarId := ⟨0⟩
  let origin : SourceInference.IntegerPatternOrigin := {
    metavariable
    span := solverRegressionSpan
    requirement := ⟨0⟩
  }
  let initial := SourceInference.State.initial solverRegressionOwner
  let state : SourceInference.State := {
    initial with
    inference := {
      next := 1
      substitution := [(metavariable, .bool)]
    }
  }
  match SourceInference.Detail.validateIntegerPatternTarget origin state with
  | .error (.nonNumericPatternType span type) =>
      assertTrue (span == solverRegressionSpan && type == TypeSystem.Ty.bool)
        "unsupported closed integer-pattern target lost its exact diagnostic"
  | .error error => throw (IO.userError
      s!"unsupported closed integer-pattern target produced {reprStr error}")
  | .ok _ => throw (IO.userError
      "unsupported closed integer-pattern target passed final validation")

private def testSourceNamedLiteralTraitsDoNotAuthorize : IO Unit := do
  let source := String.intercalate "\n" [
    "trait Int<T> {}",
    "trait FromLiteral<T> {}",
    "trait Numeric<T> {}",
    "enum Box { Only }",
    "impl Int<Box> {}",
    "impl FromLiteral<Box> {}",
    "impl Numeric<Box> {}",
    "function literal() returns (Box) { return 1; }"
  ]
  match SourceInference.loadAndCheckProgram (workspace source) with
  | .error errors =>
      assertTrue (errors.any fun error => match error with
        | .body { error := .unsupportedIntegerLiteralTarget _ type, .. } =>
            type != TypeSystem.Ty.word && type != TypeSystem.Ty.integer
        | _ => false)
        "source traits named Int/FromLiteral/Numeric authorized a nominal literal"
  | .ok _ => throw (IO.userError
      "source traits named Int/FromLiteral/Numeric authorized a nominal literal")

private def testUnconstrainedIntegerLiteralDefaultsToWord : IO Unit := do
  let checked ← check "function defaulted() { 1; return; }"
  let function ← match checked with
    | [function] => pure function
    | functions => throw (IO.userError
        s!"unconstrained literal fixture checked {functions.length} functions")
  let literals := integerLiteralRows function
  assertTrue (decide (function.inferredBodyType = TypeSystem.Ty.unit) &&
      literals.length == 1 && literals.all (hasExactDefaultedWordEvidence function) &&
      function.solvedRequirements.length == 1 &&
      function.solvedRequirements.all hasBuiltinIntWordEvidence)
    "an unconstrained integer literal did not default exactly to builtin Int<Word>"

private def testLetBoundIntegerLiteralClosesLater : IO Unit := do
  let checked ← check
    "function closeLater() returns (Word) { let value = 1; return value; }"
  let function ← match checked with
    | [function] => pure function
    | functions => throw (IO.userError
        s!"let-bound literal fixture checked {functions.length} functions")
  assertTrue (function.solvedRequirements.length == 1 &&
      function.solvedRequirements.all fun solved =>
        solved.predicate == ProgramSignatures.builtinIntPredicate .word)
    "a later return context did not close the let-bound literal as Word"

private def testUnusedLetIntegerLiteralDefaultsIndependently : IO Unit := do
  let checked ← check
    "function unused() returns (Word) { let value = 1; return 9; }"
  let function ← match checked with
    | [function] => pure function
    | functions => throw (IO.userError
        s!"unused literal fixture checked {functions.length} functions")
  let binder ← match function.typedBody.nodes.filterMap fun
      | .statement { form := .letDecl binder (some _), .. } =>
          if binder.name == "value" then some binder else none
      | _ => none with
    | [binder] => pure binder
    | binders => throw (IO.userError
        s!"unused literal fixture retained {binders.length} value binders")
  let literals := integerLiteralRows function
  assertTrue (decide (binder.scheme = .mono .word) &&
      literals.map (fun row => row.2.rawValue) == [1, 9] &&
      literals.all (hasExactDefaultedWordEvidence function) &&
      function.solvedRequirements.length == 2 &&
      function.solvedRequirements.all hasBuiltinIntWordEvidence)
    "an unused let literal and returned literal did not retain independent Int<Word> evidence"

private def testLiteralRequirementPreservesIndependentPolymorphism : IO Unit := do
  let checked ← check (String.intercalate "\n" [
    "function run(flag: Bool) returns ((Word, Word), (Word, Bool)) {",
    "  let f = lam(value) { return (1, value); };",
    "  return (f(2), f(flag));",
    "}"
  ])
  let function ← match checked with
    | [function] => pure function
    | functions => throw (IO.userError
        s!"mixed literal-polymorphism fixture checked {functions.length} functions")
  assertTrue (decide (function.inferredBodyType =
      TypeSystem.Ty.product (.product .word .word) (.product .word .bool)) &&
      function.solvedRequirements.length == 2 &&
      function.solvedRequirements.all fun solved =>
        solved.predicate == ProgramSignatures.builtinIntPredicate .word)
    "an integer literal monomorphized an independent let-bound type variable"

private def testContextualIntegerLiteralOperators : IO Unit := do
  let checked ← check (String.intercalate "\n" [
    "function addLiterals() returns (Word) { return 1 + 1; }",
    "function complementLiteral() returns (Word) { return ~1; }"
  ])
  let intWordRequirements (function : SourceInference.CheckedFunction) :=
    function.solvedRequirements.filter fun solved =>
      solved.predicate == ProgramSignatures.builtinIntPredicate .word
  match checked with
  | [addition, complement] =>
      assertTrue (decide (addition.inferredBodyType = TypeSystem.Ty.word ∧
          (intWordRequirements addition).length = 2))
        "Word context did not close both addition literals through builtin Int"
      assertTrue (decide (complement.inferredBodyType = TypeSystem.Ty.word ∧
          (intWordRequirements complement).length = 1))
        "Word context did not close the complemented literal through builtin Int"
  | functions => throw (IO.userError
      s!"contextual operator fixture checked {functions.length} functions")

private def testNestedIntegerLiteralOperatorsCloseLater : IO Unit := do
  let checked ← check (String.intercalate "\n" [
    "function accept(value: Word) returns (Word) { return value; }",
    "function nestedAdd() returns (Word) { return accept(1 + 1); }",
    "function nestedNot() returns (Word) { return accept(~1); }",
    "function letAdd() returns (Word) {",
    "  let value = 1 + 1;",
    "  return accept(value);",
    "}",
    "function letNot() returns (Word) {",
    "  let value = ~1;",
    "  return accept(value);",
    "}"
  ])
  let validate (label : String) (literalCount : Nat)
      (acceptsOperator : SourceInference.ExpressionForm → Bool)
      (function : SourceInference.CheckedFunction) : IO Unit := do
    let literals := function.typedBody.nodes.filterMap fun
      | .expression { form := .integerLiteral _ resolution, .. } =>
          some resolution
      | _ => none
    let hasWordOperator := function.typedBody.nodes.any fun
      | .expression node =>
          node.type == TypeSystem.Ty.word && acceptsOperator node.form
      | .statement _ => false
    assertTrue (decide (function.inferredBodyType = TypeSystem.Ty.word) &&
        literals.length == literalCount &&
        (literals.all fun resolution =>
          resolution.targetType == TypeSystem.Ty.word) &&
        function.solvedRequirements.length == literalCount &&
        (function.solvedRequirements.all fun solved =>
          solved.predicate == ProgramSignatures.builtinIntPredicate .word) &&
        hasWordOperator)
      s!"{label} did not close its deferred operator and literal carriers as Word"
  match checked with
  | _ :: nestedAdd :: nestedNot :: letAdd :: letNot :: [] =>
      validate "nested addition" 2
        (fun form => form matches .binary _ .add _) nestedAdd
      validate "nested complement" 1
        (fun form => form matches .unary .bitNot _) nestedNot
      validate "let-bound addition" 2
        (fun form => form matches .binary _ .add _) letAdd
      validate "let-bound complement" 1
        (fun form => form matches .unary .bitNot _) letNot
  | functions => throw (IO.userError
      s!"nested operator fixture checked {functions.length} functions")

private def testUnconstrainedIntegerLiteralOperatorsDefaultToWord : IO Unit := do
  let unconstrained := String.intercalate "\n" [
    "function add() { 1 + 1; return; }",
    "function invert() { ~1; return; }",
    "function compare() returns (Bool) { return 1 == 1; }"
  ]
  let checked ← check unconstrained
  let validate (label : String) (expectedBody expectedOperator : TypeSystem.Ty)
      (literalCount : Nat)
      (acceptsOperator : SourceInference.ExpressionForm → Bool)
      (function : SourceInference.CheckedFunction) : IO Unit := do
    let literals := integerLiteralRows function
    let hasOperator := function.typedBody.nodes.any fun
      | .expression node =>
          node.type == expectedOperator && node.requirements.isEmpty &&
            node.coercions.isEmpty && acceptsOperator node.form
      | .statement _ => false
    assertTrue (function.inferredBodyType == expectedBody &&
        literals.length == literalCount &&
        literals.all (hasExactDefaultedWordEvidence function) &&
        function.solvedRequirements.length == literalCount &&
        function.solvedRequirements.all hasBuiltinIntWordEvidence && hasOperator)
      s!"{label} did not default its operands to the builtin Word operator"
  match checked with
  | [addition, complement, comparison] =>
      validate "unconstrained addition" .unit .word 2
        (fun form => form matches .binary _ .add _) addition
      validate "unconstrained complement" .unit .word 1
        (fun form => form matches .unary .bitNot _) complement
      validate "unconstrained equality" .bool .bool 2
        (fun form => form matches .binary _ .equal _) comparison
  | functions => throw (IO.userError
      s!"unconstrained operator fixture checked {functions.length} functions")

private def testDeferredIntegerLiteralOperatorRejections : IO Unit := do
  let unsupported := String.intercalate "\n" [
    "enum Box { Only }",
    "function acceptBox(value: Box) returns (Box) { return value; }",
    "function acceptBool(value: Bool) returns (Bool) { return value; }",
    "function box() returns (Box) { return acceptBox(1 + 1); }",
    "function boolean() returns (Bool) { return acceptBool(~1); }"
  ]
  match SourceInference.loadAndCheckProgram (workspace unsupported) with
  | .error errors =>
      let rejected := errors.filter fun error => match error with
        | .body { error := .noTraitImplementation predicate, .. } =>
            predicate.trait == ProgramTraitId.builtin .int &&
              predicate.subject != TypeSystem.Ty.word &&
              predicate.subject != TypeSystem.Ty.integer
        | _ => false
      assertTrue (rejected.length == 2)
        "a deferred operator authorized a nominal or Bool literal target"
  | .ok _ => throw (IO.userError
      "a deferred operator accepted a nominal or Bool literal target")
  let traitOwned := String.intercalate "\n" [
    "trait Add<T> {",
    "  function add(left: T, right: T) returns (T);",
    "}",
    "function accept(value: Word) returns (Word) { return value; }",
    "function rejected() returns (Word) { return accept(1 + 1); }"
  ]
  let loaded ← load traitOwned
  let add ← match loaded.environment.traitsNamed "Add" with
    | [declaration] => pure declaration.id
    | declarations => throw (IO.userError
        s!"expected one Add trait, found {declarations.length}")
  match SourceInference.checkLoadedProgram loaded with
  | .error errors =>
      assertTrue (errors.any fun error => match error with
        | .body { error := .noTraitImplementation predicate, .. } =>
            decide (predicate.trait = add) &&
              predicate.subject == TypeSystem.Ty.word &&
              predicate.arguments.isEmpty
        | _ => false)
        "a defaulted Word operator bypassed its source Add<Word> obligation"
  | .ok _ => throw (IO.userError
      "an available Add catalog was bypassed by direct builtin deferral")
  let logical := String.intercalate "\n" [
    "function accept(value: Word) returns (Word) { return value; }",
    "function badAnd() returns (Word) {",
    "  let value = 1;",
    "  value && value;",
    "  return accept(value);",
    "}",
    "function badOr() returns (Word) {",
    "  let value = 1;",
    "  value || value;",
    "  return accept(value);",
    "}",
    "function badNot() returns (Word) {",
    "  let value = 1;",
    "  !value;",
    "  return accept(value);",
    "}"
  ]
  match SourceInference.loadAndCheckProgram (workspace logical) with
  | .error errors =>
      let hasUnknown (name : String) := errors.any fun error => match error with
        | .body { error := .unknownVariable actual, .. } => actual == name
        | _ => false
      assertTrue (hasUnknown "and" && hasUnknown "or" && hasUnknown "not")
        "a Bool-domain logical operator was deferred over a Word literal target"
  | .ok _ => throw (IO.userError
      "Bool-domain logical operators were accepted over Word literal targets")
  let unrelatedStaged := String.intercalate "\n" [
    "function take(value: integer, ignored: integer) returns (integer) {",
    "  return value;",
    "}",
    "function bad(value: integer) returns (integer) {",
    "  return take(value, 1) + value;",
    "}"
  ]
  match SourceInference.loadAndCheckProgram (workspace unrelatedStaged) with
  | .error errors =>
      assertTrue (errors.any fun error => match error with
        | .body { error := .operatorNotSupported "Add" .integer, .. } => true
        | _ => false)
        "an unrelated ground integer literal authorized a staged operator"
  | .ok _ => throw (IO.userError
      "an unrelated literal authorized an integer operator on nonliteral inputs")

private def testDefaultedIntegerLiteralOperatorsRespectSourceTraits : IO Unit := do
  let source := String.intercalate "\n" [
    "trait Eq<T> {",
    "  function eq(left: T, right: T) returns (Bool);",
    "}",
    "trait BitNot<T> {",
    "  function bnot(value: T) returns (T);",
    "}",
    "function compare() returns (Bool) { return 1 == 1; }",
    "function invert() { ~1; return; }"
  ]
  let loaded ← load source
  let eq ← match loaded.environment.traitsNamed "Eq" with
    | [declaration] => pure declaration.id
    | declarations => throw (IO.userError
        s!"expected one Eq trait, found {declarations.length}")
  let bitNot ← match loaded.environment.traitsNamed "BitNot" with
    | [declaration] => pure declaration.id
    | declarations => throw (IO.userError
        s!"expected one BitNot trait, found {declarations.length}")
  match SourceInference.checkLoadedProgram loaded with
  | .error errors =>
      let misses (trait : Resolved.DeclarationId) := errors.any fun error =>
        match error with
        | .body { error := .noTraitImplementation predicate, .. } =>
            decide (predicate.trait = trait) &&
              predicate.subject == TypeSystem.Ty.word &&
              predicate.arguments.isEmpty
        | _ => false
      assertTrue (errors.length == 2 && misses eq && misses bitNot)
        "defaulted literal operators lost their exact Eq<Word> or BitNot<Word> obligation"
  | .ok _ => throw (IO.userError
      "source Eq/BitNot catalogs without Word implementations were bypassed")

private def testGroundOperatorResultKeepsCoercion : IO Unit := do
  let checked ← check (String.intercalate "\n" [
    "trait Add<T> {",
    "  function add(left: T, right: T) returns (T);",
    "}",
    "trait Coerce<From, To> {}",
    "enum Box { Only }",
    "impl Add<Box> {",
    "  function add(left: Box, right: Box) returns (Box) { return left; }",
    "}",
    "impl Coerce<Box, Word> {}",
    "function convert(left: Box, right: Box) returns (Word) {",
    "  return left + right;",
    "}"
  ])
  let function ← match checked.getLast? with
    | some function => pure function
    | none => throw (IO.userError "ground operator fixture checked no function")
  assertTrue (decide (function.inferredBodyType = TypeSystem.Ty.word ∧
      function.solvedRequirements.length = 2) &&
      (function.solvedRequirements.any fun solved =>
        solved.predicate.arguments == []) &&
      (function.solvedRequirements.any fun solved =>
        solved.predicate.arguments == [TypeSystem.Ty.word]))
    "a ground operator result lost its Add evidence or result coercion"

private def testUnsupportedStatement : IO Unit := do
  let source :=
    "function loop(flag: Bool) { while (flag) { return; } }"
  let checked ← check source
  assertTrue (checked.any fun function =>
      function.typedBody.nodes.any fun
        | .statement { form := .whileLoop .., .. } => true
        | _ => false)
    "while inference did not retain its typed control-flow node"

private def testTraitBackedCoercion : IO Unit := do
  let source := String.intercalate "\n" [
    "trait Coerce<From, To> {}",
    "enum Box { Only }",
    "impl Coerce<Word, Box> {}",
    "function accept(value: Box) returns (Box) { return value; }",
    "function convert(value: Word) returns (Box) { return accept(value); }"
  ]
  let checked ← check source
  match checked.find? fun function =>
      function.evidence.any fun evidence => match evidence with
        | .implementation _ => true
        | .assumption _ => false with
  | some function =>
      assertTrue (decide (function.predicates.length = 1))
        "coercion evidence lost its Coerce predicate"
  | none => throw (IO.userError "trait-backed coercion produced no evidence")

private def testMissingCoercion : IO Unit := do
  let source := String.intercalate "\n" [
    "trait Coerce<From, To> {}",
    "enum Box { Only }",
    "function accept(value: Box) returns (Box) { return value; }",
    "function reject(value: Word) returns (Box) { return accept(value); }"
  ]
  match SourceInference.loadAndCheckProgram (workspace source) with
  | .error errors =>
      assertTrue (errors.any fun error => match error with
        | .body { error := .noTraitImplementation predicate, .. } =>
            predicate.arguments.length == 1
        | _ => false) "missing coercion implementation was accepted"
  | .ok _ => throw (IO.userError "missing coercion implementation was accepted")

private def testInconclusiveCoercion : IO Unit := do
  let source := String.intercalate "\n" [
    "trait Coerce<From, To> {}",
    "enum Box { Only }",
    "impl Coerce<Word, Box> {}",
    "impl Coerce<Word, Box> {}",
    "function accept(value: Box) returns (Box) { return value; }",
    "function reject(value: Word) returns (Box) { return accept(value); }"
  ]
  match SourceInference.loadAndCheckProgram (workspace source) with
  | .error errors =>
      assertTrue (errors.any fun error => match error with
        | .body { error := .inconclusiveTrait (.ambiguous _ _ _), .. } => true
        | _ => false) "overlapping coercion implementations lost ambiguity"
  | .ok _ => throw (IO.userError "ambiguous coercion implementation was selected")

private def testUnsolvedCoercionMethodPredicate : IO Unit := do
  let source := String.intercalate "\n" [
    "trait Eq<T> {}",
    "trait Coerce<From, To> {",
    "  function coerce(value: From) returns (To) where From: Eq;",
    "}",
    "function acceptWord(value: Word) returns (Word) { return value; }",
    "function reject<T>(value: T) returns (Word) where T: Coerce<Word> {",
    "  return acceptWord(value);",
    "}"
  ]
  let loaded ← load source
  let eq ← match loaded.environment.traitsNamed "Eq" with
    | [declaration] => pure declaration.id
    | declarations => throw (IO.userError
        s!"expected one Eq trait, found {declarations.length}")
  match SourceInference.checkLoadedProgram loaded with
  | .error errors =>
      assertTrue (errors.any fun error => match error with
        | .body { error := .noTraitImplementation predicate, .. } =>
            decide (predicate.trait = eq) && predicate.arguments.isEmpty
        | _ => false)
        "a coercion method predicate was accepted without Eq<T>"
  | .ok _ => throw (IO.userError
      "a coercion method predicate was accepted without Eq<T>")

private def testConstrainedLetDoesNotGeneralizeAwayEvidence : IO Unit := do
  let source := String.intercalate "\n" [
    "trait Eq<T> {}",
    "impl Eq<Word> {}",
    "function keep<T>(value: T) returns (T) where T: Eq { return value; }",
    "function reject() returns (Bool) {",
    "  let f = lam(value) { return keep(value); };",
    "  return f(true);",
    "}"
  ]
  match SourceInference.loadAndCheckProgram (workspace source) with
  | .error errors =>
      assertTrue (errors.any fun error => match error with
        | .body { error := .noTraitImplementation predicate, .. } =>
            predicate.subject == TypeSystem.Ty.bool
        | _ => false)
        "a constrained let detached its predicate from the instantiated type"
  | .ok _ => throw (IO.userError "Eq<Word> evidence was reused for Bool")

private def testQualifiedLocalSchemeRequirements : IO Unit := do
  let source := String.intercalate "\n" [
    "trait Eq<T> {}",
    "impl Eq<Word> {}",
    "impl Eq<Bool> {}",
    "function keep<T>(value: T) returns (T) where T: Eq { return value; }",
    "function run(flag: Bool) returns (Word, Bool) {",
    "  let f = lam(value) { return keep(value); };",
    "  return (f(1), f(flag));",
    "}"
  ]
  let loaded ← load source
  let checked ← match SourceInference.checkLoadedProgram loaded with
    | .ok checked => pure checked
    | .error errors => throw (IO.userError
        s!"qualified local inference failed: {reprStr errors}")
  let function ← checkedNamed loaded.environment checked "run"
  let eq ← match loaded.environment.traitsNamed "Eq" with
    | [declaration] => pure declaration.id
    | declarations => throw (IO.userError
        s!"expected one Eq trait, found {declarations.length}")
  let binder ← match function.typedBody.nodes.filterMap fun
      | .statement { form := .letDecl binder (some _), .. } =>
          if binder.name == "f" then some binder else none
      | _ => none with
    | [binder] => pure binder
    | binders => throw (IO.userError
        s!"qualified local fixture retained {binders.length} f binders")
  let (quantified, template) ←
    match binder.scheme.quantified, binder.scheme.body,
        binder.schemeRequirements with
    | [quantified], .function (.variable parameter) (.variable result),
        [requirement] =>
        if quantified == parameter && parameter == result &&
            requirement.predicate.trait == .declaration eq &&
            requirement.predicate.subject == .variable quantified &&
            requirement.predicate.arguments.isEmpty then
          pure (quantified, requirement)
        else
          throw (IO.userError
            "qualified local scheme did not retain Eq<α> with its shared binder")
    | _, _, _ => throw (IO.userError
        "qualified local scheme did not retain one quantified requirement")
  let templateSolved ← match function.solvedRequirements.find? fun solved =>
      solved.id == template.templateRequirement with
    | some solved => pure solved
    | none => throw (IO.userError
        "qualified local template requirement was removed from the ledger")
  assertTrue (match templateSolved.evidence with
    | .assumption predicate =>
        predicate == templateSolved.predicate &&
          predicate.trait == .declaration eq &&
          predicate.subject == .variable quantified
    | _ => false)
    "qualified local template requirement was resolved instead of retained as an assumption"
  let references := function.typedBody.nodes.filterMap fun
    | .expression node => match node.form with
        | .reference _ (.local candidate) =>
            if candidate == binder.id then some node else none
        | _ => none
    | .statement _ => none
  let validatesReference (expected : TypeSystem.Ty)
      (node : SourceInference.ExpressionNode) : Bool :=
    node.rawType == .function expected expected &&
      match node.requirements with
      | [requirement] =>
          requirement != template.templateRequirement &&
            match function.solvedRequirements.find? fun solved =>
                solved.id == requirement with
            | some solved =>
                solved.predicate.trait == .declaration eq &&
                  solved.predicate.subject == expected &&
                  solved.predicate.arguments.isEmpty &&
                  match solved.evidence with
                  | .implementation (.byImpl goal _ _) =>
                      goal == solved.predicate
                  | _ => false
            | none => false
      | _ => false
  assertTrue (references.length == 2 &&
      references.any (validatesReference .word) &&
      references.any (validatesReference .bool))
    "qualified local references did not freshen type and Eq evidence together"

private def testNestedQualifiedRequirementOwnership : IO Unit := do
  let source := String.intercalate "\n" [
    "trait Eq<T> {}",
    "function keep<T>(value: T) returns (T) where T: Eq { return value; }",
    "function run(flag: Bool) returns (Word, Bool) {",
    "  let outer = lam(value) {",
    "    let inner = lam(item) { return keep(item); };",
    "    return value;",
    "  };",
    "  return (outer(1), outer(flag));",
    "}"
  ]
  let loaded ← load source
  let checked ← match SourceInference.checkLoadedProgram loaded with
    | .ok checked => pure checked
    | .error errors => throw (IO.userError
        s!"nested qualified ownership failed: {reprStr errors}")
  let function ← checkedNamed loaded.environment checked "run"
  let binders := function.typedBody.nodes.filterMap fun
    | .statement { form := .letDecl binder (some _), .. } => some binder
    | _ => none
  let outer ← match binders.find? fun binder => binder.name == "outer" with
    | some binder => pure binder
    | none => throw (IO.userError "nested qualified fixture lost outer")
  let inner ← match binders.find? fun binder => binder.name == "inner" with
    | some binder => pure binder
    | none => throw (IO.userError "nested qualified fixture lost inner")
  let template ← match inner.schemeRequirements with
    | [requirement] => pure requirement
    | requirements => throw (IO.userError
        s!"inner retained {requirements.length} qualified requirements")
  let owners := binders.filter fun binder =>
    binder.schemeRequirements.any fun requirement =>
      requirement.templateRequirement == template.templateRequirement
  assertTrue (decide (outer.schemeRequirements = [] ∧ owners = [inner]))
    "an outer local scheme recaptured its nested binder's template requirement"

private def testOperatorMethodPredicates : IO Unit := do
  let source := String.intercalate "\n" [
    "trait Eq<T> {}",
    "trait Noise<T> {}",
    "trait Add<T> {",
    "  function tag(value: T) returns (T) where T: Noise;",
    "  function add(left: T, right: T) returns (T) where T: Eq;",
    "}",
    "trait BitNot<T> {",
    "  function bnot(value: T) returns (T) where T: Eq;",
    "}",
    "function addWithMethodEvidence<T>(left: T, right: T) returns (T)",
    "    where T: Add, T: Eq {",
    "  return left + right;",
    "}",
    "function bitNotWithMethodEvidence<T>(value: T) returns (T)",
    "    where T: BitNot, T: Eq {",
    "  return ~value;",
    "}"
  ]
  let loaded ← load source
  let checked ← match SourceInference.checkLoadedProgram loaded with
    | .ok checked => pure checked
    | .error errors => throw (IO.userError
        s!"operator method predicates were rejected: {reprStr errors}")
  let addition ← checkedNamed loaded.environment checked
    "addWithMethodEvidence"
  let bitNot ← checkedNamed loaded.environment checked
    "bitNotWithMethodEvidence"
  let names (function : SourceInference.CheckedFunction) :=
    function.solvedRequirements.map fun solved =>
      traitNameOf loaded.environment solved.predicate
  let assumptionEvidence (function : SourceInference.CheckedFunction) :=
    function.solvedRequirements.all fun solved =>
      match solved.evidence with
      | .assumption predicate => predicate == solved.predicate
      | .implementation _ => false
  assertTrue (decide (names addition = [some "Add", some "Eq"]) &&
      assumptionEvidence addition)
    "binary inference did not retain Add<T>, Eq<T> in declaration order"
  assertTrue (decide (names bitNot = [some "BitNot", some "Eq"]) &&
      assumptionEvidence bitNot)
    "unary inference did not retain BitNot<T>, Eq<T> in declaration order"

private def testUnsolvedOperatorMethodPredicates : IO Unit := do
  let source := String.intercalate "\n" [
    "trait Eq<T> {}",
    "trait Add<T> {",
    "  function add(left: T, right: T) returns (T) where T: Eq;",
    "}",
    "trait BitNot<T> {",
    "  function bnot(value: T) returns (T) where T: Eq;",
    "}",
    "function rejectAdd<T>(left: T, right: T) returns (T) where T: Add {",
    "  return left + right;",
    "}",
    "function rejectBitNot<T>(value: T) returns (T) where T: BitNot {",
    "  return ~value;",
    "}"
  ]
  let loaded ← load source
  let eq ← match loaded.environment.traitsNamed "Eq" with
    | [declaration] => pure declaration.id
    | declarations => throw (IO.userError
        s!"expected one Eq trait, found {declarations.length}")
  match SourceInference.checkLoadedProgram loaded with
  | .error errors =>
      let unsolved := errors.filter fun error => match error with
        | .body { error := .noTraitImplementation predicate, .. } =>
            decide (predicate.trait = eq)
        | _ => false
      assertTrue (unsolved.length == 2)
        "a binary or unary method predicate was accepted without Eq<T>"
  | .ok _ => throw (IO.userError
      "operator method predicates were accepted without Eq<T>")

private def testOperatorMethodCatalogDiagnostics : IO Unit := do
  let missingSource := String.intercalate "\n" [
    "trait Add<T> {",
    "  function tag(value: T) returns (T);",
    "}",
    "function reject<T>(left: T, right: T) returns (T) where T: Add {",
    "  return left + right;",
    "}"
  ]
  match SourceInference.loadAndCheckProgram (workspace missingSource) with
  | .error errors =>
      assertTrue (errors.any fun error => match error with
        | .body { error := .missingOperatorTraitMethod _ "add", .. } => true
        | _ => false)
        "a trait catalog without the named add method lost its diagnostic"
  | .ok _ => throw (IO.userError
      "a trait catalog without the named add method was accepted")

  let malformedSource := String.intercalate "\n" [
    "trait Add<T> {",
    "  function add(value: T) returns (Bool);",
    "}",
    "function reject<T>(left: T, right: T) returns (T) where T: Add {",
    "  return left + right;",
    "}"
  ]
  match SourceInference.loadAndCheckProgram (workspace malformedSource) with
  | .error errors =>
      assertTrue (errors.any fun error => match error with
        | .body { error := (.operatorTraitMethodSignatureMismatch _ "add"
            expectedParameters actualParameters expectedReturns actualReturns),
            .. } => decide (expectedParameters.length = 2 ∧
              actualParameters.length = 1 ∧ expectedReturns.length = 1 ∧
              actualReturns = [.bool])
        | _ => false)
        "a malformed add method lost its operator-signature diagnostic"
  | .ok _ => throw (IO.userError
      "a malformed add method was accepted as binary operator semantics")

  let duplicateSource := String.intercalate "\n" [
    "trait Add<T> {",
    "  function add(left: T, right: T) returns (T);",
    "}",
    "function reject<T>(left: T, right: T) returns (T) where T: Add {",
    "  return left + right;",
    "}"
  ]
  let loaded ← load duplicateSource
  let signatures ← match buildProgramSignatures loaded.environment with
    | .ok signatures => pure signatures
    | .error errors => throw (IO.userError
        s!"operator catalog fixture failed: {reprStr errors}")
  let add ← match signatures.traits.filter fun trait => trait.name == "Add" with
    | [trait] => pure trait
    | traits => throw (IO.userError
        s!"expected one Add catalog, found {traits.length}")
  let method ← match add.methods with
    | [method] => pure method
    | methods => throw (IO.userError
        s!"expected one Add method, found {methods.length}")
  let duplicate := {
    method with id := { method.id with methodIndex := method.id.methodIndex + 1 }
  }
  let tampered := {
    signatures with
    traits := signatures.traits.map fun trait =>
      if trait.id = add.id then { trait with methods := trait.methods ++ [duplicate] }
      else trait
  }
  match SourceInference.checkFunctionBodies loaded.environment tampered with
  | .error errors =>
      assertTrue (errors.any fun error => match error.error with
        | .duplicateOperatorTraitMethod trait "add" 2 => trait == add.id
        | _ => false)
        "a duplicate named operator method lost its defensive diagnostic"
  | .ok _ => throw (IO.userError
      "a duplicate named operator method was selected silently")

private def testAmbiguousCoercionTrait : IO Unit := do
  let raw : Workspace.RawWorkspace := {
    entry := "main.solc"
    mainSources := [
      { path := "left.solc", content :=
          "export {Coerce}; trait Coerce<From, To> {}" },
      { path := "right.solc", content :=
          "export {Coerce}; trait Coerce<From, To> {}" },
      {
        path := "main.solc"
        content := String.intercalate "\n" [
          "import * from left;",
          "import * from right;",
          "function accept(value: Bool) returns (Bool) { return value; }",
          "function reject(value: Word) returns (Bool) { return accept(value); }"
        ]
      }
    ]
    externalLibraries := []
  }
  match SourceInference.loadAndCheckProgram raw with
  | .error errors =>
      assertTrue (errors.any fun error => match error with
        | .body { error := .ambiguousOperatorTrait "Coerce" candidates, .. } =>
            candidates.length == 2
        | _ => false) "ambiguous Coerce declarations lost their diagnostic"
  | .ok _ => throw (IO.userError "ambiguous Coerce declaration was selected")

private def testGenericBodyAnnotationFormation : IO Unit := do
  let checked ← check (String.intercalate "\n" [
    "function keep<T>(value: T) returns (T) {",
    "  let local: T = value;",
    "  return local;",
    "}"
  ])
  assertTrue (checked.length == 1)
    "a declaration-owned generic body annotation failed formation validation"

private def testRecoveryBodyAnnotationFormation : IO Unit := do
  match SourceInference.Detail.resolveSourceType solverRegressionContext
      solverRegressionRecoveryType with
  | .error (.typeFormation (.recoveryType owner)) =>
      assertTrue (owner == solverRegressionOwner)
        "a recovery body annotation lost its declaration owner"
  | .error error => throw (IO.userError
      s!"a recovery body annotation produced the wrong error: {reprStr error}")
  | .ok type => throw (IO.userError
      s!"a recovery body annotation was accepted as {reprStr type}")

/-- Exercise parsed lambdas, local schemes, tuples, grouping, conditionals,
operators, contextual integer literals, and explicit deferrals. -/
def testSourceInference : IO Unit := do
  testGenericBodyAnnotationFormation
  testRecoveryBodyAnnotationFormation
  testLambdaLetTupleConditional
  testDiscardedPolymorphicReferenceResidual
  testAmbiguousOverload
  testIntegerLiteralExpectedType
  testClosedUnsupportedIntegerLiteralTarget
  testIntegerLiteralLedgerValidation
  testSourceGraphValidation
  testClosedUnsupportedIntegerPatternTarget
  testSourceNamedLiteralTraitsDoNotAuthorize
  testUnconstrainedIntegerLiteralDefaultsToWord
  testLetBoundIntegerLiteralClosesLater
  testUnusedLetIntegerLiteralDefaultsIndependently
  testLiteralRequirementPreservesIndependentPolymorphism
  testContextualIntegerLiteralOperators
  testNestedIntegerLiteralOperatorsCloseLater
  testUnconstrainedIntegerLiteralOperatorsDefaultToWord
  testDeferredIntegerLiteralOperatorRejections
  testDefaultedIntegerLiteralOperatorsRespectSourceTraits
  testGroundOperatorResultKeepsCoercion
  testUnsupportedStatement
  testTraitBackedCoercion
  testMissingCoercion
  testInconclusiveCoercion
  testUnsolvedCoercionMethodPredicate
  testConstrainedLetDoesNotGeneralizeAwayEvidence
  testQualifiedLocalSchemeRequirements
  testNestedQualifiedRequirementOwnership
  testOperatorMethodPredicates
  testUnsolvedOperatorMethodPredicates
  testOperatorMethodCatalogDiagnostics
  testAmbiguousCoercionTrait

end Tests.SourceInference
end

section
-- leanmerge: from Solcore.Test.SourceLambdaSourceAlignment
#check_failure Solcore.Frontend.SourceTypedRuntime.run

/-! Static preparation receipts and actual raw metadata replacements. The raw
fixtures test retained occurrence/form provenance, not source typing or the
execution meaning of the edited evidence. The contract flags survive edits to
an ancestor and to the lambda's own metadata. No evaluator is imported. -/

set_option autoImplicit false
namespace Tests.SourceLambdaSourceAlignment
open Solcore Solcore.Frontend Solcore.Frontend.SourceInference
open Solcore.SourceSemantics Solcore.SourceSemantics.CoreLowering
open LambdaMetadataViews

private def moduleId : Workspace.ModuleId := ⟨.main, ⟨[⟨"lambda_source_alignment", by decide⟩], by decide⟩⟩
private def owner : Resolved.DeclarationId := ⟨moduleId, 0⟩
private def id (index : Nat) : ExpressionId := ⟨⟨owner, index⟩⟩
private def span : Syntax.SourceSpan := ⟨⟨.main, "lambda_source_alignment.solc"⟩, 0, 1⟩
private def parameter : TypedBinder := {
  id := ⟨owner, 0⟩, name := "input", scheme := .mono .word, comptime := true }
private def sourceType : TypeSystem.Ty := .function .word .unit
private def requirement (index : Nat) : RequirementId := ⟨index⟩
private def coercion (index : Nat) : CoercionStep := {
  requirement := requirement index, source := sourceType, target := sourceType }
private def lambda : ExpressionNode := {
  id := id 1, span, type := sourceType, form := .lambda [parameter] .unit []
  requirements := [requirement 1], coercions := [coercion 1] }
private def ancestor : ExpressionNode := {
  id := id 0, span, type := sourceType, form := .group (id 1)
  requirements := [requirement 0], coercions := [coercion 0] }
private def source : TypedSource := {
  owner, inputs := [], roots := [.expression (id 0)], nodes := [.expression ancestor, .expression lambda] }
private def raw (node : ExpressionNode) : ExpressionNode := {
  node with type := node.rawType, requirements := [], coercions := [] }
private def firstView : TypedSource := SourceCoreEvidence.withNode source (raw ancestor)
private def finalView : TypedSource := SourceCoreEvidence.withNode firstView (raw lambda)

private theorem unique : NodeOccurrencesUnique source := by
  unfold NodeOccurrencesUnique nodeOccurrenceIds
  decide

private theorem first_metadata : MetadataView source firstView :=
  raw_view unique rfl []

private theorem final_metadata : MetadataView source finalView :=
  first_metadata.trans (raw_view (first_metadata.unique unique) rfl [])

/-- Replacing a raw ancestor does change the full table. -/
example : source ≠ firstView := by decide

/-- The real evidence helper also changes the lambda's own metadata. -/
example : firstView ≠ finalView := by decide

/-- Original staging flags and body IDs are nevertheless unchanged. -/
example : ∃ node, source.lookupExpression? (id 1) = some node ∧
    node.form = .lambda [parameter] .unit [] := by
  obtain ⟨node, found, _, form⟩ := final_metadata.expression
    (show finalView.lookupExpression? (id 1) = some (raw lambda) from rfl)
  exact ⟨node, found, form⟩

example : NodeOccurrencesUnique finalView := final_metadata.unique unique

/-- Preparation eliminates source equality as a free premise. Both the
canonical caller and the entire active substitution are extracted from the
actual local-evidence factory, including its original-source checks. -/
example {program : CheckedProgram} {plan : SourceSpecializationWorklist.Plan}
    {candidate : SourceCoreLocalPolymorphism.Instance} {parent : Option SourceCoreLocalEvidence.Prepared}
    {prepared : SourceCoreLocalEvidence.Prepared}
    {id : ExpressionId} {contract : SourceCoreStageContracts.Contract}
    (accepted : SourceCoreLocalEvidence.prepare program plan candidate parent = .ok prepared)
    (original : AuthenticatedCallableLedger.LambdaSource plan candidate.origin.caller id prepared.substitution contract) :
    prepared.source = original.source :=
  LambdaSourceAlignment.source_alignment (.contextual accepted) original

/-- Distinct source tables can have the same complete expression forms;
empty active substitution retains every original metadata field exactly. -/
example : source.applySubstitution [] = source := EmptySourceSubstitution.source _

/-- Normalization's real acceptance checks suffice for another view step. -/
example {program : CheckedProgram} {plan : SourceSpecializationWorklist.Plan}
    {binding : SourceCoreLocalPolymorphism.Binding} {parent : Option SourceCoreLocalEvidence.Prepared}
    {result : TypedSource} {expression : ExpressionId}
    (accepted : SourceCoreLocalEvidence.normalizeOccurrence program plan binding parent finalView expression = .ok result) :
    MetadataView source result :=
  final_metadata.trans (normalized_view (final_metadata.unique unique) accepted)

end Tests.SourceLambdaSourceAlignment
end

section
-- leanmerge: from Solcore.Test.SourceMappingDefaultFault
#check_failure Solcore.Frontend.SourceTypedRuntime.run
#check_failure Solcore.Frontend.SourceTypedRuntime.updateResolvedValue
#check_failure Solcore.Frontend.SourceTypedRuntime.writeResolvedPlace

/-! An absent mapping entry whose value type has no default is a source fault.
Independent source faults determine the actual Core selector/updater token.
Their administrative allocations preserve the initial store prefix, and failure
suppresses replacement and commit continuations. -/

set_option autoImplicit false

namespace Solcore.Test.SourceMappingDefaultFault

open Frontend
open Frontend.SourceInference
open SourceSemantics
open SourceSemantics.Dynamic
open TypeSystem

private def functionType : Ty := .function .word .word

/-- Non-defaultable mapping values remain admitted source types. -/
example (context : SourceSemantics.Context) :
    TypeWellScoped context [] (.mapping .word functionType) :=
  .mapping (.builtin .word) (.function (.builtin .word) (.builtin .word))

/-- Both successful evaluation prefixes contribute their heap effects before
missing-default failure; no result or failure of either child is invented. -/
example (program : Program) (context : SourceSemantics.Context)
    (evidence : EvidenceEnvironment) (source : TypedSource)
    (environment : Dynamic.Environment) (before middle after : Heap)
    (id base index : ExpressionId) (node : ExpressionNode) (key : Core.Word)
    (contains : ContainsExpression source id node)
    (form_eq : node.form = .index base index)
    (layout : OrdinaryRequirementLayout node.requirements node.coercions [])
    (base_evaluates : ExpressionEvaluates program context evidence source
      environment before base (.mapping .word functionType []) middle)
    (index_evaluates : ExpressionEvaluates program context evidence source
      environment middle index (.word key) after) :
    ExpressionEvaluatesOutcome program context evidence source environment
      before id (.fault (.missingMappingDefault functionType)) after := by
  apply ExpressionEvaluatesOutcome.fault
  apply ExpressionFaults.form contains
  rw [form_eq]
  exact .indexDefaultUnavailable layout base_evaluates index_evaluates
    (.word key) .nil (by intro defaultable; cases defaultable)

/-- No function is synthesized to fill an absent entry. -/
example (value : Value) : ¬ DefaultValue functionType value :=
  DefaultValue.not_function .word .word value

/-- The runtime's existing default calculation reports the same absence. -/
example : SourceTypedRuntime.defaultValue? (functionType.size + 1) functionType =
    none := by
  rfl

/-- Missing-default failure propagates through a successfully defaulted mapping
prefix; the outer mapping itself has a default even though its leaf does not. -/
example (outerKey innerKey : Core.Word) :
    ProjectionsFaults
      (some (.mapping .word (.mapping .word functionType) []))
      [.index (.word outerKey), .index (.word innerKey)]
      (.missingMappingDefault functionType) :=
  .indexDefault (.word outerKey) .nil (.mapping .word functionType)
    (.indexDefaultUnavailable (.word innerKey) .nil
      (by intro defaultable; cases defaultable))

/-- Real entries and constructor members also form successful prefixes. -/
example (instantiation : DataConstructorInstantiation) (key : Core.Word) :
    ProjectionsFaults
      (some (.constructed instantiation [.mapping .word functionType []]))
      [.member "table" 0, .index (.word key)]
      (.missingMappingDefault functionType) :=
  .member .head (.indexDefaultUnavailable (.word key) .nil
    (by intro defaultable; cases defaultable))

example (outerKey innerKey : Core.Word) :
    ProjectionsFaults
      (some (.mapping .word (.mapping .word functionType)
        [(.word outerKey, .mapping .word functionType [])]))
      [.index (.word outerKey), .index (.word innerKey)]
      (.missingMappingDefault functionType) :=
  .indexFound (.word outerKey) (.head (.refl (.word outerKey)))
    (.indexDefaultUnavailable (.word innerKey) .nil
      (by intro defaultable; cases defaultable))

/-- Every index expression has run before the pure read faults, and its effects
are preserved in the returned post-index heap. -/
example (program : Program) (context : SourceSemantics.Context)
    (evidence : EvidenceEnvironment) (source : TypedSource)
    (environment : Dynamic.Environment) (before after : Heap)
    (place : PlaceResolution) (location : Location) (initialCell : Cell)
    (key : Core.Word)
    (lookup : Dynamic.Environment.LooksUp environment place.root location)
    (initial_read : Heap.Reads before location initialCell)
    (evaluate : SourceProjectionsEvaluate program context evidence source
      environment before place.projections [.index (.word key)] after)
    (current_read : Heap.Reads after location
      { type := .mapping .word functionType,
        value := some (.mapping .word functionType []) }) :
    SourcePlaceFaults program context evidence source environment before place
      (.missingMappingDefault functionType) after :=
  .projectionRead lookup initial_read evaluate current_read .initialized
    (.indexDefaultUnavailable (.word key) .nil
      (by intro defaultable; cases defaultable))

/-- Resolution may have found an existing entry, while the RHS later clears
that mapping. Even plain replacement must traverse the latest root, so it
faults at the missing non-defaultable entry and retains the entire RHS heap. -/
example (program : Program) (context : SourceSemantics.Context)
    (evidence : EvidenceEnvironment) (source : TypedSource)
    (environment : Dynamic.Environment) (before targetHeap rhsHeap : Heap)
    (place : PlaceResolution) (target : ResolvedPlace) (rhs : ExpressionId)
    (right : Value) (key : Core.Word)
    (resolve : SourcePlaceResolves program context evidence source environment
      before place target targetHeap)
    (evaluate : ExpressionEvaluates program context evidence source environment
      targetHeap rhs right rhsHeap)
    (projections : target.projections = [.index (.word key)])
    (root_type : target.rootType = .mapping .word functionType)
    (current_read : Heap.Reads rhsHeap target.location
      { type := .mapping .word functionType,
        value := some (.mapping .word functionType []) }) :
    SourcePlaceAssignmentFaults program context evidence source environment before
      place .equal rhs (.missingMappingDefault functionType) rhsHeap := by
  apply SourcePlaceAssignmentFaults.structuralUpdate resolve evaluate
    current_read root_type.symm .initialized
  rw [projections]
  exact .indexDefaultUnavailable (.word key) .nil
    (by intro defaultable; cases defaultable)

/-- Invalid compound operands do not take precedence over a missing-default
failure while traversing the latest root. The readable-path premise needed
by the operand-fault rule is also impossible for this same root and path. -/
example (program : Program) (context : SourceSemantics.Context)
    (evidence : EvidenceEnvironment) (source : TypedSource)
    (environment : Dynamic.Environment) (before targetHeap rhsHeap : Heap)
    (place : PlaceResolution) (target : ResolvedPlace) (rhs : ExpressionId)
    (right : Core.Word) (currentCell : Cell) (initial : Option Value)
    (reason : SemanticFault)
    (resolve : SourcePlaceResolves program context evidence source environment
      before place target targetHeap)
    (evaluate : ExpressionEvaluates program context evidence source environment
      targetHeap rhs (.word right) rhsHeap)
    (selected : target.selected = some (.bool false))
    (current_read : Heap.Reads rhsHeap target.location currentCell)
    (root_type : currentCell.type = target.rootType)
    (root_value : RootInitialValue currentCell initial)
    (fault : ProjectionsFaults initial target.projections reason) :
    AssignmentOperandsInvalid .add target.selected (.word right) ∧
      SourcePlaceAssignmentFaults program context evidence source environment before
        place .add rhs reason rhsHeap ∧
      ¬ ∃ currentSelected, ProjectionsRead initial target.projections currentSelected := by
  refine ⟨?_, .structuralUpdate resolve evaluate current_read root_type root_value fault,
    ?_⟩
  · rw [selected]
    exact .compound .add (.numeric .add (by simp [NumericPair]))
  · rintro ⟨_, read⟩
    exact fault.excludes_read read

/-- The pure fault excludes both a successful read and every leaf modifier's
successful update, without assuming a global evaluation determinism theorem. -/
example (current : Option Value) (projections : List EvaluatedProjection)
    (reason : SemanticFault) (fault : ProjectionsFaults current projections reason)
    (modify : Option Value → Value → Prop) (selected : Option Value) (updated : Value) :
    ¬ ProjectionsRead current projections selected ∧
      ¬ ProjectionsUpdate modify current projections updated :=
  ⟨fault.excludes_read, fault.excludes_update⟩

/-- Without an RHS, bit-not's structural write cannot acquire a missing-default
failure after target resolution in the same post-index heap. -/
example (program : Program) (context : SourceSemantics.Context)
    (evidence : EvidenceEnvironment) (source : TypedSource)
    (environment : Dynamic.Environment) (before after : Heap)
    (place : PlaceResolution) (target : ResolvedPlace)
    (resolved : SourcePlaceResolves program context evidence source environment
      before place target after)
    (currentCell : Cell) (initial : Option Value) (reason : SemanticFault)
    (current_read : Heap.Reads after target.location currentCell)
    (initial_value : RootInitialValue currentCell initial) :
    ¬ ProjectionsFaults initial target.projections reason :=
  resolved.excludes_projection_fault current_read initial_value

namespace CoreBridge
open Core SourceSemantics.CoreLowering SourceCoreCompatibleDataPlaces
open CompatiblePayload CompatibleMixedRoute CompatibleMapping.MixedPaths

/-- An independently derived missing default, including a defaulted or member
prefix, constructs the actual Core getter and updater failures. The updater's
replacement and commit continuation can be any expressions: neither is evaluated.
The old snapshot does not participate in this traversal of the current root. -/
theorem current_root_missing_default
    {checked : SourceCoreCompatibleCatalog.Checked} {registry : SourceCoreRawMetadata.Registry}
    {functions : FunctionModel checked.catalog} {mapping : GeneralHeap.LocationMap} {world : Core.StoreTyping}
    {source : TypedSource} {site : SourceCoreElaboration.ErrorSite}
    {root leaf : TypeSystem.Ty} {sourceProjections : List PlaceProjection} {position : Nat}
    {steps : List PreparedStep} {keySites : List (ExpressionId × Core.Ty)}
    {path : PreparedPath checked source site root sourceProjections position steps keySites leaf}
    {prepared : Prepared} {keys : List Core.Value} {projections : List Dynamic.EvaluatedProjection}
    (arguments : Arguments checked registry functions mapping world source site keys path projections)
    {current : Dynamic.Value} {value : Core.Value} {type : Core.Ty}
    (represented : ValueRep checked registry functions mapping world root current value type)
    (fault : Dynamic.ProjectionsFaults (some current) projections (.missingMappingDefault functionType))
    {identities : Dynamic.Value → Core.Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
    (observations : CompatibleEquality.FunctionObservations checked.catalog functions identities)
    (keyLength : prepared.keyTypes.length = keys.length)
    (environment : Core.Environment) (store : Core.Store) (currentExpression keyExpression replacement next : Core.Expr)
    (selected : DataEquality.Selects environment currentExpression value)
    (keysSelected : DataEquality.Selects environment keyExpression (DataPatternValues.packValues keys))
    (output : Core.Ty) :
    ∃ token count finalStore administrative,
      FaultToken checked registry current steps projections (.missingMappingDefault functionType) token count ∧
      Core.Evaluates environment store (select prepared steps currentExpression keyExpression)
        (.inLeft prepared.optionalLeaf (.word token)) finalStore ∧
      Core.Evaluates environment store
        (Core.LanguageResult.bind output (update prepared steps type currentExpression keyExpression replacement) next)
        (.inLeft output (.word token)) finalStore ∧
      finalStore = store ++ administrative ∧ administrative.length = count := by
  obtain ⟨token, count, receipt, tree⟩ := arguments.faultTree represented fault prepared
  obtain ⟨finalStore, administrative, _, read, updated, appended, counted⟩ :=
    tree.preserves faithful observations keyLength environment store currentExpression keyExpression replacement selected keysSelected
  exact ⟨token, count, finalStore, administrative, receipt, read,
    Core.LanguageResult.bind_failure output updated, appended, counted⟩

end CoreBridge

end Solcore.Test.SourceMappingDefaultFault
end

section
-- leanmerge: from Solcore.Test.SourceTypedClosureCaptureBoundary
#check_failure Solcore.Frontend.SourceTypedRuntime.runDeepCertifiedWithValidationFuel

/-! Checked-source examples of the legacy capture boundary.  The code and
evidence stay authentic; only caller-supplied capture lists change.  This is
an audit regression, not an implementation of a new import policy. -/

set_option autoImplicit false

namespace Tests.SourceTypedClosureCaptureBoundary

open Solcore Solcore.Frontend Solcore.TypeSystem
open SourceTypedRuntime

private def assertTrue (condition : Bool) (message : String) : IO Unit := do
  unless condition do throw (IO.userError message)

private def workspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := []
  mainSources := [{ path := "main.solc", content := String.intercalate "\n" [
    "function make(value: Word) returns (function() returns (Word)) {",
    "  return lam() -> Word { return value; };",
    "}",
    "function invoke(f: function() returns (Word)) returns (Word) { return f(); }",
    "function constant() returns (Word) { return 13; }"
  ] }]
}

private def request (program : CheckedProgram) (name : String) :
    IO SourceSpecializationWorklist.Request := do
  match program.signatures.functions.filter (·.name == name) with
  | [signature] => pure { declaration := signature.id, parameterSubstitution := [] }
  | _ => throw (IO.userError s!"capture fixture missing function {name}")

private def prepared : IO (CheckedProgram × Plan × Key × Key × Key) := do
  let program ← match checkProgram workspace with
    | .ok program => pure program
    | .error errors => throw (IO.userError s!"capture fixture check failed: {reprStr errors}")
  let requests ← ["make", "invoke", "constant"].mapM (request program)
  let plan ← match SourceSpecializationWorklist.run program requests 100 with
    | .ok (.complete plan) => pure plan
    | result => throw (IO.userError s!"capture fixture plan failed: {reprStr result}")
  match plan.seedKeys with
  | [make, invoke, constant] => pure (program, plan, make, invoke, constant)
  | _ => throw (IO.userError "capture fixture seed keys changed")

private def expectedType : Ty := .function .unit .word

private def replaceCaptures (value : Value) (captured : SourceTypedRuntime.Environment) : Value :=
  match value with
  | .closure parameters result body source owner _ evidence =>
      .closure parameters result body source owner captured evidence
  | value => value

private def expectWord (expected : Nat) : RunResult → IO Unit
  | .done (.word value) _ =>
      assertTrue (value == Core.Word.ofNatModulo expected) "capture result changed"
  | result => throw (IO.userError s!"capture call did not return Word: {reprStr result}")

/-- Deep-safety alone does not certify captures.  The actual public boundary
rejects all raw closure arguments, including genuine returned ones.  Unused
initial-heap closures are admitted but do not become callable inputs. -/
def run : IO Unit := do
  let (program, plan, make, invoke, constant) ← prepared
  let cached ← SourceCoreUnifiedCorpusSupport.preparePlan "capture boundary" program plan make
  let (closure, state) ← match ← SourceCoreUnifiedCorpusSupport.observe cached make
      [.word (Core.Word.ofNatModulo 37)] 300000 {} 100 with
    | .done value state => pure (value, state)
    | result => throw (IO.userError s!"checked make failed: {reprStr result}")
  let captures ← match closure with
    | .closure _ _ _ _ _ captured _ => pure captured
    | _ => throw (IO.userError "checked make did not return a closure")
  let (binder, originalLocation) ← match captures with
    | [binding] => pure binding
    | _ => throw (IO.userError s!"unexpected checked captures: {reprStr captures}")
  let executablePlan ← match prepareExecutablePlanEvidence program plan with
    | .ok plan => pure plan
    | .error error => throw (IO.userError s!"capture evidence preparation failed: {reprStr error}")
  let rejected := fun value initial => do
    assertTrue (initial.isDeeplySafe 100 program.signatures executablePlan)
      "audit state must satisfy the deep validator"
    assertTrue (value.isDeeplySafe 100 program.signatures executablePlan initial expectedType)
      "audit closure must satisfy the deep validator"
    match ← SourceCoreUnifiedCorpusSupport.observe cached invoke [value] 300000 initial 100 with
    | .fault (.typeMismatch expected (some actual)) finalState =>
        assertTrue (expected == expectedType && actual == expectedType)
          "raw closure boundary diagnostic changed"
        assertTrue (reprStr finalState == reprStr initial)
          "raw closure boundary executed before rejecting"
    | result => throw (IO.userError s!"raw closure input was admitted: {reprStr result}")
  rejected closure state
  let missing := replaceCaptures closure []
  rejected missing state
  let otherBinder := { binder with binderIndex := binder.binderIndex + 1000 }
  rejected (replaceCaptures closure [(otherBinder, originalLocation)]) state
  let (boolLocation, wrongState) := state.allocate .bool (some (.bool true))
  let wrong := replaceCaptures closure [(binder, boolLocation)]
  rejected wrong wrongState
  rejected (replaceCaptures closure (captures ++ [(otherBinder, boolLocation)])) wrongState
  rejected (replaceCaptures closure (captures ++ [(binder, boolLocation)])) wrongState
  rejected (replaceCaptures closure ((binder, boolLocation) :: captures)) wrongState
  -- An authentic global is an admitted callable.  Adding a deeply safe but
  -- lexically malformed closure to the unused old heap does not expose it.
  let (_, unusedMissing) := wrongState.allocate expectedType (some missing)
  let (_, unusedWrong) := unusedMissing.allocate expectedType (some wrong)
  assertTrue (unusedWrong.isDeeplySafe 100 program.signatures executablePlan)
    "unused malformed capture lists stopped satisfying current deep safety"
  let final ← SourceCoreUnifiedCorpusSupport.observe cached invoke [.global constant []] 300000 unusedWrong 100
  expectWord 13 final
  match final with
  | .done _ state =>
      assertTrue (reprStr (state.heap.take unusedWrong.heap.length) == reprStr unusedWrong.heap)
        "Core execution changed the inert source heap prefix"
  | _ => pure ()

end Tests.SourceTypedClosureCaptureBoundary
end

section
-- leanmerge: from Solcore.Test.SourceTypedIR
/-! Executable coverage for the additive occurrence-addressed typed IR carrier. -/

set_option autoImplicit false

namespace Tests.SourceTypedIR

open Solcore Solcore.Frontend Solcore.Frontend.SourceInference

private def assertTrue (condition : Bool) (message : String) : IO Unit := do
  unless condition do
    throw (IO.userError message)

private def ownerModule : Workspace.ModuleId :=
  ⟨.main, ⟨[⟨"source_typed_ir", by decide⟩], by decide⟩⟩

private def declaration (index : Nat) : Resolved.DeclarationId :=
  ⟨ownerModule, index⟩

private def owner := declaration 0
private def trait := declaration 1

private def sourceId : Syntax.SourceId := {
  origin := .main
  path := "source_typed_ir.solc"
}

private def span : Syntax.SourceSpan := {
  source := sourceId
  startByte := 0
  endByte := 1
}

private def expressionId : ExpressionId :=
  ⟨⟨owner, 0⟩⟩

private def requirementId : RequirementId := ⟨4⟩
private def schemeRequirementId : RequirementId := ⟨7⟩
private def methodRequirement0 : RequirementId := ⟨5⟩
private def methodRequirement1 : RequirementId := ⟨6⟩
private def variable0 : TypeSystem.Ty := .variable ⟨0⟩
private def variable1 : TypeSystem.Ty := .variable ⟨1⟩

private def instantiation : DeclarationInstantiation := {
  declaration := declaration 2
  parameterSubstitution := [(⟨declaration 2, 0⟩, variable0)]
  type := variable0
  predicates := [{ trait, subject := variable0, arguments := [] }]
}

private def expression : ExpressionNode := {
  id := expressionId
  span
  type := variable1
  form := .reference "chosen" (.declaration instantiation)
  requirements := [requirementId, methodRequirement0, methodRequirement1]
  coercions := [{
    requirement := requirementId
    methodRequirements := [methodRequirement0, methodRequirement1]
    source := variable0
    target := variable1
  }]
}

private def source : TypedSource := {
  owner
  inputs := [{
    id := { owner, binderIndex := 0 }
    name := "input"
    scheme := { quantified := [⟨0⟩], body := .product variable0 variable1 }
    schemeRequirements := [{
      templateRequirement := schemeRequirementId
      predicate := { trait, subject := variable0, arguments := [variable1] }
    }]
    span := some span
  }]
  roots := [.expression expressionId]
  nodes := [.expression expression]
}

private def testFinalSubstitutionPreservesIdentity : IO Unit := do
  let substitution : TypeSystem.Substitution :=
    [(⟨0⟩, .word), (⟨1⟩, .bool)]
  let closed := source.applySubstitution substitution
  assertTrue (decide (closed.owner = owner ∧ closed.roots = source.roots ∧
      closed.nodes.map Node.id = source.nodes.map Node.id))
    "final substitution changed typed-source identities"
  match closed.inputs with
  | [input] =>
      assertTrue (decide (input.scheme.body = .product variable0 .bool ∧
          input.schemeRequirements = [{
            templateRequirement := schemeRequirementId
            predicate := { trait, subject := variable0, arguments := [.bool] }
          }]))
        "final substitution entered a quantified binder, missed a free type, or changed requirement identity"
  | _ => throw (IO.userError "typed-source inputs changed shape")
  match closed.lookupExpression? expressionId with
  | none => throw (IO.userError "typed expression lookup lost its node")
  | some node =>
      assertTrue (decide (node.rawType = .word ∧ node.type = .bool ∧
          node.hasValidCoercionPath ∧
          node.requirements =
            [requirementId, methodRequirement0, methodRequirement1] ∧
          node.coercions = [{
            requirement := requirementId
            methodRequirements := [methodRequirement0, methodRequirement1]
            source := .word
            target := .bool
          }]))
        "typed expression type/coercion closure changed"
      match node.coercions with
      | [step] =>
          assertTrue (decide (step.requirements =
              [requirementId, methodRequirement0, methodRequirement1]))
            "coercion obligations lost primary-first declaration order"
      | _ => throw (IO.userError "typed coercion path changed shape")
      match node.form with
      | .reference "chosen" (.declaration selected) =>
          assertTrue (decide (selected.type = .word ∧
              selected.parameterSubstitution =
                [(⟨declaration 2, 0⟩, .word)] ∧
              selected.predicates = [{
                trait, subject := .word, arguments := []
              }]))
            "selected declaration instantiation was not closed consistently"
      | _ => throw (IO.userError "typed reference resolution changed shape")
  assertTrue (decide (closed.lookupStatement? ⟨⟨owner, 0⟩⟩ = none))
    "category-safe lookup reinterpreted an expression as a statement"
  let indirect := CallResolution.indirect {
    argumentCount := 2
    argumentTypeBeforeCoercion := variable0
    argumentTypeAfterCoercion := variable1
    argumentCoercions := [{
      requirement := requirementId
      methodRequirements := [methodRequirement0, methodRequirement1]
      source := variable0
      target := variable1
    }]
  }
  match indirect.applySubstitution substitution with
  | .indirect metadata =>
      assertTrue (decide (metadata.argumentTypeBeforeCoercion = .word ∧
          metadata.argumentCount = 2 ∧
          metadata.argumentTypeAfterCoercion = .bool ∧
          metadata.argumentCoercions = [{
            requirement := requirementId
            methodRequirements := [methodRequirement0, methodRequirement1]
            source := .word
            target := .bool
          }] ∧ metadata.hasValidArgumentCoercionPath))
        "final substitution did not close indirect argument coercion metadata"
  | .declaration _ => throw (IO.userError
      "final substitution changed an indirect call into a declaration call")
  | .builtinFunction _ => throw (IO.userError
      "final substitution changed an indirect call into a builtin call")

private def testCoercionPathValidation : IO Unit := do
  let secondRequirement : RequirementId := ⟨5⟩
  let disconnected : ExpressionNode := {
    expression with
    type := .unit
    coercions := [
      { requirement := requirementId, source := .word, target := .bool },
      { requirement := secondRequirement, source := .word, target := .unit }
    ]
  }
  assertTrue (!disconnected.hasValidCoercionPath)
    "a disconnected expression coercion path was accepted"
  let wrongTarget : ExpressionNode := {
    expression with
    type := .unit
    coercions := [{
      requirement := requirementId
      source := .word
      target := .bool
    }]
  }
  assertTrue (!wrongTarget.hasValidCoercionPath)
    "an expression coercion path ending before node.type was accepted"
  let exact : ExpressionNode := {
    expression with
    type := .unit
    coercions := []
  }
  assertTrue (decide (exact.rawType = .unit ∧ exact.hasValidCoercionPath))
    "an uncoerced expression did not use its stored type as its raw type"

private def testIntegerLiteralFlexibleSubstitution : IO Unit := do
  let resolution : IntegerLiteralResolution := {
    rawValue := 42
    targetType := variable0
    requirement := requirementId
  }
  let substitution : TypeSystem.Substitution := [(⟨0⟩, .word)]
  match (ExpressionForm.integerLiteral (.decimal "42") resolution)
      |>.applySubstitution substitution with
  | .integerLiteral source closed =>
      assertTrue (decide (source = .decimal "42" ∧
          closed.rawValue = 42 ∧
          closed.targetType = .word ∧
          closed.requirement = requirementId ∧
          closed.predicate = ProgramSignatures.builtinIntPredicate .word))
        "flexible substitution changed integer literal provenance or missed its target"
  | _ => throw (IO.userError
      "flexible substitution changed the integer-literal expression form")

private def testRigidSchemeRequirementSubstitution : IO Unit := do
  let parameter : TypeSystem.TypeParameterId := ⟨declaration 2, 0⟩
  let binder : TypedBinder := {
    id := { owner, binderIndex := 1 }
    name := "qualified"
    scheme := {
      quantified := [⟨0⟩]
      body := .product (.parameter parameter) variable0
    }
    schemeRequirements := [{
      templateRequirement := schemeRequirementId
      predicate := {
        trait
        subject := .parameter parameter
        arguments := [variable0]
      }
    }]
    span := some span
  }
  let substitution : TypeSystem.ParameterSubstitution := [(parameter, .word)]
  let expected : TypedBinder := {
    binder with
    scheme := {
      quantified := [⟨0⟩]
      body := .product .word variable0
    }
    schemeRequirements := [{
      templateRequirement := schemeRequirementId
      predicate := { trait, subject := .word, arguments := [variable0] }
    }]
  }
  assertTrue (decide
      (Solcore.Frontend.SourceSpecialization.applyBinder substitution binder =
        expected))
    "executable rigid substitution missed a qualified local requirement"
  assertTrue (decide
      (Solcore.SourceSemantics.StructuralSubstitution.applyBinder substitution
        binder = expected))
    "structural rigid substitution disagreed on a qualified local requirement"

private def testInferenceStateScaffolding : IO Unit := do
  let locals : TypeSystem.Environment :=
    [("first", .mono .word), ("second", .mono .bool)]
  let initial := State.initial owner locals
  let outer := initial.lexicalScope
  assertTrue (decide (initial.owner = owner ∧ initial.nextLocal = 2 ∧
      initial.inputs.map (·.id) = [⟨owner, 0⟩, ⟨owner, 1⟩] ∧
      initial.localBinders = initial.inputs))
    "initial inference binders were not assigned stable declaration-local IDs"
  let (nested, state) := initial.allocateBinder "first" (.mono .word) (some span)
  let (expressionId, state) := state.allocateExpressionId
  let (statementId, state) := state.allocateStatementId
  assertTrue (decide (nested.id = ⟨owner, 2⟩ ∧
      state.lookupBinder? "first" = some nested ∧
      expressionId.occurrence = ⟨owner, 0⟩ ∧
      statementId.occurrence = ⟨owner, 1⟩))
    "inference-state allocators did not use independent stable ID streams"
  let expressionNode : ExpressionNode := {
    id := expressionId
    span
    type := .word
    form := .proxy .word
  }
  let statementNode : StatementNode := {
    id := statementId
    span
    type := .word
    form := .expression expressionId false
  }
  let state := state.recordNode (.expression expressionNode)
    |>.recordNode (.statement statementNode)
    |>.modifyExpressionNode expressionId fun node => {
        node with
        id := ⟨⟨owner, 99⟩⟩
        type := .bool
      }
  let state := state.restoreLexicalScope outer
  let typed := state.toTypedSource
    [.expression expressionId, .statement statementId]
  assertTrue (decide (state.locals = locals ∧
      state.localBinders = initial.localBinders ∧
      state.lookupBinder? "first" = initial.inputs.head? ∧
      state.nextLocal = 3 ∧ state.nextOccurrence = 2 ∧
      typed.owner = owner ∧ typed.inputs = initial.inputs ∧
      typed.nodes.length = 2))
    "lexical restoration rewound semantic state or changed typed inputs"
  match typed.lookupExpression? expressionId with
  | some node =>
      assertTrue (decide (node.id = expressionId ∧ node.type = .bool))
        "typed-node modification changed its stable identity"
  | none => throw (IO.userError "recorded expression was absent from typed source")
  match typed.lookupStatement? statementId with
  | some node =>
      assertTrue (decide (node.id = statementId ∧
          node.form = .expression expressionId false))
        "recorded statement changed while modifying an expression"
  | none => throw (IO.userError "recorded statement was absent from typed source")

def testSourceTypedIR : IO Unit := do
  testFinalSubstitutionPreservesIdentity
  testCoercionPathValidation
  testIntegerLiteralFlexibleSubstitution
  testRigidSchemeRequirementSubstitution
  testInferenceStateScaffolding

end Tests.SourceTypedIR
end

section
-- leanmerge: from Solcore.Test.TypedTraitResolution
set_option autoImplicit false

namespace Tests.TypedTraitResolution

open Solcore
open Solcore.Frontend
open Solcore.Frontend.TypedTraitResolution
open Solcore.TypeSystem

private def assertTrue (condition : Bool) (message : String) : IO Unit := do
  unless condition do
    throw (IO.userError message)

private def ownerModule : Workspace.ModuleId :=
  ⟨.main, ⟨[⟨"typed_trait_resolution", by decide⟩], by decide⟩⟩

private def declaration (index : Nat) : Resolved.DeclarationId :=
  ⟨ownerModule, index⟩

private def equalityTrait := declaration 0
private def showTrait := declaration 1
private def convertTrait := declaration 2
private def boxType := declaration 3
private def equalityWordImpl := declaration 10
private def showBoxImpl := declaration 11
private def convertSameImpl := declaration 12
private def whereOnlyImpl := declaration 13

private def predicate (trait : TraitId) (subject : Ty)
    (arguments : List Ty := []) : Predicate :=
  { trait, subject, arguments }

private def equality (type : Ty) : Predicate :=
  predicate equalityTrait type

private def showPredicate (type : Ty) : Predicate :=
  predicate showTrait type

private def convert (source target : Ty) : Predicate :=
  predicate convertTrait source [target]

private def box (argument : Ty) : Ty :=
  Ty.nominal boxType [argument]

private def variable0 : Ty := .variable ⟨0⟩

private def earlierPredicateSubstitution : Substitution :=
  [(⟨20⟩, .variable ⟨21⟩)]

private def predicateSubstitutionUpdate : Substitution :=
  [(⟨21⟩, .word)]

private def laterPredicateSubstitution : Substitution :=
  predicateSubstitutionUpdate.compose earlierPredicateSubstitution

private theorem earlierPredicateSubstitution_solved :
    earlierPredicateSubstitution.SolvedBelow 22 := by
  apply Substitution.SolvedBelow.mono
  · decide
  · intro rangeVariable member
    have same : rangeVariable = ⟨21⟩ := by
      simpa [earlierPredicateSubstitution, Ty.freeVariables] using member
    subst rangeVariable
    decide
  · simp [Ty.freeVariables]

private def composedSubstitutionPredicate : Predicate :=
  convert (box (.variable ⟨20⟩))
    (.product (.variable ⟨21⟩) (.variable ⟨20⟩))

/-- A composed solution collapses both the original variable and its
intermediate replacement throughout a predicate. -/
example :
    applySubstitution laterPredicateSubstitution
        (applySubstitution earlierPredicateSubstitution
          composedSubstitutionPredicate) =
      convert (box .word) (.product .word .word) := by
  have extension : laterPredicateSubstitution.SemanticallyExtends
      earlierPredicateSubstitution := by
    exact Substitution.SemanticallyExtends.compose_left
      predicateSubstitutionUpdate earlierPredicateSubstitution_solved
  rw [applySubstitution_semanticallyExtends extension]
  rfl

private def showBoxParameter : TypeParameterId :=
  { owner := showBoxImpl, index := 0 }

private def showBoxParameterType : Ty :=
  .parameter showBoxParameter

private def equalityWordRule : ImplRule :=
  { id := equalityWordImpl
    head := equality .word
    wherePredicates := [] }

private def showBoxRule : ImplRule :=
  { id := showBoxImpl
    head := showPredicate (box showBoxParameterType)
    wherePredicates := [equality showBoxParameterType] }

private def convertSameRule : ImplRule :=
  { id := convertSameImpl
    head := convert variable0 variable0
    wherePredicates := [] }

private def whereOnlyParameter : TypeParameterId :=
  { owner := whereOnlyImpl, index := 0 }

private def whereOnlyRule : ImplRule :=
  { id := whereOnlyImpl
    head := equality .word
    wherePredicates := [convert (.parameter whereOnlyParameter) variable0] }

private def expectedFreshShowBoxRule : ImplRule :=
  { id := showBoxImpl
    head := showPredicate (box (.variable ⟨0⟩))
    wherePredicates := [equality (.variable ⟨0⟩)] }

example : freshenRuleFor showBoxRule (showPredicate (box .word)) =
    expectedFreshShowBoxRule := by
  rfl

example : matchImplHead? showBoxRule (showPredicate (box .word)) =
    some [equality .word] := by
  rfl

example : Solcore.SourceSemantics.ImplHeadInstantiates showBoxRule
    (showPredicate (box .word)) [equality .word] := by
  exact Solcore.SourceSemantics.TraitResolutionSoundness.matchImplHead?_sound
    (by rfl)

example : matchImplHeadWithParameters? [showBoxParameter] showBoxRule
    (showPredicate (box .word)) = some {
      parameterSubstitution := [(showBoxParameter, .word)]
      wherePredicates := [equality .word]
    } := by
  rfl

example : ∃ substitution, HeadMatchCertificate showBoxRule
    (showPredicate (box .word)) [equality .word] substitution := by
  exact matchImplHead?_certificate (by rfl)

example : ∃ substitution, HeadMatchCertificate showBoxRule
    (showPredicate (box .word)) [equality .word] substitution := by
  have matched : matchImplHeadWithParameters? [showBoxParameter] showBoxRule
      (showPredicate (box .word)) = some {
        parameterSubstitution := [(showBoxParameter, .word)]
        wherePredicates := [equality .word]
      } := by rfl
  exact matchImplHeadWithParameters?_certificate matched

example : ∃ substitution : RuleMatchSubstitution,
    substitution.parameters.map Prod.fst = [showBoxParameter] ∧
      substitution.variables.domain = [] ∧
      substitution.applyPredicate showBoxRule.head =
        showPredicate (box .word) ∧
      showBoxRule.wherePredicates.map substitution.applyPredicate =
        [equality .word] := by
  rcases matchImplHead?_certificate (rule := showBoxRule)
      (goal := showPredicate (box .word)) (premises := [equality .word])
      (by rfl) with ⟨substitution, certificate⟩
  cases certificate with
  | intro _ _ parameter_domain variable_domain head_eq premises_eq =>
      have parameters_eq : ruleParameters showBoxRule =
          [showBoxParameter] := by native_decide
      have variables_eq : ruleVariables showBoxRule = [] := by native_decide
      rw [parameters_eq] at parameter_domain
      rw [variables_eq] at variable_domain
      exact ⟨substitution, parameter_domain, variable_domain, head_eq,
        premises_eq⟩

example : matchImplHead? showBoxRule (equality (box .word)) = none := by
  rfl

example : matchImplHead? convertSameRule (convert .word .bool) = none := by
  rfl

example : matchImplHead? convertSameRule (convert .word .word) = some [] := by
  rfl

example : ∃ substitution : RuleMatchSubstitution,
    substitution.parameters.map Prod.fst = [] ∧
      substitution.variables.domain = [⟨0⟩] ∧
      substitution.applyPredicate convertSameRule.head =
        convert .word .word := by
  rcases matchImplHead?_certificate (rule := convertSameRule)
      (goal := convert .word .word) (premises := []) (by rfl) with
    ⟨substitution, certificate⟩
  cases certificate with
  | intro _ _ parameter_domain variable_domain head_eq _ =>
      have parameters_eq : ruleParameters convertSameRule = [] := by
        native_decide
      have variables_eq : ruleVariables convertSameRule = [⟨0⟩] := by
        native_decide
      rw [parameters_eq] at parameter_domain
      rw [variables_eq] at variable_domain
      exact ⟨substitution, parameter_domain, variable_domain, head_eq⟩

example : matchImplHead? whereOnlyRule (equality .word) =
    some [convert (.variable ⟨1⟩) (.variable ⟨2⟩)] := by
  rfl

example : Solcore.SourceSemantics.ImplHeadInstantiates whereOnlyRule
    (equality .word)
    [convert (.variable ⟨1⟩) (.variable ⟨2⟩)] := by
  exact Solcore.SourceSemantics.TraitResolutionSoundness.matchImplHead?_sound
    (by rfl)

example : ∃ substitution : RuleMatchSubstitution,
    substitution.parameters.map Prod.fst = [whereOnlyParameter] ∧
      substitution.variables.domain = [⟨0⟩] ∧
      substitution.applyPredicate whereOnlyRule.head = equality .word ∧
      whereOnlyRule.wherePredicates.map substitution.applyPredicate =
        [convert (.variable ⟨1⟩) (.variable ⟨2⟩)] := by
  rcases matchImplHead?_certificate (rule := whereOnlyRule)
      (goal := equality .word)
      (premises := [convert (.variable ⟨1⟩) (.variable ⟨2⟩)])
      (by rfl) with ⟨substitution, certificate⟩
  cases certificate with
  | intro _ _ parameter_domain variable_domain head_eq premises_eq =>
      have parameters_eq : ruleParameters whereOnlyRule =
          [whereOnlyParameter] := by native_decide
      have variables_eq : ruleVariables whereOnlyRule = [⟨0⟩] := by
        native_decide
      rw [parameters_eq] at parameter_domain
      rw [variables_eq] at variable_domain
      exact ⟨substitution, parameter_domain, variable_domain, head_eq,
        premises_eq⟩

example : (ruleParameters showBoxRule).Nodup :=
  ruleParameters_nodup showBoxRule

example : showBoxParameter ∈ ruleParameters showBoxRule := by
  rw [mem_ruleParameters_iff]
  exact .inl (by native_decide)

private def evidenceMatches : Evidence → Bool
  | .byImpl actualGoal actualImpl [
      .byImpl actualPremise actualPremiseImpl []] =>
      decide (actualGoal = showPredicate (box .word) ∧
        actualImpl = showBoxImpl ∧
        actualPremise = equality .word ∧
        actualPremiseImpl = equalityWordImpl)
  | _ => false

private def successfulResolution : Bool :=
  match (resolve [equalityWordRule, showBoxRule] 2
      (showPredicate (box .word))).outcome with
  | .success evidence => evidenceMatches evidence
  | _ => false

private def expectedResolutionEvidence : Evidence :=
  .byImpl (showPredicate (box .word)) showBoxImpl
    [.byImpl (equality .word) equalityWordImpl []]

private def expectedSemanticEvidence :
    Solcore.SourceSemantics.TraitEvidence :=
  .implementation (showPredicate (box .word)) showBoxImpl
    [.implementation (equality .word) equalityWordImpl []]

/-- Typed resolution retains the exact outer and nested implementation
identities after instantiating the generic where predicate. -/
theorem nestedResolution_exact :
    (resolve [equalityWordRule, showBoxRule] 2
      (showPredicate (box .word))).outcome =
        .success expectedResolutionEvidence := by
  rfl

/-- The generic resolver-to-source-semantics bridge validates the same nested
evidence tree, including both selected implementation identities. -/
theorem nestedResolution_evidenceValid :
    Solcore.SourceSemantics.EvidenceValid []
      [equalityWordRule, showBoxRule] (showPredicate (box .word))
      expectedSemanticEvidence := by
  obtain ⟨semantic, represents, valid⟩ :=
    Solcore.SourceSemantics.TraitResolutionSoundness.resolve_success_evidenceValid
      nestedResolution_exact
  have expectedRep :
      Solcore.SourceSemantics.ImplementationEvidenceRepresents
        expectedResolutionEvidence expectedSemanticEvidence := by
    exact .byImpl (.cons (.byImpl .nil) .nil)
  have semanticEq : semantic = expectedSemanticEvidence :=
    represents.functional expectedRep
  simpa [semanticEq] using valid

private def rejectedArgumentMismatch : Bool :=
  match (resolve [convertSameRule] 1 (convert .word .bool)).outcome with
  | .noSolution => true
  | _ => false

private def fresheningAvoidsGoalCollision : Bool :=
  let goal := equality (.variable ⟨5⟩)
  let freshened := freshenRuleFor showBoxRule goal
  decide (freshened.head = showPredicate (box (.variable ⟨6⟩)) ∧
    freshened.wherePredicates = [equality (.variable ⟨6⟩)])

private def concreteImplDoesNotBindGoal : Bool :=
  decide (matchImplHead? equalityWordRule (equality (.variable ⟨5⟩)) = none)

/-- Execute the typed impl-head/unification bridge without umbrella registration. -/
def testTypedTraitResolution : IO Unit := do
  assertTrue successfulResolution
    "generic impl head did not instantiate its where predicate and evidence"
  assertTrue rejectedArgumentMismatch
    "full predicate arguments were not included in impl-head unification"
  assertTrue fresheningAvoidsGoalCollision
    "impl variables were not freshened away from goal variables"
  assertTrue concreteImplDoesNotBindGoal
    "a concrete impl silently bound a caller-owned goal variable"
  assertTrue (decide (matchImplHead? showBoxRule (showPredicate (box .word)) =
      some [equality .word]))
    "typed head matcher did not expose instantiated where predicates"
  assertTrue (decide (matchImplHeadWithParameters? [showBoxParameter]
      showBoxRule (showPredicate (box .word)) = some {
        parameterSubstitution := [(showBoxParameter, .word)]
        wherePredicates := [equality .word]
      }))
    "detailed head matching did not retain the canonical ground parameter"

end Tests.TypedTraitResolution
end
