import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedGeneralOrdinaryLambdaExpressionHeads
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedExpressionTreeBounds

/-! Accepted unrestricted ordinary formation and literal selected calls feed
the same existing expression support fold and finite dispatcher. Runtime literal
meaning comes from the actual Source ledger. Every heap retains supplied
functions; only formed closures are included forward. Strict extended-family
body children remain the shared measured IH, with independent Source grades. -/
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedGeneralOrdinaryLambdaExpressionRuntimeBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedGeneralOrdinaryLambdaExpressionHeads (Head)
open CallableIndexedOwnedGeneralOrdinaryLambdaFormationHeads (bridge model)
open CallableIndexedOwnedExtendedJointReadyContinuations (PreservingBelow ReflectingBelow)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  (caller : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))
  (context : SourceSemantics.Context) (evidence : Dynamic.EvidenceEnvironment)
  {source : TypedSource}
  {solved : List SolvedRequirement} {reasonAt : ExpressionId → Word} {fuel : Nat}

/-- The original Tree construction retains the genuine finite ordinary Head. -/
abbrev Tree : GenericExpressionMeaning.Certificate :=
  CompatibleExpressionCalls.Tree
    (Head (registry := registry) (faults := faults) caller context evidence)
    fuel (.initial compiled.compatible.checked) source context solved reasonAt

/-- The literal receipt is the actual original Source requirement ledger. -/
abbrev RuntimeTree : GenericExpressionMeaning.Certificate :=
  CompatibleExpressionCalls.Tree.WithLiterals
    (calls := Head (registry := registry) (faults := faults) caller context evidence) (fuel := fuel)
    (values := .initial compiled.compatible.checked) (source := source) (context := context)
    (solved := solved) (reasonAt := reasonAt)
    (fun _ id lowered => CompatibleExpressionLiteralRuntime.Certificate solved source id lowered)

variable
  (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
  (profile : compiled.compatible.checked.catalog.callableContracts = true)
  (functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  (inclusion : (CallableIndexedOwnedGeneralLambdaValues.model headers keys registry faults profile).Includes functions)
  (complete : RecursiveNamedCatalogNativeContexts.Complete (values := .initial compiled.compatible.checked)
    (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed) headers)
  (globals : caller.globals = compiled.indexed.base.globals.length)
  (prefixZero : owner.key.capturePrefix = 0)
  (slots : ∀ header, header ∈ headers → header.slot < compiled.indexed.base.globals.length)
  (extension : SourceCoreRawMetadata.Extends (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked).registry registry)
  {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
  (observations : CompatibleEquality.FunctionObservations compiled.compatible.checked.catalog
    functions identities)
  (functionTypes : FunctionRuntimeViews functions)
  (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
  (runtime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) context
    source)
  (covers : evidence.Covers context)
  (sameSource : source = CallableIndexedNamedGeneration.source caller.named)
  (unique : NodeOccurrencesUnique source)
  (uninitialized : ∀ id location, faults (.uninitializedLocation location) (reasonAt id))
  (missing : ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((reasonAt id).add tag))
  {certificates : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram) →
    SourceSemantics.Context → GenericExpressionMeaning.Certificate}
  {expressionSyntax : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram) → ExpressionId → Prop}

include inclusion complete globals prefixZero slots extension faithful observations functionTypes wellFormed runtime covers sameSource unique uninitialized missing in
theorem preserves_at_with_literals {literals : GenericExpressionMeaning.Certificate}
    (literalMeaning : GenericExpressionMeaning.Preserves
      (model (registry := registry) functions)
      (Program.ofChecked compiled.sourceProgram) context evidence
      source literals faults)
    (budget size : Nat) (within : size ≤ budget)
    (below : PreservingBelow (headers := headers) (keys := keys) (registry := registry) (faults := faults)
      (certificates := certificates) (expressionSyntax := expressionSyntax)
      functions wellFormed budget) :
    CallableIndexedOwnedAdmittedExpressionBounds.PreservesAt
      (bridge (headers := headers) caller owner)
      (model (registry := registry) functions)
      context evidence source
      (CompatibleExpressionCalls.Tree.WithLiterals
        (calls := Head (registry := registry) (faults := faults) caller context evidence) (fuel := fuel)
        (values := .initial compiled.compatible.checked)
        (source := source) (context := context)
        (solved := solved) (reasonAt := reasonAt) literals) faults size := by
  apply CallableIndexedOwnedAdmittedExpressionBounds.preserves_tree_at_with_literals
    functions
    (Head (registry := registry) (faults := faults) caller context evidence) budget size within
  · intro child _within
    exact CallableIndexedOwnedAdmittedExpressionBounds.PreservesAt.of_stateful
      wellFormed runtime covers
      (ProtectedStateTransition.PreservesAt.of_administrative _ _ _ _ _ _ _ _
        (CallableIndexedOwnedNestedCanonicalState.administrativeTransport (headers := headers) owner caller)
        (RecursiveNamedBoundedContracts.preserves_at_of_unbounded
          (ProtectedExpressionMeaning.preserves_of_typed _
            (CompatibleExpressionBuiltins.preserves_with_literals
              functions
              extension faithful observations functionTypes (Program.ofChecked compiled.sourceProgram)
              evidence unique uninitialized missing literalMeaning)) child))
  · intro certificate child childWithin children
    apply CallableIndexedOwnedAdmittedExpressionCallsHeads.preserves_at_with_calls
      (bridge (headers := headers) caller owner)
      (CallableIndexedOwnedNestedCanonicalState.administrativeTransport (headers := headers) owner caller)
      functions
      extension faithful observations functionTypes evidence unique missing wellFormed runtime covers
      (Head (registry := registry) (faults := faults) caller context evidence) budget child childWithin children
    exact CallableIndexedOwnedGeneralOrdinaryLambdaExpressionHeads.preserves_at
      caller context evidence owner profile functions inclusion complete globals slots prefixZero wellFormed runtime covers sameSource budget child childWithin
      (fun smaller strict => children smaller (Nat.le_of_lt strict)) below

include inclusion complete globals prefixZero slots extension faithful observations functionTypes wellFormed runtime covers sameSource unique uninitialized missing in
theorem reflects_at_with_literals {literals : GenericExpressionMeaning.Certificate}
    (literalMeaning : GenericExpressionMeaning.Reflects
      (model (registry := registry) functions)
      (Program.ofChecked compiled.sourceProgram) context evidence
      source literals faults)
    (budget size : Nat) (within : size ≤ budget)
    (below : ReflectingBelow (headers := headers) (keys := keys) (registry := registry) (faults := faults)
      (certificates := certificates) (expressionSyntax := expressionSyntax)
      functions wellFormed budget) :
    CallableIndexedOwnedAdmittedExpressionBounds.ReflectsAt
      (bridge (headers := headers) caller owner)
      (model (registry := registry) functions)
      context evidence source
      (CompatibleExpressionCalls.Tree.WithLiterals
        (calls := Head (registry := registry) (faults := faults) caller context evidence) (fuel := fuel)
        (values := .initial compiled.compatible.checked)
        (source := source) (context := context)
        (solved := solved) (reasonAt := reasonAt) literals) faults size := by
  apply CallableIndexedOwnedAdmittedExpressionBounds.reflects_tree_at_with_literals
    functions
    (Head (registry := registry) (faults := faults) caller context evidence) budget size within
  · intro child _within
    exact CallableIndexedOwnedAdmittedExpressionBounds.ReflectsAt.of_stateful
      wellFormed runtime covers
      (ProtectedStateTransition.ReflectsAt.of_administrative _ _ _ _ _ _ _ _
        (CallableIndexedOwnedNestedCanonicalState.administrativeTransport (headers := headers) owner caller)
        (RecursiveNamedBoundedContracts.reflects_at_of_unbounded
          (ProtectedExpressionMeaning.reflects_of_typed _
            (CompatibleExpressionBuiltins.reflects_with_literals
              functions
              extension faithful observations functionTypes (Program.ofChecked compiled.sourceProgram)
              evidence uninitialized missing literalMeaning)) child))
  · intro certificate child childWithin children
    apply CallableIndexedOwnedAdmittedExpressionCallsHeads.reflects_at_with_calls
      (bridge (headers := headers) caller owner)
      (CallableIndexedOwnedNestedCanonicalState.administrativeTransport (headers := headers) owner caller)
      functions
      extension faithful observations functionTypes evidence unique missing wellFormed runtime covers
      (Head (registry := registry) (faults := faults) caller context evidence) budget child childWithin children
    exact CallableIndexedOwnedGeneralOrdinaryLambdaExpressionHeads.reflects_at
      caller context evidence owner profile functions inclusion complete globals slots prefixZero wellFormed runtime covers sameSource budget child childWithin
      (fun smaller strict => children smaller (Nat.le_of_lt strict)) below

include inclusion complete globals prefixZero slots extension faithful observations functionTypes wellFormed runtime covers sameSource unique uninitialized missing in
/-- The runtime literal producer and concrete heads discharge expression
semantics internally through the original support fold. -/
theorem preserves_at_runtime (sameLedger : context.solvedRequirements = solved)
    (runtimeLedger : RuntimeRequirementLedgerValid context) (budget size : Nat) (within : size ≤ budget)
    (below : PreservingBelow (headers := headers) (keys := keys) (registry := registry) (faults := faults)
      (certificates := certificates) (expressionSyntax := expressionSyntax)
      functions wellFormed budget) :
    CallableIndexedOwnedAdmittedExpressionBounds.PreservesAt
      (bridge (headers := headers) caller owner)
      (model (registry := registry) functions)
      context evidence source
      (RuntimeTree (registry := registry) (faults := faults) (source := source) (solved := solved)
        (reasonAt := reasonAt) (fuel := fuel) caller context evidence) faults size := by
  exact preserves_at_with_literals caller context evidence owner profile functions inclusion complete globals prefixZero slots extension faithful observations
    functionTypes wellFormed runtime covers sameSource unique uninitialized missing
    (CompatibleExpressionLiteralRuntime.preserves
      functions
      (Program.ofChecked compiled.sourceProgram) context evidence sameLedger runtimeLedger unique faults)
    budget size within below

include inclusion complete globals prefixZero slots extension faithful observations functionTypes wellFormed runtime covers sameSource unique uninitialized missing in
/-- The runtime literal producer and concrete heads discharge expression
semantics internally through the original support fold. -/
theorem reflects_at_runtime (sameLedger : context.solvedRequirements = solved)
    (runtimeLedger : RuntimeRequirementLedgerValid context) (budget size : Nat) (within : size ≤ budget)
    (below : ReflectingBelow (headers := headers) (keys := keys) (registry := registry) (faults := faults)
      (certificates := certificates) (expressionSyntax := expressionSyntax)
      functions wellFormed budget) :
    CallableIndexedOwnedAdmittedExpressionBounds.ReflectsAt
      (bridge (headers := headers) caller owner)
      (model (registry := registry) functions)
      context evidence source
      (RuntimeTree (registry := registry) (faults := faults) (source := source) (solved := solved)
        (reasonAt := reasonAt) (fuel := fuel) caller context evidence) faults size := by
  exact reflects_at_with_literals caller context evidence owner profile functions inclusion complete globals prefixZero slots extension faithful observations
    functionTypes wellFormed runtime covers sameSource unique uninitialized missing
    (CompatibleExpressionLiteralRuntime.reflects
      functions
      (Program.ofChecked compiled.sourceProgram) context evidence sameLedger runtimeLedger source faults)
    budget size within below

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedGeneralOrdinaryLambdaExpressionRuntimeBounds
