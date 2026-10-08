import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedGeneralMethodMixedExpressionHeads
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedMethodMixedExpressionRuntimeBounds
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedExpressionTreeBounds

/-! Original mixed named/method certificates run with complete principal
lambda provenance under one supplied function model. The same expression Tree
fold and finite dispatcher consume authentic heads and internally constructed
runtime literals. Strict original family children supply only the body IH. -/
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedGeneralMethodMixedExpressionRuntimeBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedMethodLambdaExpressionHeads (bridge)
open CallableIndexedOwnedGeneralMethodMixedExpressionHeads (Head)
open CallableIndexedOwnedPrincipalLambdaExpressionHeads (model)
open CallableIndexedOwnedExtendedJointReadyContinuations (PreservingBelow ReflectingBelow)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  {method : ExecutableImplMethods.CheckedMethod}
  (principal : CallableIndexedOwnedMethodPrincipal.Principal compiled method)
  (context : SourceSemantics.Context) (compilation : SourceCoreFunctions.Context)
  {solved : List SolvedRequirement} {reasonAt : ExpressionId → Word} {fuel : Nat}

/-- The same original Tree uses the unchanged genuine finite Head sum. -/
abbrev Tree : GenericExpressionMeaning.Certificate :=
  CallableIndexedOwnedMethodMixedExpressionRuntimeBounds.Tree
    (headers := headers) (registry := registry) (faults := faults) (solved := solved)
    (reasonAt := reasonAt) (fuel := fuel) principal context compilation

/-- Runtime literals keep the same original actual requirement ledger. -/
abbrev RuntimeTree : GenericExpressionMeaning.Certificate :=
  CallableIndexedOwnedMethodMixedExpressionRuntimeBounds.RuntimeTree
    (headers := headers) (registry := registry) (faults := faults) (solved := solved)
    (reasonAt := reasonAt) (fuel := fuel) principal context compilation

variable
  (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
  (profile : compiled.compatible.checked.catalog.callableContracts = true)
  (functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  (inclusion : (CallableIndexedOwnedGeneralLambdaValues.model headers keys registry faults profile).Includes functions)
  (prefixOne : compilation.administrativePrefix = 1)
  (prefixZero : owner.key.capturePrefix = 0)
  (globalCounts : ∀ header, header ∈ headers → header.globals = compiled.indexed.base.globals.length)
  (complete : RecursiveNamedCatalogNativeContexts.Complete (values := .initial compiled.compatible.checked)
    (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed) headers)
  (slots : ∀ header, header ∈ headers → header.slot < compiled.indexed.base.globals.length)
  (extension : SourceCoreRawMetadata.Extends (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked).registry registry)
  {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
  (observations : CompatibleEquality.FunctionObservations compiled.compatible.checked.catalog
    functions identities)
  (functionTypes : FunctionRuntimeViews functions)
  (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
  (runtime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) context
    (CallableIndexedNamedGeneration.source principal.named))
  (covers : principal.dictionary.Covers context)
  (unique : NodeOccurrencesUnique (CallableIndexedNamedGeneration.source principal.named))
  (owners : ((Program.ofChecked compiled.sourceProgram).functions.map (fun definition => definition.body.owner)).Nodup)
  (idsUnique : RequirementIdsUnique context)
  (uninitialized : ∀ id location, faults (.uninitializedLocation location) (reasonAt id))
  (missing : ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((reasonAt id).add tag))
  {certificates : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram) →
    SourceSemantics.Context → GenericExpressionMeaning.Certificate}
  {expressionSyntax : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram) → ExpressionId → Prop}

  (sameLayouts : ∀ header, header ∈ headers → header.layouts = compiled.indexed.layouts)
  (escaped : ∀ header, header ∈ headers → faults .controlEscapedFunction header.escaped)
  (profiles : ∀ header, header ∈ headers → CallableIndexedOwnedAdmittedNamedExpressionHeads.ProfilesFor
    (headers := headers) (owner := owner) (functions := functions) (registry := registry) (faults := faults)
    (certificates := certificates) (expressionSyntax := expressionSyntax)
    (diagnosticPolicy := .reachable) (runtime := true) header)
  (syntaxTrees : ∀ header, header ∈ headers → GenericImperativeMatch.Syntax header.function.source
    (expressionSyntax header) header.context (.statements true header.function.body) header.function.resultType)

include inclusion prefixOne prefixZero globalCounts complete slots extension faithful observations functionTypes
  wellFormed runtime covers unique uninitialized missing sameLayouts escaped profiles syntaxTrees owners idsUnique in
theorem preserves_at_with_literals {literals : GenericExpressionMeaning.Certificate}
    (literalMeaning : GenericExpressionMeaning.Preserves
      (model (registry := registry) functions)
      (Program.ofChecked compiled.sourceProgram) context principal.dictionary
      (CallableIndexedNamedGeneration.source principal.named) literals faults)
    (budget size : Nat) (within : size ≤ budget)
    (below : PreservingBelow (headers := headers) (keys := keys) (registry := registry) (faults := faults)
      (certificates := certificates) (expressionSyntax := expressionSyntax)
      functions wellFormed budget) :
    CallableIndexedOwnedAdmittedExpressionBounds.PreservesAt
      (bridge (headers := headers) principal owner)
      (model (registry := registry) functions)
      context principal.dictionary (CallableIndexedNamedGeneration.source principal.named)
      (CompatibleExpressionCalls.Tree.WithLiterals
        (calls := Head (headers := headers) (registry := registry) (faults := faults) principal context compilation) (fuel := fuel)
        (values := .initial compiled.compatible.checked)
        (source := CallableIndexedNamedGeneration.source principal.named) (context := context)
        (solved := solved) (reasonAt := reasonAt) literals) faults size := by
  apply CallableIndexedOwnedAdmittedExpressionBounds.preserves_tree_at_with_literals
    functions
    (Head (headers := headers) (registry := registry) (faults := faults) principal context compilation) budget size within
  · intro child _within
    exact CallableIndexedOwnedAdmittedExpressionBounds.PreservesAt.of_stateful
      wellFormed runtime covers
      (ProtectedStateTransition.PreservesAt.of_administrative _ _ _ _ _ _ _ _
        (CallableIndexedOwnedOriginCanonicalState.administrativeTransport (headers := headers) owner principal.named)
        (RecursiveNamedBoundedContracts.preserves_at_of_unbounded
          (ProtectedExpressionMeaning.preserves_of_typed _
            (CompatibleExpressionBuiltins.preserves_with_literals
              functions
              extension faithful observations functionTypes (Program.ofChecked compiled.sourceProgram)
              principal.dictionary unique uninitialized missing literalMeaning)) child))
  · intro certificate child childWithin children
    apply CallableIndexedOwnedAdmittedExpressionCallsHeads.preserves_at_with_calls
      (bridge (headers := headers) principal owner)
      (CallableIndexedOwnedOriginCanonicalState.administrativeTransport (headers := headers) owner principal.named)
      functions
      extension faithful observations functionTypes principal.dictionary unique missing wellFormed runtime covers
      (Head (headers := headers) (registry := registry) (faults := faults) principal context compilation) budget child childWithin children
    exact CallableIndexedOwnedGeneralMethodMixedExpressionHeads.preserves_at
      (principal := principal) (context := context) (compilation := compilation) (owner := owner)
      (profile := profile) (functions := functions) (inclusion := inclusion) (prefixOne := prefixOne)
      (prefixZero := prefixZero) (globalCounts := globalCounts) (complete := complete) (slots := slots)
      (wellFormed := wellFormed) (runtime := runtime) (covers := covers) (unique := unique)
      (owners := owners) (idsUnique := idsUnique) (sameLayouts := sameLayouts) (escaped := escaped)
      (profiles := profiles) (syntaxTrees := syntaxTrees) budget child childWithin
      (fun smaller strict => children smaller (Nat.le_of_lt strict)) below

include inclusion prefixOne prefixZero globalCounts complete slots extension faithful observations functionTypes
  wellFormed runtime covers unique uninitialized missing sameLayouts escaped profiles syntaxTrees in
theorem reflects_at_with_literals {literals : GenericExpressionMeaning.Certificate}
    (literalMeaning : GenericExpressionMeaning.Reflects
      (model (registry := registry) functions)
      (Program.ofChecked compiled.sourceProgram) context principal.dictionary
      (CallableIndexedNamedGeneration.source principal.named) literals faults)
    (budget size : Nat) (within : size ≤ budget)
    (below : ReflectingBelow (headers := headers) (keys := keys) (registry := registry) (faults := faults)
      (certificates := certificates) (expressionSyntax := expressionSyntax)
      functions wellFormed budget) :
    CallableIndexedOwnedAdmittedExpressionBounds.ReflectsAt
      (bridge (headers := headers) principal owner)
      (model (registry := registry) functions)
      context principal.dictionary (CallableIndexedNamedGeneration.source principal.named)
      (CompatibleExpressionCalls.Tree.WithLiterals
        (calls := Head (headers := headers) (registry := registry) (faults := faults) principal context compilation) (fuel := fuel)
        (values := .initial compiled.compatible.checked)
        (source := CallableIndexedNamedGeneration.source principal.named) (context := context)
        (solved := solved) (reasonAt := reasonAt) literals) faults size := by
  apply CallableIndexedOwnedAdmittedExpressionBounds.reflects_tree_at_with_literals
    functions
    (Head (headers := headers) (registry := registry) (faults := faults) principal context compilation) budget size within
  · intro child _within
    exact CallableIndexedOwnedAdmittedExpressionBounds.ReflectsAt.of_stateful
      wellFormed runtime covers
      (ProtectedStateTransition.ReflectsAt.of_administrative _ _ _ _ _ _ _ _
        (CallableIndexedOwnedOriginCanonicalState.administrativeTransport (headers := headers) owner principal.named)
        (RecursiveNamedBoundedContracts.reflects_at_of_unbounded
          (ProtectedExpressionMeaning.reflects_of_typed _
            (CompatibleExpressionBuiltins.reflects_with_literals
              functions
              extension faithful observations functionTypes (Program.ofChecked compiled.sourceProgram)
              principal.dictionary uninitialized missing literalMeaning)) child))
  · intro certificate child childWithin children
    apply CallableIndexedOwnedAdmittedExpressionCallsHeads.reflects_at_with_calls
      (bridge (headers := headers) principal owner)
      (CallableIndexedOwnedOriginCanonicalState.administrativeTransport (headers := headers) owner principal.named)
      functions
      extension faithful observations functionTypes principal.dictionary unique missing wellFormed runtime covers
      (Head (headers := headers) (registry := registry) (faults := faults) principal context compilation) budget child childWithin children
    exact CallableIndexedOwnedGeneralMethodMixedExpressionHeads.reflects_at
      (principal := principal) (context := context) (compilation := compilation) (owner := owner)
      (profile := profile) (functions := functions) (inclusion := inclusion) (prefixOne := prefixOne)
      (prefixZero := prefixZero) (globalCounts := globalCounts) (complete := complete) (slots := slots)
      (wellFormed := wellFormed) (runtime := runtime) (covers := covers) (unique := unique)
      (sameLayouts := sameLayouts) (escaped := escaped)
      (profiles := profiles) (syntaxTrees := syntaxTrees) budget child childWithin
      (fun smaller strict => children smaller (Nat.le_of_lt strict)) below

include inclusion prefixOne prefixZero globalCounts complete slots extension faithful observations functionTypes
  wellFormed runtime covers unique uninitialized missing sameLayouts escaped profiles syntaxTrees owners idsUnique in
/-- The runtime literal producer and concrete heads discharge expression
semantics internally through the original support fold. -/
theorem preserves_at_runtime (sameLedger : context.solvedRequirements = solved)
    (runtimeLedger : RuntimeRequirementLedgerValid context) (budget size : Nat) (within : size ≤ budget)
    (below : PreservingBelow (headers := headers) (keys := keys) (registry := registry) (faults := faults)
      (certificates := certificates) (expressionSyntax := expressionSyntax)
      functions wellFormed budget) :
    CallableIndexedOwnedAdmittedExpressionBounds.PreservesAt
      (bridge (headers := headers) principal owner)
      (model (registry := registry) functions)
      context principal.dictionary (CallableIndexedNamedGeneration.source principal.named)
      (RuntimeTree (headers := headers) (registry := registry) (faults := faults) (solved := solved)
        (reasonAt := reasonAt) (fuel := fuel) principal context compilation) faults size := by
  exact preserves_at_with_literals
    (principal := principal) (context := context) (compilation := compilation) (owner := owner)
    (profile := profile) (functions := functions) (inclusion := inclusion) (prefixOne := prefixOne)
    (prefixZero := prefixZero) (globalCounts := globalCounts) (complete := complete) (slots := slots)
    (extension := extension) (faithful := faithful) (observations := observations) (functionTypes := functionTypes)
    (wellFormed := wellFormed) (runtime := runtime) (covers := covers) (unique := unique)
    (owners := owners) (idsUnique := idsUnique) (uninitialized := uninitialized) (missing := missing)
    (sameLayouts := sameLayouts) (escaped := escaped) (profiles := profiles) (syntaxTrees := syntaxTrees)
    (CompatibleExpressionLiteralRuntime.preserves
      functions
      (Program.ofChecked compiled.sourceProgram) context principal.dictionary sameLedger runtimeLedger unique faults)
    budget size within below

include inclusion prefixOne prefixZero globalCounts complete slots extension faithful observations functionTypes
  wellFormed runtime covers unique uninitialized missing sameLayouts escaped profiles syntaxTrees in
/-- The runtime literal producer and concrete heads discharge expression
semantics internally through the original support fold. -/
theorem reflects_at_runtime (sameLedger : context.solvedRequirements = solved)
    (runtimeLedger : RuntimeRequirementLedgerValid context) (budget size : Nat) (within : size ≤ budget)
    (below : ReflectingBelow (headers := headers) (keys := keys) (registry := registry) (faults := faults)
      (certificates := certificates) (expressionSyntax := expressionSyntax)
      functions wellFormed budget) :
    CallableIndexedOwnedAdmittedExpressionBounds.ReflectsAt
      (bridge (headers := headers) principal owner)
      (model (registry := registry) functions)
      context principal.dictionary (CallableIndexedNamedGeneration.source principal.named)
      (RuntimeTree (headers := headers) (registry := registry) (faults := faults) (solved := solved)
        (reasonAt := reasonAt) (fuel := fuel) principal context compilation) faults size := by
  exact reflects_at_with_literals
    (principal := principal) (context := context) (compilation := compilation) (owner := owner)
    (profile := profile) (functions := functions) (inclusion := inclusion) (prefixOne := prefixOne)
    (prefixZero := prefixZero) (globalCounts := globalCounts) (complete := complete) (slots := slots)
    (extension := extension) (faithful := faithful) (observations := observations) (functionTypes := functionTypes)
    (wellFormed := wellFormed) (runtime := runtime) (covers := covers) (unique := unique)
    (uninitialized := uninitialized) (missing := missing)
    (sameLayouts := sameLayouts) (escaped := escaped) (profiles := profiles) (syntaxTrees := syntaxTrees)
    (CompatibleExpressionLiteralRuntime.reflects
      functions
      (Program.ofChecked compiled.sourceProgram) context principal.dictionary sameLedger runtimeLedger (CallableIndexedNamedGeneration.source principal.named) faults)
    budget size within below

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedGeneralMethodMixedExpressionRuntimeBounds
