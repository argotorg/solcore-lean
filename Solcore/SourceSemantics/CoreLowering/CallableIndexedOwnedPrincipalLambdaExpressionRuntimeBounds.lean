import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPrincipalLambdaExpressionHeads
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedMethodLambdaExpressionRuntimeBounds
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedExpressionTreeBounds

/-! The original expression support fold consumes authentic principal-lambda
formation and selected-call heads. Formed closures retain their actual globals
and leading bundle in the shared model. Runtime literal meaning is internal;
all heaps use the caller's function model and body children use its strict IH. -/
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPrincipalLambdaExpressionRuntimeBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedMethodLambdaExpressionHeads (bridge Head)
open CallableIndexedOwnedPrincipalLambdaExpressionHeads (model)
open CallableIndexedOwnedExtendedJointReadyContinuations (PreservingBelow ReflectingBelow)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  {method : ExecutableImplMethods.CheckedMethod}
  (principal : CallableIndexedOwnedMethodPrincipal.Principal compiled method)
  (context : SourceSemantics.Context)
  {solved : List SolvedRequirement} {reasonAt : ExpressionId → Word} {fuel : Nat}

/-- Certificate identity is the original static compiler Tree. -/
abbrev Tree : GenericExpressionMeaning.Certificate :=
  CallableIndexedOwnedMethodLambdaExpressionRuntimeBounds.Tree (registry := registry) (faults := faults)
    (solved := solved) (reasonAt := reasonAt) (fuel := fuel) principal context

/-- Runtime literal receipts remain the original static certificate family. -/
abbrev RuntimeTree : GenericExpressionMeaning.Certificate :=
  CallableIndexedOwnedMethodLambdaExpressionRuntimeBounds.RuntimeTree (registry := registry) (faults := faults)
    (solved := solved) (reasonAt := reasonAt) (fuel := fuel) principal context

variable
  (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
  (profile : compiled.compatible.checked.catalog.callableContracts = true)
  (functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  (inclusion : (CallableIndexedOwnedGeneralLambdaValues.model headers keys registry faults profile).Includes functions)
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
  (uninitialized : ∀ id location, faults (.uninitializedLocation location) (reasonAt id))
  (missing : ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((reasonAt id).add tag))
  {certificates : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram) →
    SourceSemantics.Context → GenericExpressionMeaning.Certificate}
  {expressionSyntax : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram) → ExpressionId → Prop}

include inclusion complete slots extension faithful observations functionTypes wellFormed runtime covers unique uninitialized missing in
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
        (calls := Head (registry := registry) (faults := faults) principal context) (fuel := fuel)
        (values := .initial compiled.compatible.checked)
        (source := CallableIndexedNamedGeneration.source principal.named) (context := context)
        (solved := solved) (reasonAt := reasonAt) literals) faults size := by
  apply CallableIndexedOwnedAdmittedExpressionBounds.preserves_tree_at_with_literals
    functions
    (Head (registry := registry) (faults := faults) principal context) budget size within
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
      (Head (registry := registry) (faults := faults) principal context) budget child childWithin children
    exact CallableIndexedOwnedPrincipalLambdaExpressionHeads.preserves_at
      principal context owner profile functions inclusion complete slots wellFormed runtime covers budget child childWithin
      (fun smaller strict => children smaller (Nat.le_of_lt strict)) below

include inclusion complete slots extension faithful observations functionTypes wellFormed runtime covers unique uninitialized missing in
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
        (calls := Head (registry := registry) (faults := faults) principal context) (fuel := fuel)
        (values := .initial compiled.compatible.checked)
        (source := CallableIndexedNamedGeneration.source principal.named) (context := context)
        (solved := solved) (reasonAt := reasonAt) literals) faults size := by
  apply CallableIndexedOwnedAdmittedExpressionBounds.reflects_tree_at_with_literals
    functions
    (Head (registry := registry) (faults := faults) principal context) budget size within
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
      (Head (registry := registry) (faults := faults) principal context) budget child childWithin children
    exact CallableIndexedOwnedPrincipalLambdaExpressionHeads.reflects_at
      principal context owner profile functions inclusion complete slots wellFormed runtime covers budget child childWithin
      (fun smaller strict => children smaller (Nat.le_of_lt strict)) below

include inclusion complete slots extension faithful observations functionTypes wellFormed runtime covers unique uninitialized missing in
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
      (RuntimeTree (registry := registry) (faults := faults) (solved := solved)
        (reasonAt := reasonAt) (fuel := fuel) principal context) faults size := by
  exact preserves_at_with_literals principal context owner profile functions inclusion complete slots extension faithful observations
    functionTypes wellFormed runtime covers unique uninitialized missing
    (CompatibleExpressionLiteralRuntime.preserves
      functions
      (Program.ofChecked compiled.sourceProgram) context principal.dictionary sameLedger runtimeLedger unique faults)
    budget size within below

include inclusion complete slots extension faithful observations functionTypes wellFormed runtime covers unique uninitialized missing in
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
      (RuntimeTree (registry := registry) (faults := faults) (solved := solved)
        (reasonAt := reasonAt) (fuel := fuel) principal context) faults size := by
  exact reflects_at_with_literals principal context owner profile functions inclusion complete slots extension faithful observations
    functionTypes wellFormed runtime covers unique uninitialized missing
    (CompatibleExpressionLiteralRuntime.reflects
      functions
      (Program.ofChecked compiled.sourceProgram) context principal.dictionary sameLedger runtimeLedger (CallableIndexedNamedGeneration.source principal.named) faults)
    budget size within below

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPrincipalLambdaExpressionRuntimeBounds
