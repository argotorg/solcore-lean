import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedSelectedPositiveLambdaPackets

/-! An actual used raw lambda occurrence constructs its tagged static compiler
packet, then the positive runtime formation leaf runs once. The fixed-prefix
native witness belongs to this same occurrence; the actual semantic admission
keeps the original Ordinary or Principal caller packet. No execution theorem is
accepted as static compiler input. The finite child occurrence factory remains
an explicit static construction obligation at the generated Receipt. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedEligibleSelectedLambdaCallBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedNamedGeneration CallableIndexedLambdaGeneration CallableIndexedLambdaValues
open CallableIndexedOwnedFunctionValues (Header Key OwnedKey)
open CallableIndexedOwnedContextualCompilerPolicyProfiles
open CallableIndexedOwnedSelectedDiagnosticIssuerReceipts (SelectedReceipt lowered)
open CallableIndexedOwnedPreparedNativeSiteShellReceipts (FiniteBodyReceipts)
open CallableIndexedOwnedPreparedNativeLambdaCompilerReceipts (Receipt)
open CallableIndexedOwnedPreparedCanonicalCaptureReceipts («prefix»)
open CallableIndexedOwnedPreparedNativeFamilyStaticQualification (OccurrenceFactory)
variable {compiled : SourceCoreUnifiedCompilation.Compiled}

/-- Only this literal occurrence is selected; no child or body meaning is stored. -/
def Point (scope : SourceCoreLocalCell.Scope) (id : ExpressionId)
    (lowered : SourceCoreBasic.LoweredExpr) : GenericExpressionMeaning.Certificate :=
  fun current expression code => current = scope ∧ expression = id ∧ code = lowered

namespace Ordinary
variable {caller : Header compiled (Program.ofChecked compiled.sourceProgram)} {index : Nat}
  (selected : SelectedReceipt compiled caller.named index)
  {rootFuel : Nat} {rootSource : TypedSource} {rootScope : SourceCoreLocalCell.Scope}
  {rootId : ExpressionId} {rootReasonAt : ExpressionId → Word} {rootLowered : SourceCoreBasic.LoweredExpr}
  (root : RootPolicyReceipt (compiled := compiled) caller.named (lowered compiled selected.diagnostics)
    selected.code selected.compilation rootFuel rootSource rootScope rootId rootReasonAt rootLowered)
  (expressionSyntax : TypedSource → ExpressionId → Prop)
  (headers : RecursiveNamedCatalog.Inventory compiled.indexed.ancestry (.initial compiled.compatible.checked)
    (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions (Program.ofChecked compiled.sourceProgram))
  {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment} {scope : SourceCoreLocalCell.Scope}
  (profile : compiled.compatible.checked.catalog.callableContracts = true)
  (runtime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) context (source caller.named))
  (covers : evidence.Covers context)
  (ownership : LocalIdentityOwnership (source caller.named))
  (declarations : CompatibleExpressionReads.ScopeDeclarations (source caller.named) scope context)
  (sameReason : rootReasonAt = selected.diagnostics.program.reasonAt caller.named.signature.key)
  (sameLedger : context.solvedRequirements = (CallableIndexedNamedGeneration.context compiled.indexed caller.named).solvedRequirements)
  {childFuel : Nat} {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr} {node : ExpressionNode}
  {parameters : List TypedBinder} {result : TypeSystem.Ty} {statements : List StatementId}
  {reported nativeType : Ty}
  (allowed : expressionSyntax (source caller.named) id)
  (found : (source caller.named).lookupExpression? id = some node)
  (form : node.form = .lambda parameters result statements)
  (certificate : CallableIndexedLambdaCertificates.Certificate root.selected.policy root.selected.lowerBody childFuel
    (CallableIndexedNamedGeneration.context compiled.indexed caller.named) (source caller.named) scope
    id node parameters result statements reported rootReasonAt lowered)
  (accepted : SourceCoreFunctions.lowerExpressionWithPolicy root.selected.policy root.selected.lowerBody (childFuel + 1)
    (CallableIndexedNamedGeneration.context compiled.indexed caller.named) (source caller.named) scope id rootReasonAt = .ok lowered)
  (sourceTyped : ExpressionHasType (source caller.named) context id node.type)
  (metadata : CompatibleExpressionReads.Metadata compiled.compatible.checked (source caller.named) id node lowered.type)
  (coercions : node.coercions = [])
  (raw : HasType (SourceCoreLocalCell.coreContext scope ++ «prefix» (compiled := compiled) caller.named)
    lowered.expression nativeType compiled.indexed.layouts.definitions)
  (finite : FiniteBodyReceipts (source caller.named) (expressionSyntax (source caller.named)) context parameters result statements)
  (occurrences : ∀ receipt : Receipt root expressionSyntax certificate (sourceContext := context) (evidence := evidence),
    receipt.shell.issued = CallableIndexedOwnedPreparedNativeSiteShellReceipts.issued_at_site selected receipt.site →
    OccurrenceFactory root expressionSyntax (some evidence) headers receipt.body.readFuel)
  {keys : List (Key compiled (Program.ofChecked compiled.sourceProgram))}
  {bodyRegistry registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  (owner : OwnedKey keys)
  (member : caller ∈ headers)
  (complete : RecursiveNamedCatalogNativeContexts.Complete
    (prepared := compiled.indexed.ancestry) (values := .initial compiled.compatible.checked)
    (program := Program.ofChecked compiled.sourceProgram)
    (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed) headers)
  (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
  (owners : CallableIndexedOwnedPreparedPositiveFunctionOrigins.OwnerCover headers keys bodyRegistry profile)

local notation "nativeFacet" => CallableIndexedOwnedPreparedSelectedNativeFamilyQualification.facet (compiled := compiled) headers
local notation "bridge" => CallableIndexedOwnedOrdinaryLambdaEntries.bridge (headers := headers) owner caller
local notation "model" => CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry
  (CallableIndexedOwnedPreparedPositiveFunctionOrigins.functions nativeFacet headers keys bodyRegistry faults profile)

include profile runtime covers ownership declarations sameReason sameLedger allowed found form certificate accepted sourceTyped
  metadata coercions raw finite occurrences member complete wellFormed owners in
/-- One static Receipt construction precedes one genuine preserves runtime leaf. -/
theorem preserves_at (size : Nat) :
    CallableIndexedOwnedAdmittedExpressionBounds.PreservesAt bridge model context evidence (source caller.named)
      (Point scope id lowered) faults size := by
  have compiled : CallableIndexedOwnedPreparedSelectedPositiveOrdinaryLambdaHeads.Lambdas selected root expressionSyntax headers
      (context := context) (evidence := evidence) (scope := scope) (fun _ _ _ => False) scope id lowered :=
    CallableIndexedOwnedPreparedSelectedPositiveLambdaPackets.Ordinary.of_compiler selected root expressionSyntax headers profile runtime covers
      ownership declarations sameReason sameLedger allowed found form certificate accepted sourceTyped metadata coercions raw finite occurrences
  intro current expression code certified currentNode
  obtain ⟨rfl, rfl, rfl⟩ := certified
  exact CallableIndexedOwnedPreparedSelectedPositiveOrdinaryLambdaHeads.preserves_at
    (profile := profile) (owners := owners) (member := member) (complete := complete)
    (wellFormed := wellFormed) (runtime := runtime) (covers := covers)
    selected root expressionSyntax headers owner size compiled (node := currentNode)

include profile runtime covers ownership declarations sameReason sameLedger allowed found form certificate accepted sourceTyped
  metadata coercions raw finite occurrences member complete wellFormed owners in
/-- One static Receipt construction precedes one genuine reflects runtime leaf. -/
theorem reflects_at (size : Nat) :
    CallableIndexedOwnedAdmittedExpressionBounds.ReflectsAt bridge model context evidence (source caller.named)
      (Point scope id lowered) faults size := by
  have compiled : CallableIndexedOwnedPreparedSelectedPositiveOrdinaryLambdaHeads.Lambdas selected root expressionSyntax headers
      (context := context) (evidence := evidence) (scope := scope) (fun _ _ _ => False) scope id lowered :=
    CallableIndexedOwnedPreparedSelectedPositiveLambdaPackets.Ordinary.of_compiler selected root expressionSyntax headers profile runtime covers
      ownership declarations sameReason sameLedger allowed found form certificate accepted sourceTyped metadata coercions raw finite occurrences
  intro current expression code certified currentNode
  obtain ⟨rfl, rfl, rfl⟩ := certified
  exact CallableIndexedOwnedPreparedSelectedPositiveOrdinaryLambdaHeads.reflects_at
    (profile := profile) (owners := owners) (member := member) (complete := complete)
    (wellFormed := wellFormed) (runtime := runtime) (covers := covers)
    selected root expressionSyntax headers owner size compiled (node := currentNode)

end Ordinary

namespace Principal
variable {method : ExecutableImplMethods.CheckedMethod}
  (principal : CallableIndexedOwnedMethodPrincipal.Principal compiled method)
  (selected : SelectedReceipt compiled principal.named principal.cached.index)
  {rootFuel : Nat} {rootSource : TypedSource} {rootScope : SourceCoreLocalCell.Scope}
  {rootId : ExpressionId} {rootReasonAt : ExpressionId → Word} {rootLowered : SourceCoreBasic.LoweredExpr}
  (root : RootPolicyReceipt (compiled := compiled) principal.named (lowered compiled selected.diagnostics)
    selected.code selected.compilation rootFuel rootSource rootScope rootId rootReasonAt rootLowered)
  (expressionSyntax : TypedSource → ExpressionId → Prop)
  (headers : RecursiveNamedCatalog.Inventory compiled.indexed.ancestry (.initial compiled.compatible.checked)
    (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions (Program.ofChecked compiled.sourceProgram))
  {context : SourceSemantics.Context} {scope : SourceCoreLocalCell.Scope}
  (profile : compiled.compatible.checked.catalog.callableContracts = true)
  (runtime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) context (source principal.named))
  (covers : principal.dictionary.Covers context)
  (ownership : LocalIdentityOwnership (source principal.named))
  (declarations : CompatibleExpressionReads.ScopeDeclarations (source principal.named) scope context)
  (sameLedger : context.solvedRequirements = (CallableIndexedNamedGeneration.context compiled.indexed principal.named).solvedRequirements)
  {childFuel : Nat} {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr} {node : ExpressionNode}
  {parameters : List TypedBinder} {result : TypeSystem.Ty} {statements : List StatementId}
  {reported nativeType : Ty}
  (allowed : expressionSyntax (source principal.named) id)
  (found : (source principal.named).lookupExpression? id = some node)
  (form : node.form = .lambda parameters result statements)
  (certificate : CallableIndexedLambdaCertificates.Certificate root.selected.policy root.selected.lowerBody childFuel
    (CallableIndexedNamedGeneration.context compiled.indexed principal.named) (source principal.named) scope
    id node parameters result statements reported rootReasonAt lowered)
  (accepted : SourceCoreFunctions.lowerExpressionWithPolicy root.selected.policy root.selected.lowerBody (childFuel + 1)
    (CallableIndexedNamedGeneration.context compiled.indexed principal.named) (source principal.named) scope id rootReasonAt = .ok lowered)
  (sourceTyped : ExpressionHasType (source principal.named) context id node.type)
  (metadata : CompatibleExpressionReads.Metadata compiled.compatible.checked (source principal.named) id node lowered.type)
  (coercions : node.coercions = [])
  (raw : HasType (SourceCoreLocalCell.coreContext scope ++ «prefix» (compiled := compiled) principal.named)
    lowered.expression nativeType compiled.indexed.layouts.definitions)
  (finite : FiniteBodyReceipts (source principal.named) (expressionSyntax (source principal.named)) context parameters result statements)
  (occurrences : ∀ receipt : Receipt root expressionSyntax certificate (sourceContext := context) (evidence := principal.dictionary),
    receipt.shell.issued = CallableIndexedOwnedPreparedNativeSiteShellReceipts.issued_at_site selected receipt.site →
    OccurrenceFactory root expressionSyntax (some principal.dictionary) headers receipt.body.readFuel)
  {keys : List (Key compiled (Program.ofChecked compiled.sourceProgram))}
  {bodyRegistry registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  (owner : OwnedKey keys)
  (complete : RecursiveNamedCatalogNativeContexts.Complete
    (prepared := compiled.indexed.ancestry) (values := .initial compiled.compatible.checked)
    (program := Program.ofChecked compiled.sourceProgram)
    (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed) headers)
  (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
  (owners : CallableIndexedOwnedPreparedPositiveFunctionOrigins.OwnerCover headers keys bodyRegistry profile)

local notation "nativeFacet" => CallableIndexedOwnedPreparedSelectedNativeFamilyQualification.facet (compiled := compiled) headers
local notation "bridge" => CallableIndexedOwnedMethodLambdaEntries.bridge (headers := headers) owner principal.named
local notation "model" => CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry
  (CallableIndexedOwnedPreparedPositiveFunctionOrigins.functions nativeFacet headers keys bodyRegistry faults profile)

include profile runtime covers ownership declarations sameLedger allowed found form certificate accepted sourceTyped
  metadata coercions raw finite occurrences complete wellFormed owners in
/-- One static Receipt construction precedes one genuine preserves runtime leaf. -/
theorem preserves_at (size : Nat) :
    CallableIndexedOwnedAdmittedExpressionBounds.PreservesAt bridge model context principal.dictionary (source principal.named)
      (Point scope id lowered) faults size := by
  have compiled : CallableIndexedOwnedPreparedSelectedPositivePrincipalLambdaHeads.Lambdas principal selected root expressionSyntax headers
      (context := context) (scope := scope) (fun _ _ _ => False) scope id lowered :=
    CallableIndexedOwnedPreparedSelectedPositiveLambdaPackets.Principal.of_compiler principal selected root expressionSyntax headers profile runtime covers
      ownership declarations sameLedger allowed found form certificate accepted sourceTyped metadata coercions raw finite occurrences
  intro current expression code certified currentNode
  obtain ⟨rfl, rfl, rfl⟩ := certified
  exact CallableIndexedOwnedPreparedSelectedPositivePrincipalLambdaHeads.preserves_at
    (profile := profile) (owners := owners) (complete := complete)
    (wellFormed := wellFormed) (runtime := runtime) (covers := covers)
    principal selected root expressionSyntax headers owner size compiled (node := currentNode)

include profile runtime covers ownership declarations sameLedger allowed found form certificate accepted sourceTyped
  metadata coercions raw finite occurrences complete wellFormed owners in
/-- One static Receipt construction precedes one genuine reflects runtime leaf. -/
theorem reflects_at (size : Nat) :
    CallableIndexedOwnedAdmittedExpressionBounds.ReflectsAt bridge model context principal.dictionary (source principal.named)
      (Point scope id lowered) faults size := by
  have compiled : CallableIndexedOwnedPreparedSelectedPositivePrincipalLambdaHeads.Lambdas principal selected root expressionSyntax headers
      (context := context) (scope := scope) (fun _ _ _ => False) scope id lowered :=
    CallableIndexedOwnedPreparedSelectedPositiveLambdaPackets.Principal.of_compiler principal selected root expressionSyntax headers profile runtime covers
      ownership declarations sameLedger allowed found form certificate accepted sourceTyped metadata coercions raw finite occurrences
  intro current expression code certified currentNode
  obtain ⟨rfl, rfl, rfl⟩ := certified
  exact CallableIndexedOwnedPreparedSelectedPositivePrincipalLambdaHeads.reflects_at
    (profile := profile) (owners := owners) (complete := complete)
    (wellFormed := wellFormed) (runtime := runtime) (covers := covers)
    principal selected root expressionSyntax headers owner size compiled (node := currentNode)

end Principal

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedEligibleSelectedLambdaCallBounds
