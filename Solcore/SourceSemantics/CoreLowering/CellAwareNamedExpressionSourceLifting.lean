import Solcore.SourceSemantics.CoreLowering.CellAwareNamedExpressionMeaning
import Solcore.SourceSemantics.CoreLowering.CellAwareSourceReadProductLifting
import Solcore.SourceSemantics.CoreLowering.CellAwareScopeSourceProductLifting
import Solcore.SourceSemantics.CoreLowering.CellAwareScopeSourceIndirectLifting

/-! The accepted finite expression tree lifts independent Source executions
through the actual mixed state and the selected call gates. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
namespace Solcore.SourceSemantics.CoreLowering.CellAwareNamedExpressionSourceLifting
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CellAwareNamedExpressionCertificates (Tree)
open CellAwareScopeSourceLiftBounds (LiftsAt)
universe u

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {named : SourceCoreGeneralFunctions.Function}
  {diagnostics : SourceCoreDataPlaceFaultSites.Program} {code : Expr}
  (generation : CallableIndexedNamedGeneration.Compilation compiled.indexed named diagnostics code)
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {bodyRegistry : SourceCoreRawMetadata.Registry} {semanticFaults : FunctionCalls.FaultRep}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
  (profile : compiled.compatible.checked.catalog.callableContracts = true)
  {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver compiled.indexed}
  (receiver : CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt compiled.indexed completion.entry
    completion.result.context.registry completion.result.extension completion.result.diagnostics)
  (extension : SourceCoreRawMetadata.Extends (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked).registry completion.result.context.registry)
  {context : SourceSemantics.Context} {invocation : Staging.Recursive.Scope}
  (authority : CellAwareNamedCallPorts.Authority (compiled := compiled) named invocation)
  (sourceEq : invocation.source = CallableIndexedNamedGeneration.source named)
  (issuer : CellAwareNamedDiagnosticIssuer.Named compiled.indexed named (diagnostics.reasonAt named.signature.key))
  (record : SourceCompilationPlan.exactSpecialization compiled.indexed.base.plan named.signature.key = .ok named.specialized)
  (sameLedger : context.solvedRequirements = (CallableIndexedNamedGeneration.context compiled.indexed named).solvedRequirements)
  (runtime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) context invocation.source)
  (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
  (covers : invocation.evidence.Covers context)

local notation "functions" => CellAwarePhysicalFunctionOrigins.functions headers keys bodyRegistry semanticFaults profile
local notation "model" => CompatibleAmbientHeap.payloadModel compiled.compatible.checked completion.result.context.registry functions
local notation "stages" => SelectedCompilationPhysicalProgramSupport.stages compiled
local notation "callFaults" => CallableIndexedOwnedPublicDecodedStagedCallFaults.faults completion.result.diagnostics


private def Point (scope : SourceCoreLocalCell.Scope) (id : ExpressionId)
    (lowered : SourceCoreBasic.LoweredExpr) : GenericExpressionMeaning.Certificate :=
  fun current child code => current = scope ∧ child = id ∧ code = lowered

private def Two (scope : SourceCoreLocalCell.Scope) (left right : ExpressionId)
    (first second : SourceCoreBasic.LoweredExpr) : GenericExpressionMeaning.Certificate :=
  fun current child code => current = scope ∧ ((child = left ∧ code = first) ∨ (child = right ∧ code = second))

include receiver extension authority sourceEq issuer record sameLedger runtime wellFormed covers in
private theorem preserve_tree {rootFuel : Nat} {scope : SourceCoreLocalCell.Scope} {id : ExpressionId}
    {lowered : SourceCoreBasic.LoweredExpr}
    (tree : Tree generation rootFuel invocation.source context (diagnostics.reasonAt named.signature.key) scope id lowered)
    (size : Nat) : CellAwareScopeExpressionBounds.PreservesAt bridge context model named stages invocation
      (Point scope id lowered) callFaults size := by
  intro current expression code point
  obtain ⟨rfl, rfl, rfl⟩ := point
  exact CellAwareNamedExpressionMeaning.preserves generation bridge profile receiver extension authority sourceEq issuer
    record sameLedger runtime wellFormed covers size ⟨rootFuel, by simpa only [sourceEq] using tree⟩

include receiver extension authority sourceEq issuer record sameLedger runtime wellFormed covers in
theorem tree {rootFuel : Nat} {scope : SourceCoreLocalCell.Scope} {id : ExpressionId}
    {lowered : SourceCoreBasic.LoweredExpr}
    (certificate : Tree generation rootFuel invocation.source context (diagnostics.reasonAt named.signature.key) scope id lowered)
    (size : Nat) : LiftsAt bridge context model named stages invocation (Point scope id lowered) size := by
  have unique := runtime.graph.nodeOccurrencesUnique
  induction certificate generalizing size with
  | plain receipt =>
    intro current expression code point node found typed mapping world administrative environment canonical actual actualContext
      before store embedding outcome after environments heaps locals agrees actualTyped initial admitted scopeAuthority physical owner ownerFrame trace
    obtain ⟨rfl, rfl, rfl⟩ := point
    exact .completed (CellAwareSourceReadProductLifting.exact_trace receipt unique trace.sound)
  | generalized receipt recipe =>
    intro current expression code point node found typed mapping world administrative environment canonical actual actualContext
      before store embedding outcome after environments heaps locals agrees actualTyped initial admitted scopeAuthority physical owner ownerFrame trace
    obtain ⟨rfl, rfl, rfl⟩ := point
    exact .completed (CellAwareSourceReadLifting.read unique receipt.observations.originalFound
      receipt.observations.originalForm receipt.observations.originalCoercions trace.sound)
  | @group id node inner innerNode lowered metadata form innerFound sourceType child ih =>
    intro current expression code point
    obtain ⟨rfl, rfl, rfl⟩ := point
    exact CellAwareScopeSourceProductLifting.group bridge model unique ih size
      (.actual metadata form innerFound sourceType ⟨rfl, rfl, rfl⟩)
  | @pair id node left right leftNode rightNode first second metadata form leftFound rightFound sourceType
      leftTree rightTree leftIH rightIH =>
    have children : ∀ size, LiftsAt bridge context model named stages invocation
        (Two scope left right first second) size := by
      intro childSize current expression code point
      obtain ⟨rfl, alternative⟩ := point
      cases alternative with
      | inl left => obtain ⟨rfl, rfl⟩ := left; exact leftIH childSize ⟨rfl, rfl, rfl⟩
      | inr right => obtain ⟨rfl, rfl⟩ := right; exact rightIH childSize ⟨rfl, rfl, rfl⟩
    have preservation : ∀ size, CellAwareScopeExpressionBounds.PreservesAt bridge context model named stages invocation
        (Two scope left right first second) callFaults size := by
      intro childSize current expression code point
      obtain ⟨rfl, alternative⟩ := point
      cases alternative with
      | inl left =>
        obtain ⟨rfl, rfl⟩ := left
        exact preserve_tree generation bridge profile receiver extension authority sourceEq issuer record sameLedger
          runtime wellFormed covers leftTree childSize ⟨rfl, rfl, rfl⟩
      | inr right =>
        obtain ⟨rfl, rfl⟩ := right
        exact preserve_tree generation bridge profile receiver extension authority sourceEq issuer record sameLedger
          runtime wellFormed covers rightTree childSize ⟨rfl, rfl, rfl⟩
    intro current expression code point
    obtain ⟨rfl, rfl, rfl⟩ := point
    exact CellAwareScopeSourceProductLifting.pair bridge model unique children preservation size
      (.actual metadata form leftFound rightFound sourceType
        ⟨rfl, .inl ⟨rfl, rfl⟩⟩ ⟨rfl, .inr ⟨rfl, rfl⟩⟩)
  | @call id callee ids metadata fuel lowered types compiler calleeReceipt calleeRecipe parent sequence children ih =>
    have childLift : ∀ childSize, childSize < size → LiftsAt bridge context model named stages invocation
        (RecursiveStageTupleMeaning.Entries scope compiler.entries) childSize := by
      intro childSize _smaller current expression code entry
      obtain ⟨rfl, member⟩ := entry
      exact ih expression code member childSize ⟨rfl, rfl, rfl⟩
    have preservation : ∀ childSize, CellAwareScopeExpressionBounds.PreservesAt bridge context model named stages invocation
        (RecursiveStageTupleMeaning.Entries scope compiler.entries) callFaults childSize := by
      intro childSize current expression code entry
      obtain ⟨rfl, member⟩ := entry
      exact preserve_tree generation bridge profile receiver extension authority sourceEq issuer record sameLedger
        runtime wellFormed covers (children expression code member) childSize ⟨rfl, rfl, rfl⟩
    obtain ⟨port⟩ := CellAwareNamedCallPorts.port generation compiler authority rfl parent calleeReceipt
    have catalog : SignatureCatalogWellFormed context.signatures := runtime.signatures.symm ▸ wellFormed.signatures
    intro current expression code point
    obtain ⟨rfl, rfl, rfl⟩ := point
    exact CellAwareScopeSourceIndirectLifting.indirect (bodyRegistry := bodyRegistry) (semanticFaults := semanticFaults) bridge profile compiler port runtime unique size
      calleeReceipt calleeRecipe sequence childLift preservation
      (CellAwareNamedGeneralizedReadBounds.preserves bridge profile unique runtime.requirements.idsUnique covers catalog) ⟨rfl, rfl, rfl⟩

include receiver extension authority sourceEq issuer record sameLedger runtime wellFormed covers in
theorem lifts (size : Nat) : LiftsAt bridge context model named stages invocation
    (CellAwareNamedBodyProducer.Certificate generation context) size := by
  intro scope id lowered certificate
  obtain ⟨rootFuel, actual⟩ := certificate
  rw [← sourceEq] at actual
  exact tree generation bridge profile receiver extension authority sourceEq issuer record sameLedger runtime
    wellFormed covers actual size ⟨rfl, rfl, rfl⟩

end Solcore.SourceSemantics.CoreLowering.CellAwareNamedExpressionSourceLifting
