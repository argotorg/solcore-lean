import Solcore.SourceSemantics.CoreLowering.Internal.OwnedPrepared.FormationReceipts
import Solcore.SourceSemantics.CoreLowering.Internal.Owned.NestedEntries
import Solcore.SourceSemantics.CoreLowering.Internal.Owned.FunctionValuesAndState
import Solcore.SourceSemantics.CoreLowering.Internal.Compatible.ExpressionRuntime
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedPrepared.NativeLambdas
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedPrepared.CatalogTerminalClosures
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedPrepared.AcceptedPackets
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedPrepared.OrdinaryLambdas
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedPrepared.OrdinaryCatalog
import Solcore.SourceSemantics.CoreLowering.Internal.RecursiveNamed.PublicRoots
import Solcore.SourceSemantics.CoreLowering.Internal.RecursiveNamed.PublicActualRegistry
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedPrepared.NamedLambdaFormation
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedStaged.IndexDiagnostics
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedPrepared.LambdaBodySupport
import Solcore.SourceSemantics.CoreLowering.Internal.Callable.LambdaViewTrees

/-!
# Prepared callables: eligible selected lambdas

Eligible selected lambdas, native family flow steps and same-policy producers, with the catalog's public admission.
-/

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedPairedReachedNativeExpressionTreeBounds
/-! The same compiler Tree and LiteralSites induction retains native typing
at the actual administrative context and at a genuine fixed compiler prefix.
Each original head is inverted at both contexts. One ordered child inventory
carries both independent witnesses; unused child slots receive neither.

Semantic admission uses the actual context. A lambda call leaf can use the
fixed witness to construct its authentic selected compiler receipt without
rebasing arbitrary body-state typing. No Tree or execution law is a static
input; the remaining raw call alternatives consume the strict body family.
-/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedPairedReachedNativeExpressionTreeBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedNamedGeneration CallableIndexedLambdaGeneration CallableIndexedLambdaValues
open CallableIndexedOwnedContextualCompilerPolicyProfiles
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedPreparedExpressionNativeChildren (WithRaw)
open CallableIndexedOwnedPreparedNativeAssignmentChildren (RawTyped)

universe u
variable {compiled : SourceCoreUnifiedCompilation.Compiled} {named : Named}
  {diagnostics : SourceCoreDataPlaceFaultSites.Program} {namedCode : Expr}
  {compilation : Compilation compiled.indexed named diagnostics namedCode}
  {rootFuel : Nat} {rootSource : TypedSource} {rootScope : SourceCoreLocalCell.Scope}
  {rootId : ExpressionId} {rootReasonAt : ExpressionId → Word} {rootLowered : SourceCoreBasic.LoweredExpr}
  (root : RootPolicyReceipt (compiled := compiled) named diagnostics namedCode compilation
    rootFuel rootSource rootScope rootId rootReasonAt rootLowered)
  (expressionSyntax : TypedSource → ExpressionId → Prop)
  {sourceContext : SourceSemantics.Context} {compilerScope : SourceCoreLocalCell.Scope}
  (callerEvidence : Option Dynamic.EvidenceEnvironment)
  (inventory : RecursiveNamedCatalog.Inventory compiled.indexed.ancestry (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked)
    (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions (Program.ofChecked compiled.sourceProgram))
  (administrative : Core.Context)
  (fixedAdministrative : Core.Context)

/-- Static raw typing at the literal occurrence context. It has no runtime
or Source typing conclusion. The arbitrary native result remains existential. -/
def NativeAt (certificate : GenericExpressionMeaning.Certificate) : GenericExpressionMeaning.Certificate :=
  fun scope id lowered => certificate scope id lowered ∧
    RawTyped (SourceCoreLocalCell.coreContext scope ++ administrative)
      lowered.expression compiled.indexed.layouts.definitions ∧
    RawTyped (SourceCoreLocalCell.coreContext scope ++ fixedAdministrative)
      lowered.expression compiled.indexed.layouts.definitions

/-- Both witnesses belong to the same used child. Native result types stay independent. -/
def WithBoth (administrative fixedAdministrative : Core.Context)
    (scope : SourceCoreLocalCell.Scope) (definitions : DataEnvironment)
    (children : GenericExpressionMeaning.Certificate) : GenericExpressionMeaning.Certificate :=
  WithRaw (SourceCoreLocalCell.coreContext scope ++ fixedAdministrative) definitions
    (WithRaw (SourceCoreLocalCell.coreContext scope ++ administrative) definitions children)

private abbrev rawCalls : CompatibleExpressionCalls.CallHeads :=
  CallableIndexedOwnedPreparedRawCompilerHeads.Head root expressionSyntax callerEvidence inventory
    (sourceContext := sourceContext) (scope := compilerScope)

/-- Each call carries the same authentic static receipt and its own local raw
typing. In particular the zero-child lambda still retains parent typing. -/
abbrev NativeCalls (children : GenericExpressionMeaning.Certificate) : GenericExpressionMeaning.Certificate :=
  NativeAt (compiled := compiled) administrative fixedAdministrative (rawCalls (sourceContext := sourceContext) (compilerScope := compilerScope) root expressionSyntax callerEvidence inventory children)

private def pointCertificate (scope : SourceCoreLocalCell.Scope) (id : ExpressionId)
    (lowered : SourceCoreBasic.LoweredExpr) : GenericExpressionMeaning.Certificate :=
  fun current expression code => current = scope ∧ expression = id ∧ code = lowered

/-- Only actual used child slots are strengthened by the same parent typing.
The additional call field is that parent witness, not a child/body law. -/
theorem native_head {children : GenericExpressionMeaning.Certificate}
    {scope : SourceCoreLocalCell.Scope} {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}
    {nativeType : Ty}
    (head : CompatibleExpressionCalls.Head (rawCalls (sourceContext := sourceContext) (compilerScope := compilerScope) root expressionSyntax callerEvidence inventory)
      (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked) (source named) sourceContext rootReasonAt children scope id lowered)
    (typed : HasType (SourceCoreLocalCell.coreContext scope ++ administrative)
      lowered.expression nativeType compiled.indexed.layouts.definitions)
    {fixedType : Ty}
    (fixedTyped : HasType (SourceCoreLocalCell.coreContext scope ++ fixedAdministrative)
      lowered.expression fixedType compiled.indexed.layouts.definitions) :
    CompatibleExpressionCalls.Head (NativeCalls (sourceContext := sourceContext) (compilerScope := compilerScope) root expressionSyntax callerEvidence inventory administrative fixedAdministrative)
      (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked) (source named) sourceContext rootReasonAt
      (WithBoth administrative fixedAdministrative scope
        compiled.indexed.layouts.definitions children) scope id lowered := by
  have actual := CallableIndexedOwnedPreparedExpressionNativeChildren.head_with_raw
    (fun actual _nativeType actualTyped =>
      CallableIndexedOwnedPreparedRawCompilerHeadNativeChildren.raw_children
        (sourceContext := sourceContext) (scope := compilerScope)
        root expressionSyntax callerEvidence inventory actual actualTyped) head typed
  have paired := CallableIndexedOwnedPreparedExpressionNativeChildren.head_with_raw
    (fun actual _nativeType actualTyped =>
      CallableIndexedOwnedPreparedRawCompilerHeadNativeChildren.raw_children
        (sourceContext := sourceContext) (scope := compilerScope)
        root expressionSyntax callerEvidence inventory actual actualTyped) actual fixedTyped
  cases paired with
  | primitive head => exact .primitive head
  | constructor receipt form valid sequence => exact .constructor receipt form valid sequence
  | member metadata baseMetadata form layout certified =>
      exact .member metadata baseMetadata form layout certified
  | index header keyFound form sourceType baseCertified keyCertified =>
      exact .index header keyFound form sourceType baseCertified keyCertified
  | builtin head => exact .builtin head
  | tuple receipt sequence => exact .tuple receipt sequence
  | call head => exact .call ⟨head, ⟨_, typed⟩, ⟨_, fixedTyped⟩⟩

variable {fuel : Nat} {solved : List SolvedRequirement} {literals : GenericExpressionMeaning.Certificate}

/-- The exact original Tree and literal receipts, together with its actual
root native witness. No typing is asserted for an unused Entries member. -/
abbrev NativeTree : GenericExpressionMeaning.Certificate :=
  NativeAt (compiled := compiled) administrative fixedAdministrative
    (CompatibleExpressionCalls.Tree.WithLiterals
      (calls := rawCalls (sourceContext := sourceContext) (compilerScope := compilerScope) root expressionSyntax callerEvidence inventory) (fuel := fuel)
      (values := .initial compiled.compatible.checked) (source := source named)
      (context := sourceContext) (solved := solved) (reasonAt := rootReasonAt) literals)

/-- This induction follows the SAME LiteralSites proof and ordered Entries.
The one-level head inversion supplies a raw witness before selecting a child
IH. An unused child IH is never invoked. -/
private theorem fold_native
    (Meaning : Nat → GenericExpressionMeaning.Certificate → Prop)
    (select : ∀ {size certificate}, Meaning size certificate → ∀ {scope id lowered},
      certificate scope id lowered → Meaning size (pointCertificate scope id lowered))
    (gather : ∀ {size certificate},
      (∀ {scope id lowered}, certificate scope id lowered → Meaning size (pointCertificate scope id lowered)) →
      Meaning size certificate)
    (budget size : Nat) (within : size ≤ budget)
    (fragments : ∀ child, child ≤ budget → Meaning child
      (CompatibleExpressionBuiltins.Tree.WithLiterals (fuel := fuel) (values := .initial compiled.compatible.checked)
        (source := source named) (context := sourceContext) (solved := solved) (reasonAt := rootReasonAt) literals))
    (nodes : ∀ scope entries child, child ≤ budget →
      (∀ smaller, smaller ≤ budget → Meaning smaller
        (WithBoth administrative fixedAdministrative scope compiled.indexed.layouts.definitions
          (CompatibleExpressionCalls.Entries scope entries))) →
      Meaning child
        (CompatibleExpressionCalls.Head (NativeCalls (sourceContext := sourceContext) (compilerScope := compilerScope) root expressionSyntax callerEvidence inventory administrative fixedAdministrative)
          (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked) (source named) sourceContext rootReasonAt
          (WithBoth administrative fixedAdministrative scope compiled.indexed.layouts.definitions
            (CompatibleExpressionCalls.Entries scope entries)))) :
    Meaning size (NativeTree (sourceContext := sourceContext) (compilerScope := compilerScope)
      (fuel := fuel) (solved := solved) (literals := literals) root expressionSyntax callerEvidence inventory administrative fixedAdministrative) := by
  apply gather
  intro scope id lowered supported
  obtain ⟨⟨tree, sites⟩, ⟨nativeType, typed⟩, ⟨fixedType, fixedTyped⟩⟩ := supported
  induction sites generalizing size nativeType fixedType with
  | fragment child childSites =>
      exact select (fragments size within) ⟨child, childSites⟩
  | @node id lowered entries head children childSites ih =>
      have meanings : ∀ smaller, smaller ≤ budget → Meaning smaller
          (WithBoth administrative fixedAdministrative scope compiled.indexed.layouts.definitions
            (CompatibleExpressionCalls.Entries scope entries)) := by
        intro smaller smallerWithin
        apply gather
        intro current expression code certified
        obtain ⟨⟨⟨rfl, member⟩, childType, childTyped⟩, fixedChildType, fixedChildTyped⟩ := certified
        exact ih expression code member (size := smaller) (nativeType := childType)
          (fixedType := fixedChildType) smallerWithin childTyped fixedChildTyped
      exact select (nodes scope entries size within meanings)
        (native_head (sourceContext := sourceContext) (compilerScope := compilerScope) root expressionSyntax callerEvidence inventory administrative fixedAdministrative head typed fixedTyped)

section Semantics
variable {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
  (transport : ProtectedStateTransition.AdministrativeTransport callerProtocol)
  (functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  {registry : SourceCoreRawMetadata.Registry}
  (extension : SourceCoreRawMetadata.Extends (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked).registry registry)
  {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
  (observations : CompatibleEquality.FunctionObservations compiled.compatible.checked.catalog functions identities)
  (functionTypes : FunctionRuntimeViews functions)
  (evidence : Dynamic.EvidenceEnvironment) {faults : FunctionCalls.FaultRep}
  (unique : NodeOccurrencesUnique (source named))
  (reads : ReachedLoweredReadOutcomePorts.ReadPolicies fuel (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked)
    (source named) sourceContext rootReasonAt faults)
  (missing : IndexFaultPostContracts.MissingPolicies (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked)
    (source named) functions registry program sourceContext evidence rootReasonAt faults)
  (wellFormed : ProgramWellFormed program)
  (runtime : Dynamic.SourceRuntimeValid program sourceContext (source named))
  (covers : evidence.Covers sourceContext)

private abbrev P (certificate : GenericExpressionMeaning.Certificate) (size : Nat) : Prop :=
  CallableIndexedOwnedAdmittedExpressionBounds.PreservesAt bridge
    (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
    sourceContext evidence (source named) certificate faults size

private abbrev R (certificate : GenericExpressionMeaning.Certificate) (size : Nat) : Prop :=
  CallableIndexedOwnedAdmittedExpressionBounds.ReflectsAt bridge
    (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
    sourceContext evidence (source named) certificate faults size

include transport extension faithful observations functionTypes unique reads missing wellFormed runtime covers in
/-- All non-call heads and exact builtin fragments are closed internally.
Only the actual raw lambda/named/indirect alternatives remain in callLeaves;
that dispatcher must consume the strict F induction at the retained body. -/
private theorem preserves_with_literals
    (literalMeaning : GenericExpressionMeaning.Preserves
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
      program sourceContext evidence (source named) literals faults)
    (budget size : Nat) (within : size ≤ budget)
    (callLeaves : ∀ scope entries child, child ≤ budget →
      (∀ smaller, smaller ≤ budget → P (named := named) (sourceContext := sourceContext) (registry := registry) (faults := faults) bridge functions evidence
        (WithBoth administrative fixedAdministrative scope compiled.indexed.layouts.definitions
          (CompatibleExpressionCalls.Entries scope entries)) smaller) →
      P (named := named) (sourceContext := sourceContext) (registry := registry) (faults := faults) bridge functions evidence
        (NativeCalls (sourceContext := sourceContext) (compilerScope := compilerScope) root expressionSyntax callerEvidence inventory administrative fixedAdministrative
          (WithBoth administrative fixedAdministrative scope compiled.indexed.layouts.definitions
            (CompatibleExpressionCalls.Entries scope entries))) child) :
    P (named := named) (sourceContext := sourceContext) (registry := registry) (faults := faults) bridge functions evidence (NativeTree (sourceContext := sourceContext) (compilerScope := compilerScope)
      (fuel := fuel) (solved := solved) (literals := literals) root expressionSyntax callerEvidence inventory administrative fixedAdministrative) size := by
  apply fold_native (sourceContext := sourceContext) (compilerScope := compilerScope)
    (fuel := fuel) (solved := solved) (literals := literals) root expressionSyntax callerEvidence inventory administrative fixedAdministrative
    (fun size certificate => P (named := named) (sourceContext := sourceContext) (registry := registry) (faults := faults) bridge functions evidence certificate size)
    (fun meaning _ _ _ certified _ _ _ point => by
      obtain ⟨rfl, rfl, rfl⟩ := point
      exact meaning certified)
    (fun meanings scope id lowered certified => meanings certified ⟨rfl, rfl, rfl⟩)
    budget size within
  · intro child _within
    exact CallableIndexedOwnedAdmittedExpressionBounds.PreservesAt.of_stateful wellFormed runtime covers
      (ProtectedStateTransition.PreservesAt.of_administrative _ _ _ _ _ _ _ _ transport
        (RecursiveNamedBoundedContracts.preserves_at_of_unbounded
          (ProtectedExpressionMeaning.preserves_of_typed _
            (CallableIndexedOwnedReachedExpressionDiagnosticBounds.preserves_with_literals functions extension faithful observations functionTypes
              program evidence unique reads missing literalMeaning)) child))
  · intro scope entries child childWithin children
    exact CallableIndexedOwnedReachedAdmittedExpressionCallsHeads.preserves_at_with_calls
      bridge transport functions extension faithful observations functionTypes evidence unique missing wellFormed runtime covers
      (NativeCalls (sourceContext := sourceContext) (compilerScope := compilerScope) root expressionSyntax callerEvidence inventory administrative fixedAdministrative) budget child childWithin children
      (callLeaves scope entries child childWithin children)

include transport extension faithful observations functionTypes unique reads missing wellFormed runtime covers in
/-- Reflection follows each actual Core grade; each head returns its own
independent Source grade and the same admitted reached witness. -/
private theorem reflects_with_literals
    (literalMeaning : GenericExpressionMeaning.Reflects
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
      program sourceContext evidence (source named) literals faults)
    (budget size : Nat) (within : size ≤ budget)
    (callLeaves : ∀ scope entries child, child ≤ budget →
      (∀ smaller, smaller ≤ budget → R (named := named) (sourceContext := sourceContext) (registry := registry) (faults := faults) bridge functions evidence
        (WithBoth administrative fixedAdministrative scope compiled.indexed.layouts.definitions
          (CompatibleExpressionCalls.Entries scope entries)) smaller) →
      R (named := named) (sourceContext := sourceContext) (registry := registry) (faults := faults) bridge functions evidence
        (NativeCalls (sourceContext := sourceContext) (compilerScope := compilerScope) root expressionSyntax callerEvidence inventory administrative fixedAdministrative
          (WithBoth administrative fixedAdministrative scope compiled.indexed.layouts.definitions
            (CompatibleExpressionCalls.Entries scope entries))) child) :
    R (named := named) (sourceContext := sourceContext) (registry := registry) (faults := faults) bridge functions evidence (NativeTree (sourceContext := sourceContext) (compilerScope := compilerScope)
      (fuel := fuel) (solved := solved) (literals := literals) root expressionSyntax callerEvidence inventory administrative fixedAdministrative) size := by
  apply fold_native (sourceContext := sourceContext) (compilerScope := compilerScope)
    (fuel := fuel) (solved := solved) (literals := literals) root expressionSyntax callerEvidence inventory administrative fixedAdministrative
    (fun size certificate => R (named := named) (sourceContext := sourceContext) (registry := registry) (faults := faults) bridge functions evidence certificate size)
    (fun meaning _ _ _ certified _ _ _ point => by
      obtain ⟨rfl, rfl, rfl⟩ := point
      exact meaning certified)
    (fun meanings scope id lowered certified => meanings certified ⟨rfl, rfl, rfl⟩)
    budget size within
  · intro child _within
    exact CallableIndexedOwnedAdmittedExpressionBounds.ReflectsAt.of_stateful wellFormed runtime covers
      (ProtectedStateTransition.ReflectsAt.of_administrative _ _ _ _ _ _ _ _ transport
        (RecursiveNamedBoundedContracts.reflects_at_of_unbounded
          (ProtectedExpressionMeaning.reflects_of_typed _
            (CallableIndexedOwnedReachedExpressionDiagnosticBounds.reflects_with_literals functions extension faithful observations functionTypes
              program evidence unique reads missing literalMeaning)) child))
  · intro scope entries child childWithin children
    exact CallableIndexedOwnedReachedAdmittedExpressionCallsHeads.reflects_at_with_calls
      bridge transport functions extension faithful observations functionTypes evidence unique missing wellFormed runtime covers
      (NativeCalls (sourceContext := sourceContext) (compilerScope := compilerScope) root expressionSyntax callerEvidence inventory administrative fixedAdministrative) budget child childWithin children
      (callLeaves scope entries child childWithin children)


/-- The actual runtime literal family retains only validator-selected rows of
this same compiler Tree. Its denotation is constructed from the real ledger. -/
abbrev RuntimeTree : GenericExpressionMeaning.Certificate :=
  NativeTree (sourceContext := sourceContext) (compilerScope := compilerScope)
      (fuel := fuel) (solved := solved) root expressionSyntax callerEvidence inventory administrative fixedAdministrative
    (literals := fun _ id lowered =>
      CompatibleExpressionLiteralRuntime.Certificate solved (source named) id lowered)

include transport extension faithful observations functionTypes unique reads missing wellFormed runtime covers in
/-- Actual runtime literal and non-call meanings are manufactured internally.
The remaining three call alternatives must use the strict body family. -/
theorem preserves_at (sameLedger : sourceContext.solvedRequirements = solved)
    (runtimeLedger : RuntimeRequirementLedgerValid sourceContext)
    (budget size : Nat) (within : size ≤ budget)
    (callLeaves : ∀ scope entries child, child ≤ budget →
      (∀ smaller, smaller ≤ budget → P (named := named) (sourceContext := sourceContext) (registry := registry) (faults := faults) bridge functions evidence
        (WithBoth administrative fixedAdministrative scope compiled.indexed.layouts.definitions
          (CompatibleExpressionCalls.Entries scope entries)) smaller) →
      P (named := named) (sourceContext := sourceContext) (registry := registry) (faults := faults) bridge functions evidence
        (NativeCalls (sourceContext := sourceContext) (compilerScope := compilerScope) root expressionSyntax callerEvidence inventory administrative fixedAdministrative
          (WithBoth administrative fixedAdministrative scope compiled.indexed.layouts.definitions
            (CompatibleExpressionCalls.Entries scope entries))) child) :
    P (named := named) (sourceContext := sourceContext) (registry := registry) (faults := faults) bridge functions evidence (RuntimeTree (sourceContext := sourceContext) (compilerScope := compilerScope)
    (fuel := fuel) (solved := solved) root expressionSyntax callerEvidence inventory administrative fixedAdministrative) size :=
  preserves_with_literals (sourceContext := sourceContext) (compilerScope := compilerScope)
    (fuel := fuel) (solved := solved) root expressionSyntax callerEvidence inventory administrative fixedAdministrative
    bridge transport functions extension faithful observations functionTypes evidence unique reads missing
    wellFormed runtime covers
    (CompatibleExpressionLiteralRuntime.preserves functions program sourceContext evidence
      sameLedger runtimeLedger unique faults) budget size within callLeaves

include transport extension faithful observations functionTypes unique reads missing wellFormed runtime covers in
/-- The same native Tree yields an independent Source grade and the actual
reached admission. No literal or completed-expression execution law is input. -/
theorem reflects_at (sameLedger : sourceContext.solvedRequirements = solved)
    (runtimeLedger : RuntimeRequirementLedgerValid sourceContext)
    (budget size : Nat) (within : size ≤ budget)
    (callLeaves : ∀ scope entries child, child ≤ budget →
      (∀ smaller, smaller ≤ budget → R (named := named) (sourceContext := sourceContext) (registry := registry) (faults := faults) bridge functions evidence
        (WithBoth administrative fixedAdministrative scope compiled.indexed.layouts.definitions
          (CompatibleExpressionCalls.Entries scope entries)) smaller) →
      R (named := named) (sourceContext := sourceContext) (registry := registry) (faults := faults) bridge functions evidence
        (NativeCalls (sourceContext := sourceContext) (compilerScope := compilerScope) root expressionSyntax callerEvidence inventory administrative fixedAdministrative
          (WithBoth administrative fixedAdministrative scope compiled.indexed.layouts.definitions
            (CompatibleExpressionCalls.Entries scope entries))) child) :
    R (named := named) (sourceContext := sourceContext) (registry := registry) (faults := faults) bridge functions evidence (RuntimeTree (sourceContext := sourceContext) (compilerScope := compilerScope)
    (fuel := fuel) (solved := solved) root expressionSyntax callerEvidence inventory administrative fixedAdministrative) size :=
  reflects_with_literals (sourceContext := sourceContext) (compilerScope := compilerScope)
    (fuel := fuel) (solved := solved) root expressionSyntax callerEvidence inventory administrative fixedAdministrative
    bridge transport functions extension faithful observations functionTypes evidence unique reads missing
    wellFormed runtime covers
    (CompatibleExpressionLiteralRuntime.reflects functions program sourceContext evidence
      sameLedger runtimeLedger (source named) faults) budget size within callLeaves

end Semantics
end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedPairedReachedNativeExpressionTreeBounds
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedEligibleSelectedNativeFamilyFlowStep
/-! The closure F step asks E only for a literal selected ordinary Header
or the literal selected Principal and dictionary retained at formation. It
never asks for an unrelated Origin or caller evidence. The same fixed-prefix
raw occurrence witness supplies both views of the paired expression Tree.

The authentic occurrence factory constructs the finite Tree internally.
Receiving table/token/reached-interpretation facts stay static inputs; graded
E is the mutual induction hypothesis. The original prepared F producer runs
once with the same body, protocol, owner and independent reflection grade. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedEligibleSelectedNativeFamilyFlowStep
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory CallableIndexedLambdaValues CallableIndexedNamedGeneration CallableIndexedLambdaGeneration
open CallableIndexedOwnedContextualCompilerPolicyProfiles
open CallableIndexedOwnedFunctionValues (Header Key OwnedKey)
open CallableIndexedOwnedPreparedSelectedNativeFamilyQualification (facet)
open CallableIndexedOwnedSelectedDiagnosticIssuerReceipts (SelectedReceipt lowered)
open CallableIndexedOwnedPreparedCanonicalCaptureReceipts («prefix»)
open CallableIndexedOwnedPreparedCanonicalFlowBounds (Origin)
open CallableIndexedOwnedTypedLambdaBodyContinuations (Validity)
open CallableIndexedOwnedTypedLambdaProtocolContinuations (FlowPreserves FlowReflects)
open CallableIndexedOwnedContextualLambdaSourceDiagnostics
open CallableIndexedOwnedContextualLambdaJointStaticReceipts (trackedFactory)
open RecursiveNamedCatalogInvocationBounds (Below)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (Key compiled (Program.ofChecked compiled.sourceProgram))}
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  (functions : FunctionModel compiled.compatible.checked.catalog
    (CallableIndexedAmbient.ambientDefinitions compiled.indexed))

/-- The root is attached positively to the actual caller domain. Methods
retain their complete selector and literal dictionary; no Header is synthesized. -/
inductive Eligible : {named : Named} → {index : Nat} →
    SelectedReceipt compiled named index → Origin compiled →
    Option Dynamic.EvidenceEnvironment → Dynamic.EvidenceEnvironment → Prop where
  | ordinary {caller : Header compiled (Program.ofChecked compiled.sourceProgram)}
      (member : caller ∈ headers) {index : Nat}
      (selected : SelectedReceipt compiled caller.named index)
      (callerEvidence : Option Dynamic.EvidenceEnvironment)
      {evidence : Dynamic.EvidenceEnvironment}
      (sameEvidence : CallableIndexedOwnedPreparedCatalogTypedNamedCallBounds.CallerEvidence
        callerEvidence evidence) :
      Eligible selected (.ordinary caller) callerEvidence evidence
  | principal {method : ExecutableImplMethods.CheckedMethod}
      (principal : CallableIndexedOwnedMethodPrincipal.Principal compiled method)
      (selected : SelectedReceipt compiled principal.named principal.cached.index) :
      Eligible selected (.principal principal.named) (some principal.dictionary) principal.dictionary

section Expressions
variable {named : Named} {index : Nat} (selected : SelectedReceipt compiled named index)
  {rootFuel : Nat} {rootSource : TypedSource} {rootScope : SourceCoreLocalCell.Scope}
  {rootId : ExpressionId} {rootReasonAt : ExpressionId → Word} {rootLowered : SourceCoreBasic.LoweredExpr}
  (root : RootPolicyReceipt (compiled := compiled) named (lowered compiled selected.diagnostics)
    selected.code selected.compilation rootFuel rootSource rootScope rootId rootReasonAt rootLowered)
  (expressionSyntax : TypedSource → ExpressionId → Prop)
  (callerEvidence : Option Dynamic.EvidenceEnvironment) (readFuel : Nat)
  (origin : Origin compiled) (owner : OwnedKey keys)
  (context : SourceSemantics.Context) (evidence : Dynamic.EvidenceEnvironment)

/-- E is measured at the actual selected-root RuntimeTree. Its meaning is an
induction hypothesis, separate from every static receipt. -/
def ExpressionPreserves (size : Nat) : Prop :=
  ∀ compilerScope, CallableIndexedOwnedAdmittedExpressionBounds.PreservesAt
    (Origin.bridge (headers := headers) origin owner)
    (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
    context evidence (source named)
    (CallableIndexedOwnedPreparedPairedReachedNativeExpressionTreeBounds.RuntimeTree
      (sourceContext := context) (compilerScope := compilerScope) (fuel := readFuel)
      (solved := (CallableIndexedNamedGeneration.context compiled.indexed named).solvedRequirements)
      root expressionSyntax callerEvidence headers («prefix» (compiled := compiled) named)
      («prefix» (compiled := compiled) named)) faults size

def ExpressionReflects (size : Nat) : Prop :=
  ∀ compilerScope, CallableIndexedOwnedAdmittedExpressionBounds.ReflectsAt
    (Origin.bridge (headers := headers) origin owner)
    (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
    context evidence (source named)
    (CallableIndexedOwnedPreparedPairedReachedNativeExpressionTreeBounds.RuntimeTree
      (sourceContext := context) (compilerScope := compilerScope) (fuel := readFuel)
      (solved := (CallableIndexedNamedGeneration.context compiled.indexed named).solvedRequirements)
      root expressionSyntax callerEvidence headers («prefix» (compiled := compiled) named)
      («prefix» (compiled := compiled) named)) faults size
end Expressions

/-- This is the numeric E family over authentic selected compiler roots.
Its RuntimeTree argument is built from the same accepted child and raw native
witness. It is a semantic induction hypothesis, never a static packet field. -/
def ExpressionsPreserves (budget : Nat) : Prop :=
  ∀ {named : Named} {index : Nat} (selected : SelectedReceipt compiled named index)
    {rootFuel : Nat} {rootSource : TypedSource} {rootScope : SourceCoreLocalCell.Scope}
    {rootId : ExpressionId} {rootReasonAt : ExpressionId → Word} {rootLowered : SourceCoreBasic.LoweredExpr}
    (root : RootPolicyReceipt (compiled := compiled) named (lowered compiled selected.diagnostics)
      selected.code selected.compilation rootFuel rootSource rootScope rootId rootReasonAt rootLowered)
    (expressionSyntax : TypedSource → ExpressionId → Prop)
    (callerEvidence : Option Dynamic.EvidenceEnvironment) (readFuel : Nat)
    (origin : Origin compiled) (owner : OwnedKey keys)
    (context : SourceSemantics.Context) (evidence : Dynamic.EvidenceEnvironment),
    Eligible (headers := headers) selected origin callerEvidence evidence →
    CompatibleRuntimeContextValidity.Valid (CallableIndexedNamedGeneration.context compiled.indexed named).solvedRequirements
      context evidence → Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) context (source named) →
    RecursiveNamedHeaderContracts.AtMost budget (ExpressionPreserves (headers := headers) (registry := registry) (faults := faults)
      functions selected root expressionSyntax callerEvidence readFuel origin owner context evidence)

def ExpressionsReflects (budget : Nat) : Prop :=
  ∀ {named : Named} {index : Nat} (selected : SelectedReceipt compiled named index)
    {rootFuel : Nat} {rootSource : TypedSource} {rootScope : SourceCoreLocalCell.Scope}
    {rootId : ExpressionId} {rootReasonAt : ExpressionId → Word} {rootLowered : SourceCoreBasic.LoweredExpr}
    (root : RootPolicyReceipt (compiled := compiled) named (lowered compiled selected.diagnostics)
      selected.code selected.compilation rootFuel rootSource rootScope rootId rootReasonAt rootLowered)
    (expressionSyntax : TypedSource → ExpressionId → Prop)
    (callerEvidence : Option Dynamic.EvidenceEnvironment) (readFuel : Nat)
    (origin : Origin compiled) (owner : OwnedKey keys)
    (context : SourceSemantics.Context) (evidence : Dynamic.EvidenceEnvironment),
    Eligible (headers := headers) selected origin callerEvidence evidence →
    CompatibleRuntimeContextValidity.Valid (CallableIndexedNamedGeneration.context compiled.indexed named).solvedRequirements
      context evidence → Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) context (source named) →
    Below budget (ExpressionReflects (headers := headers) (registry := registry) (faults := faults)
      functions selected root expressionSyntax callerEvidence readFuel origin owner context evidence)

section Closure
variable {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope}
  {mapping : LocationMap} {world : StoreTyping} {actual : Environment}
  (captured : Captures compiled.indexed mapping world scope function.captured actual)
  (code : Code compiled.indexed function scope captured.administrative)
  (owner : OwnedKey keys)
  (extension : SourceCoreRawMetadata.Extends
    (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked).registry registry)
  {identities : Dynamic.Value → Word → Prop}
  (faithful : DataEquality.IdentityFaithful identities)
  (observations : CompatibleEquality.FunctionObservations compiled.compatible.checked.catalog functions identities)
  (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))

namespace Ordinary
variable (support : CallableIndexedOwnedPreparedOrdinaryLambdaSupport.Support code)
  (qualified : CallableIndexedOwnedPreparedSelectedNativeFamilyQualification.Ordinary headers code support)

/-- Only the actual issuer's rebuilt table, token inclusions and static
readiness at reached valid contexts are retained. -/
def Receiving : Prop :=
  ∃ table : SourceCoreFaultSites.Table,
    support.issued.diagnostics.tableForRegistry registry extension = .ok table ∧
    (∀ reason token, GenericAssignmentDiagnostics.OperandRep support.issued.assignments reason token → faults reason token) ∧
    (∀ reason token, EmittedDiagnosticTokenPlan.UnaryRep support.issued.assignments reason token → faults reason token) ∧
    ∀ context, Validity (program := Program.ofChecked compiled.sourceProgram) captured code context →
      CallableIndexedOwnedContextualLambdaAssignmentReadiness.ReachedInterpretations
        (context := context) (certificates := support.certificates support.body.readFuel function.source)
        (administrative := captured.administrative)
        (factory := trackedFactory support.diagnosticPolicy function.source support.issued.invalidOperand)
        (faults := faults) (registry := registry) support.issued
        (Origin.bridge (headers := headers) (.ordinary support.caller) owner) functions table

include qualified faithful observations wellFormed in
/-- The actual selected occurrence factory builds the same Tree before one
original F producer is invoked. Reflection keeps an independent Source grade. -/
theorem preserves_flow (budget : Nat)
    (receiving : Receiving (headers := headers) (registry := registry) (faults := faults) functions captured code owner extension support)

    (expressionIH : ExpressionsPreserves (headers := headers) (keys := keys) (registry := registry) (faults := faults) functions budget) :
    RecursiveNamedHeaderContracts.AtMost budget
      (FlowPreserves captured code support.body.toBody functions
        (Origin.bridge (headers := headers) (.ordinary support.caller) owner)
        (registry := registry) (faults := faults)) := by
  cases captured with
  | mk administrative canonical actualContext embedding represented agrees respects typed =>
    cases qualified with
    | @actual caller member index selected rootFuel rootSource rootScope rootId rootReasonAt rootLowered root expressionSyntax sourceContext evidence scope id lowered node parameters result statements reported childFuel certificate receipt bodyReasons declarations sameIssuer factory environment =>
        obtain ⟨table, rebuilt, operands, unaries, interprets⟩ := receiving
        apply CallableIndexedOwnedPreparedNativeFamilyFlowStep.preserves_flow
          selected.compilation root expressionSyntax (some evidence)
          ⟨_, canonical, actualContext, embedding, represented, agrees, respects, typed⟩ (RecursiveNamedLambdaFormationHeads.recaptureCode
            (values := .initial compiled.compatible.checked) (indexed := compiled.indexed) receipt.site.code environment)
          rfl receipt.shell.issued
          ((CallableIndexedOwnedPreparedOrdinaryLambdaSupport.Support.of_site
            caller selected.compilation receipt.site expressionSyntax
            (CallableIndexedOwnedPreparedNativeCompilerChildren.certificates root expressionSyntax
              («prefix» (compiled := compiled) caller.named)) receipt.shell.issued receipt.shell.diagnosticPolicy receipt.body).recapture environment).body
          factory (.ordinary caller) owner functions
          extension faithful observations wellFormed rebuilt operands unaries interprets budget

        intro context valid child within compilerScope currentScope expression lowered accepted node
        have eligible : Eligible (headers := headers) selected (.ordinary caller) (some evidence) evidence :=
          .ordinary member selected (some evidence) rfl
        have currentValid : CompatibleRuntimeContextValidity.Valid
            (CallableIndexedNamedGeneration.context compiled.indexed caller.named).solvedRequirements context evidence := by
          simpa only [Validity, RecursiveNamedLambdaFormationHeads.recaptureCode, receipt.site.compilation,
            CallableIndexedLambdaGeneration.closure] using valid.1
        exact expressionIH selected root expressionSyntax (some evidence) receipt.body.readFuel
          (.ordinary caller) owner context evidence eligible currentValid valid.2
          child within compilerScope ⟨accepted.1, accepted.2, accepted.2⟩ (node := node)

include qualified faithful observations wellFormed in
/-- The actual selected occurrence factory builds the same Tree before one
original F producer is invoked. Reflection keeps an independent Source grade. -/
theorem reflects_flow (budget : Nat)
    (receiving : Receiving (headers := headers) (registry := registry) (faults := faults) functions captured code owner extension support)
    (functionTypes : FunctionRuntimeViews functions)
    (expressionIH : ExpressionsReflects (headers := headers) (keys := keys) (registry := registry) (faults := faults) functions budget) :
    Below budget
      (FlowReflects captured code support.body.toBody functions
        (Origin.bridge (headers := headers) (.ordinary support.caller) owner)
        (registry := registry) (faults := faults)) := by
  cases captured with
  | mk administrative canonical actualContext embedding represented agrees respects typed =>
    cases qualified with
    | @actual caller member index selected rootFuel rootSource rootScope rootId rootReasonAt rootLowered root expressionSyntax sourceContext evidence scope id lowered node parameters result statements reported childFuel certificate receipt bodyReasons declarations sameIssuer factory environment =>
        obtain ⟨table, rebuilt, operands, unaries, interprets⟩ := receiving
        apply CallableIndexedOwnedPreparedNativeFamilyFlowStep.reflects_flow
          selected.compilation root expressionSyntax (some evidence)
          ⟨_, canonical, actualContext, embedding, represented, agrees, respects, typed⟩ (RecursiveNamedLambdaFormationHeads.recaptureCode
            (values := .initial compiled.compatible.checked) (indexed := compiled.indexed) receipt.site.code environment)
          rfl receipt.shell.issued
          ((CallableIndexedOwnedPreparedOrdinaryLambdaSupport.Support.of_site
            caller selected.compilation receipt.site expressionSyntax
            (CallableIndexedOwnedPreparedNativeCompilerChildren.certificates root expressionSyntax
              («prefix» (compiled := compiled) caller.named)) receipt.shell.issued receipt.shell.diagnosticPolicy receipt.body).recapture environment).body
          factory (.ordinary caller) owner functions
          extension faithful observations wellFormed rebuilt operands unaries interprets budget
          functionTypes
        intro context valid child within compilerScope currentScope expression lowered accepted node
        have eligible : Eligible (headers := headers) selected (.ordinary caller) (some evidence) evidence :=
          .ordinary member selected (some evidence) rfl
        have currentValid : CompatibleRuntimeContextValidity.Valid
            (CallableIndexedNamedGeneration.context compiled.indexed caller.named).solvedRequirements context evidence := by
          simpa only [Validity, RecursiveNamedLambdaFormationHeads.recaptureCode, receipt.site.compilation,
            CallableIndexedLambdaGeneration.closure] using valid.1
        exact expressionIH selected root expressionSyntax (some evidence) receipt.body.readFuel
          (.ordinary caller) owner context evidence eligible currentValid valid.2
          child within compilerScope ⟨accepted.1, accepted.2, accepted.2⟩ (node := node)

end Ordinary

namespace Principal
variable (support : CallableIndexedOwnedPreparedPrincipalLambdaSupport.Support code)
  (qualified : CallableIndexedOwnedPreparedSelectedNativeFamilyQualification.Principal headers code support)

/-- Only the actual issuer's rebuilt table, token inclusions and static
readiness at reached valid contexts are retained. -/
def Receiving : Prop :=
  ∃ table : SourceCoreFaultSites.Table,
    support.issued.diagnostics.tableForRegistry registry extension = .ok table ∧
    (∀ reason token, GenericAssignmentDiagnostics.OperandRep support.issued.assignments reason token → faults reason token) ∧
    (∀ reason token, EmittedDiagnosticTokenPlan.UnaryRep support.issued.assignments reason token → faults reason token) ∧
    ∀ context, Validity (program := Program.ofChecked compiled.sourceProgram) captured code context →
      CallableIndexedOwnedContextualLambdaAssignmentReadiness.ReachedInterpretations
        (context := context) (certificates := support.certificates support.body.readFuel function.source)
        (administrative := captured.administrative)
        (factory := trackedFactory support.diagnosticPolicy function.source support.issued.invalidOperand)
        (faults := faults) (registry := registry) support.issued
        (Origin.bridge (headers := headers) (.principal support.principal.named) owner) functions table

include qualified faithful observations wellFormed in
/-- The actual selected occurrence factory builds the same Tree before one
original F producer is invoked. Reflection keeps an independent Source grade. -/
theorem preserves_flow (budget : Nat)
    (receiving : Receiving (headers := headers) (registry := registry) (faults := faults) functions captured code owner extension support)

    (expressionIH : ExpressionsPreserves (headers := headers) (keys := keys) (registry := registry) (faults := faults) functions budget) :
    RecursiveNamedHeaderContracts.AtMost budget
      (FlowPreserves captured code support.body.toBody functions
        (Origin.bridge (headers := headers) (.principal support.principal.named) owner)
        (registry := registry) (faults := faults)) := by
  cases captured with
  | mk administrative canonical actualContext embedding represented agrees respects typed =>
    cases qualified with
    | @actual method principal selected rootFuel rootSource rootScope rootId rootReasonAt rootLowered root expressionSyntax sourceContext scope id lowered node parameters result statements reported childFuel certificate receipt sameIssuer factory environment =>
        obtain ⟨table, rebuilt, operands, unaries, interprets⟩ := receiving
        apply CallableIndexedOwnedPreparedNativeFamilyFlowStep.preserves_flow
          selected.compilation root expressionSyntax (some principal.dictionary)
          ⟨_, canonical, actualContext, embedding, represented, agrees, respects, typed⟩ (RecursiveNamedLambdaFormationHeads.recaptureCode
            (values := .initial compiled.compatible.checked) (indexed := compiled.indexed) receipt.site.code environment)
          rfl receipt.shell.issued
          ((CallableIndexedOwnedPreparedPrincipalLambdaSupport.Support.of_site
            (SelectedReceipt.principal principal selected) receipt.site expressionSyntax
            (CallableIndexedOwnedPreparedNativeCompilerChildren.certificates root expressionSyntax
              («prefix» (compiled := compiled) principal.named)) receipt.shell.issued receipt.shell.diagnosticPolicy receipt.body).recapture environment).body
          factory (.principal principal.named) owner functions
          extension faithful observations wellFormed rebuilt operands unaries interprets budget

        intro context valid child within compilerScope currentScope expression lowered accepted node
        have eligible : Eligible (headers := headers) selected (.principal principal.named)
            (some principal.dictionary) principal.dictionary := .principal principal selected
        have currentValid : CompatibleRuntimeContextValidity.Valid
            (CallableIndexedNamedGeneration.context compiled.indexed principal.named).solvedRequirements
            context principal.dictionary := by
          simpa only [Validity, RecursiveNamedLambdaFormationHeads.recaptureCode, receipt.site.compilation,
            CallableIndexedLambdaGeneration.closure] using valid.1
        exact expressionIH selected root expressionSyntax (some principal.dictionary) receipt.body.readFuel
          (.principal principal.named) owner context principal.dictionary eligible currentValid valid.2
          child within compilerScope ⟨accepted.1, accepted.2, accepted.2⟩ (node := node)

include qualified faithful observations wellFormed in
/-- The actual selected occurrence factory builds the same Tree before one
original F producer is invoked. Reflection keeps an independent Source grade. -/
theorem reflects_flow (budget : Nat)
    (receiving : Receiving (headers := headers) (registry := registry) (faults := faults) functions captured code owner extension support)
    (functionTypes : FunctionRuntimeViews functions)
    (expressionIH : ExpressionsReflects (headers := headers) (keys := keys) (registry := registry) (faults := faults) functions budget) :
    Below budget
      (FlowReflects captured code support.body.toBody functions
        (Origin.bridge (headers := headers) (.principal support.principal.named) owner)
        (registry := registry) (faults := faults)) := by
  cases captured with
  | mk administrative canonical actualContext embedding represented agrees respects typed =>
    cases qualified with
    | @actual method principal selected rootFuel rootSource rootScope rootId rootReasonAt rootLowered root expressionSyntax sourceContext scope id lowered node parameters result statements reported childFuel certificate receipt sameIssuer factory environment =>
        obtain ⟨table, rebuilt, operands, unaries, interprets⟩ := receiving
        apply CallableIndexedOwnedPreparedNativeFamilyFlowStep.reflects_flow
          selected.compilation root expressionSyntax (some principal.dictionary)
          ⟨_, canonical, actualContext, embedding, represented, agrees, respects, typed⟩ (RecursiveNamedLambdaFormationHeads.recaptureCode
            (values := .initial compiled.compatible.checked) (indexed := compiled.indexed) receipt.site.code environment)
          rfl receipt.shell.issued
          ((CallableIndexedOwnedPreparedPrincipalLambdaSupport.Support.of_site
            (SelectedReceipt.principal principal selected) receipt.site expressionSyntax
            (CallableIndexedOwnedPreparedNativeCompilerChildren.certificates root expressionSyntax
              («prefix» (compiled := compiled) principal.named)) receipt.shell.issued receipt.shell.diagnosticPolicy receipt.body).recapture environment).body
          factory (.principal principal.named) owner functions
          extension faithful observations wellFormed rebuilt operands unaries interprets budget
          functionTypes
        intro context valid child within compilerScope currentScope expression lowered accepted node
        have eligible : Eligible (headers := headers) selected (.principal principal.named)
            (some principal.dictionary) principal.dictionary := .principal principal selected
        have currentValid : CompatibleRuntimeContextValidity.Valid
            (CallableIndexedNamedGeneration.context compiled.indexed principal.named).solvedRequirements
            context principal.dictionary := by
          simpa only [Validity, RecursiveNamedLambdaFormationHeads.recaptureCode, receipt.site.compilation,
            CallableIndexedLambdaGeneration.closure] using valid.1
        exact expressionIH selected root expressionSyntax (some principal.dictionary) receipt.body.readFuel
          (.principal principal.named) owner context principal.dictionary eligible currentValid valid.2
          child within compilerScope ⟨accepted.1, accepted.2, accepted.2⟩ (node := node)

end Principal

end Closure
end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedEligibleSelectedNativeFamilyFlowStep
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedEligiblePairedExpressionFamilies
/-! The central E family keeps the actual body administrative context separate
from the genuine fixed compiler prefix. Closure F specializes to prefix/prefix;
named F uses the actual BodyState context. Neither direction rebases raw typing
or recovers Source authority by inverting a weaker heap model. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedEligiblePairedExpressionFamilies
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedNamedGeneration CallableIndexedLambdaGeneration CallableIndexedLambdaValues
open CallableIndexedOwnedContextualCompilerPolicyProfiles
open CallableIndexedOwnedFunctionValues (Header Key OwnedKey)
open CallableIndexedOwnedSelectedDiagnosticIssuerReceipts (SelectedReceipt lowered)
open CallableIndexedOwnedPreparedCanonicalCaptureReceipts («prefix»)
open CallableIndexedOwnedPreparedCanonicalFlowBounds (Origin)
open RecursiveNamedCatalogInvocationBounds (Below)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (Key compiled (Program.ofChecked compiled.sourceProgram))}
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  (functions : FunctionModel compiled.compatible.checked.catalog
    (CallableIndexedAmbient.ambientDefinitions compiled.indexed))

section Expressions
variable {named : Named} {index : Nat} (selected : SelectedReceipt compiled named index)
  {rootFuel : Nat} {rootSource : TypedSource} {rootScope : SourceCoreLocalCell.Scope}
  {rootId : ExpressionId} {rootReasonAt : ExpressionId → Word} {rootLowered : SourceCoreBasic.LoweredExpr}
  (root : RootPolicyReceipt (compiled := compiled) named (lowered compiled selected.diagnostics)
    selected.code selected.compilation rootFuel rootSource rootScope rootId rootReasonAt rootLowered)
  (expressionSyntax : TypedSource → ExpressionId → Prop)
  (callerEvidence : Option Dynamic.EvidenceEnvironment) (readFuel : Nat)
  (administrative : Core.Context) (origin : Origin compiled) (owner : OwnedKey keys)
  (context : SourceSemantics.Context) (evidence : Dynamic.EvidenceEnvironment)

/-- E is measured at the actual selected-root RuntimeTree. Its meaning is an
induction hypothesis, separate from every static receipt. -/
def ExpressionPreserves (size : Nat) : Prop :=
  ∀ compilerScope, CallableIndexedOwnedAdmittedExpressionBounds.PreservesAt
    (Origin.bridge (headers := headers) origin owner)
    (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
    context evidence (source named)
    (CallableIndexedOwnedPreparedPairedReachedNativeExpressionTreeBounds.RuntimeTree
      (sourceContext := context) (compilerScope := compilerScope) (fuel := readFuel)
      (solved := (CallableIndexedNamedGeneration.context compiled.indexed named).solvedRequirements)
      root expressionSyntax callerEvidence headers administrative
      («prefix» (compiled := compiled) named)) faults size

def ExpressionReflects (size : Nat) : Prop :=
  ∀ compilerScope, CallableIndexedOwnedAdmittedExpressionBounds.ReflectsAt
    (Origin.bridge (headers := headers) origin owner)
    (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
    context evidence (source named)
    (CallableIndexedOwnedPreparedPairedReachedNativeExpressionTreeBounds.RuntimeTree
      (sourceContext := context) (compilerScope := compilerScope) (fuel := readFuel)
      (solved := (CallableIndexedNamedGeneration.context compiled.indexed named).solvedRequirements)
      root expressionSyntax callerEvidence headers administrative
      («prefix» (compiled := compiled) named)) faults size
end Expressions

/-- The numeric E hypothesis retains actual administrative typing and the
independent fixed-prefix witness at one literal occurrence. Static compiler
packets carry neither this hypothesis nor a completed execution law. -/
def ExpressionsPreserves (budget : Nat) : Prop :=
  ∀ {named : Named} {index : Nat} (selected : SelectedReceipt compiled named index)
    {rootFuel : Nat} {rootSource : TypedSource} {rootScope : SourceCoreLocalCell.Scope}
    {rootId : ExpressionId} {rootReasonAt : ExpressionId → Word} {rootLowered : SourceCoreBasic.LoweredExpr}
    (root : RootPolicyReceipt (compiled := compiled) named (lowered compiled selected.diagnostics)
      selected.code selected.compilation rootFuel rootSource rootScope rootId rootReasonAt rootLowered)
    (expressionSyntax : TypedSource → ExpressionId → Prop)
    (callerEvidence : Option Dynamic.EvidenceEnvironment) (readFuel : Nat)
    (administrative : Core.Context) (origin : Origin compiled) (owner : OwnedKey keys)
    (context : SourceSemantics.Context) (evidence : Dynamic.EvidenceEnvironment),
    CallableIndexedOwnedPreparedEligibleSelectedNativeFamilyFlowStep.Eligible (headers := headers) selected origin callerEvidence evidence →
    CompatibleRuntimeContextValidity.Valid (CallableIndexedNamedGeneration.context compiled.indexed named).solvedRequirements
      context evidence → Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) context (source named) →
    RecursiveNamedHeaderContracts.AtMost budget (ExpressionPreserves (headers := headers) (registry := registry) (faults := faults)
      functions selected root expressionSyntax callerEvidence readFuel administrative origin owner context evidence)

def ExpressionsReflects (budget : Nat) : Prop :=
  ∀ {named : Named} {index : Nat} (selected : SelectedReceipt compiled named index)
    {rootFuel : Nat} {rootSource : TypedSource} {rootScope : SourceCoreLocalCell.Scope}
    {rootId : ExpressionId} {rootReasonAt : ExpressionId → Word} {rootLowered : SourceCoreBasic.LoweredExpr}
    (root : RootPolicyReceipt (compiled := compiled) named (lowered compiled selected.diagnostics)
      selected.code selected.compilation rootFuel rootSource rootScope rootId rootReasonAt rootLowered)
    (expressionSyntax : TypedSource → ExpressionId → Prop)
    (callerEvidence : Option Dynamic.EvidenceEnvironment) (readFuel : Nat)
    (administrative : Core.Context) (origin : Origin compiled) (owner : OwnedKey keys)
    (context : SourceSemantics.Context) (evidence : Dynamic.EvidenceEnvironment),
    CallableIndexedOwnedPreparedEligibleSelectedNativeFamilyFlowStep.Eligible (headers := headers) selected origin callerEvidence evidence →
    CompatibleRuntimeContextValidity.Valid (CallableIndexedNamedGeneration.context compiled.indexed named).solvedRequirements
      context evidence → Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) context (source named) →
    Below budget (ExpressionReflects (headers := headers) (registry := registry) (faults := faults)
      functions selected root expressionSyntax callerEvidence readFuel administrative origin owner context evidence)

/-- The original closure F receives this specialization of the shared E IH.
The actual and fixed contexts are literally equal at this port. -/
theorem preserves_at_prefix {budget : Nat}
    (expressions : ExpressionsPreserves (headers := headers) (keys := keys)
      (registry := registry) (faults := faults) functions budget) :
    CallableIndexedOwnedPreparedEligibleSelectedNativeFamilyFlowStep.ExpressionsPreserves
      (headers := headers) (keys := keys) (registry := registry) (faults := faults) functions budget := by
  intro named index selected rootFuel rootSource rootScope rootId rootReasonAt rootLowered
    root expressionSyntax callerEvidence readFuel origin owner context evidence eligible valid runtime
  exact expressions selected root expressionSyntax callerEvidence readFuel («prefix» (compiled := compiled) named)
    origin owner context evidence eligible valid runtime

/-- The same literal specialization preserves reflection's independent Source grade. -/
theorem reflects_at_prefix {budget : Nat}
    (expressions : ExpressionsReflects (headers := headers) (keys := keys)
      (registry := registry) (faults := faults) functions budget) :
    CallableIndexedOwnedPreparedEligibleSelectedNativeFamilyFlowStep.ExpressionsReflects
      (headers := headers) (keys := keys) (registry := registry) (faults := faults) functions budget := by
  intro named index selected rootFuel rootSource rootScope rootId rootReasonAt rootLowered
    root expressionSyntax callerEvidence readFuel origin owner context evidence eligible valid runtime
  exact expressions selected root expressionSyntax callerEvidence readFuel («prefix» (compiled := compiled) named)
    origin owner context evidence eligible valid runtime

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedEligiblePairedExpressionFamilies
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedEligibleSelectedAssociationFlowBounds
/-! Every dispatcher closure keeps the actual selected qualification and body.
The receiving facts belong to that literal association. Eligible selected-root graded E induction is
forwarded through its actual ordinary or principal F step, retaining the same
protocol, owner and body; no static field contains a completed execution law. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedEligibleSelectedAssociationFlowBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionValues (Header Key)
open CallableIndexedOwnedPreparedNativeDirectCellOrigins (Association)
open CallableIndexedOwnedPreparedSelectedNativeFamilyQualification (facet)
open CallableIndexedOwnedPreparedEligibleSelectedNativeFamilyFlowStep
open CallableIndexedOwnedPreparedCatalogIndirectInvocationDispatcher
open RecursiveNamedCatalogInvocationBounds (Below)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (Key compiled (Program.ofChecked compiled.sourceProgram))}
  {bodyRegistry registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  (functions : FunctionModel compiled.compatible.checked.catalog
    (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  (extension : SourceCoreRawMetadata.Extends
    (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked).registry registry)

/-- Pointwise receiving authority is indexed by the actual retained member. -/
def Receiving {mapping world function native bindings parameter result}
    (member : Association (facet headers) headers keys bodyRegistry faults
      mapping world function native bindings parameter result) : Prop :=
  match member with
  | .ordinary owner captured code _history support _origin _prepared _qualified _prefix _globals _reference _typed =>
      Ordinary.Receiving (headers := headers) (registry := registry) (faults := faults)
        functions captured code owner extension support
  | .principal owner captured code _history support _origin _prepared _qualified _globals _leading _reference _typed =>
      Principal.Receiving (headers := headers) (registry := registry) (faults := faults)
        functions captured code owner extension support

/-- All facts here are static table/token/reached-interpretation receipts. -/
def Receivings : Prop :=
  ∀ {mapping world function native bindings parameter result}
    (member : Association (facet headers) headers keys bodyRegistry faults
      mapping world function native bindings parameter result),
    Receiving (registry := registry) functions extension member

variable {identities : Dynamic.Value → Word → Prop}
  (faithful : DataEquality.IdentityFaithful identities)
  (observations : CompatibleEquality.FunctionObservations compiled.compatible.checked.catalog functions identities)
  (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
  (receiving : Receivings (headers := headers) (keys := keys) (bodyRegistry := bodyRegistry)
    (registry := registry) (faults := faults) functions extension)

include faithful observations wellFormed receiving in
/-- E through n produces the actual closure F through n. -/
theorem preserves_at_most (budget : Nat)
    (expressionIH : ExpressionsPreserves (headers := headers) (keys := keys)
      (registry := registry) (faults := faults) functions budget) :
    ∀ {mapping world function native bindings parameter result}
      (member : Association (facet headers) headers keys bodyRegistry faults
        mapping world function native bindings parameter result),
      RecursiveNamedHeaderContracts.AtMost budget
        (CallableIndexedOwnedPreparedDirectLambdaInvocationBounds.FlowPreserves
          functions member (registry := registry)) := by
  intro mapping world function native bindings parameter result member
  have ready := receiving member
  cases member with
  | ordinary owner captured code history support origin prepared qualified prefixContext globals reference typed =>
      exact Ordinary.preserves_flow functions captured code owner extension faithful observations wellFormed
        support qualified budget ready expressionIH
  | principal owner captured code history support origin prepared qualified globals leading reference typed =>
      exact Principal.preserves_flow functions captured code owner extension faithful observations wellFormed
        support qualified budget ready expressionIH

include faithful observations wellFormed receiving in
/-- The application dispatcher consumes strictly smaller F grades. -/
theorem preserves_below (budget : Nat)
    (expressionIH : ∀ child, child < budget → ExpressionsPreserves
      (headers := headers) (keys := keys) (registry := registry) (faults := faults) functions child) :
    ClosurePreservesBelow (qualification := facet headers) (headers := headers)
      (keys := keys) (bodyRegistry := bodyRegistry) (registry := registry) (faults := faults)
      functions budget := by
  intro mapping world function native bindings parameter result member child smaller
  exact preserves_at_most functions extension faithful observations wellFormed receiving
    child (expressionIH child smaller) member child (Nat.le_refl child)

include faithful observations wellFormed receiving in
/-- Native strict E builds strict F with an independent reconstructed Source grade. -/
theorem reflects_below (budget : Nat) (functionTypes : FunctionRuntimeViews functions)
    (expressionIH : ExpressionsReflects (headers := headers) (keys := keys)
      (registry := registry) (faults := faults) functions budget) :
    ClosureReflectsBelow (qualification := facet headers) (headers := headers)
      (keys := keys) (bodyRegistry := bodyRegistry) (registry := registry) (faults := faults)
      functions budget := by
  intro mapping world function native bindings parameter result member
  have ready := receiving member
  cases member with
  | ordinary owner captured code history support origin prepared qualified prefixContext globals reference typed =>
      exact Ordinary.reflects_flow functions captured code owner extension faithful observations wellFormed
        support qualified budget ready functionTypes expressionIH
  | principal owner captured code history support origin prepared qualified globals leading reference typed =>
      exact Principal.reflects_flow functions captured code owner extension faithful observations wellFormed
        support qualified budget ready functionTypes expressionIH

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedEligibleSelectedAssociationFlowBounds
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedEligibleSelectedLambdaCallBounds
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
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedEligibleSelectedLambdaRecipes
/-! The final call domain retains a positive static packet factory at each
literal raw lambda occurrence. Its output is the authentic selected compiler
Receipt, same issuer tag and finite OccurrenceFactory already retained by the
positive Lambdas constructor. The producer125 can manufacture that output from
original compiler/static inputs. No semantic expression/body law is a field.
Runtime formation consumes the same packet once at the actual Origin bridge.
The universal construction of these static factories remains explicit. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedEligibleSelectedLambdaRecipes
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedNamedGeneration CallableIndexedLambdaGeneration CallableIndexedLambdaValues
open CallableIndexedOwnedFunctionValues (Header Key OwnedKey)
open CallableIndexedOwnedContextualCompilerPolicyProfiles
open CallableIndexedOwnedSelectedDiagnosticIssuerReceipts (SelectedReceipt lowered)
open CallableIndexedOwnedPreparedCanonicalCaptureReceipts («prefix»)
open CallableIndexedOwnedPreparedCanonicalFlowBounds (Origin)
open CallableIndexedOwnedPreparedNativeAssignmentChildren (RawTyped)
open CallableIndexedOwnedPreparedNativeSiteShellReceipts (FiniteBodyReceipts)
open CallableIndexedOwnedPreparedNativeLambdaCompilerReceipts (Receipt)
open CallableIndexedOwnedPreparedNativeFamilyStaticQualification (OccurrenceFactory)
variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (Header compiled (Program.ofChecked compiled.sourceProgram))}
  {named : Named} {index : Nat} (selected : SelectedReceipt compiled named index)
  {rootFuel : Nat} {rootSource : TypedSource} {rootScope : SourceCoreLocalCell.Scope}
  {rootId : ExpressionId} {rootReasonAt : ExpressionId → Word} {rootLowered : SourceCoreBasic.LoweredExpr}
  (root : RootPolicyReceipt (compiled := compiled) named (lowered compiled selected.diagnostics)
    selected.code selected.compilation rootFuel rootSource rootScope rootId rootReasonAt rootLowered)
  (expressionSyntax : TypedSource → ExpressionId → Prop)
  {context : SourceSemantics.Context} {compilerScope : SourceCoreLocalCell.Scope}

/-- The literal compiler action and its genuine fixed-prefix witness contain
no child meaning, runtime Tree or execution result. -/
inductive RawLambda : GenericExpressionMeaning.Certificate where
  | actual {childFuel id lowered node parameters result statements reported}
      (allowed : expressionSyntax (source named) id)
      (found : (source named).lookupExpression? id = some node)
      (form : node.form = .lambda parameters result statements)
      (certificate : CallableIndexedLambdaCertificates.Certificate root.selected.policy root.selected.lowerBody childFuel
        (CallableIndexedNamedGeneration.context compiled.indexed named) (source named) compilerScope
        id node parameters result statements reported rootReasonAt lowered)
      (accepted : SourceCoreFunctions.lowerExpressionWithPolicy root.selected.policy root.selected.lowerBody (childFuel + 1)
        (CallableIndexedNamedGeneration.context compiled.indexed named) (source named) compilerScope id rootReasonAt = .ok lowered)
      (sourceTyped : ExpressionHasType (source named) context id node.type)
      (metadata : CompatibleExpressionReads.Metadata compiled.compatible.checked (source named) id node lowered.type)
      (fixed : RawTyped (SourceCoreLocalCell.coreContext compilerScope ++ «prefix» (compiled := compiled) named)
        lowered.expression compiled.indexed.layouts.definitions) :
      RawLambda compilerScope id lowered

/-- These are original compiler and Source inputs at this actual occurrence.
The occurrence factory is requested only for the one tagged Receipt constructed
from them. No completed expression, body or application is retained. -/
inductive CompilerInputs (evidence : Dynamic.EvidenceEnvironment) : GenericExpressionMeaning.Certificate where
  | actual {childFuel id lowered node parameters result statements reported nativeType}
      (allowed : expressionSyntax (source named) id)
      (found : (source named).lookupExpression? id = some node)
      (form : node.form = .lambda parameters result statements)
      (certificate : CallableIndexedLambdaCertificates.Certificate root.selected.policy root.selected.lowerBody childFuel
        (CallableIndexedNamedGeneration.context compiled.indexed named) (source named) compilerScope
        id node parameters result statements reported rootReasonAt lowered)
      (accepted : SourceCoreFunctions.lowerExpressionWithPolicy root.selected.policy root.selected.lowerBody (childFuel + 1)
        (CallableIndexedNamedGeneration.context compiled.indexed named) (source named) compilerScope id rootReasonAt = .ok lowered)
      (sourceTyped : ExpressionHasType (source named) context id node.type)
      (metadata : CompatibleExpressionReads.Metadata compiled.compatible.checked (source named) id node lowered.type)
      (coercions : node.coercions = [])
      (raw : HasType (SourceCoreLocalCell.coreContext compilerScope ++ «prefix» (compiled := compiled) named)
        lowered.expression nativeType compiled.indexed.layouts.definitions)
      (finite : FiniteBodyReceipts (source named) (expressionSyntax (source named)) context parameters result statements)
      (ownership : LocalIdentityOwnership (source named))
      (declarations : CompatibleExpressionReads.ScopeDeclarations (source named) compilerScope context)
      (sameLedger : context.solvedRequirements =
        (CallableIndexedNamedGeneration.context compiled.indexed named).solvedRequirements)
      (occurrences : ∀ receipt : Receipt root expressionSyntax certificate
          (sourceContext := context) (evidence := evidence),
        receipt.shell.issued = CallableIndexedOwnedPreparedNativeSiteShellReceipts.issued_at_site selected receipt.site →
        OccurrenceFactory root expressionSyntax (some evidence) headers receipt.body.readFuel) :
      CompilerInputs evidence compilerScope id lowered

namespace CompilerInputs

/-- One original tagged compiler producer constructs the ordinary packet. -/
theorem ordinary {caller : Header compiled (Program.ofChecked compiled.sourceProgram)} {index : Nat}
    (selected : SelectedReceipt compiled caller.named index)
    {rootFuel : Nat} {rootSource : TypedSource} {rootScope : SourceCoreLocalCell.Scope}
    {rootId : ExpressionId} {rootReasonAt : ExpressionId → Word} {rootLowered : SourceCoreBasic.LoweredExpr}
    (root : RootPolicyReceipt (compiled := compiled) caller.named (lowered compiled selected.diagnostics)
      selected.code selected.compilation rootFuel rootSource rootScope rootId rootReasonAt rootLowered)
    (expressionSyntax : TypedSource → ExpressionId → Prop)
    {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
    {compilerScope scope : SourceCoreLocalCell.Scope} {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}
    (profile : compiled.compatible.checked.catalog.callableContracts = true)
    (runtime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) context (source caller.named))
    (covers : evidence.Covers context)
    (sameReason : rootReasonAt = selected.diagnostics.program.reasonAt caller.named.signature.key)
    (inputs : CompilerInputs (headers := headers) selected root expressionSyntax evidence
      (context := context) (compilerScope := compilerScope) scope id lowered)
    (children : GenericExpressionMeaning.Certificate) :
    CallableIndexedOwnedPreparedSelectedPositiveOrdinaryLambdaHeads.Lambdas selected root expressionSyntax headers
      (context := context) (evidence := evidence) (scope := compilerScope) children scope id lowered := by
  cases inputs with
  | actual allowed found form certificate accepted sourceTyped metadata coercions raw finite ownership declarations sameLedger occurrences =>
    exact CallableIndexedOwnedPreparedSelectedPositiveLambdaPackets.Ordinary.of_compiler
      selected root expressionSyntax headers profile runtime covers ownership declarations sameReason sameLedger
      allowed found form certificate accepted sourceTyped metadata coercions raw finite occurrences

/-- The principal producer retains the complete literal method dictionary. -/
theorem principal {method : ExecutableImplMethods.CheckedMethod}
    (principal : CallableIndexedOwnedMethodPrincipal.Principal compiled method)
    (selected : SelectedReceipt compiled principal.named principal.cached.index)
    {rootFuel : Nat} {rootSource : TypedSource} {rootScope : SourceCoreLocalCell.Scope}
    {rootId : ExpressionId} {rootReasonAt : ExpressionId → Word} {rootLowered : SourceCoreBasic.LoweredExpr}
    (root : RootPolicyReceipt (compiled := compiled) principal.named (lowered compiled selected.diagnostics)
      selected.code selected.compilation rootFuel rootSource rootScope rootId rootReasonAt rootLowered)
    (expressionSyntax : TypedSource → ExpressionId → Prop)
    {context : SourceSemantics.Context} {compilerScope scope : SourceCoreLocalCell.Scope}
    {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}
    (profile : compiled.compatible.checked.catalog.callableContracts = true)
    (runtime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) context (source principal.named))
    (covers : principal.dictionary.Covers context)
    (inputs : CompilerInputs (headers := headers) selected root expressionSyntax principal.dictionary
      (context := context) (compilerScope := compilerScope) scope id lowered)
    (children : GenericExpressionMeaning.Certificate) :
    CallableIndexedOwnedPreparedSelectedPositivePrincipalLambdaHeads.Lambdas principal selected root expressionSyntax headers
      (context := context) (scope := compilerScope) children scope id lowered := by
  cases inputs with
  | actual allowed found form certificate accepted sourceTyped metadata coercions raw finite ownership declarations sameLedger occurrences =>
    exact CallableIndexedOwnedPreparedSelectedPositiveLambdaPackets.Principal.of_compiler
      principal selected root expressionSyntax headers profile runtime covers ownership declarations sameLedger
      allowed found form certificate accepted sourceTyped metadata coercions raw finite occurrences
end CompilerInputs

/-- The finite positive call packet is a static output. Its actual selected
Receipt and OccurrenceFactory are retained by Lambdas.actual; no execution law
is accepted and no old raw Domain is inverted to manufacture this factory. -/
inductive Recipes : {named : Named} → {index : Nat} →
    (selected : SelectedReceipt compiled named index) →
    {rootFuel : Nat} → {rootSource : TypedSource} → {rootScope : SourceCoreLocalCell.Scope} →
    {rootId : ExpressionId} → {rootReasonAt : ExpressionId → Word} → {rootLowered : SourceCoreBasic.LoweredExpr} →
    RootPolicyReceipt (compiled := compiled) named (lowered compiled selected.diagnostics)
      selected.code selected.compilation rootFuel rootSource rootScope rootId rootReasonAt rootLowered →
    (TypedSource → ExpressionId → Prop) → SourceSemantics.Context →
    Option Dynamic.EvidenceEnvironment → Dynamic.EvidenceEnvironment → Origin compiled → Prop where
  | ordinary {caller : Header compiled (Program.ofChecked compiled.sourceProgram)}
      (member : caller ∈ headers) {index : Nat}
      (selected : SelectedReceipt compiled caller.named index)
      {rootFuel : Nat} {rootSource : TypedSource} {rootScope : SourceCoreLocalCell.Scope}
      {rootId : ExpressionId} {rootReasonAt : ExpressionId → Word} {rootLowered : SourceCoreBasic.LoweredExpr}
      (root : RootPolicyReceipt (compiled := compiled) caller.named (lowered compiled selected.diagnostics)
        selected.code selected.compilation rootFuel rootSource rootScope rootId rootReasonAt rootLowered)
      (expressionSyntax : TypedSource → ExpressionId → Prop) (context : SourceSemantics.Context)
      (callerEvidence : Option Dynamic.EvidenceEnvironment) (evidence : Dynamic.EvidenceEnvironment)
      (sameEvidence : CallableIndexedOwnedPreparedCatalogTypedNamedCallBounds.CallerEvidence callerEvidence evidence)
      (build : ∀ {compilerScope scope id lowered},
        RawLambda selected root expressionSyntax (context := context) (compilerScope := compilerScope) scope id lowered →
        CallableIndexedOwnedPreparedSelectedPositiveOrdinaryLambdaHeads.Lambdas selected root expressionSyntax headers
          (context := context) (evidence := evidence) (scope := compilerScope) (fun _ _ _ => False) scope id lowered) :
      Recipes selected root expressionSyntax context callerEvidence evidence (.ordinary caller)
  | principal {method : ExecutableImplMethods.CheckedMethod}
      (principal : CallableIndexedOwnedMethodPrincipal.Principal compiled method)
      (selected : SelectedReceipt compiled principal.named principal.cached.index)
      {rootFuel : Nat} {rootSource : TypedSource} {rootScope : SourceCoreLocalCell.Scope}
      {rootId : ExpressionId} {rootReasonAt : ExpressionId → Word} {rootLowered : SourceCoreBasic.LoweredExpr}
      (root : RootPolicyReceipt (compiled := compiled) principal.named (lowered compiled selected.diagnostics)
        selected.code selected.compilation rootFuel rootSource rootScope rootId rootReasonAt rootLowered)
      (expressionSyntax : TypedSource → ExpressionId → Prop) (context : SourceSemantics.Context)
      (build : ∀ {compilerScope scope id lowered},
        RawLambda selected root expressionSyntax (context := context) (compilerScope := compilerScope) scope id lowered →
        CallableIndexedOwnedPreparedSelectedPositivePrincipalLambdaHeads.Lambdas principal selected root expressionSyntax headers
          (context := context) (scope := compilerScope) (fun _ _ _ => False) scope id lowered) :
      Recipes selected root expressionSyntax context (some principal.dictionary) principal.dictionary (.principal principal.named)

namespace Recipes

/-- Genuine per-occurrence compiler inputs supply the ordinary static recipe.
The tagged Receipt is constructed once when that exact occurrence is selected. -/
theorem of_ordinary_inputs {caller : Header compiled (Program.ofChecked compiled.sourceProgram)}
    (member : caller ∈ headers) {index : Nat}
    (selected : SelectedReceipt compiled caller.named index)
    {rootFuel : Nat} {rootSource : TypedSource} {rootScope : SourceCoreLocalCell.Scope}
    {rootId : ExpressionId} {rootReasonAt : ExpressionId → Word} {rootLowered : SourceCoreBasic.LoweredExpr}
    (root : RootPolicyReceipt (compiled := compiled) caller.named (lowered compiled selected.diagnostics)
      selected.code selected.compilation rootFuel rootSource rootScope rootId rootReasonAt rootLowered)
    (expressionSyntax : TypedSource → ExpressionId → Prop) (context : SourceSemantics.Context)
    (callerEvidence : Option Dynamic.EvidenceEnvironment) (evidence : Dynamic.EvidenceEnvironment)
    (sameEvidence : CallableIndexedOwnedPreparedCatalogTypedNamedCallBounds.CallerEvidence callerEvidence evidence)
    (profile : compiled.compatible.checked.catalog.callableContracts = true)
    (runtime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) context (source caller.named))
    (covers : evidence.Covers context)
    (sameReason : rootReasonAt = selected.diagnostics.program.reasonAt caller.named.signature.key)
    (inputs : ∀ {compilerScope scope id lowered},
      RawLambda selected root expressionSyntax (context := context) (compilerScope := compilerScope) scope id lowered →
      CompilerInputs (headers := headers) selected root expressionSyntax evidence
        (context := context) (compilerScope := compilerScope) scope id lowered) :
    Recipes (headers := headers) selected root expressionSyntax context callerEvidence evidence (.ordinary caller) := by
  apply Recipes.ordinary member selected root expressionSyntax context callerEvidence evidence sameEvidence
  intro compilerScope scope id lowered raw
  exact CompilerInputs.ordinary selected root expressionSyntax profile runtime covers sameReason (inputs raw) (fun _ _ _ => False)

/-- The selected principal and full dictionary are retained by the same static
compiler-input producer; no earlier weak qualification is inverted. -/
theorem of_principal_inputs {method : ExecutableImplMethods.CheckedMethod}
    (principal : CallableIndexedOwnedMethodPrincipal.Principal compiled method)
    (selected : SelectedReceipt compiled principal.named principal.cached.index)
    {rootFuel : Nat} {rootSource : TypedSource} {rootScope : SourceCoreLocalCell.Scope}
    {rootId : ExpressionId} {rootReasonAt : ExpressionId → Word} {rootLowered : SourceCoreBasic.LoweredExpr}
    (root : RootPolicyReceipt (compiled := compiled) principal.named (lowered compiled selected.diagnostics)
      selected.code selected.compilation rootFuel rootSource rootScope rootId rootReasonAt rootLowered)
    (expressionSyntax : TypedSource → ExpressionId → Prop) (context : SourceSemantics.Context)
    (profile : compiled.compatible.checked.catalog.callableContracts = true)
    (runtime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) context (source principal.named))
    (covers : principal.dictionary.Covers context)
    (inputs : ∀ {compilerScope scope id lowered},
      RawLambda selected root expressionSyntax (context := context) (compilerScope := compilerScope) scope id lowered →
      CompilerInputs (headers := headers) selected root expressionSyntax principal.dictionary
        (context := context) (compilerScope := compilerScope) scope id lowered) :
    Recipes (headers := headers) selected root expressionSyntax context (some principal.dictionary)
      principal.dictionary (.principal principal.named) := by
  apply Recipes.principal principal selected root expressionSyntax context
  intro compilerScope scope id lowered raw
  exact CompilerInputs.principal principal selected root expressionSyntax profile runtime covers (inputs raw) (fun _ _ _ => False)
end Recipes

section Semantics
variable {callerEvidence : Option Dynamic.EvidenceEnvironment} {evidence : Dynamic.EvidenceEnvironment}
  {origin : Origin compiled}
  (recipes : Recipes (headers := headers) selected root expressionSyntax context callerEvidence evidence origin)
  {keys : List (Key compiled (Program.ofChecked compiled.sourceProgram))}
  {bodyRegistry registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  (owner : OwnedKey keys) (profile : compiled.compatible.checked.catalog.callableContracts = true)
  (owners : CallableIndexedOwnedPreparedPositiveFunctionOrigins.OwnerCover headers keys bodyRegistry profile)
  (complete : RecursiveNamedCatalogNativeContexts.Complete
    (prepared := compiled.indexed.ancestry) (values := .initial compiled.compatible.checked)
    (program := Program.ofChecked compiled.sourceProgram)
    (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed) headers)
  (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
  (runtime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) context (source named))
  (covers : evidence.Covers context)

local notation "nativeFacet" => CallableIndexedOwnedPreparedSelectedNativeFamilyQualification.facet (compiled := compiled) headers
local notation "functions" => CallableIndexedOwnedPreparedPositiveFunctionOrigins.functions nativeFacet headers keys bodyRegistry faults profile
local notation "bridge" => Origin.bridge (headers := headers) origin owner
local notation "model" => CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions

include recipes profile owners complete wellFormed runtime covers in
/-- Original positive runtime formation runs once at this same raw occurrence. -/
theorem preserves_at (size : Nat) :
    CallableIndexedOwnedAdmittedExpressionBounds.PreservesAt bridge model context evidence (source named)
      (RawLambda selected root expressionSyntax (context := context) (compilerScope := compilerScope)) faults size := by
  intro scope id lowered raw
  cases recipes with
  | ordinary member selected root expressionSyntax context callerEvidence evidence sameEvidence build =>
    exact CallableIndexedOwnedPreparedSelectedPositiveOrdinaryLambdaHeads.preserves_at
      (profile := profile) (owners := owners) (member := member) (complete := complete)
      (wellFormed := wellFormed) (runtime := runtime) (covers := covers)
      selected root expressionSyntax headers owner size (build raw)
  | principal principal selected root expressionSyntax context build =>
    exact CallableIndexedOwnedPreparedSelectedPositivePrincipalLambdaHeads.preserves_at
      (profile := profile) (owners := owners) (complete := complete)
      (wellFormed := wellFormed) (runtime := runtime) (covers := covers)
      principal selected root expressionSyntax headers owner size (build raw)

include recipes profile owners complete wellFormed runtime covers in
/-- Reflection retains its own native grade and reconstructed Source grade. -/
theorem reflects_at (size : Nat) :
    CallableIndexedOwnedAdmittedExpressionBounds.ReflectsAt bridge model context evidence (source named)
      (RawLambda selected root expressionSyntax (context := context) (compilerScope := compilerScope)) faults size := by
  intro scope id lowered raw
  cases recipes with
  | ordinary member selected root expressionSyntax context callerEvidence evidence sameEvidence build =>
    exact CallableIndexedOwnedPreparedSelectedPositiveOrdinaryLambdaHeads.reflects_at
      (profile := profile) (owners := owners) (member := member) (complete := complete)
      (wellFormed := wellFormed) (runtime := runtime) (covers := covers)
      selected root expressionSyntax headers owner size (build raw)
  | principal principal selected root expressionSyntax context build =>
    exact CallableIndexedOwnedPreparedSelectedPositivePrincipalLambdaHeads.reflects_at
      (profile := profile) (owners := owners) (complete := complete)
      (wellFormed := wellFormed) (runtime := runtime) (covers := covers)
      principal selected root expressionSyntax headers owner size (build raw)
end Semantics

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedEligibleSelectedLambdaRecipes
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedPairedNativeMatchCollectors
/-! The same match certificate retains actual and fixed native witnesses.
Two independent constructor inversions strengthen one accepted compiler
certificate. One finite_children call then keeps the original ordered body
requests, with both typings at their identical scopes and code. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedPairedNativeMatchCollectors
open Core Frontend SourceInference SourceCoreCompatibleDataMatches
open CompatibleMatchCertificates GenericMatchChildren

/-- Native witnesses are supplied only for the actual emitted scrutinee and
ordered body requests. Their result types and contexts remain independent. -/
theorem finite_typed_of_lower
    {compilation : SourceCoreCompatibleDataMatches.Context}
    {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
    {active : TypeSystem.Substitution} {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
    (onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error)
    (allocator : compilation.sourceCells = some (SourceCoreCallableIndexedAllocationFrames.allocator frame globals
      (layouts.allocatorAt owner active onError)))
    {definitions : DataEnvironment} (sameDefinitions : compilation.definitions = definitions)
    {lowerExpression : ExpressionLowerer} {lowerBody : BodyLowerer} {fuel : Nat}
    {source : TypedSource} {scope : Scope} {id : StatementId} {resolution : MatchResolution}
    {result : Ty} {reasonAt : ExpressionId → Word} {reason : Word} {code : Expr}
    {expressionCertificate : ExpressionCertificate} {administrative fixedAdministrative : Core.Context}
    (expressionExtract : ∀ childFuel lowered,
      lowerExpression childFuel source scope resolution.scrutinee reasonAt = .ok lowered →
      ∀ {nativeType fixedNativeType}, HasType (SourceCoreLocalCell.coreContext scope ++ administrative)
        lowered.expression nativeType definitions →
      HasType (SourceCoreLocalCell.coreContext scope ++ fixedAdministrative)
        lowered.expression fixedNativeType definitions → expressionCertificate scope resolution.scrutinee lowered)
    (accepted : lowerWithReasons compilation lowerExpression lowerBody fuel source scope id resolution
      result reasonAt reason = .ok code)
    {type fixedType : Ty}
    (typed : HasType (SourceCoreLocalCell.coreContext scope ++ administrative) code type definitions)
    (fixedTyped : HasType (SourceCoreLocalCell.coreContext scope ++ fixedAdministrative) code fixedType definitions) :
    ∃ requests,
      Certificate compilation source scope id resolution result reason expressionCertificate (Occurs requests) code ∧
      requests.length = resolution.cases.length + (if resolution.defaultBody.isSome then 1 else 0) ∧
      ∀ request ∈ requests,
        (∃ childFuel, lowerBody childFuel source request.scope request.statements result reasonAt reason = .ok request.code) ∧
        HasType (SourceCoreLocalCell.coreContext request.scope ++ administrative) request.code type definitions ∧
        HasType (SourceCoreLocalCell.coreContext request.scope ++ fixedAdministrative) request.code fixedType definitions := by
  have raw := certificate_of_lowerWithReasons
    (expressionCertificate := fun scope id lowered => ∃ childFuel,
      lowerExpression childFuel source scope id reasonAt = .ok lowered)
    (bodyCertificate := fun scope statements code => ∃ childFuel,
      lowerBody childFuel source scope statements result reasonAt reason = .ok code)
    (fun childFuel _ _ _ generated => ⟨childFuel, generated⟩)
    (fun childFuel _ _ _ generated => ⟨childFuel, generated⟩) accepted
  have actual := CallableIndexedOwnedPreparedNativeMatchCollectors.typed_expressions_and_bodies
    onError allocator sameDefinitions raw typed
  have paired := CallableIndexedOwnedPreparedNativeMatchCollectors.typed_expressions_and_bodies
    onError allocator sameDefinitions actual fixedTyped
  have selected := Certificate.mapExpressionAt paired (fun lowered generated => by
    obtain ⟨⟨⟨childFuel, compiled⟩, nativeType, childTyped⟩, fixedNativeType, fixedChildTyped⟩ := generated
    exact expressionExtract childFuel lowered compiled childTyped fixedChildTyped)
  obtain ⟨requests, receipt, length, known⟩ := Certificate.finite_children selected
  refine ⟨requests, receipt, length, ?_⟩
  intro request member
  obtain ⟨⟨generated, actualTyped⟩, fixedBodyTyped⟩ := known request member
  exact ⟨generated, actualTyped, fixedBodyTyped⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedPairedNativeMatchCollectors
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedOrdinaryCatalogPublicRoots
/-! An eligible actual public root selects a Header from the filtered ordinary
catalog. The real factory and first-match equations retain the original root,
physical slot and complete cached row. Unrelated roots need no coverage. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicRootMeaning
open Core Frontend SourceInference
open RecursiveNamedCatalog RecursiveNamedCatalogNativeContexts

/-- Exact first-match provenance selects a member of any ordinary Header
inventory. Its retained physical position identifies the complete cached row. -/
theorem selection_at
    {compiled : SourceCoreUnifiedCompilation.Compiled}
    {values : SourceCoreCompatibleValues.Context}
    {ambient : AmbientDefinitions values.checked.catalog.definitions}
    {program : Program}
    {headers : Inventory compiled.indexed.ancestry values ambient.definitions program}
    {header : Header compiled.indexed.ancestry values ambient.definitions program}
    (member : header ∈ headers)
    {root : SourceCoreIndexedSession.Root compiled}
    {entry : SourceCoreCallableIndexedPrograms.Entry compiled.indexed.layouts}
    (entryMember : entry ∈ compiled.indexed.entries)
    (shape : root.FactoryShape compiled entry)
    {named : SourceCoreGeneralFunctions.Function} {index : Nat}
    (found : compiled.indexed.base.functions.zipIdx.find?
      (fun item => decide (item.1.signature.key = entry.key)) = some (named, index))
    (slot : header.slot = index) : RootSelection headers root header := by
  have row : compiled.indexed.base.functions[index]? = some named :=
    List.mk_mem_zipIdx_iff_getElem?.mp (List.mem_of_find?_eq_some found)
  have selected : compiled.indexed.base.functions[index]? = some header.named := slot ▸ header.selected
  have same : header.named = named := Option.some.inj (selected.symm.trans row)
  refine ⟨member, entry, entryMember, shape, ?_⟩
  simpa only [same, slot] using found

end Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicRootMeaning

namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedOrdinaryCatalogReceipts
open Core Frontend SourceInference
open CallableIndexedOwnedPreparedFiniteNamedInventories (headers)
open RecursiveNamedPublicRootMeaning (RootSelection)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}

/-- One actual eligible cache row is sufficient for Source root selection. -/
theorem Catalog.selected_at (catalog : Catalog compiled)
    {root : SourceCoreIndexedSession.Root compiled}
    {entry : SourceCoreCallableIndexedPrograms.Entry compiled.indexed.layouts}
    (member : entry ∈ compiled.indexed.entries)
    (shape : root.FactoryShape compiled entry)
    {named : SourceCoreGeneralFunctions.Function} {index : Nat}
    (found : compiled.indexed.base.functions.zipIdx.find?
      (fun item => decide (item.1.signature.key = entry.key)) = some (named, index))
    (eligible : Eligible compiled named.specialized) :
    ∃ header, RootSelection
      (values := .initial compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
      (program := Program.ofChecked compiled.sourceProgram)
      (headers catalog.rows) root header := by
  have selected : compiled.indexed.base.functions[index]? = some named :=
    List.mk_mem_zipIdx_iff_getElem?.mp (List.mem_of_find?_eq_some found)
  obtain ⟨header, retained, slot, _same⟩ := catalog.header_at selected eligible
  exact ⟨header, RecursiveNamedPublicRootMeaning.selection_at retained member shape found slot⟩

/-- Apply eligibility only to the first matching cache row of this actual
issued root. A caller may derive it from independent Source entry admission. -/
theorem Catalog.selected_of_issued (catalog : Catalog compiled)
    {root : SourceCoreIndexedSession.Root compiled}
    (issued : root.Issued compiled)
    (eligible : ∀ entry, entry ∈ compiled.indexed.entries → root.FactoryShape compiled entry →
      ∀ named index, compiled.indexed.base.functions.zipIdx.find?
        (fun item => decide (item.1.signature.key = entry.key)) = some (named, index) →
        Eligible compiled named.specialized) :
    ∃ header, RootSelection
      (values := .initial compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
      (program := Program.ofChecked compiled.sourceProgram)
      (headers catalog.rows) root header := by
  obtain ⟨entry, member, shape⟩ := issued
  have factory := shape
  obtain ⟨named, index, found, _rest⟩ := factory
  exact catalog.selected_at member shape found (eligible entry member shape named index found)

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedOrdinaryCatalogReceipts
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedOrdinaryCatalogPublicAdmission
/-! Independent Source entry admission supplies the eligible actual public row.
The exact target equation and successful public start determine its first
matching root and cached Header. Source arguments, dictionaries and heap
representation remain separate from this static selection receipt. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedOrdinaryCatalogReceipts
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open SourceCoreIndexedSession RecursiveNamedPublicStartMeaning RecursiveNamedPublicHistoryFrontdoor
open CallableIndexedOwnedPreparedFiniteNamedInventories (headers)
open RecursiveNamedPublicRootMeaning (RootSelection)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}

/-- Admission is required only for the actual first matching cache row. -/
theorem Catalog.selected_at_entry (catalog : Catalog compiled)
    (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
    {root : Root compiled}
    {publicEntry : SourceCoreCallableIndexedPrograms.Entry compiled.indexed.layouts}
    (member : publicEntry ∈ compiled.indexed.entries)
    (shape : root.FactoryShape compiled publicEntry)
    {named : SourceCoreGeneralFunctions.Function} {index : Nat}
    (found : compiled.indexed.base.functions.zipIdx.find?
      (fun item => decide (item.1.signature.key = publicEntry.key)) = some (named, index))
    {entry : Dynamic.ProgramEntry} {heap : Dynamic.Heap} {body : Dynamic.BodyInstance}
    (matched : CallableNamedMetadata.Matches named.specialized entry.instantiation)
    (valid : Dynamic.ProgramEntryValid (Program.ofChecked compiled.sourceProgram) entry heap body)
    (ordinaryReturn : entry.instantiation.returnComptime = false)
    (ordinaryParameters : ∀ flag ∈ entry.instantiation.parameterComptime, flag = false) :
    ∃ header, RootSelection
      (values := .initial compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
      (program := Program.ofChecked compiled.sourceProgram) (headers catalog.rows) root header ∧
      CallableNamedMetadata.Matches header.named.specialized entry.instantiation := by
  have selected : compiled.indexed.base.functions[index]? = some named :=
    List.mk_mem_zipIdx_iff_getElem?.mp (List.mem_of_find?_eq_some found)
  obtain ⟨header, retained, slot, same⟩ := catalog.header_at selected
    (CallableIndexedOwnedPreparedOrdinaryCatalog.eligible_of_entry wellFormed selected matched valid
      ordinaryReturn ordinaryParameters)
  exact ⟨header, RecursiveNamedPublicRootMeaning.selection_at retained member shape found slot,
    by simpa only [same] using matched⟩

/-- The actual target equation identifies the Source entry's complete cached
row. No caller-supplied Header or whole-root coverage is needed. -/
theorem Catalog.selected_entry (catalog : Catalog compiled)
    (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
    {root : Root compiled} (issued : root.Issued compiled)
    {entry : Dynamic.ProgramEntry} {heap : Dynamic.Heap} {body : Dynamic.BodyInstance}
    (target : SourceCompilationPlan.exactInstantiationKey compiled.indexed.base.plan entry.instantiation =
      .ok root.key)
    (valid : Dynamic.ProgramEntryValid (Program.ofChecked compiled.sourceProgram) entry heap body)
    (ordinaryReturn : entry.instantiation.returnComptime = false)
    (ordinaryParameters : ∀ flag ∈ entry.instantiation.parameterComptime, flag = false) :
    ∃ header, RootSelection
      (values := .initial compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
      (program := Program.ofChecked compiled.sourceProgram) (headers catalog.rows) root header ∧
      CallableNamedMetadata.Matches header.named.specialized entry.instantiation := by
  obtain ⟨publicEntry, member, shape⟩ := issued
  have factory := shape
  obtain ⟨named, index, found, key, rootKey, _rest⟩ := factory
  have selected : compiled.indexed.base.functions[index]? = some named :=
    List.mk_mem_zipIdx_iff_getElem?.mp (List.mem_of_find?_eq_some found)
  have matched := CallableNamedMetadata.matches_of_exact
    (show SourceCompilationPlan.exactInstantiationKey compiled.indexed.base.plan entry.instantiation =
      .ok named.signature.key by simpa only [rootKey, key] using target)
    (CallableIndexedOwnedPreparedOrdinaryCachedInputs.cached_record compiled selected)
  exact catalog.selected_at_entry wellFormed member shape found matched valid ordinaryReturn ordinaryParameters

/-- Recover one successful public start using independent Source entry
admission and its real compiled target. The returned receipt retains the exact
current native state and the Source match for its actual selected Header. -/
theorem Catalog.recover_start_entry (catalog : Catalog compiled)
    (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
    {recipe : Recipe} (prepared : Recipe.prepare compiled = .ok recipe)
    {nativeArtifact : Artifact} {session : Session nativeArtifact}
    (atRecipe : ArtifactRecipe nativeArtifact recipe)
    {world : StoreTyping} {store : Store} (native : session.NativeAt world store)
    {publicArtifact : SourceCoreExecution.Artifact}
    {publicSession : SourceCoreExecution.Session publicArtifact}
    {publicCheckpoint : SourceCoreExecution.Checkpoint publicArtifact}
    (atSession : publicSession.IndexedAt session)
    {key : Key} {publicArguments : List SourceCorePublicValues.Value} {fuel : Nat}
    {entry : Dynamic.ProgramEntry} {heap : Dynamic.Heap} {body : Dynamic.BodyInstance}
    (target : SourceCompilationPlan.exactInstantiationKey compiled.indexed.base.plan entry.instantiation =
      .ok key)
    (valid : Dynamic.ProgramEntryValid (Program.ofChecked compiled.sourceProgram) entry heap body)
    (ordinaryReturn : entry.instantiation.returnComptime = false)
    (ordinaryParameters : ∀ flag ∈ entry.instantiation.parameterComptime, flag = false)
    (accepted : publicSession.start key publicArguments fuel = .ok publicCheckpoint) :
    ∃ request : Started (headers catalog.rows) prepared publicCheckpoint session key publicArguments fuel world store,
      CallableNamedMetadata.Matches request.header.named.specialized entry.instantiation := by
  apply RecursiveNamedPublicPhysicalFrontdoor.recover_start_at_with prepared catalog.inputs catalog.rows
    atRecipe native atSession (fun _ header =>
      CallableNamedMetadata.Matches header.named.specialized entry.instantiation) _ accepted
  intro root selected
  have sameCompiled := Recipe.prepare_compiled prepared
  cases sameCompiled
  change recipe.roots.find? (fun candidate => decide (candidate.key = key)) = some root at selected
  have issued := Recipe.prepare_roots prepared (List.mem_of_find?_eq_some selected)
  have keyEq : root.key = key := by simpa only [decide_eq_true_eq] using (List.find?_some selected)
  exact catalog.selected_entry wellFormed issued (by simpa only [keyEq] using target)
    valid ordinaryReturn ordinaryParameters

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedOrdinaryCatalogReceipts

namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedOrdinaryCatalog
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open SourceCoreIndexedSession RecursiveNamedPublicStartMeaning RecursiveNamedPublicHistoryFrontdoor
open CallableIndexedOwnedPreparedOrdinaryCatalogReceipts
open CallableIndexedOwnedPreparedFiniteNamedInventories (headers)

/-- Accepted compilation and independent Source entry admission produce the
ordinary catalog and recover this actual public start in one endpoint. -/
theorem recover_start_entry {compiled : SourceCoreUnifiedCompilation.Compiled}
    (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
    {recipe : Recipe} (prepared : Recipe.prepare compiled = .ok recipe)
    {nativeArtifact : Artifact} {session : Session nativeArtifact}
    (atRecipe : ArtifactRecipe nativeArtifact recipe)
    {world : StoreTyping} {store : Store} (native : session.NativeAt world store)
    {publicArtifact : SourceCoreExecution.Artifact}
    {publicSession : SourceCoreExecution.Session publicArtifact}
    {publicCheckpoint : SourceCoreExecution.Checkpoint publicArtifact}
    (atSession : publicSession.IndexedAt session)
    {key : Key} {publicArguments : List SourceCorePublicValues.Value} {fuel : Nat}
    {entry : Dynamic.ProgramEntry} {heap : Dynamic.Heap} {body : Dynamic.BodyInstance}
    (target : SourceCompilationPlan.exactInstantiationKey compiled.indexed.base.plan entry.instantiation =
      .ok key)
    (valid : Dynamic.ProgramEntryValid (Program.ofChecked compiled.sourceProgram) entry heap body)
    (ordinaryReturn : entry.instantiation.returnComptime = false)
    (ordinaryParameters : ∀ flag ∈ entry.instantiation.parameterComptime, flag = false)
    (accepted : publicSession.start key publicArguments fuel = .ok publicCheckpoint) :
    ∃ catalog : Catalog compiled,
      ∃ request : Started (headers catalog.rows) prepared publicCheckpoint session key publicArguments fuel world store,
      CallableNamedMetadata.Matches request.header.named.specialized entry.instantiation := by
  obtain ⟨catalog⟩ := of_compiled compiled wellFormed
  obtain ⟨request, matched⟩ := catalog.recover_start_entry wellFormed prepared atRecipe native atSession
    target valid ordinaryReturn ordinaryParameters accepted
  exact ⟨catalog, request, matched⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedOrdinaryCatalog
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedOrdinarySamePolicyLambdaProducer
/-! A nested ordinary lambda retains the exact policy, compiler view and child
budget of the closure being invoked. Its Site is derived from that accepted
action and the actual native child typing. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2000000
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedOrdinarySamePolicyLambdaProducer
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedLambdaValues CallableIndexedNamedGeneration CallableIndexedLambdaGeneration
open CallableIndexedOwnedContextualLambdaProducerReceipts (Produced)
open CallableLambdaBodyReachability

private theorem lambda_policy
    {checked : SourceCoreCompatibleCatalog.Checked} {prepared : CallableIndexedNamedGeneration.Prepared checked}
    {named : Named} {diagnostics : SourceCoreDataPlaceFaultSites.Program} {namedCode : Expr}
    {compilation : Compilation prepared named diagnostics namedCode} {rootFuel : Nat}
    {policy : SourceCoreFunctions.Policy}
    (recipe : CallableIndexedOwnedContextualLambdaPolicyRecipes.PolicyRecipe compilation rootFuel policy)
    {source : TypedSource} {id : ExpressionId} {node : ExpressionNode}
    {parameters : List TypedBinder} {result : TypeSystem.Ty} {statements : List StatementId}
    (found : source.lookupExpression? id = some node) (form : node.form = .lambda parameters result statements)
    (requirements : node.requirements = []) (coercions : node.coercions = [])
    (ordinary : prepared.base.locals.bindings.find? (fun binding =>
      decide (binding.caller = (context prepared named).owner ∧ binding.initializer = id)) = none)
    (scope : SourceCoreLocalCell.Scope) (reasonAt : ExpressionId → Word) :
    policy.readExpression source id = SourceCoreCompatibleDataExpressions.readExpression checked source id ∧
    ∀ child budget, (match policy.lowerSpecial? with
      | none => (Except.ok none : Except SourceCoreBasic.Error (Option SourceCoreBasic.LoweredExpr))
      | some lower => lower (context prepared named) child budget source scope id reasonAt) = .ok none := by
  have sameSource : SourceCoreGeneralFunctions.contextualSource prepared.base.sourceProgram
      (context prepared named).plan prepared.base.locals (context prepared named).owner none source id = .ok source := by
    simp [SourceCoreGeneralFunctions.contextualSource, found, form]
  constructor
  · rw [recipe.readExpression]
    simp only [sameSource, bind, Except.bind]
    rfl
  · intro child budget
    rw [recipe.lowerSpecial]
    unfold CallableIndexedOwnedContextualLambdaPolicyRecipes.special
    have owned : SourceCompilationPlan.ordinaryOwnedRequirements? node = some [] := by
      unfold SourceCompilationPlan.ordinaryOwnedRequirements?
      rw [requirements, coercions]
      rfl
    have noEvidence : SourceCoreEvidence.lowerWithProjector prepared.base.sourceProgram
        ((representation prepared).atContext named.signature.key []).expressions.projectType
        named.specialized (context prepared named) child budget source scope id reasonAt
        (SourceCoreGeneralFunctions.callablePolicy prepared.base.callableContext []) = .ok none := by
      simp [SourceCoreEvidence.lowerWithProjector, found, form, owned, requirements, coercions]
    simp only [sameSource, bind, Except.bind, found, pure, Except.pure, ordinary, Option.filter_none, noEvidence, form]

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {function : Dynamic.Closure} {captured : SourceCoreLocalCell.Scope} {administrative : Core.Context}
  (code : Code compiled.indexed function captured administrative)
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  (support : CallableIndexedOwnedOrdinaryLambdaSupport.Support code registry faults)
  (provenance : CallableIndexedOwnedContextualLambdaProvenance.OrdinaryAt code support)
  {sourceContext : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
  {scope : SourceCoreLocalCell.Scope} {id : ExpressionId} {childFuel : Nat}
  {lowered : SourceCoreBasic.LoweredExpr}

include provenance in
theorem of_expression
    (profile : compiled.compatible.checked.catalog.callableContracts = true)
    {node : ExpressionNode} {reported : Ty}
    {parameters : List TypedBinder} {result : TypeSystem.Ty} {statements : List StatementId}
    (found : function.source.lookupExpression? id = some node)
    (form : node.form = .lambda parameters result statements)
    (owner : id.occurrence.owner = function.source.owner)
    (requirements : node.requirements = []) (coercions : node.coercions = [])
    (ordinary : compiled.indexed.base.locals.bindings.find? (fun binding =>
      decide (binding.caller = (context compiled.indexed support.caller.named).owner ∧ binding.initializer = id)) = none)
    (read : SourceCoreCompatibleDataExpressions.readExpression compiled.compatible.checked function.source id = .ok (node, reported))
    (reached : Reaches function.source (function.body.map NodeId.statement) (.expression id))
    (accepted : SourceCoreFunctions.lowerExpressionWithPolicy code.policy code.lowerBody childFuel
      code.compilation code.view scope id code.reasonAt = .ok lowered)
    {nativeType : Ty}
    (nativeTyped : HasType (SourceCoreLocalCell.coreContext scope ++
      RecursiveNamedLambdaFormationHeads.nativePrefix (values := .initial compiled.compatible.checked) support.caller)
      lowered.expression nativeType compiled.indexed.layouts.definitions) :
    ∃ produced : Produced (compiled := compiled) support.caller.named parameters result statements sourceContext evidence
      scope (RecursiveNamedLambdaFormationHeads.nativePrefix (values := .initial compiled.compatible.checked) support.caller) id lowered,
      produced.site.code.view = code.view ∧ produced.site.code.reasonAt = code.reasonAt := by
  have nonzero : childFuel ≠ 0 := by
    intro zero
    simp only [zero, SourceCoreFunctions.lowerExpressionWithPolicy] at accepted
    cases accepted
  obtain ⟨fuel, fuelEq⟩ := Nat.exists_eq_succ_of_ne_zero nonzero
  have viewFound := (provenance.body_view id reached).symm.trans found
  have viewRead := (CallableIndexedOwnedPreparedStagedRecursiveBodyViewTransport.compatible_read_eq
    code.viewOfSource (provenance.body_view id reached)).symm.trans read
  obtain ⟨diagnostics, namedCode, compilation, rootFuel, issued, bodyRecipe, recipe, sameCompilation⟩ := provenance.issued_recipe
  have pointwise := lambda_policy recipe viewFound form requirements coercions ordinary scope code.reasonAt
  have actualAccepted := fuelEq ▸ accepted
  rw [support.compilation] at actualAccepted
  have special : DecoratedFunctionCode.SpecialPasses code.policy code.lowerBody fuel
      (context compiled.indexed support.caller.named) code.view scope id code.reasonAt := pointwise.2 _ _
  obtain ⟨certificate⟩ := CallableIndexedLambdaCertificates.of_accepted special
    (owner.trans code.viewOfSource.owner) viewFound (pointwise.1.trans viewRead) form actualAccepted
  have hook : code.policy.rawLambdaExpression = SourceCoreCallableIndexedAncestry.expressionHook
      compiled.indexed.ancestry support.caller.named.signature.key [] := by
    simpa only [support.compilation, support.active, CallableIndexedNamedGeneration.context, CompatibleNamedBody.bodyContext] using code.expressionProfile
  have callables : code.policy.callables = SourceCoreGeneralFunctions.callablePolicy
      (some compiled.indexed.ancestry.graph.inputs.callable) [] := support.active ▸ code.callables
  have native := CallableIndexedOwnedPreparedLambdaOccurrenceNativeTyping.certificate_native
    compiled.indexed certificate viewFound hook callables nativeTyped
  obtain ⟨site, identifier, emitted, samePolicy, sameBody, _sameFuel, view, reason,
      _sourceNode, _node, _sameCertificate⟩ :=
    CallableIndexedLambdaGeneration.of_certificate compiled.indexed sourceContext evidence [] certificate actualAccepted
      profile (by rw [← support.source]; exact code.viewOfSource)
      (by rw [← support.source]; exact found) form viewFound rfl recipe.sourceCells
      (by simpa only [support.compilation, support.active, CallableIndexedNamedGeneration.context, CompatibleNamedBody.bodyContext] using code.manifest)
      hook callables recipe.projectType (by rw [recipe.snapshotLambda]) native
  have issuedRecipe : CallableIndexedOwnedContextualLambdaIssuedRecipes.Retained support.caller.named site.code := by
    apply CallableIndexedOwnedContextualLambdaIssuedRecipes.Retained.of_recipes (rootFuel := rootFuel)
      compilation issued (sameBody.trans bodyRecipe) _ site.compilation
    rw [samePolicy]
    exact recipe
  let produced : Produced (compiled := compiled) support.caller.named parameters result statements sourceContext evidence
      scope (RecursiveNamedLambdaFormationHeads.nativePrefix (values := .initial compiled.compatible.checked) support.caller) id lowered := {
    site := site
    identifier := identifier
    emitted := emitted
    binderPolicy := (congrArg SourceCoreFunctions.Policy.lowerBinder samePolicy).trans provenance.binder_policy
    recipe := issuedRecipe.body_recipe
    compilerPolicy := issuedRecipe.policy_recipe
    issuedRecipe := issuedRecipe }
  exact ⟨produced, view, reason⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedOrdinarySamePolicyLambdaProducer
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedOrdinarySamePolicyLambdaFormation
/-! Nested formation derives the inner frame from the actual outer closure's
Source typing and reached lexical context. Both views keep the original body
nodes, and the original policy supplies the exact emitted inner Site. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2400000
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedOrdinarySamePolicyLambdaFormation
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedLambdaValues CallableIndexedNamedGeneration CallableIndexedLambdaGeneration
open CallableIndexedOwnedContextualLambdaFormationReceipts (OrdinaryFormation)
open CallableLambdaBodyReachability

private theorem reached_body {source : TypedSource} {roots : List NodeId}
    {id : ExpressionId} {node : ExpressionNode} {parameters : List TypedBinder}
    {result : TypeSystem.Ty} {body : List StatementId}
    (parent : Reaches source roots (.expression id))
    (found : source.lookupExpression? id = some node) (form : node.form = .lambda parameters result body)
    {target : NodeId} (reached : Reaches source (body.map NodeId.statement) target) :
    Reaches source roots target := by
  induction reached with
  | root member => exact .expression parent found (by simpa only [form, ExpressionForm.references] using member)
  | expression _ selected edge ih => exact .expression ih selected edge
  | statement _ selected edge ih => exact .statement ih selected edge

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {function : Dynamic.Closure} {captured : SourceCoreLocalCell.Scope} {administrative : Core.Context}
  (code : Code compiled.indexed function captured administrative)
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  (support : CallableIndexedOwnedOrdinaryLambdaSupport.Support code registry faults)
  (provenance : CallableIndexedOwnedContextualLambdaProvenance.OrdinaryAt code support)
  {sourceContext : SourceSemantics.Context} {scope : SourceCoreLocalCell.Scope}
  {id : ExpressionId} {childFuel : Nat} {lowered : SourceCoreBasic.LoweredExpr}

include provenance in
theorem of_expression
    (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
    (profile : compiled.compatible.checked.catalog.callableContracts = true)
    {stages : Staging.Recursive.Registry} {child : Staging.Recursive.Scope}
    (selected : stages.Closure function child)
    {node : ExpressionNode} {reported : Ty} {result : TypeSystem.Ty} {parameters : List TypedBinder}
    {statement : StatementId} {returnNode : StatementNode} {expression : ExpressionId}
    (found : function.source.lookupExpression? id = some node)
    (form : node.form = .lambda parameters result [statement])
    (owner : id.occurrence.owner = function.source.owner)
    (requirements : node.requirements = []) (coercions : node.coercions = [])
    (ordinary : compiled.indexed.base.locals.bindings.find? (fun binding =>
      decide (binding.caller = (context compiled.indexed support.caller.named).owner ∧ binding.initializer = id)) = none)
    (read : SourceCoreCompatibleDataExpressions.readExpression compiled.compatible.checked function.source id = .ok (node, reported))
    (returnFound : function.source.lookupStatement? statement = some returnNode)
    (returnForm : returnNode.form = .returnStmt (some expression))
    (returnType : returnNode.type = result)
    (fields : Dynamic.RuntimeContextFields support.body.context sourceContext)
    (declarations : CompatibleExpressionReads.ScopeDeclarations function.source scope sourceContext)
    (sourceTyped : ExpressionHasType function.source sourceContext id node.type)
    (reached : Reaches function.source (function.body.map NodeId.statement) (.expression id))
    (accepted : SourceCoreFunctions.lowerExpressionWithPolicy code.policy code.lowerBody childFuel
      code.compilation code.view scope id code.reasonAt = .ok lowered)
    {nativeType : Ty}
    (nativeTyped : HasType (SourceCoreLocalCell.coreContext scope ++
      RecursiveNamedLambdaFormationHeads.nativePrefix (values := .initial compiled.compatible.checked) support.caller)
      lowered.expression nativeType compiled.indexed.layouts.definitions) :
    Nonempty (OrdinaryFormation (registry := registry) (faults := faults)
      support.caller sourceContext child.evidence scope id lowered) := by
  obtain ⟨produced, view, reason⟩ := CallableIndexedOwnedPreparedOrdinarySamePolicyLambdaProducer.of_expression
    (sourceContext := sourceContext) (evidence := child.evidence) code support provenance profile
    found form owner requirements coercions ordinary read reached accepted nativeTyped
  let inner := closure support.caller.named parameters result [statement] sourceContext child.evidence []
  have original : inner.source = function.source := support.source.symm
  have actualFound : function.source.lookupExpression? id = some produced.site.code.sourceNode := by
    simpa only [closure, produced.identifier, source, support.source] using produced.site.code.sourceFound
  have sameNode : produced.site.code.sourceNode = node := Option.some.inj (actualFound.symm.trans found)
  have innerTyped : ExpressionHasType inner.source sourceContext id produced.site.code.sourceNode.type := by
    simpa only [original, sameNode] using sourceTyped
  have facts : CallableIndexedOwnedOrdinaryLambdaSourceFacts.Facts inner id produced.site.code.sourceNode :=
    CallableIndexedOwnedOrdinaryLambdaSourceFacts.of_typed
      (by simpa only [original] using support.unique)
      (by simpa only [original] using actualFound) produced.site.code.sourceForm innerTyped (sameNode ▸ coercions)
  have runtime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) inner.context inner.source := by
    change Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) sourceContext inner.source
    rw [original]
    exact ((CallableIndexedOwnedLambdaSourceAdmission.runtime_at_parameters
      support.body.frame support.body.extended).1).transport fields
  have covers : inner.evidence.Covers inner.context := by
    change child.evidence.Covers sourceContext
    rw [stages.evidence selected]
    exact fields.covers support.body.valid.covers
  have frame := facts.frame runtime covers
  have ownership : LocalIdentityOwnership inner.source := by
    obtain ⟨_, certificate⟩ := RecursiveNamedHeaderSourceTyping.certificate support.caller wellFormed
    rw [original, support.source]
    change LocalIdentityOwnership support.caller.named.specialized.function.typedBody
    rw [← support.caller.agreement.source, support.caller.frame.source]
    exact certificate.local_identity_ownership
  have kinds := CallableIndexedOwnedLocalIdentityFreshness.lowered_parameter_kinds
    (values := .initial compiled.compatible.checked) produced.site.code ownership facts.contains facts.form
  have referenceIndex : produced.site.code.referenceIndex = scope.length + 1 + compiled.indexed.base.globals.length := by
    change SourceCoreCallableIndexedAncestry.creationReferenceIndex produced.site.code.compilation _ = _
    rw [produced.site.compilation]
    rfl
  obtain ⟨inputs, _finalContext, _bodyFacts, _bodyTyped, _completes⟩ :=
    CallableIndexedOwnedLiteralReturnLambdaStaticFacts.entry_of_source_facts
      (values := .initial compiled.compatible.checked) produced.site.code facts kinds referenceIndex
  have ledger : inner.context.solvedRequirements = produced.site.code.compilation.solvedRequirements := by
    rw [produced.site.compilation, ← support.compilation]
    exact fields.solvedRequirements.trans support.body.valid.ledger
  have invocationSource : child.source = inner.source := (stages.source selected).trans original.symm
  have innerReturn : inner.source.lookupStatement? statement = some returnNode := by simpa only [original] using returnFound
  have head : CallableIndexedOwnedAdmittedStagedTerminalStatements.Head child expression inner.body := by
    change CallableIndexedOwnedAdmittedStagedTerminalStatements.Head child expression [statement]
    exact .returning [] (by rw [invocationSource]; exact lookupStatement?_sound innerReturn) returnForm
  obtain ⟨readNode, childFound, childType, childTyped⟩ :=
    CallableIndexedOwnedPreparedStagedTerminalBodyTyping.at_parameters frame inputs.extended invocationSource head
  rw [invocationSource] at childFound childTyped
  have inside : Reaches function.source (function.body.map NodeId.statement) (.expression expression) :=
    reached_body reached found form (.statement (.root (by simp)) returnFound
      (by simp only [returnForm, StatementForm.references]; simp))
  have childOriginal : function.source.lookupExpression? expression = some readNode := by
    simpa only [original] using childFound
  have viewFound : produced.site.code.view.lookupStatement? statement = some returnNode := by
    rw [view]
    exact code.viewOfSource.symm.statement returnFound
  have viewRead : produced.site.code.view.lookupExpression? expression = some readNode := by
    rw [view]
    exact (provenance.body_view expression inside).symm.trans childOriginal
  have viewTyped : ExpressionHasType produced.site.code.view inputs.context expression readNode.type := by
    rw [view]
    exact CallableLambdaViewStaticTyping.expression
      (CallableIndexedLambdaBodyViewEdits.local_view code.viewOfSource)
      (CallableIndexedLambdaBodyViewEdits.avoids provenance.body_view) support.unique
      (by simpa only [original] using childTyped) inside
  obtain ⟨loweredBody, body, _sameInputs, syntaxTree⟩ := CallableIndexedOwnedPreparedReturnLambdaBodySupport.of_return_view
    produced.site.code produced.recipe inputs frame ledger profile rfl innerReturn returnForm returnType
    childFound childType childTyped viewFound viewRead viewTyped
  have bodyView : CallableIndexedOwnedContextualLambdaProvenance.BodyView produced.site.code := by
    intro childId childReached
    have path : Reaches function.source ([statement].map NodeId.statement) (.expression childId) := by
      change Reaches inner.source ([statement].map NodeId.statement) (.expression childId) at childReached
      rw [original] at childReached
      exact childReached
    rw [view]
    exact original ▸ provenance.body_view childId (reached_body reached found form path)
  have bodyReasons : CallableIndexedOwnedContextualLambdaProvenance.BodyReasons produced.site.code support.caller.named := by
    intro childId childReached
    have path : Reaches function.source ([statement].map NodeId.statement) (.expression childId) := by
      change Reaches inner.source ([statement].map NodeId.statement) (.expression childId) at childReached
      rw [original] at childReached
      exact childReached
    rw [reason]
    exact provenance.body_reasons childId (reached_body reached found form path)
  obtain ⟨callerReceipt⟩ := provenance.body_caller_receipt
  exact ⟨CallableIndexedOwnedContextualLambdaFormationReceipts.ordinary_of_producer support.caller produced
    (CallableIndexedOwnedPreparedReturnLambdaBodySupport.Syntax expression)
    (CallableIndexedOwnedPreparedReturnLambdaBodySupport.Child expression loweredBody) body bodyView bodyReasons
    (by simpa only [support.source] using declarations) syntaxTree facts.sourceType facts.ordinary facts.coercions
    ((callerReceipt.extend fields).with_evidence (stages.evidence selected))⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedOrdinarySamePolicyLambdaFormation
end
