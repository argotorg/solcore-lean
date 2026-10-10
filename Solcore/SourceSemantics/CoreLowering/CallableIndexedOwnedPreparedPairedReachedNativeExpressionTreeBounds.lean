import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedRawCompilerHeadNativeChildren
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedReachedAdmittedExpressionCallsHeads
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedReachedExpressionDiagnosticBounds
import Solcore.SourceSemantics.CoreLowering.CompatibleExpressionBuiltinRuntime

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
