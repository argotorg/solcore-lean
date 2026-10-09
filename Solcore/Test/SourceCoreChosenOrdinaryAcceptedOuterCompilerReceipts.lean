import Solcore.Test.SourceCoreChosenOrdinaryAcceptedParentCompilerReceipts
import Solcore.SourceSemantics.CoreLowering.CallableIndexedAllocationCompletion
import Solcore.SourceSemantics.CoreLowering.TypedLexicalControlTree

/-! The actual accepted named body retains its initialized allocation and
outer return. Finite original compiler inversions authenticate both children,
the marked request and the exact flow; no execution or body law is supplied. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192
namespace Tests.SourceCoreChosenOrdinaryAcceptedOuterCompilerReceipts
open Solcore Core Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open CallableIndexedNamedGeneration
open CompatibleEncoding (bind_ok)
open SourceCoreChosenOrdinaryAcceptedFixture SourceCoreChosenOrdinaryAcceptedHeader

def request (fixture : AcceptedFixture) : SourceCoreSourceCells.Request :=
  TypedLexicalControl.initializedRequest (source fixture.packet.named) (initialScope fixture.packet)
    fixture.graph.binder fixture.calls.payload

def returned (fixture : AcceptedFixture) : Expr :=
  LocalLoop.returnValue fixture.packet.named.signature.resultType fixture.calls.parent.expression

def emittedFlow (fixture : AcceptedFixture) (allocation : Expr) : Expr :=
  TypedLexicalControl.sequence fixture.packet.named.signature.resultType
    fixture.calls.initializer.expression allocation (returned fixture)

/-- Every field comes from the original named-body compiler action. -/
structure Receipt (fixture : AcceptedFixture) where
  bodyAccepted : SourceCoreLoops.lowerStatementsWithPolicy (policy fixture) 500 (source fixture.packet.named)
    (initialScope fixture.packet) [statementId fixture.packet 0, statementId fixture.packet 4]
    fixture.packet.named.signature.resultType
    (SourceCoreChosenOrdinaryAcceptedParentCompilerReceipts.parentReason fixture)
    fixture.calls.own.fellThroughReason fixture.calls.own.table.escapedReason = .ok fixture.calls.body
  binderAccepted : (policy fixture).lowerBinder (source fixture.packet.named) (initialScope fixture.packet)
    fixture.graph.binder = .ok fixture.calls.payload
  initializerAccepted : (policy fixture).lowerExpression 499 (source fixture.packet.named)
    (initialScope fixture.packet) (expressionId fixture.packet 1)
    (SourceCoreChosenOrdinaryAcceptedParentCompilerReceipts.parentReason fixture) = .ok fixture.calls.initializer
  initializerType : fixture.calls.initializer.type = fixture.calls.payload
  parentAccepted : (policy fixture).lowerExpression 498 (source fixture.packet.named)
    (SourceCoreChosenOrdinaryAcceptedParentCompilerReceipts.parentScope fixture) (expressionId fixture.packet 5)
    (SourceCoreChosenOrdinaryAcceptedParentCompilerReceipts.parentReason fixture) = .ok fixture.calls.parent
  parentType : fixture.calls.parent.type = fixture.packet.named.signature.resultType
  cells : (policy fixture).sourceCells = some (allocator fixture.packet.compiled.indexed fixture.packet.named)
  allocation : SourceCoreAllocationLayouts.Allocation fixture.packet.compiled.indexed.layouts
    fixture.packet.named.signature.key [] (request fixture)
  annotation : SourceCoreCallableIndexedAllocationFrames.Annotated fixture.packet.compiled.indexed.ancestry.layout.frame
    fixture.packet.compiled.indexed.base.globals.length
    (fixture.packet.compiled.indexed.layouts.allocatorAt fixture.packet.named.signature.key []
      (fun error => .sourceAllocation (reprStr error))) (request fixture)
  same : annotation.original = allocation.expression
  allocationAccepted : allocator fixture.packet.compiled.indexed fixture.packet.named (request fixture) = .ok annotation.expression
  flowAccepted : SourceCoreLoops.lowerFlowStatementsWithPolicy (policy fixture) 500 (source fixture.packet.named)
    (initialScope fixture.packet) [statementId fixture.packet 0, statementId fixture.packet 4]
    fixture.packet.named.signature.resultType
    (SourceCoreChosenOrdinaryAcceptedParentCompilerReceipts.parentReason fixture) true
    fixture.calls.own.table.escapedReason = .ok (emittedFlow fixture annotation.expression)
  emitted : fixture.calls.body = CompatibleStatements.finish fixture.packet.named.signature.resultType
    (emittedFlow fixture annotation.expression) fixture.calls.own.fellThroughReason fixture.calls.own.table.escapedReason

private theorem ensure_same {site : SourceCoreElaboration.ErrorSite} {expected actual : Ty}
    (accepted : SourceCoreBasic.ensureType site expected actual = .ok ()) : expected = actual := by
  unfold SourceCoreBasic.ensureType at accepted
  split at accepted
  · assumption
  · cases accepted

/-- The actual loop policy preserves the fixed read, binder and marked allocator. -/
theorem policy_fields (fixture : AcceptedFixture) :
    (policy fixture).readStatement = SourceCoreCompatibleDataExpressions.readStatement fixture.packet.compiled.compatible.checked ∧
    (policy fixture).sourceCells = some (allocator fixture.packet.compiled.indexed fixture.packet.named) ∧
    (policy fixture).lowerBinder (source fixture.packet.named) (initialScope fixture.packet) fixture.graph.binder =
      binderAction fixture.packet fixture.graph ∧
    (∀ fuel scope id reason, (policy fixture).lowerExpression fuel (source fixture.packet.named) scope id reason =
      SourceCoreGeneralFunctions.lowerContextualExpression fixture.packet.compiled.indexed.base.sourceProgram
        ((representation fixture.packet.compiled.indexed).atContext fixture.packet.named.signature.key [])
        fixture.packet.compiled.indexed.base.sourceProgram.signatures fixture.packet.compiled.indexed.base.locals
        fixture.calls.parents fixture.calls.own.assignments (effectiveDiagnostics fixture.packet.compiled fixture.packet.diagnostics)
        (context fixture.packet.compiled.indexed fixture.packet.named) fixture.packet.compiled.indexed.base.callableContext
        none none fuel (source fixture.packet.named) scope id reason) := by
  exact ⟨rfl, rfl, rfl, fun _ _ _ _ => rfl⟩

/-- One original body acceptance supplies the initialized and returned branches. -/
theorem of_body (fixture : AcceptedFixture) : Nonempty (Receipt fixture) := by
  obtain ⟨readPolicy, cells, binderPolicy, expressionPolicy⟩ := policy_fields fixture
  have bodyAccepted : SourceCoreLoops.lowerStatementsWithPolicy (policy fixture) 500 (source fixture.packet.named)
      (initialScope fixture.packet) [statementId fixture.packet 0, statementId fixture.packet 4]
      fixture.packet.named.signature.resultType
      (SourceCoreChosenOrdinaryAcceptedParentCompilerReceipts.parentReason fixture)
      fixture.calls.own.fellThroughReason fixture.calls.own.table.escapedReason = .ok fixture.calls.body := by
    simpa only [bodyAction, SourceCoreGeneralFunctions.bodyLowererWithRepresentation,
      fixture.calls.fuel, policy, initialScope, SourceCoreChosenOrdinaryAcceptedParentCompilerReceipts.parentReason]
      using fixture.calls.bodyCompiled
  have binderAccepted := binderPolicy.trans fixture.calls.binderPrepared
  have initializerAccepted : (policy fixture).lowerExpression 499 (source fixture.packet.named)
      (initialScope fixture.packet) (expressionId fixture.packet 1)
      (SourceCoreChosenOrdinaryAcceptedParentCompilerReceipts.parentReason fixture) = .ok fixture.calls.initializer := by
    simpa only [expressionPolicy, contextualAction, SourceCoreChosenOrdinaryAcceptedParentCompilerReceipts.parentReason]
      using fixture.calls.initializerCompiled
  have parentAccepted : (policy fixture).lowerExpression 498 (source fixture.packet.named)
      (SourceCoreChosenOrdinaryAcceptedParentCompilerReceipts.parentScope fixture) (expressionId fixture.packet 5)
      (SourceCoreChosenOrdinaryAcceptedParentCompilerReceipts.parentReason fixture) = .ok fixture.calls.parent := by
    simpa only [expressionPolicy, contextualAction, SourceCoreChosenOrdinaryAcceptedParentCompilerReceipts.parentReason,
      SourceCoreChosenOrdinaryAcceptedParentCompilerReceipts.parentScope]
      using fixture.calls.parentCompiled
  simp only [SourceCoreChosenOrdinaryAcceptedParentCompilerReceipts.parentScope] at parentAccepted
  have accepted := bodyAccepted
  unfold SourceCoreLoops.lowerStatementsWithPolicy at accepted
  obtain ⟨flow, generated, completed⟩ := bind_ok accepted
  have flowGenerated := generated
  rw [SourceCoreLoops.lowerFlowStatementsWithPolicy, readPolicy, fixture.calls.initializedRead] at generated
  simp only [bind, Except.bind, fixture.graph.initializedForm, binderAccepted, initializerAccepted] at generated
  obtain ⟨checked, payloadMatch, generated⟩ := bind_ok generated
  cases checked
  have payloadMatch := ensure_same payloadMatch
  obtain ⟨tail, tailGenerated, generated⟩ := bind_ok generated
  rw [SourceCoreLoops.lowerFlowStatementsWithPolicy, readPolicy, fixture.calls.returnedRead] at tailGenerated
  simp only [bind, Except.bind, fixture.graph.outerReturnForm] at tailGenerated
  rw [parentAccepted] at tailGenerated
  obtain ⟨checked, _, tailGenerated⟩ := bind_ok tailGenerated
  cases checked
  obtain ⟨checked, resultMatch, tailGenerated⟩ := bind_ok tailGenerated
  cases checked
  have resultMatch := ensure_same resultMatch
  have tailEq : tail = returned fixture := Except.ok.inj tailGenerated.symm
  subst tail
  simp only [SourceCoreSourceCells.letInitialized, cells] at generated
  obtain ⟨allocationCode, allocationAccepted, generated⟩ := bind_ok generated
  obtain ⟨allocation, annotation, same, allocationEq⟩ :=
    CallableIndexedAllocationCompletion.accepted_receipts
      (fun error => .sourceAllocation (reprStr error)) allocationAccepted
  have flowEq : flow = emittedFlow fixture annotation.expression := by
    cases generated
    rw [allocationEq]
    rfl
  subst flow
  have emitted : fixture.calls.body = CompatibleStatements.finish fixture.packet.named.signature.resultType
      (emittedFlow fixture annotation.expression) fixture.calls.own.fellThroughReason fixture.calls.own.table.escapedReason :=
    (Except.ok.inj completed).symm
  exact ⟨⟨bodyAccepted, binderAccepted, initializerAccepted, payloadMatch.symm, parentAccepted, resultMatch.symm,
    cells, allocation, annotation, same, allocationEq ▸ allocationAccepted, flowGenerated, emitted⟩⟩

/-- Raw Source annotation and native initializer payload remain independent. -/
theorem raw_initializer_type (fixture : AcceptedFixture)
    (metadata : SourceCoreChosenOrdinaryAcceptedOuterTyping.Metadata fixture) :
    fixture.graph.lambdaNode.type = fixture.graph.binder.scheme.body := by
  rw [metadata.scheme]
  exact fixture.graph.lambdaType

/-- The original Header receives the same emitted body and lexical scope. -/
theorem emitted_at_header (fixture : AcceptedFixture) {caller : ActualHeader fixture}
    (atHeader : HeaderAt fixture caller) (receipt : Receipt fixture) :
    caller.body = CompatibleStatements.finish fixture.packet.named.signature.resultType
      (emittedFlow fixture receipt.annotation.expression)
      fixture.calls.own.fellThroughReason fixture.calls.own.table.escapedReason ∧
    caller.bindings.reverse.map (fun binding => (binding.1.id, binding.2)) = initialScope fixture.packet := by
  exact ⟨atHeader.body.trans receipt.emitted, congrArg (fun bindings =>
    bindings.reverse.map (fun binding => (binding.1.id, binding.2))) atHeader.bindings⟩

/-- Body and both expression children retain the actual supplied chosen root. -/
structure ChosenOuterReceipt (fixture : AcceptedFixture) {caller : ActualHeader fixture}
    {compilation : Compilation fixture.packet.compiled.indexed caller.named
      (effectiveDiagnostics fixture.packet.compiled fixture.packet.diagnostics) fixture.packet.namedCode}
    (root : SourceCoreChosenOrdinaryAcceptedParentCompilerReceipts.Root fixture caller compilation) where
  outer : Receipt fixture
  chosen : SourceCoreChosenOrdinaryAcceptedParentCompilerReceipts.ChosenParentReceipt fixture root

/-- The existing original initializer selector runs once. Body extraction uses
the independently retained actual named acceptance without another selector. -/
theorem at_original_root (fixture : AcceptedFixture) {caller : ActualHeader fixture}
    (atHeader : HeaderAt fixture caller)
    (shape : SourceCoreChosenOrdinaryAcceptedTyping.Shape fixture)
    (metadata : SourceCoreChosenOrdinaryAcceptedBodyMetadata.Receipt fixture.packet fixture.graph)
    (inventory : SourceCoreChosenOrdinaryAcceptedStaticInventory.Inventory fixture) :
    ∃ actualCompilation : Compilation fixture.packet.compiled.indexed caller.named
        (effectiveDiagnostics fixture.packet.compiled fixture.packet.diagnostics) fixture.packet.namedCode,
      ∃ actualRoot : SourceCoreChosenOrdinaryAcceptedParentCompilerReceipts.Root fixture caller actualCompilation,
        Nonempty (ChosenOuterReceipt fixture actualRoot) := by
  obtain ⟨actualCompilation, actualRoot, ⟨chosen⟩⟩ :=
    SourceCoreChosenOrdinaryAcceptedParentCompilerReceipts.at_original_root fixture atHeader shape metadata inventory
  obtain ⟨outer⟩ := of_body fixture
  exact ⟨actualCompilation, actualRoot, ⟨⟨outer, chosen⟩⟩⟩

end Tests.SourceCoreChosenOrdinaryAcceptedOuterCompilerReceipts
