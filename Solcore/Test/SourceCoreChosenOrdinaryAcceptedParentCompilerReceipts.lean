import Solcore.Test.SourceCoreChosenOrdinaryAcceptedLiteralFactory
import Solcore.Test.SourceCoreChosenOrdinaryAcceptedOuterTyping
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedIndirectCompilerReceipts
import Solcore.SourceSemantics.CoreLowering.CompatibleExpressionBuiltinCertificates

/-! The original accepted parent and chosen lambda retain one initializer
policy. Compiler receipts expose the actual callee, physical arguments and
prepared site without supplying execution, dispatch or body meaning. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 3000000
set_option maxRecDepth 8192
namespace Tests.SourceCoreChosenOrdinaryAcceptedParentCompilerReceipts
open Solcore Core Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open CallableIndexedNamedGeneration CallableIndexedLambdaGeneration
open CallableIndexedOwnedLiteralReturnSiteShells
open CallableIndexedOwnedPreparedMixedBodySiteInputs
open SourceCoreChosenOrdinaryAcceptedFixture SourceCoreChosenOrdinaryAcceptedHeader

/-- The actual fresh let binding precedes this parent occurrence. -/
def parentScope (fixture : AcceptedFixture) : SourceCoreLocalCell.Scope :=
  (fixture.graph.binder.id, fixture.calls.payload) :: initialScope fixture.packet

def parentReason (fixture : AcceptedFixture) : ExpressionId → Word :=
  (effectiveDiagnostics fixture.packet.compiled fixture.packet.diagnostics).reasonAt
    fixture.packet.named.signature.key

abbrev Root (fixture : AcceptedFixture) (caller : ActualHeader fixture)
    (compilation : Compilation fixture.packet.compiled.indexed caller.named
      (effectiveDiagnostics fixture.packet.compiled fixture.packet.diagnostics) fixture.packet.namedCode) :=
  LiteralRootReceipt (compiled := fixture.packet.compiled) caller.named
    (effectiveDiagnostics fixture.packet.compiled fixture.packet.diagnostics) fixture.packet.namedCode compilation
    498 (source fixture.packet.named) (initialScope fixture.packet) (expressionId fixture.packet 1)
    (parentReason fixture) fixture.calls.initializer

variable (fixture : AcceptedFixture) {caller : ActualHeader fixture}
  {compilation : Compilation fixture.packet.compiled.indexed caller.named
    (effectiveDiagnostics fixture.packet.compiled fixture.packet.diagnostics) fixture.packet.namedCode}
  (root : Root fixture caller compilation)

abbrev Compiler :=
  CallableIndirectCallCertificates.Receipt root.root.selected.policy root.root.selected.lowerBody
    497 (context fixture.packet.compiled.indexed caller.named) (source fixture.packet.named)
    (parentScope fixture) (expressionId fixture.packet 5) (expressionId fixture.packet 9)
    [expressionId fixture.packet 6] indirectMetadata (parentReason fixture) fixture.calls.parent

/-- Both original and policy-read nodes are authenticated at the same parent. -/
structure ParentReceipt where
  compiler : Compiler fixture root
  accepted : SourceCoreFunctions.lowerExpressionWithPolicy root.root.selected.policy root.root.selected.lowerBody
    498 (context fixture.packet.compiled.indexed caller.named) (source fixture.packet.named)
    (parentScope fixture) (expressionId fixture.packet 5) (parentReason fixture) = .ok fixture.calls.parent
  original : compiler.original = fixture.graph.parent
  node : compiler.node = fixture.graph.parent
  parent : CallableIndexedOwnedIndirectSourceAdapters.SourceParent compiler
  prepared : CallableIndexedOwnedIndirectSourceAdapters.Prepared compiler
    fixture.packet.compiled.indexed.ancestry.graph.inputs.callable

/-- This finite extraction consumes the actual selected policy acceptance. -/
theorem at_root (atHeader : HeaderAt fixture caller)
    (accepted : SourceCoreFunctions.lowerExpressionWithPolicy root.root.selected.policy root.root.selected.lowerBody
      498 (context fixture.packet.compiled.indexed caller.named) (source fixture.packet.named)
      (parentScope fixture) (expressionId fixture.packet 5) (parentReason fixture) = .ok fixture.calls.parent) :
    Nonempty (ParentReceipt fixture root) := by
  have ordinary : fixture.packet.compiled.indexed.base.locals.bindings.find? (fun binding =>
      decide (binding.caller = (context fixture.packet.compiled.indexed caller.named).owner ∧
        binding.initializer = expressionId fixture.packet 5)) = none := by
    simpa only [atHeader.named, context, CompatibleNamedBody.bodyContext] using fixture.calls.parentOrdinary
  have pointwise := CallableIndexedOwnedContextualCompilerPolicyProfiles.indirect_policy root.root
    (scope := parentScope fixture) (reasonAt := parentReason fixture)
    fixture.graph.parentFound fixture.graph.parentForm fixture.graph.parentRequirements
    fixture.graph.parentCoercions rfl ordinary
  have read : root.root.selected.policy.readExpression (source fixture.packet.named) (expressionId fixture.packet 5) =
      .ok (fixture.graph.parent, fixture.parentRows.parentCore) := by
    rw [pointwise.read]
    exact fixture.parentRows.parentRead
  obtain ⟨compiler⟩ := CallableIndirectCallCertificates.of_functions
    fixture.graph.parentFound fixture.graph.parentForm pointwise.special read fixture.graph.parentForm accepted
  have original : compiler.original = fixture.graph.parent :=
    Option.some.inj (compiler.found.symm.trans fixture.graph.parentFound)
  have node : compiler.node = fixture.graph.parent := (Prod.mk.inj (Except.ok.inj (compiler.read.symm.trans read))).1
  have nodeId : compiler.node.id = expressionId fixture.packet 5 :=
    (congrArg ExpressionNode.id node).trans (lookupExpression?_sound fixture.graph.parentFound).2
  obtain ⟨prepared⟩ := CallableIndexedOwnedIndirectSourceAdapters.Prepared.of_receipt
    compiler fixture.packet.compiled.indexed.ancestry.graph.inputs.callable [] root.root.callables nodeId
  refine ⟨⟨compiler, accepted, original, node, ?_, prepared⟩⟩
  exact ⟨original.symm ▸ fixture.graph.parentRequirements,
    original.symm ▸ fixture.graph.parentCoercions, rfl⟩

/-- Actual chosen code and parent code belong to one retained root receipt. -/
structure ChosenParentReceipt where
  parent : ParentReceipt fixture root
  chosen : CallableIndexedOwnedPreparedOrdinaryLambdaCompilerReceipts.Receipt caller
    (effectiveDiagnostics fixture.packet.compiled fixture.packet.diagnostics) fixture.packet.namedCode compilation
    (runtimeContext fixture.packet) [] (initialScope fixture.packet) (expressionId fixture.packet 1) fixture.calls.initializer
  policy : chosen.formation.produced.site.code.policy = root.root.selected.policy
  body : chosen.formation.produced.site.code.lowerBody = root.root.selected.lowerBody
  fuel : chosen.formation.produced.site.code.fuel = 498
  view : chosen.formation.produced.site.code.view = source caller.named
  reason : chosen.formation.produced.site.code.reasonAt = parentReason fixture
  factory : ChosenFactory root.root (SourceCoreChosenOrdinaryAcceptedLiteralFactory.literalSyntax fixture) chosen
  readFuel : chosen.formation.body.readFuel = fixture.packet.compiled.indexed.fuel

private theorem transported_parent
    (originalCompilation : Compilation fixture.packet.compiled.indexed fixture.packet.named
      (effectiveDiagnostics fixture.packet.compiled fixture.packet.diagnostics) fixture.packet.namedCode)
    (named : Named) (same : fixture.packet.named = named) :
    let originalRoot := fixture.calls.initializer_root originalCompilation
    let actualRoot := Eq.rec
      (motive := fun (named : Named) (same : fixture.packet.named = named) =>
        LiteralRootReceipt (compiled := fixture.packet.compiled) named
          (effectiveDiagnostics fixture.packet.compiled fixture.packet.diagnostics) fixture.packet.namedCode
          (same ▸ originalCompilation) 498 (source fixture.packet.named) (initialScope fixture.packet)
          (expressionId fixture.packet 1) (parentReason fixture) fixture.calls.initializer)
      originalRoot same
    SourceCoreFunctions.lowerExpressionWithPolicy actualRoot.root.selected.policy actualRoot.root.selected.lowerBody
      498 (context fixture.packet.compiled.indexed named) (source fixture.packet.named)
      (parentScope fixture) (expressionId fixture.packet 5) (parentReason fixture) = .ok fixture.calls.parent := by
  cases same
  exact fixture.calls.parent_at_initializer_root fixture.parentRows fixture.parentAccepted originalCompilation

/-- One original named compilation and initializer selector supply both
receipts. The parent action is never selected as a fresh contextual root. -/
theorem at_original_root (atHeader : HeaderAt fixture caller)
    (shape : SourceCoreChosenOrdinaryAcceptedTyping.Shape fixture)
    (metadata : SourceCoreChosenOrdinaryAcceptedBodyMetadata.Receipt fixture.packet fixture.graph)
    (inventory : SourceCoreChosenOrdinaryAcceptedStaticInventory.Inventory fixture) :
    ∃ actualCompilation : Compilation fixture.packet.compiled.indexed caller.named
        (effectiveDiagnostics fixture.packet.compiled fixture.packet.diagnostics) fixture.packet.namedCode,
      ∃ actualRoot : Root fixture caller actualCompilation, Nonempty (ChosenParentReceipt fixture actualRoot) := by
  obtain ⟨originalCompilation⟩ := fixture.packet.named_compilation
  let originalRoot := fixture.calls.initializer_root originalCompilation
  let actualCompilation : Compilation fixture.packet.compiled.indexed caller.named
      (effectiveDiagnostics fixture.packet.compiled fixture.packet.diagnostics) fixture.packet.namedCode :=
    atHeader.named.symm ▸ originalCompilation
  let actualRoot := Eq.rec
    (motive := fun (named : Named) (same : fixture.packet.named = named) =>
      LiteralRootReceipt (compiled := fixture.packet.compiled) named
        (effectiveDiagnostics fixture.packet.compiled fixture.packet.diagnostics) fixture.packet.namedCode
        (same ▸ originalCompilation) 498 (source fixture.packet.named) (initialScope fixture.packet)
        (expressionId fixture.packet 1) (parentReason fixture) fixture.calls.initializer)
    originalRoot atHeader.named.symm
  obtain ⟨parent⟩ := at_root fixture actualRoot atHeader
    (transported_parent fixture originalCompilation caller.named atHeader.named.symm)
  obtain ⟨chosen, policy, body, fuel, view, reason, factory, readFuel⟩ :=
    SourceCoreChosenOrdinaryAcceptedLiteralFactory.chosen_at_root fixture atHeader shape metadata inventory actualRoot
  exact ⟨actualCompilation, actualRoot, ⟨⟨parent, chosen, policy, body, fuel, view, reason, factory, readFuel⟩⟩⟩

end Tests.SourceCoreChosenOrdinaryAcceptedParentCompilerReceipts
