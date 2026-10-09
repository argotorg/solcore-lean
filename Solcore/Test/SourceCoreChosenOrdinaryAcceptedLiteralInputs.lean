import Solcore.Test.SourceCoreChosenOrdinaryAcceptedTyping
import Solcore.Test.SourceCoreChosenOrdinaryAcceptedBodyMetadata
import Solcore.Test.SourceCoreChosenOrdinaryAcceptedHeader
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedLiteralPlaceDiagnosticShells

/-! The accepted fixture supplies the literal shell's actual Source fields.
All compiler identities belong to the same selected Produced and root. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreChosenOrdinaryAcceptedLiteralInputs
open Solcore Core Frontend SourceInference SourceSemantics CoreLowering
open SourceCoreChosenOrdinaryAcceptedFixture SourceCoreChosenOrdinaryAcceptedHeader
open CallableIndexedNamedGeneration CallableIndexedLambdaGeneration
open CallableIndexedOwnedPreparedOrdinaryLambdaSupport
open CallableIndexedOwnedContextualLambdaSourceDiagnostics
open CallableIndexedOwnedLiteralReturnSiteShells
open CallableIndexedOwnedLiteralPlaceDiagnosticShells

variable (fixture : AcceptedFixture) {caller : ActualHeader fixture}
    (atHeader : HeaderAt fixture caller)
    (shape : SourceCoreChosenOrdinaryAcceptedTyping.Shape fixture)
    (metadata : SourceCoreChosenOrdinaryAcceptedBodyMetadata.Receipt fixture.packet fixture.graph)
    {diagnostics : SourceCoreDataPlaceFaultSites.Program} {namedCode : Expr}
    {compilation : Compilation fixture.packet.compiled.indexed caller.named diagnostics namedCode}
    {rootFuel : Nat} {rootReasonAt : ExpressionId → Word} {rootLowered : SourceCoreBasic.LoweredExpr}
    (root : LiteralRootReceipt (compiled := fixture.packet.compiled) caller.named diagnostics namedCode compilation
      rootFuel (source fixture.packet.named) (initialScope fixture.packet)
      (expressionId fixture.packet 1) rootReasonAt rootLowered)
    {lowered : SourceCoreBasic.LoweredExpr}
    (produced : Produced (compiled := fixture.packet.compiled) caller.named fixture.graph.parameters wordType
      [statementId fixture.packet 2] (runtimeContext fixture.packet) [] (initialScope fixture.packet)
      (RecursiveNamedLambdaFormationHeads.nativePrefix (values := .initial fixture.packet.compiled.compatible.checked) caller)
      (expressionId fixture.packet 1) lowered)

include atHeader in
/-- The selected Code's original Source lookup identifies the retained lambda row. -/
theorem source_node : produced.site.code.sourceNode = fixture.graph.lambdaNode := by
  have found : (source fixture.packet.named).lookupExpression? (expressionId fixture.packet 1) =
      some produced.site.code.sourceNode := by
    simpa only [closure, produced.identifier, atHeader.named] using produced.site.code.sourceFound
  exact Option.some.inj (found.symm.trans fixture.graph.lambdaFound)

/-- The fixture's independent context retains the real catalog signatures. -/
theorem signatures : (runtimeContext fixture.packet).signatures =
    fixture.packet.compiled.compatible.checked.signatures := by
  have owned := fixture.packet.compiled.indexed.base.signatureOwnership
  rw [(SourceCoreUnifiedPreparationCertificates.compiled_fields fixture.packet.compiled).1] at owned
  exact owned.symm

/-- The original declaration context has no assumptions to populate with evidence. -/
theorem covers : Dynamic.EvidenceEnvironment.Covers (runtimeContext fixture.packet) [] := by
  constructor
  · intro goal evidence found
    cases found
  · intro predicate member
    cases member

include atHeader shape metadata in
/-- Every Source and body field is constructed from the actual fixture.
Issued diagnostic preparation and policy/view identity remain genuine compiler receipts. -/
theorem body_inputs
    (issued : IssuedSource fixture.packet.compiled produced.site.code.compilation.owner (source caller.named))
    (sameAssignments : issued.assignments = produced.compilation.own.assignments)
    (samePlaces : PlaceReasonsEq issued.diagnostics.program produced.diagnostics)
    (samePolicy : produced.site.code.policy = root.root.selected.policy)
    (sameView : produced.site.code.view = source caller.named) :
    Nonempty (PlaceDiagnosticBodyInputs produced root) := by
  have sameNode := source_node fixture atHeader produced
  refine ⟨{
    issued := issued
    sameAssignments := sameAssignments
    placeReasons := samePlaces
    samePolicy := samePolicy
    canonical := sameView
    typed := ?_
    lambdaCoercions := ?_
    signatures := signatures fixture
    runtime := ?_
    covers := covers fixture
    kinds := ?_
    declarations := ?_
    ledger := ?_
    statement := statementId fixture.packet 2
    statementNode := fixture.graph.returned
    expression := expressionId fixture.packet 3
    expressionNode := fixture.graph.literal
    singleton := rfl
    statementFound := ?_
    statementForm := fixture.graph.returnedForm
    statementOwner := ?_
    statementCore := .word
    statementProjected := metadata.projected
    expressionFound := ?_
    atomic := ?_
    unitType := ?_
    owned := [⟨0⟩]
    ordinaryRequirements := fixture.graph.literalOwned
    literalCoercions := fixture.graph.literalCoercions
    literalRequirements := Or.inr ⟨_, _, fixture.graph.literalForm⟩
    initializer := ?_
    noMatches := ?_ }⟩
  · rw [sameNode, atHeader.named]
    exact SourceCoreChosenOrdinaryAcceptedTyping.lambda_typed shape
  · rw [sameNode]
    exact fixture.graph.lambdaCoercions
  · rw [atHeader.named]
    exact fixture.runtime.source_runtime
  · intro binder member
    rw [shape.parameters] at member
    have same := List.mem_singleton.mp member
    subst binder
    simpa only [atHeader.named] using shape.notInput
  · simpa only [atHeader.named] using metadata.initial_declarations
  · rw [atHeader.named]
    rfl
  · simpa only [atHeader.named] using fixture.graph.returnedFound
  · rw [atHeader.named]
    rfl
  · simpa only [atHeader.named] using fixture.graph.literalFound
  · rw [fixture.graph.literalForm]
    exact .integer _ _
  · rw [fixture.graph.literalForm]
    intro impossible
    cases impossible
  · simpa only [atHeader.named, context, CompatibleNamedBody.bodyContext] using fixture.calls.literalOrdinary
  · simpa only [atHeader.named] using metadata.no_matches

include atHeader shape metadata in
/-- The actual static body shell follows from these constructed Source fields. -/
theorem shell
    (issued : IssuedSource fixture.packet.compiled produced.site.code.compilation.owner (source caller.named))
    (sameAssignments : issued.assignments = produced.compilation.own.assignments)
    (samePlaces : PlaceReasonsEq issued.diagnostics.program produced.diagnostics)
    (samePolicy : produced.site.code.policy = root.root.selected.policy)
    (sameView : produced.site.code.view = source caller.named)
    (readFuel : Nat) :
    ∃ inputs : PlaceDiagnosticBodyInputs produced root,
      Nonempty (CallableIndexedOwnedPreparedMixedBodyCompilerFactory.SiteShell
        (approved produced root inputs) produced) := by
  obtain ⟨inputs⟩ := body_inputs fixture atHeader shape metadata root produced issued sameAssignments samePlaces samePolicy sameView
  exact ⟨inputs, literal_shell produced root inputs readFuel⟩

end Tests.SourceCoreChosenOrdinaryAcceptedLiteralInputs
