import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedLiteralReturnSiteShells
import Solcore.SourceSemantics.CoreLowering.CompatibleExpressionLiteralRuntime
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedExpressionBounds

/-! A fixed approved Word literal has admitted meaning at the same chosen
recaptured support. The original literal producer leaves its actual state
unchanged; numeric evidence and all current rows remain genuine inputs. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2400000
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedChosenWordLiteralExpressionBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedNamedGeneration CallableIndexedLambdaGeneration
open CallableIndexedOwnedContextualCompilerPolicyProfiles
open CallableIndexedOwnedPreparedMixedBodyCompilerFactory
open CallableIndexedOwnedPreparedMixedBodySiteInputs
open CallableIndexedOwnedLiteralReturnSiteShells
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission

/-- The approved occurrence is fixed before selecting the actual Site. -/
def approved (literalId : ExpressionId) : TypedSource → ExpressionId → Prop :=
  fun _ child => child = literalId

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {caller : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram)}
  {diagnostics : SourceCoreDataPlaceFaultSites.Program} {namedCode : Expr}
  {compilation : Compilation compiled.indexed caller.named diagnostics namedCode}
  {rootFuel : Nat} {rootSource : TypedSource} {rootScope : SourceCoreLocalCell.Scope}
  {rootId : ExpressionId} {rootReasonAt : ExpressionId → Word} {rootLowered : SourceCoreBasic.LoweredExpr}
  (literalRoot : LiteralRootReceipt (compiled := compiled) caller.named diagnostics namedCode compilation
    rootFuel rootSource rootScope rootId rootReasonAt rootLowered)
  (literalId : ExpressionId) (node : ExpressionNode)

/-- Actual Source and compiler metadata for the approved Word occurrence. -/
structure WordNodeFacts : Prop where
  found : (source caller.named).lookupExpression? literalId = some node
  form : (∃ literal, node.form = .literal literal) ∨
    ∃ literal resolution, node.form = .integerLiteral literal resolution
  wordType : node.type = .word
  coercions : node.coercions = []
  ordinary : ∃ owned, SourceCompilationPlan.ordinaryOwnedRequirements? node = some owned
  requirements : node.requirements = [] ∨ ∃ literal resolution, node.form = .integerLiteral literal resolution
  initializer : compiled.indexed.base.locals.bindings.find? (fun binding =>
    decide (binding.caller = (context compiled.indexed caller.named).owner ∧ binding.initializer = literalId)) = none

/-- Only actual Word spellings and resolved numeric occurrences are admitted. -/
theorem WordNodeFacts.atomic (facts : WordNodeFacts (caller := caller) literalId node) :
    CompatibleExpressionLiterals.Atomic node.form := by
  rcases facts.form with ⟨literal, form⟩ | ⟨literal, resolution, form⟩
  · rw [form]; exact .word literal
  · rw [form]; exact .integer literal resolution

variable {parameters : List TypedBinder} {result : TypeSystem.Ty} {statements : List StatementId}
  {sourceContext : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
  {scope : SourceCoreLocalCell.Scope} {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}
  (receipt : CallableIndexedOwnedPreparedOrdinaryLambdaCompilerReceipts.Receipt caller diagnostics namedCode compilation
    sourceContext evidence scope id lowered)
  (chosen : ChosenFactory literalRoot.root (approved literalId) receipt)
  (capturedEnvironment : Dynamic.Environment)
  (facts : WordNodeFacts (caller := caller) literalId node)

include chosen facts in
/-- The same recaptured factory retains the original accepted child action.
Only its actual literal compiler branch supplies the selected numeric row. -/
theorem certificate_at_support
    {currentContext : SourceSemantics.Context} {childScope : SourceCoreLocalCell.Scope}
    {child : ExpressionId} {output : SourceCoreBasic.LoweredExpr}
    (actual : (receipt.formation.support capturedEnvironment).certificates
      (receipt.formation.support capturedEnvironment).body.readFuel
      (receipt.formation.function capturedEnvironment).source currentContext childScope child output) :
    child = literalId ∧ CompatibleExpressionLiteralRuntime.Certificate
      (context compiled.indexed caller.named).solvedRequirements
      (receipt.formation.function capturedEnvironment).source child output := by
  change child = literalId ∧ CompatibleExpressionLiteralRuntime.Certificate
    (context compiled.indexed caller.named).solvedRequirements (source caller.named) child output
  change receipt.formation.certificates receipt.formation.body.readFuel (source caller.named)
    currentContext childScope child output at actual
  have same := congrArg (fun family => family receipt.formation.body.readFuel (source caller.named)
    currentContext childScope child output) (formation_factories literalRoot.root (approved literalId) receipt chosen).2
  have accepted := same.mp actual
  cases accepted with
  | intro found _ allowed _ _ _ _ accepted =>
    change child = literalId at allowed
    subst child
    obtain ⟨owned, ordinary⟩ := facts.ordinary
    have policy := literal_policy literalRoot.root facts.found facts.atomic ordinary facts.coercions
      facts.requirements facts.initializer (childScope := childScope) (reasonAt := rootReasonAt)
    refine ⟨rfl, ?_⟩
    exact CompatibleExpressionLiteralRuntime.of_functions (values := .initial compiled.compatible.checked)
      (source := source caller.named) facts.found facts.atomic
      (by intro form; rcases facts.form with ⟨literal, other⟩ | ⟨literal, resolution, other⟩ <;> rw [other] at form <;> cases form)
      policy.special policy.read literalRoot.leaf accepted

private theorem literal_word_type {solved : List SolvedRequirement} {node : ExpressionNode} {type : Ty} {code : Expr}
    (literal : CompatibleExpressionLiterals.Literal solved node type code) (wordType : node.type = .word) : type = .word := by
  cases literal with
  | unit _ typed _ _ | bool _ _ typed _ _ => cases typed.symm.trans wordType
  | word => rfl
  | resolvedWord => rfl
  | resolvedInteger _ metadata => cases metadata.nodeType.symm.trans wordType

private theorem word_typed {solved : List SolvedRequirement} {node : ExpressionNode} {code : Expr}
    (literal : CompatibleExpressionLiterals.Literal solved node .word code)
    {program : Program} {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
    {source : TypedSource} {environment : Dynamic.Environment} {heap : Dynamic.Heap} {value : Dynamic.Value}
    (raw : Dynamic.ExpressionFormEvaluates program context evidence source environment heap
      node.form node.requirements node.coercions value heap) : Dynamic.ValueHasType context heap value .word := by
  cases literal with
  | word _ form _ _ _ _ =>
    rw [form] at raw
    cases raw with | literal _ constructed => cases constructed; exact .word _
  | resolvedWord form metadata =>
    rw [form] at raw
    cases raw with | integerLiteral _ constructed =>
      cases constructed with
      | word => exact .word _
      | integer => cases metadata.targetType

private theorem word_outcome_unique {solved : List SolvedRequirement} {node : ExpressionNode} {code : Expr}
    (literal : CompatibleExpressionLiterals.Literal solved node .word code)
    {program : Program} {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
    (numeric : CompatibleExpressionLiterals.NumericEvidence context evidence node)
    {source : TypedSource} {id : ExpressionId} (found : source.lookupExpression? id = some node)
    (unique : NodeOccurrencesUnique source) (empty : node.coercions = [])
    {environment : Dynamic.Environment} {before after : Dynamic.Heap}
    {value : Dynamic.Value} {outcome : Dynamic.ExpressionOutcome}
    (raw : Dynamic.ExpressionFormEvaluates program context evidence source environment before
      node.form node.requirements node.coercions value before)
    (trace : Dynamic.ExpressionEvaluatesOutcome program context evidence source environment before id outcome after) :
    outcome = .value value ∧ after = before := by
  have contains := lookupExpression?_sound found
  have sameNode : ∀ other, ContainsExpression source id other → other = node := by
    intro other present
    exact Option.some.inj ((lookupExpression?_complete unique present).symm.trans found)
  have nonlocal : ∀ name binder, node.form ≠ .reference name (.local binder) := by
    cases literal <;> intros <;> simp_all
  cases trace with
  | value evaluation =>
    cases evaluation with
    | intro other actual coercions =>
      have same := sameNode _ other
      subst same
      rw [empty] at coercions
      cases coercions
      cases literal with
      | word _ form _ _ _ _ =>
        rw [form] at raw actual
        cases raw with | literal _ first =>
          cases actual with | literal _ second => exact ⟨congrArg _ (second.functional first), rfl⟩
      | resolvedWord form _ =>
        rw [form] at raw actual
        cases raw with | integerLiteral _ first =>
          cases actual with | integerLiteral _ second => exact ⟨congrArg _ (second.functional first), rfl⟩
    | generalizedLocal other form _ _ _ _ _ _ _ =>
      exact False.elim (nonlocal _ _ (sameNode _ other ▸ form))
  | @fault _ _ reason failed =>
    have rawFault : Dynamic.ExpressionFormFaults program context evidence source environment before
        node.form node.requirements node.coercions reason after := by
      cases failed with
      | missing absent => exact False.elim (Dynamic.ExpressionAbsentIn.excludes_contains absent contains)
      | form other failed => exact sameNode _ other ▸ failed
      | coercion other _ failed =>
        have same := sameNode _ other
        subst same
        rw [empty] at failed
        cases failed
      | generalizedLocalRequirement other form _ _ _ _ _ _ _
      | generalizedLocalCoercion other form _ _ _ _ _ _ _ =>
        exact False.elim (nonlocal _ _ (sameNode _ other ▸ form))
    cases literal with
    | word _ form _ _ _ _ => rw [form] at rawFault; cases rawFault
    | resolvedWord form _ =>
      rw [form] at rawFault
      cases rawFault with | integerRequirement _ unavailable => exact False.elim ((numeric _ _ form).2 unavailable)

section Admitted
universe u
variable {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
  (functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  (currentContext : SourceSemantics.Context) (currentEvidence : Dynamic.EvidenceEnvironment)
  (ledger : currentContext.solvedRequirements = (context compiled.indexed caller.named).solvedRequirements)
  (runtime : RuntimeRequirementLedgerValid currentContext)

include chosen facts ledger runtime in
/-- A real Source child returns the same state with successful Word admission.
The literal producer is the only semantic child consumer. -/
theorem preserves_at_support
    (unique : NodeOccurrencesUnique (receipt.formation.function capturedEnvironment).source) (size : Nat) :
    CallableIndexedOwnedAdmittedExpressionBounds.PreservesAt bridge
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
      currentContext currentEvidence (receipt.formation.function capturedEnvironment).source
      ((receipt.formation.support capturedEnvironment).certificates
        (receipt.formation.support capturedEnvironment).body.readFuel
        (receipt.formation.function capturedEnvironment).source currentContext) faults size := by
  intro childScope child output actual actualNode found _sourceTyped mapping world administrative environment canonical native
    actualContext before store ξ outcome after _environments heaps _locals _agrees _typed initial admitted trace
  obtain ⟨sameId, actualLiteral⟩ := certificate_at_support literalRoot literalId node receipt chosen capturedEnvironment facts actual
  subst child
  obtain ⟨other, otherFound, literal, selected⟩ := actualLiteral
  have sameNode := Option.some.inj (otherFound.symm.trans facts.found)
  subst other
  have nodeEq := Option.some.inj (found.symm.trans facts.found)
  subst actualNode
  have nativeWord := literal_word_type literal facts.wordType
  rw [nativeWord] at literal
  have numeric := selected.evidence ledger runtime currentEvidence
  obtain ⟨sourceValue, coreValue, raw, related, evaluated⟩ := literal.evaluates_with_evidence (registry := registry)
    functions (Program.ofChecked compiled.sourceProgram) currentContext currentEvidence numeric
    _ environment before mapping world native store ξ
  obtain ⟨sameOutcome, sameHeap⟩ := word_outcome_unique literal numeric facts.found unique facts.coercions raw trace.sound
  subst outcome
  subst after
  refine ⟨.inRight .word coreValue, store, mapping, world, evaluated, .value (by simpa only [CompatibleAmbientHeap.payloadModel, nativeWord] using related), heaps,
    .refl _, .refl _, .refl _ _, .refl _, initial, callerProtocol.refl initial, admitted.rows, ?_⟩
  intro value same
  cases same
  rw [facts.wordType]
  exact ⟨word_typed literal raw, admitted.heap⟩

include chosen facts ledger runtime in
/-- A native completion constructs its genuine independently sized Source
trace. The same current state authenticates every successful post row. -/
theorem reflects_at_support (size : Nat) :
    CallableIndexedOwnedAdmittedExpressionBounds.ReflectsAt bridge
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
      currentContext currentEvidence (receipt.formation.function capturedEnvironment).source
      ((receipt.formation.support capturedEnvironment).certificates
        (receipt.formation.support capturedEnvironment).body.readFuel
        (receipt.formation.function capturedEnvironment).source currentContext) faults size := by
  intro childScope child output actual actualNode found _sourceTyped mapping world administrative environment canonical native
    actualContext before store ξ value finalStore _environments heaps _locals _agrees _typed initial admitted completed
  obtain ⟨sameId, actualLiteral⟩ := certificate_at_support literalRoot literalId node receipt chosen capturedEnvironment facts actual
  subst child
  obtain ⟨other, otherFound, literal, selected⟩ := actualLiteral
  have sameNode := Option.some.inj (otherFound.symm.trans facts.found)
  subst other
  have nodeEq := Option.some.inj (found.symm.trans facts.found)
  subst actualNode
  have nativeWord := literal_word_type literal facts.wordType
  rw [nativeWord] at literal
  have numeric := selected.evidence ledger runtime currentEvidence
  obtain ⟨sourceValue, coreValue, raw, related, evaluated⟩ := literal.evaluates_with_evidence (registry := registry)
    functions (Program.ofChecked compiled.sourceProgram) currentContext currentEvidence numeric
    _ environment before mapping world native store ξ
  obtain ⟨sameValue, sameStore⟩ := evaluation_deterministic evaluated completed.sound
  subst value
  subst finalStore
  have sourceTrace : Dynamic.ExpressionEvaluates (Program.ofChecked compiled.sourceProgram)
      currentContext currentEvidence (receipt.formation.function capturedEnvironment).source
      environment before literalId sourceValue before := by
    apply Dynamic.ExpressionEvaluates.intro (lookupExpression?_sound facts.found) raw
    rw [facts.coercions]
    exact .nil
  obtain ⟨sourceSize, sized⟩ := RecursiveNamedCallBounds.ExpressionOutcome.has_size (.value sourceTrace)
  refine ⟨sourceSize, .value sourceValue, before, mapping, world, sized, .value (by simpa only [CompatibleAmbientHeap.payloadModel, nativeWord] using related), heaps,
    .refl _, .refl _, .refl _ _, .refl _, initial, callerProtocol.refl initial, admitted.rows, ?_⟩
  intro value same
  cases same
  rw [facts.wordType]
  exact ⟨word_typed literal raw, admitted.heap⟩

end Admitted
end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedChosenWordLiteralExpressionBounds
