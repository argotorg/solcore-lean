import Solcore.SourceSemantics.CoreLowering.BasicExpressions

/-! Recover the structural expression certificate from the actual basic
lowerer's success. Extraction inspects compiler checks and finite traversal
only; it has no source-evaluation or Core-evaluation premise. -/

set_option autoImplicit false

namespace Solcore.SourceSemantics.CoreLowering.BasicExpressions

open Frontend Frontend.SourceInference TypeSystem LocalCell

theorem typeRepresents_of_lowerType
    {site : SourceCoreElaboration.ErrorSite} {sourceType : Ty} {type : Core.Ty}
    (lowered : SourceCoreElaboration.lowerType site sourceType = .ok type) :
    TypeRepresents sourceType type := by
  induction sourceType generalizing type with
  | «variable» | parameter | function | mapping | proxy | comptime | error => cases lowered
  | constructor constructor =>
      cases constructor with
      | declaration => cases lowered
      | builtin builtin =>
          cases builtin with
          | unit => cases lowered; exact .unit
          | bool => cases lowered; exact .bool
          | word => cases lowered; exact .word
          | integer => cases lowered
  | application function argument =>
      simp only [SourceCoreElaboration.lowerType] at lowered
      split at lowered <;> cases lowered
  | product left right leftIH rightIH =>
      simp only [SourceCoreElaboration.lowerType] at lowered
      cases leftResult : SourceCoreElaboration.lowerType site left with
      | error error => simp [leftResult, bind, Except.bind] at lowered
      | ok leftType =>
          cases rightResult : SourceCoreElaboration.lowerType site right with
          | error error => simp [leftResult, rightResult, bind, Except.bind] at lowered
          | ok rightType =>
              simp only [leftResult, rightResult, bind, Except.bind, pure, Pure.pure,
                Except.pure, Except.ok.injEq] at lowered
              subst type
              exact .product (leftIH leftResult) (rightIH rightResult)

private theorem projectType_ok
    {site : SourceCoreElaboration.ErrorSite} {sourceType : Ty} {type : Core.Ty}
    (projected : SourceCoreBasic.projectType site sourceType = .ok type) :
    SourceCoreElaboration.lowerType site sourceType = .ok type := by
  unfold SourceCoreBasic.projectType at projected
  cases result : SourceCoreElaboration.lowerType site sourceType with
  | error error => simp [result, Except.mapError] at projected
  | ok lowered =>
      simp only [result, Except.mapError, Except.ok.injEq] at projected
      subst lowered
      rfl

/-- Successful metadata checks establish declarative occurrence membership,
ownership, an exact scalar/product type, and absence of runtime obligations. -/
theorem readExpression_certificate
    {source : TypedSource} {id : ExpressionId} {node : ExpressionNode} {type : Core.Ty}
    (read : SourceCoreBasic.readExpression source id = .ok (node, type)) :
    source.lookupExpression? id = some node ∧ Metadata source id node type := by
  by_cases owned : id.occurrence.owner = source.owner
  · cases found : source.lookupExpression? id with
    | none => simp [SourceCoreBasic.readExpression, owned, found, bind, Except.bind] at read
    | some selected =>
        by_cases requirements : selected.requirements = []
        · by_cases coercions : selected.coercions = []
          · cases projected : SourceCoreBasic.projectType (.occurrence id.occurrence) selected.type with
            | error error =>
                simp [SourceCoreBasic.readExpression, owned, found, requirements, coercions,
                  projected, bind, Except.bind, pure, Pure.pure, Except.pure] at read
            | ok projectedType =>
                simp [SourceCoreBasic.readExpression, owned, found, requirements, coercions,
                  projected, bind, Except.bind, pure, Pure.pure, Except.pure] at read
                rcases read with ⟨rfl, rfl⟩
                exact ⟨rfl, lookupExpression?_sound found, owned,
                  typeRepresents_of_lowerType (projectType_ok projected), requirements, coercions⟩
          · simp [SourceCoreBasic.readExpression, owned, found, requirements, coercions,
              bind, Except.bind, pure, Pure.pure, Except.pure] at read
        · simp [SourceCoreBasic.readExpression, owned, found, requirements,
            bind, Except.bind, pure, Pure.pure, Except.pure] at read
  · simp [SourceCoreBasic.readExpression, owned, bind, Except.bind] at read

theorem metadata_of_readExpression
    {source : TypedSource} {id : ExpressionId} {node : ExpressionNode} {type : Core.Ty}
    (read : SourceCoreBasic.readExpression source id = .ok (node, type)) :
    Metadata source id node type :=
  (readExpression_certificate read).2

private theorem ensureType_ok {site : SourceCoreElaboration.ErrorSite} {expected actual : Core.Ty}
    (accepted : SourceCoreBasic.ensureType site expected actual = .ok ()) : expected = actual := by
  unfold SourceCoreBasic.ensureType at accepted
  split at accepted
  · assumption
  · cases accepted

private theorem localRead_of_lowerRead
    {source : TypedSource} {scope : SourceCoreLocalCell.Scope} {id : ExpressionId}
    {node : ExpressionNode} {type : Core.Ty} {name : String} {binder : Resolved.LocalId}
    {reason : Core.Word} {expression : Core.Expr}
    (metadata : Metadata source id node type)
    (found : source.lookupExpression? id = some node)
    (form : node.form = .reference name (.local binder))
    (lowered : SourceCoreLocalCell.lowerRead source scope id reason = .ok expression) :
    ∃ index, binder.owner = source.owner ∧
      SourceCoreLocalCell.lookup? scope binder = some (index, type) ∧
      expression = Core.OptionalCell.read type (.var index) reason := by
  by_cases owned : binder.owner = source.owner
  · cases slot : SourceCoreLocalCell.lookup? scope binder with
    | none =>
        simp [SourceCoreLocalCell.lowerRead, found, form, owned,
          metadata.requirements, metadata.coercions, slot, bind, Except.bind,
          pure, Pure.pure, Except.pure] at lowered
    | some pair =>
        rcases pair with ⟨index, payloadType⟩
        by_cases same : type = payloadType
        · subst payloadType
          simp [SourceCoreLocalCell.lowerRead, found, form, owned,
            metadata.requirements, metadata.coercions, slot, metadata.types.lower _,
            Except.mapError, bind, Except.bind, pure, Pure.pure, Except.pure] at lowered
          exact ⟨index, owned, rfl, lowered.symm⟩
        · simp [SourceCoreLocalCell.lowerRead, found, form, owned,
            metadata.requirements, metadata.coercions, slot, metadata.types.lower _, same,
            Except.mapError, bind, Except.bind, pure, Pure.pure, Except.pure] at lowered
  · simp [SourceCoreLocalCell.lowerRead, found, form, owned,
      bind, Except.bind, pure, Pure.pure, Except.pure] at lowered

/-- Every successful expression compilation has a structural certificate whose
depth fits that exact traversal budget. Rejection branches cannot supply one. -/
theorem tree_of_lowerExpression
    {fuel : Nat} {source : TypedSource} {scope : SourceCoreLocalCell.Scope}
    {id : ExpressionId} {reason : Core.Word} {lowered : SourceCoreBasic.LoweredExpr}
    (accepted : SourceCoreBasic.lowerExpression fuel source scope id reason = .ok lowered) :
    ∃ depth, depth ≤ fuel ∧ Tree source scope reason id lowered.type lowered.expression depth := by
  induction fuel generalizing id lowered with
  | zero => simp [SourceCoreBasic.lowerExpression] at accepted
  | succ fuel ih =>
      cases read : SourceCoreBasic.readExpression source id with
      | error error => simp [SourceCoreBasic.lowerExpression, read, bind, Except.bind] at accepted
      | ok pair =>
          rcases pair with ⟨node, type⟩
          obtain ⟨found, metadata⟩ := readExpression_certificate read
          simp only [SourceCoreBasic.lowerExpression, read, bind, Except.bind] at accepted
          cases form : node.form with
          | literal literal =>
              simp only [form] at accepted
              cases checked : SourceCoreBasic.ensureType (.occurrence id.occurrence) .word type with
              | error error => simp [checked] at accepted
              | ok checkedUnit =>
                  cases checkedUnit
                  have same := ensureType_ok checked
                  subst type
                  cases decoded : interpretWordLiteral? ⟨node.span, literal⟩ with
                  | none => simp [checked, decoded] at accepted
                  | some value =>
                      simp only [checked, decoded, pure, Pure.pure,
                        Except.pure, Except.ok.injEq] at accepted
                      subst lowered
                      exact ⟨1, by omega, .word value metadata form (interpretWordLiteral?_sound decoded)⟩
          | reference name resolution =>
              cases resolution with
              | declaration | builtinFunction => simp [form] at accepted
              | builtinBoolean value =>
                  simp only [form] at accepted
                  cases checked : SourceCoreBasic.ensureType (.occurrence id.occurrence) .bool type with
                  | error error => simp [checked] at accepted
                  | ok checkedUnit =>
                      cases checkedUnit
                      have same := ensureType_ok checked
                      subst type
                      simp only [checked, pure, Pure.pure,
                        Except.pure, Except.ok.injEq] at accepted
                      subst lowered
                      exact ⟨1, by omega, .bool value metadata form⟩
              | «local» binder =>
                  simp only [form] at accepted
                  cases localRead : SourceCoreLocalCell.lowerRead source scope id reason with
                  | error error => simp [localRead, Except.mapError] at accepted
                  | ok expression =>
                      simp only [localRead, Except.mapError, pure, Pure.pure,
                        Except.pure, Except.ok.injEq] at accepted
                      subst lowered
                      obtain ⟨index, owned, slot, rfl⟩ :=
                        localRead_of_lowerRead metadata found form localRead
                      exact ⟨1, by omega, .localRead metadata form owned slot⟩
          | group inner =>
              simp only [form] at accepted
              cases child : SourceCoreBasic.lowerExpression fuel source scope inner reason with
              | error error => simp [child] at accepted
              | ok result =>
                  simp only [child] at accepted
                  cases checked : SourceCoreBasic.ensureType (.occurrence id.occurrence) type result.type with
                  | error error => simp [checked] at accepted
                  | ok checkedUnit =>
                      cases checkedUnit
                      have same := ensureType_ok checked
                      simp only [checked, pure, Pure.pure,
                        Except.pure, Except.ok.injEq] at accepted
                      subst lowered
                      obtain ⟨depth, bound, tree⟩ := ih child
                      exact ⟨depth + 1, by omega, .group (same ▸ metadata) form tree⟩
          | tuple elements =>
              cases elements with
              | nil =>
                  simp only [form] at accepted
                  cases checked : SourceCoreBasic.ensureType (.occurrence id.occurrence) .unit type with
                  | error error => simp [checked] at accepted
                  | ok checkedUnit =>
                      cases checkedUnit
                      have same := ensureType_ok checked
                      subst type
                      simp only [checked, pure, Pure.pure,
                        Except.pure, Except.ok.injEq] at accepted
                      subst lowered
                      exact ⟨1, by omega, .unit metadata form⟩
              | cons left rest =>
                  cases rest with
                  | nil => simp [form] at accepted
                  | cons right rest =>
                      cases rest with
                      | cons => simp [form] at accepted
                      | nil =>
                          simp only [form] at accepted
                          cases leftResult : SourceCoreBasic.lowerExpression fuel source scope left reason with
                          | error error => simp [leftResult] at accepted
                          | ok leftLowered =>
                              cases rightResult : SourceCoreBasic.lowerExpression fuel source scope right reason with
                              | error error => simp [leftResult, rightResult] at accepted
                              | ok rightLowered =>
                                  simp only [leftResult, rightResult] at accepted
                                  cases checked : SourceCoreBasic.ensureType (.occurrence id.occurrence) type
                                      (.product leftLowered.type rightLowered.type) with
                                  | error error => simp [checked] at accepted
                                  | ok checkedUnit =>
                                      cases checkedUnit
                                      have same := ensureType_ok checked
                                      subst type
                                      simp only [checked, pure, Pure.pure,
                                        Except.pure, Except.ok.injEq] at accepted
                                      subst lowered
                                      obtain ⟨leftDepth, leftBound, leftTree⟩ := ih leftResult
                                      obtain ⟨rightDepth, rightBound, rightTree⟩ := ih rightResult
                                      exact ⟨max leftDepth rightDepth + 1, by omega,
                                        .pair metadata form leftTree rightTree⟩
          | integerLiteral | unary | binary | conditional | lambda | call | constructor | member | proxy | index =>
              simp [form] at accepted

theorem lowerExpression_hasType
    {fuel : Nat} {source : TypedSource} {scope : SourceCoreLocalCell.Scope}
    {id : ExpressionId} {reason : Core.Word} {lowered : SourceCoreBasic.LoweredExpr}
    (accepted : SourceCoreBasic.lowerExpression fuel source scope id reason = .ok lowered) :
    Core.HasType (SourceCoreLocalCell.coreContext scope) lowered.expression
      (Core.LanguageResult.resultType lowered.type) := by
  obtain ⟨_, _, tree⟩ := tree_of_lowerExpression accepted
  exact tree.hasType

/-- Accepted compiler output can use meaning preservation directly. The
remaining premises are occurrence uniqueness and the initial environment/heap
representation, not a manually supplied tree or an evaluation result. -/
theorem lowerExpression_run_preserves
    {compilationFuel : Nat} {source : TypedSource} {scope : SourceCoreLocalCell.Scope}
    {id : ExpressionId} {reason : Core.Word} {lowered : SourceCoreBasic.LoweredExpr}
    (accepted : SourceCoreBasic.lowerExpression compilationFuel source scope id reason = .ok lowered)
    (unique : NodeOccurrencesUnique source)
    (program : Program) (context : Context) (evidence : Dynamic.EvidenceEnvironment)
    {environment : Dynamic.Environment} {heap : Dynamic.Heap}
    {coreEnvironment : Core.Environment} {store : Core.Store} {world : Core.StoreTyping}
    (environments : EnvRepresents world scope environment coreEnvironment)
    (heaps : HeapRepresents heap.cells store world) :
    Core.infer? (SourceCoreLocalCell.coreContext scope) lowered.expression =
      some (Core.LanguageResult.resultType lowered.type) ∧
    ∃ sourceOutcome coreValue required,
      Dynamic.ExpressionEvaluatesOutcome program context evidence source environment heap id
        sourceOutcome heap ∧
      OutcomeRepresents lowered.type reason sourceOutcome coreValue ∧
      (∀ fuel, required ≤ fuel → Core.runStateful fuel
        (.initial lowered.expression coreEnvironment store) = .done coreValue store) ∧
      (∀ fuel result finalStore, Core.runStateful fuel
        (.initial lowered.expression coreEnvironment store) = .done result finalStore →
          result = coreValue ∧ finalStore = store) := by
  obtain ⟨depth, bound, tree⟩ := tree_of_lowerExpression accepted
  exact (tree.lower_run_preserves unique compilationFuel bound program context evidence
    environments heaps).2

end Solcore.SourceSemantics.CoreLowering.BasicExpressions
