import Solcore.SourceSemantics.CoreLowering.CompatibleAssignmentStatementTree
import Solcore.SourceSemantics.CoreLowering.CompatiblePlaceLayoutCertificates

/-! Assignment certificates follow the successful production place callback
and flow branch. Independent source typing and native site typing remain
explicit static inputs; no child execution is assumed. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleAssignmentStatements
open Core Frontend SourceInference SourceCoreCompatibleDataPlaces
open CompatibleEncoding (bind_ok)

private theorem stored_type {source : TypedSource} {context : SourceSemantics.Context} {rhs : ExpressionId}
    {node : ExpressionNode} {type : TypeSystem.Ty}
    (unique : NodeOccurrencesUnique source) (found : source.lookupExpression? rhs = some node)
    (typed : ExpressionHasType source context rhs type) : node.type = type := by
  obtain ⟨actual, contains, same⟩ := typed.stored_type
  have identical := Option.some.inj (found.symm.trans (lookupExpression?_complete unique contains))
  exact identical ▸ same

theorem Head.of_lower {readFuel : Nat} {values : ValuesContext} {source : TypedSource}
    {context : SourceSemantics.Context} {solved : List SolvedRequirement} {reasonAt : ExpressionId → Word}
    {scope : Scope} {administrative : Core.Context} {definitions : DataEnvironment}
    {assignment : AssignmentResolution} {operator : Solcore.Syntax.ValueAssignOp} {rhs : ExpressionId}
    {expression : ExpressionLowerer} {fuel : Nat} {site : SourceCoreElaboration.ErrorSite}
    {next code : Expr} {output result : Ty} {invalidProjection invalidOperand : Word} {missing : TypeSystem.Ty → Word}
    (unique : NodeOccurrencesUnique source) (signatures : context.signatures = values.checked.signatures)
    (sourceTyped : ∀ binder, rootBinder source assignment.target.root = .ok binder →
      SourceProjectionsHaveType source context binder.scheme.body assignment.target.projections assignment.target.type)
    (writable : ∀ binder, rootBinder source assignment.target.root = .ok binder → WritableLocal context assignment.target.root binder.scheme.body)
    (rightTyped : ExpressionHasType source context rhs assignment.target.type)
    (profile : operator = .equal ∨ SourceCoreRawMetadata.runtimeType assignment.target.type = .word ∨
      SourceCoreRawMetadata.runtimeType assignment.target.type = .integer)
    (extract : ∀ id lowered, expression fuel source scope id reasonAt = .ok lowered → ∃ node,
      source.lookupExpression? id = some node ∧ CompatibleExpressionTyped.Tree readFuel values source context solved reasonAt scope id lowered ∧
      HasType (SourceCoreLocalCell.coreContext scope ++ administrative) lowered.expression (LanguageResult.resultType lowered.type) definitions)
    (accepted : lower values values.checked.signatures expression fuel source scope site assignment operator (some rhs)
      output next reasonAt invalidProjection invalidOperand missing = .ok code)
    (typed : HasType (SourceCoreLocalCell.coreContext scope ++ administrative) code result definitions) :
    ∃ head : Head readFuel values source context solved reasonAt scope administrative definitions assignment operator rhs,
      code = head.emit next output := by
  classical
  by_cases bare : assignment.target.projections = []
  · obtain ⟨binder, prepared, index, lowered, binding, rootType, rawView, slot, layout, generated, sameType, _, codeEq⟩ :=
      CompatibleBareAssignment.of_lower bare accepted
    obtain ⟨node, found, tree, _⟩ := extract rhs lowered generated
    have rawType := stored_type unique found rightTyped
    refine ⟨⟨prepared, index, [], prepared.route.rootSourceType, lowered, node, invalidOperand,
      .bare bare layout, slot, rootType ▸ writable binder binding, found, tree,
      by simpa only [rawType] using rawView, sameType, ?_⟩, codeEq⟩
    rcases profile with equal | word | integer
    · exact .inl equal
    · exact .inr (.inl (rawView.trans word))
    · exact .inr (.inr (rawView.trans integer))
  · obtain ⟨binder, leaf, prepared, codes, sourceTypes, index, lowered, node, _, binding, rootType, slot, layout, ordinary,
      _, found, tree, rawView, sameType, codeEq⟩ :=
      CompatiblePlaceLayoutCertificates.of_lower unique signatures sourceTyped rightTyped bare extract accepted typed
    have rawType := stored_type unique found rightTyped
    refine ⟨⟨prepared, index, codes, leaf, lowered, node, invalidOperand,
      .projected layout ordinary, slot, rootType ▸ writable binder binding, found, tree, rawView, sameType, ?_⟩, codeEq⟩
    rw [rawType] at rawView
    rcases profile with equal | word | integer
    · exact .inl equal
    · exact .inr (.inl (rawView.trans word))
    · exact .inr (.inr (rawView.trans integer))

/-- Static source obligations for the ordinary assignment branch. General
functions, unary assignments and loop syntax are deliberately separate. -/
inductive Syntax (source : TypedSource) (context : SourceSemantics.Context) : Bool → List StatementId → TypeSystem.Ty → Prop where
  | tail {mode statements expected} (body : TypedLexicalControl.Syntax source context mode statements expected) :
      Syntax source context mode statements expected
  | assign {mode id node assignment operator rhs rest expected}
      (found : source.lookupStatement? id = some node) (form : node.form = .assignValue assignment operator rhs)
      (sourceTyped : ∀ binder, rootBinder source assignment.target.root = .ok binder →
        SourceProjectionsHaveType source context binder.scheme.body assignment.target.projections assignment.target.type)
      (writable : ∀ binder, rootBinder source assignment.target.root = .ok binder → WritableLocal context assignment.target.root binder.scheme.body)
      (rightTyped : ExpressionHasType source context rhs assignment.target.type)
      (profile : operator = .equal ∨ SourceCoreRawMetadata.runtimeType assignment.target.type = .word ∨
        SourceCoreRawMetadata.runtimeType assignment.target.type = .integer)
      (remaining : Syntax source context mode rest expected) : Syntax source context mode (id :: rest) expected

private theorem read_found {checked : SourceCoreCompatibleCatalog.Checked} {source : TypedSource}
    {id : StatementId} {node : StatementNode} {type : Ty}
    (accepted : SourceCoreCompatibleDataExpressions.readStatement checked source id = .ok (node, type)) :
    source.lookupStatement? id = some node := by
  unfold SourceCoreCompatibleDataExpressions.readStatement at accepted
  by_cases owner : id.occurrence.owner ≠ source.owner
  · simp [owner, throw, bind, Except.bind] at accepted
  · simp only [owner, ↓reduceIte, bind, Except.bind, pure, Except.pure] at accepted
    cases found : source.lookupStatement? id with
    | none => simp [found] at accepted
    | some actual =>
      simp only [found] at accepted
      obtain ⟨projected, _, same⟩ := bind_ok accepted
      cases same
      rfl

/-- Field equalities identify the real compatible callback. They permit source
cell/layout instrumentation of other policy fields without changing assignment. -/
structure AssignmentPolicy (policy : SourceCoreLoops.Policy) (values : ValuesContext)
    (invalidProjection : SourceCoreElaboration.ErrorSite → Resolved.LocalId → Word)
    (invalidOperand : SourceCoreElaboration.ErrorSite → Resolved.LocalId → Solcore.Syntax.ValueAssignOp → Word)
    (missing : SourceCoreElaboration.ErrorSite → Resolved.LocalId → TypeSystem.Ty → Word) : Prop where
  read : policy.readStatement = SourceCoreCompatibleDataExpressions.readStatement values.checked
  equal : policy.assignEqual = some (fun expression fuel source scope site assignment rhs output next reasonAt =>
    lower values values.checked.signatures expression fuel source scope site assignment .equal (some rhs) output next reasonAt
      (invalidProjection site assignment.target.root) (invalidOperand site assignment.target.root .equal) (missing site assignment.target.root))
  value : policy.assignValue = some (fun expression fuel source scope site assignment operator rhs output next reasonAt =>
    lower values values.checked.signatures expression fuel source scope site assignment operator (some rhs) output next reasonAt
      (invalidProjection site assignment.target.root) (invalidOperand site assignment.target.root operator) (missing site assignment.target.root))

/-- The ordinary shared compatible factory supplies these exact callbacks. -/
theorem AssignmentPolicy.actual (values : ValuesContext) (solved : List SolvedRequirement)
    (assignments : SourceCoreAssignmentFaultSites.Table) (diagnostics : SourceCoreDataPlaceFaultSites.Program)
    (owner : SourceSpecialization.SpecializationKey) (expression : ExpressionLowerer)
    (cells : Option SourceCoreSourceCells.Allocator) (definitions : Option DataEnvironment) :
    AssignmentPolicy (SourceCoreCompatibleDataMatches.loopPolicy values solved assignments diagnostics owner expression cells definitions)
      values (fun site root => diagnostics.placeReason owner site root none)
      (fun site root operator => if operator = .equal then Word.zero else assignments.reasonAt site root (.value operator))
      (fun site root type => diagnostics.placeReason owner site root (some type)) := by
  refine ⟨rfl, rfl, ?_⟩
  change some _ = some _
  apply congrArg some
  funext expression fuel source scope site assignment operator rhs output next reasonAt
  cases operator <;> rfl

/-- Successful flow lowering is followed recursively. Static expression and
site typing callbacks are accepted compiler certificates, not meaning IHs. -/
theorem tree_of_flow {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
    {active : TypeSystem.Substitution} {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
    {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error}
    {readFuel : Nat} {values : ValuesContext} {source : TypedSource} {solved : List SolvedRequirement}
    {reasonAt : ExpressionId → Word} {context : SourceSemantics.Context} {scope : Scope}
    {administrative : Core.Context} {definitions : DataEnvironment} {policy : SourceCoreLoops.Policy}
    {invalidProjection : SourceCoreElaboration.ErrorSite → Resolved.LocalId → Word}
    {invalidOperand : SourceCoreElaboration.ErrorSite → Resolved.LocalId → Solcore.Syntax.ValueAssignOp → Word}
    {missing : SourceCoreElaboration.ErrorSite → Resolved.LocalId → TypeSystem.Ty → Word}
    (matched : AssignmentPolicy policy values invalidProjection invalidOperand missing)
    (unique : NodeOccurrencesUnique source) (signatures : context.signatures = values.checked.signatures)
    (expressions : ∀ fuel id lowered, policy.lowerExpression fuel source scope id reasonAt = .ok lowered → ∃ node,
      source.lookupExpression? id = some node ∧ CompatibleExpressionTyped.Tree readFuel values source context solved reasonAt scope id lowered ∧
      HasType (SourceCoreLocalCell.coreContext scope ++ administrative) lowered.expression (LanguageResult.resultType lowered.type) definitions)
    (sites : ∀ {fuel statements type mode selfReason code},
      SourceCoreLoops.lowerFlowStatementsWithPolicy policy fuel source scope statements type reasonAt mode selfReason = .ok code →
      HasType (SourceCoreLocalCell.coreContext scope ++ administrative) code (LocalLoop.resultType type) definitions)
    (tails : ∀ {mode statements expected fuel type selfReason code},
      TypedLexicalControl.Syntax source context mode statements expected →
      SourceCoreLoops.lowerFlowStatementsWithPolicy policy fuel source scope statements type reasonAt mode selfReason = .ok code →
      TypedLexicalControl.Tree layouts owner active frame globals onError readFuel values source solved reasonAt context scope mode statements expected type code)
    {mode : Bool} {statements : List StatementId} {expected : TypeSystem.Ty}
    (syntaxTree : Syntax source context mode statements expected)
    {fuel : Nat} {type : Ty} {selfReason : Word} {code : Expr}
    (accepted : SourceCoreLoops.lowerFlowStatementsWithPolicy policy fuel source scope statements type reasonAt mode selfReason = .ok code) :
    Tree layouts owner active frame globals onError readFuel values source solved reasonAt context scope administrative definitions
      mode statements expected type code := by
  induction syntaxTree generalizing fuel code with
  | tail body => exact .tail (tails body accepted)
  | @assign id node assignment operator rhs rest expected found form sourceTyped writable rightTyped profile remaining ih =>
    cases fuel with
    | zero => cases accepted
    | succ fuel =>
      have typed := sites accepted
      simp only [SourceCoreLoops.lowerFlowStatementsWithPolicy] at accepted
      obtain ⟨⟨actual, stored⟩, read, accepted⟩ := bind_ok accepted
      have same := Option.some.inj ((read_found (matched.read ▸ read)).symm.trans found)
      subst actual
      simp only [form] at accepted
      obtain ⟨checked, _, accepted⟩ := bind_ok accepted
      cases checked
      obtain ⟨body, compiledBody, accepted⟩ := bind_ok accepted
      have compiled : lower values values.checked.signatures policy.lowerExpression fuel source scope (.occurrence id.occurrence)
          assignment operator (some rhs) (LocalLoop.controlType type) body reasonAt
          (invalidProjection (.occurrence id.occurrence) assignment.target.root)
          (invalidOperand (.occurrence id.occurrence) assignment.target.root operator)
          (missing (.occurrence id.occurrence) assignment.target.root) = .ok code := by
        cases operator <;> simpa only [SourceCoreLoops.assignValue, matched.equal, matched.value] using accepted
      obtain ⟨head, rfl⟩ := Head.of_lower unique signatures sourceTyped writable rightTyped profile (expressions fuel) compiled typed
      exact .assign found form head (ih compiledBody)
end Solcore.SourceSemantics.CoreLowering.CompatibleAssignmentStatements
