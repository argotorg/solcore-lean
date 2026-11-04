import Solcore.SourceSemantics.CoreLowering.Internal.Compatible.RenamedBareAssignments
import Solcore.SourceSemantics.CoreLowering.Internal.Compatible.PlaceReflection
import Solcore.SourceSemantics.CoreLowering.AssignmentOperandDiagnostics
import Solcore.SourceSemantics.CoreLowering.AssignmentFaultTableCertificates
import Solcore.Frontend.SourceCoreCompatibleDataMatches
import Solcore.SourceSemantics.CoreLowering.Internal.Compatible.PatternsAndArms
import Solcore.SourceSemantics.CoreLowering.DataMatchSourceScopes
import Solcore.SourceSemantics.CoreLowering.Internal.Compatible.MatchPrefixes
import Solcore.SourceSemantics.CoreLowering.Internal.Compatible.BitNotStatements
import Solcore.SourceSemantics.CoreLowering.Internal.Protected.StatePlaceAssignments
import Solcore.SourceSemantics.CoreLowering.DataMatchSourceTrace

/-!
# Generic assignments and match children

Assignment statements, their prepared origins and diagnostics, and the children and preservation of matches.
-/

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.GenericAssignmentStatementHead
/-! Ordinary assignment certificates share one expression certificate for keys
and RHS. Source metadata and generated native layouts are retained separately.
This interface is static; expression meaning is supplied by concrete clients. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.GenericAssignmentStatements
open Core Frontend SourceInference GeneralHeap CompatiblePayload CompatibleEquality
open SourceCoreCompatibleDataPlaces
abbrev ValuesContext := SourceCoreCompatibleValues.Context
abbrev Scope := SourceCoreLocalCell.Scope

inductive Shape (values : ValuesContext) (source : TypedSource)
    (context : SourceSemantics.Context) (certificate : GenericExpressionMeaning.Certificate) (scope : Scope) (administrative : Core.Context)
    (definitions : DataEnvironment) (place : PlaceResolution) (prepared : Prepared) :
    List SourceCoreBasic.LoweredExpr → TypeSystem.Ty → Prop where
  | bare (empty : place.projections = []) (layout : CompatibleBareAssignment.Layout values prepared) :
      Shape values source context certificate scope administrative definitions place prepared [] prepared.route.rootSourceType
  | projected {codes leaf sourceTypes site}
      (layout : CompatiblePlaceAssignmentSuccess.Layout (definitions := definitions) values source
        certificate scope site place prepared codes sourceTypes leaf administrative)
      (ordinary : (∀ key value, prepared.route.rootSourceType ≠ .mapping key value) → prepared.route.rootMapping = none) :
      Shape values source context certificate scope administrative definitions place prepared codes leaf

structure Head (values : ValuesContext) (source : TypedSource)
    (context : SourceSemantics.Context) (certificate : GenericExpressionMeaning.Certificate) (scope : Scope) (administrative : Core.Context)
    (definitions : DataEnvironment) (assignment : AssignmentResolution) (operator : Syntax.ValueAssignOp)
    (rhs : ExpressionId) where
  prepared : Prepared
  index : Nat
  codes : List SourceCoreBasic.LoweredExpr
  leaf : TypeSystem.Ty
  lowered : SourceCoreBasic.LoweredExpr
  node : ExpressionNode
  invalid : Word
  shape : Shape values source context certificate scope administrative definitions assignment.target prepared codes leaf
  slot : SourceCoreLocalCell.lookup? scope assignment.target.root = some (index, prepared.route.rootType)
  writable : WritableLocal context assignment.target.root prepared.route.rootSourceType
  found : source.lookupExpression? rhs = some node
  right : certificate scope rhs lowered
  rightView : SourceCoreRawMetadata.runtimeType leaf = SourceCoreRawMetadata.runtimeType node.type
  rightType : lowered.type = prepared.route.leafType
  profile : operator = .equal ∨ SourceCoreRawMetadata.runtimeType leaf = .word ∨ SourceCoreRawMetadata.runtimeType leaf = .integer ∧ operator.wordOnly = false

namespace Head
variable {values : ValuesContext} {source : TypedSource}
  {context : SourceSemantics.Context} {certificate : GenericExpressionMeaning.Certificate} {scope : Scope} {administrative : Core.Context}
  {definitions : DataEnvironment} {assignment : AssignmentResolution} {operator : Syntax.ValueAssignOp} {rhs : ExpressionId}

def emit (head : Head values source context certificate scope administrative definitions assignment operator rhs)
    (next : Expr) (output : Ty) : Expr :=
  execute head.prepared (.var head.index) (SourceCoreCalls.packArguments head.codes) head.lowered.expression next output
    (binaryOperator (head.prepared.route.leafType = .integer) operator) false head.invalid

def writtenContext (head : Head values source context certificate scope administrative definitions assignment operator rhs)
    (actual : Core.Context) : Core.Context :=
  CompatibleRenamedPlaceSuccess.writtenContext head.prepared (SourceCoreCalls.packArguments head.codes).type actual

/-- The diagnostic table separately authenticates each emitted failure token. -/
structure Errors (head : Head values source context certificate scope administrative definitions assignment operator rhs)
    (registry : SourceCoreRawMetadata.Registry) (faults : FunctionCalls.FaultRep) : Prop where
  missing : ∀ {root resolved reason token count},
    CompatibleMixedRoute.FaultToken values.checked registry root head.prepared.steps resolved reason token count → faults reason token
  uninitialized : ∀ location, faults (.uninitializedLocation location) head.prepared.invalidProjection
  operands : faults (.invalidAssignmentOperands operator) head.invalid
end Head

end Solcore.SourceSemantics.CoreLowering.GenericAssignmentStatements
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.GenericAssignmentPreparedOrigins
/-! The selected assignment head retains its actual compiler preparation.
Bare roots keep their genuine empty projection receipt. Projected routes keep
same-site description and preparation of the exact selected head, beside its
actual path layout. These are static receipts only. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.GenericAssignmentStatements
open Core Frontend SourceInference SourceCoreCompatibleDataPlaces
variable {values : ValuesContext} {source : TypedSource}
  {context : SourceSemantics.Context} {certificate : GenericExpressionMeaning.Certificate}
  {scope : Scope} {administrative : Core.Context} {definitions : DataEnvironment}
  {assignment : AssignmentResolution} {operator : Syntax.ValueAssignOp} {rhs : ExpressionId}

/-- All site, fuel and diagnostic arguments are those used by the successful
assignment lowering that produced this same head. -/
inductive Head.PreparedAt
    (head : Head values source context certificate scope administrative definitions assignment operator rhs)
    (site : SourceCoreElaboration.ErrorSite) (fuel : Nat) (invalidProjection : Word)
    (missing : TypeSystem.Ty → Word) : Prop where
  | bare (empty : assignment.target.projections = []) :
      head.PreparedAt site fuel invalidProjection missing
  | projected {sourceTypes : List TypeSystem.Ty} (route : Route)
      (layout : CompatiblePlaceAssignmentSuccess.Layout (definitions := definitions) values source certificate
        scope site assignment.target head.prepared head.codes sourceTypes head.leaf administrative)
      (ordinary : (∀ key value, head.prepared.route.rootSourceType ≠ .mapping key value) →
        head.prepared.route.rootMapping = none)
      (shape : head.shape = .projected layout ordinary)
      (described : describe values values.checked.signatures source site assignment = .ok route)
      (preparedBy : prepare values fuel route invalidProjection missing = .ok head.prepared) :
      head.PreparedAt site fuel invalidProjection missing

end Solcore.SourceSemantics.CoreLowering.GenericAssignmentStatements
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.GenericAssignmentStatementCertificates
/-! Assignment certificates follow the successful production place callback
and flow branch. Independent source typing and native site typing remain
explicit static inputs; no child execution is assumed. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.GenericAssignmentStatements
open Core Frontend SourceInference SourceCoreCompatibleDataPlaces
open CompatibleEncoding (bind_ok)
open DataPatternValues DataPlaceCertificates CompatibleMixedRoute CompatiblePlaceCompilerCertificates

private theorem stored_type {source : TypedSource} {context : SourceSemantics.Context} {rhs : ExpressionId}
    {node : ExpressionNode} {type : TypeSystem.Ty}
    (unique : NodeOccurrencesUnique source) (found : source.lookupExpression? rhs = some node)
    (typed : ExpressionHasType source context rhs type) : node.type = type := by
  obtain ⟨actual, contains, same⟩ := typed.stored_type
  have identical := Option.some.inj (found.symm.trans (lookupExpression?_complete unique contains))
  exact identical ▸ same

/-- The bare path compiles only its RHS. Its receipt therefore requires no
certificate for unrelated source occurrences or nonexistent key computations. -/
theorem Head.of_lower_bare_with_token {values : ValuesContext} {source : TypedSource}
    {context : SourceSemantics.Context} {certificate : GenericExpressionMeaning.Certificate} {reasonAt : ExpressionId → Word}
    {scope : Scope} {administrative : Core.Context} {definitions : DataEnvironment}
    {assignment : AssignmentResolution} {operator : Solcore.Syntax.ValueAssignOp} {rhs : ExpressionId}
    {expression : ExpressionLowerer} {fuel : Nat} {site : SourceCoreElaboration.ErrorSite}
    {next code : Expr} {output : Ty} {invalidProjection invalidOperand : Word} {missing : TypeSystem.Ty → Word}
    (bare : assignment.target.projections = [])
    (unique : NodeOccurrencesUnique source)
    (writable : ∀ binder, rootBinder source assignment.target.root = .ok binder → WritableLocal context assignment.target.root binder.scheme.body)
    (rightTyped : ExpressionHasType source context rhs assignment.target.type)
    (profile : operator = .equal ∨ SourceCoreRawMetadata.runtimeType assignment.target.type = .word ∨
      SourceCoreRawMetadata.runtimeType assignment.target.type = .integer ∧ operator.wordOnly = false)
    (extract : ∀ lowered, expression fuel source scope rhs reasonAt = .ok lowered → ∃ node,
      source.lookupExpression? rhs = some node ∧ certificate scope rhs lowered)
    (accepted : lower values values.checked.signatures expression fuel source scope site assignment operator (some rhs)
      output next reasonAt invalidProjection invalidOperand missing = .ok code) :
    ∃ head : Head values source context certificate scope administrative definitions assignment operator rhs,
      code = head.emit next output ∧ head.invalid = invalidOperand := by
  obtain ⟨binder, prepared, index, lowered, binding, rootType, rawView, slot, layout, generated, sameType, _, codeEq⟩ :=
    CompatibleBareAssignment.of_lower bare accepted
  obtain ⟨node, found, tree⟩ := extract lowered generated
  have rawType := stored_type unique found rightTyped
  refine ⟨⟨prepared, index, [], prepared.route.rootSourceType, lowered, node, invalidOperand,
    .bare bare layout, slot, rootType ▸ writable binder binding, found, tree,
    by simpa only [rawType] using rawView, sameType, ?_⟩, codeEq, rfl⟩
  rcases profile with equal | word | ⟨integer, notWordOnly⟩
  · exact .inl equal
  · exact .inr (.inl (rawView.trans word))
  · exact .inr (.inr ⟨rawView.trans integer, notWordOnly⟩)

/-- Compatibility projection of the actual compiler receipt. -/
theorem Head.of_lower_bare {values : ValuesContext} {source : TypedSource}
    {context : SourceSemantics.Context} {certificate : GenericExpressionMeaning.Certificate} {reasonAt : ExpressionId → Word}
    {scope : Scope} {administrative : Core.Context} {definitions : DataEnvironment}
    {assignment : AssignmentResolution} {operator : Solcore.Syntax.ValueAssignOp} {rhs : ExpressionId}
    {expression : ExpressionLowerer} {fuel : Nat} {site : SourceCoreElaboration.ErrorSite}
    {next code : Expr} {output : Ty} {invalidProjection invalidOperand : Word} {missing : TypeSystem.Ty → Word}
    (bare : assignment.target.projections = [])
    (unique : NodeOccurrencesUnique source)
    (writable : ∀ binder, rootBinder source assignment.target.root = .ok binder → WritableLocal context assignment.target.root binder.scheme.body)
    (rightTyped : ExpressionHasType source context rhs assignment.target.type)
    (profile : operator = .equal ∨ SourceCoreRawMetadata.runtimeType assignment.target.type = .word ∨
      SourceCoreRawMetadata.runtimeType assignment.target.type = .integer ∧ operator.wordOnly = false)
    (extract : ∀ lowered, expression fuel source scope rhs reasonAt = .ok lowered → ∃ node,
      source.lookupExpression? rhs = some node ∧ certificate scope rhs lowered)
    (accepted : lower values values.checked.signatures expression fuel source scope site assignment operator (some rhs)
      output next reasonAt invalidProjection invalidOperand missing = .ok code) :
    ∃ head : Head values source context certificate scope administrative definitions assignment operator rhs,
      code = head.emit next output := by
  obtain ⟨head, emitted, _⟩ := Head.of_lower_bare_with_token bare unique writable rightTyped profile extract accepted
  exact ⟨head, emitted⟩

/-- Only actual ordered key occurrences are requested from the expression
extractor. Repeated occurrences retain their repeated compiler receipts. -/
private theorem keys_of_generated {checked : Checked} {source : TypedSource} {site : SourceCoreElaboration.ErrorSite}
    {root leaf : TypeSystem.Ty} {projections : List PlaceProjection} {position : Nat}
    {steps : List PreparedStep} {keys : List (ExpressionId × Ty)}
    (path : PreparedPath checked source site root projections position steps keys leaf)
    {expression : ExpressionLowerer} {fuel : Nat} {scope : Scope} {reasonAt : ExpressionId → Word}
    {codes : List SourceCoreBasic.LoweredExpr} {certificate : GenericExpressionMeaning.Certificate}
    (generated : ListRel (KeyGenerated expression fuel source scope reasonAt) keys codes)
    (extract : ∀ id code, id ∈ DataPlaceKeyOrder.sourceKeys projections → expression fuel source scope id reasonAt = .ok code →
      ∃ node, source.lookupExpression? id = some node ∧ certificate scope id code) :
    ∃ types, DataExpressionSequence.Tree source certificate scope (DataPlaceKeyOrder.sourceKeys projections) types codes ∧
      keys.map Prod.snd = codes.map (·.type) := by
  have collect : ∀ {keys codes}, ListRel (KeyGenerated expression fuel source scope reasonAt) keys codes →
      (∀ id code, id ∈ keys.map Prod.fst → expression fuel source scope id reasonAt = .ok code →
        ∃ node, source.lookupExpression? id = some node ∧ certificate scope id code) →
      ListRel (fun id code => ∃ node, source.lookupExpression? id = some node ∧ certificate scope id code)
        (keys.map Prod.fst) codes ∧ keys.map Prod.snd = codes.map (·.type) := by
    intro keys codes generated
    induction generated with
    | nil => intro _; exact ⟨.nil, rfl⟩
    | cons head tail ih =>
      intro extract
      have rest := ih (fun id code member compiled => extract id code (List.mem_cons_of_mem _ member) compiled)
      exact ⟨.cons (extract _ _ (by simp) head.1) rest.1, by simp only [List.map_cons, head.2, rest.2]⟩
  have receipts := collect generated (fun id code member compiled => extract id code (by simpa only [PreparedPath.key_ids path] using member) compiled)
  obtain ⟨types, tree⟩ := DataExpressionSequence.Tree.of_children receipts.1
  rw [PreparedPath.key_ids path] at tree
  exact ⟨types, tree, receipts.2⟩

theorem Head.of_lower_with_prepared {values : ValuesContext} {source : TypedSource}
    {context : SourceSemantics.Context} {certificate : GenericExpressionMeaning.Certificate} {reasonAt : ExpressionId → Word}
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
      SourceCoreRawMetadata.runtimeType assignment.target.type = .integer ∧ operator.wordOnly = false)
    (extract : ∀ id lowered, id ∈ rhs :: DataPlaceKeyOrder.sourceKeys assignment.target.projections →
      expression fuel source scope id reasonAt = .ok lowered → ∃ node,
      source.lookupExpression? id = some node ∧ certificate scope id lowered ∧
      HasType (SourceCoreLocalCell.coreContext scope ++ administrative) lowered.expression (LanguageResult.resultType lowered.type) definitions)
    (accepted : lower values values.checked.signatures expression fuel source scope site assignment operator (some rhs)
      output next reasonAt invalidProjection invalidOperand missing = .ok code)
    (typed : HasType (SourceCoreLocalCell.coreContext scope ++ administrative) code result definitions) :
    ∃ head : Head values source context certificate scope administrative definitions assignment operator rhs,
      code = head.emit next output ∧ head.invalid = invalidOperand ∧
        head.PreparedAt site fuel invalidProjection missing := by
  classical
  by_cases bare : assignment.target.projections = []
  · obtain ⟨head, emitted, token⟩ := Head.of_lower_bare_with_token bare unique writable rightTyped profile
      (fun lowered generated => by
        obtain ⟨node, found, tree, _⟩ := extract rhs lowered (by simp) generated
        exact ⟨node, found, tree⟩) accepted
    exact ⟨head, emitted, token, .bare bare⟩
  · cases generated_of_lower accepted with
    | intro route prepared index codes value described lookup preparedBy generated operatorValid rhsGenerated =>
      cases rhsGenerated with
      | @present id right rhsGenerated rhsType =>
        obtain ⟨node, found, certified, rhsTyped⟩ := extract rhs right (by simp) rhsGenerated
        obtain ⟨binder, leaf, description⟩ := CompatiblePlaceDescription.of_describe described
        obtain ⟨routeEq, _, path⟩ := description.prepared preparedBy
        obtain ⟨sourceTypes, tree, keyTypes⟩ := keys_of_generated path generated
          (fun id code member compiled => let ⟨node, found, certified, _⟩ := extract id code (List.mem_cons_of_mem rhs member) compiled; ⟨node, found, certified⟩)
        obtain ⟨views, leafView⟩ := CompatiblePlaceKeyTyping.of_typing unique signatures path rfl (sourceTyped binder description.binding) tree
        have rootEq : prepared.route.rootSourceType = binder.scheme.body := routeEq ▸ description.rootSource
        have actualPath : PreparedPath values.checked source site prepared.route.rootSourceType assignment.target.projections
            0 prepared.steps prepared.keys leaf := rootEq ▸ path
        have rhsType : right.type = prepared.route.leafType := by simpa only [routeEq] using rhsType.symm
        have layout : CompatiblePlaceAssignmentSuccess.Layout (definitions := definitions) values source certificate scope site
            assignment.target prepared codes sourceTypes leaf administrative := by
          refine ⟨actualPath, by simpa only [rootEq] using views, tree, keyTypes, ?_, ?_, ?_,
            CompatiblePlaceHelperTyping.getter_of_execute typed,
            CompatiblePlaceHelperTyping.setter_of_execute typed (CompatiblePlaceHelperTyping.rhs_shift_typed (by simpa only [rhsType] using rhsTyped))⟩
          · rw [← values.checked.catalog.project_runtimeType leaf, description.selectedType,
              values.checked.catalog.project_runtimeType, routeEq]
            exact description.leafProjected
          · intro k v declared
            rw [routeEq]
            exact description.virtual k v (rootEq.symm.trans declared)
          · intro empty
            have length := PreparedPath.steps_length path
            rw [empty, List.length_nil] at length
            exact bare (List.eq_nil_of_length_eq_zero length.symm)
        have ordinary : (∀ k v, prepared.route.rootSourceType ≠ .mapping k v) → prepared.route.rootMapping = none := by
          intro notMapping
          rw [routeEq]
          exact description.ordinary (fun k v same => notMapping k v (rootEq.trans same))
        have rawType := stored_type unique found rightTyped
        refine ⟨⟨prepared, index, codes, leaf, right, node, invalidOperand,
          .projected layout ordinary, by simpa only [routeEq] using lookup, rootEq ▸ writable binder description.binding,
          found, certified, by simpa only [rawType] using leafView, rhsType, ?_⟩, by simp [Head.emit, routeEq], rfl, ?_⟩
        · rcases profile with equal | word | ⟨integer, notWordOnly⟩
          · exact .inl equal
          · exact .inr (.inl (leafView.trans word))
          · exact .inr (.inr ⟨leafView.trans integer, notWordOnly⟩)
        · exact .projected route layout ordinary rfl described preparedBy

/-- Compatibility projection retains the original selected head and token. -/
theorem Head.of_lower_with_token {values : ValuesContext} {source : TypedSource}
    {context : SourceSemantics.Context} {certificate : GenericExpressionMeaning.Certificate} {reasonAt : ExpressionId → Word}
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
      SourceCoreRawMetadata.runtimeType assignment.target.type = .integer ∧ operator.wordOnly = false)
    (extract : ∀ id lowered, id ∈ rhs :: DataPlaceKeyOrder.sourceKeys assignment.target.projections →
      expression fuel source scope id reasonAt = .ok lowered → ∃ node,
      source.lookupExpression? id = some node ∧ certificate scope id lowered ∧
      HasType (SourceCoreLocalCell.coreContext scope ++ administrative) lowered.expression (LanguageResult.resultType lowered.type) definitions)
    (accepted : lower values values.checked.signatures expression fuel source scope site assignment operator (some rhs)
      output next reasonAt invalidProjection invalidOperand missing = .ok code)
    (typed : HasType (SourceCoreLocalCell.coreContext scope ++ administrative) code result definitions) :
    ∃ head : Head values source context certificate scope administrative definitions assignment operator rhs,
      code = head.emit next output ∧ head.invalid = invalidOperand := by
  obtain ⟨head, emitted, token, _preparedAt⟩ := Head.of_lower_with_prepared unique signatures sourceTyped writable
    rightTyped profile extract accepted typed
  exact ⟨head, emitted, token⟩


/-- Compatibility projection of the actual compiler receipt. -/
theorem Head.of_lower {values : ValuesContext} {source : TypedSource}
    {context : SourceSemantics.Context} {certificate : GenericExpressionMeaning.Certificate} {reasonAt : ExpressionId → Word}
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
      SourceCoreRawMetadata.runtimeType assignment.target.type = .integer ∧ operator.wordOnly = false)
    (extract : ∀ id lowered, id ∈ rhs :: DataPlaceKeyOrder.sourceKeys assignment.target.projections →
      expression fuel source scope id reasonAt = .ok lowered → ∃ node,
      source.lookupExpression? id = some node ∧ certificate scope id lowered ∧
      HasType (SourceCoreLocalCell.coreContext scope ++ administrative) lowered.expression (LanguageResult.resultType lowered.type) definitions)
    (accepted : lower values values.checked.signatures expression fuel source scope site assignment operator (some rhs)
      output next reasonAt invalidProjection invalidOperand missing = .ok code)
    (typed : HasType (SourceCoreLocalCell.coreContext scope ++ administrative) code result definitions) :
    ∃ head : Head values source context certificate scope administrative definitions assignment operator rhs,
      code = head.emit next output := by
  obtain ⟨head, emitted, _⟩ := Head.of_lower_with_token unique signatures sourceTyped writable rightTyped profile extract accepted typed
  exact ⟨head, emitted⟩

end Solcore.SourceSemantics.CoreLowering.GenericAssignmentStatements
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.GenericAssignmentReachableDiagnostics
/-! The existing diagnostic receipt remains available unchanged. This weaker
receipt authenticates operand tokens only for a source operand failure; missing
mapping defaults retain their original law, while uninitialized projection
errors require an actual nonempty projection path. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.GenericAssignmentStatements
open Core Frontend SourceInference

namespace Head
variable {values : ValuesContext} {source : TypedSource}
  {context : SourceSemantics.Context} {certificate : GenericExpressionMeaning.Certificate}
  {scope : Scope} {administrative : Core.Context} {definitions : DataEnvironment}
  {assignment : AssignmentResolution} {operator : Syntax.ValueAssignOp} {rhs : ExpressionId}

structure ReachableErrors (head : Head values source context certificate scope administrative definitions assignment operator rhs)
    (registry : SourceCoreRawMetadata.Registry) (faults : FunctionCalls.FaultRep) : Prop where
  missing : ∀ {root resolved reason token count},
    CompatibleMixedRoute.FaultToken values.checked registry root head.prepared.steps resolved reason token count → faults reason token
  uninitialized : head.prepared.steps ≠ [] → ∀ location, faults (.uninitializedLocation location) head.prepared.invalidProjection
  operands : AssignmentOperandDiagnostics.OperandsLaw faults operator head.invalid

theorem Errors.reachable
    {head : Head values source context certificate scope administrative definitions assignment operator rhs}
    {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
    (errors : head.Errors registry faults) : head.ReachableErrors registry faults :=
  ⟨errors.missing, fun _ => errors.uninitialized, AssignmentOperandDiagnostics.of_unconditional errors.operands⟩

theorem ReachableErrors.equal
    {head : Head values source context certificate scope administrative definitions assignment .equal rhs}
    {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
    (missing : ∀ {root resolved reason token count},
      CompatibleMixedRoute.FaultToken values.checked registry root head.prepared.steps resolved reason token count → faults reason token)
    (uninitialized : ∀ location, faults (.uninitializedLocation location) head.prepared.invalidProjection) :
    head.ReachableErrors registry faults :=
  ⟨missing, fun _ => uninitialized, AssignmentOperandDiagnostics.equal faults head.invalid⟩

/-- A plain bare write neither reads a projected leaf nor evaluates an operand
operation. Its static body needs no diagnostics for those unreachable faults. -/
theorem ReachableErrors.bare_equal
    {head : Head values source context certificate scope administrative definitions assignment .equal rhs}
    {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
    (empty : head.prepared.steps = []) : head.ReachableErrors registry faults := by
  refine ⟨?_, fun nonempty => False.elim (nonempty empty), AssignmentOperandDiagnostics.equal faults head.invalid⟩
  intro root resolved reason token count fault
  rw [empty] at fault
  cases fault

end Head
end Solcore.SourceSemantics.CoreLowering.GenericAssignmentStatements
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.GenericAssignmentDiagnosticCertificates
/-! The real loop-policy callback supplies the exact operand token. The table
relation describes only operand diagnostics; clients explicitly include it in
their whole fault relation. Missing/default and uninitialized place laws remain
separate. No native projection supplies raw scalar eligibility. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.GenericAssignmentDiagnostics
open Core Frontend SourceInference
open SourceCoreAssignmentFaultSites
open Certificates (OperandAt)

/-- A concrete relation for actual table diagnostics, with no invented entry
for plain assignment and no claim about another fault category. -/
def OperandRep (table : Table) : FunctionCalls.FaultRep
  | .invalidAssignmentOperands operator, token => ∃ diagnostic rawType,
      table.diagnostic? token = some diagnostic ∧
      diagnostic.error = .invalidAssignmentOperands operator none (some rawType)
  | _, _ => False

def token (table : Table) (site : SourceCoreElaboration.ErrorSite) (root : Resolved.LocalId)
    (operator : Syntax.ValueAssignOp) : Word :=
  if operator = .equal then .zero else table.reasonAt site root (.value operator)

theorem prepared_operands {source : TypedSource} {first : Nat} {table : Table}
    {node : StatementNode} {assignment : AssignmentResolution} {operator : Syntax.ValueAssignOp}
    (prepared : prepare source first = .ok table) (member : Node.statement node ∈ source.nodes)
    (occurs : OperandAt node assignment operator)
    (rawProfile : operator = .equal ∨ assignment.target.type = .word ∨ assignment.target.type = .integer ∧ operator.wordOnly = false) :
    AssignmentOperandDiagnostics.OperandsLaw (OperandRep table) operator
      (token table (.occurrence node.id.occurrence) assignment.target.root operator) := by
  apply AssignmentOperandDiagnostics.of_not_equal
  intro different
  have scalar : assignment.target.type = .word ∨ assignment.target.type = .integer := by
    rcases rawProfile with equal | scalar
    · exact (different equal).elim
    · exact scalar.imp_right And.left
  obtain ⟨site, _, _, _, kind, reason, diagnostic⟩ := Certificates.prepare_operand prepared member occurs different scalar
  refine ⟨site.diagnostic, site.rhsType, ?_, ?_⟩
  · simpa only [token, if_neg different, reason] using diagnostic
  · simp only [Site.diagnostic, kind]

/-- Relating operand diagnostics to a larger fault inventory is explicit. -/
theorem prepared_operands_included {source : TypedSource} {first : Nat} {table : Table}
    {node : StatementNode} {assignment : AssignmentResolution} {operator : Syntax.ValueAssignOp}
    {faults : FunctionCalls.FaultRep}
    (included : ∀ reason word, OperandRep table reason word → faults reason word)
    (prepared : prepare source first = .ok table) (member : Node.statement node ∈ source.nodes)
    (occurs : OperandAt node assignment operator)
    (rawProfile : operator = .equal ∨ assignment.target.type = .word ∨ assignment.target.type = .integer ∧ operator.wordOnly = false) :
    AssignmentOperandDiagnostics.OperandsLaw faults operator
      (token table (.occurrence node.id.occurrence) assignment.target.root operator) := by
  intro previous right invalid
  exact included _ _ (prepared_operands prepared member occurs rawProfile previous right invalid)

/-- Both ordinary statements and for-header items select this same real
callback. Equal uses zero; compound operators use the actual table lookup. -/
theorem policy_assignment (values : SourceCoreCompatibleValues.Context)
    (solved : List SolvedRequirement) (table : Table) (diagnostics : SourceCoreDataPlaceFaultSites.Program)
    (owner : SourceSpecialization.SpecializationKey) (expression : SourceCoreFunctions.ExpressionLowerer)
    (sourceCells : Option SourceCoreSourceCells.Allocator) (definitions : Option DataEnvironment)
    (fuel : Nat) (source : TypedSource) (scope : SourceCoreLocalCell.Scope)
    (site : SourceCoreElaboration.ErrorSite) (assignment : AssignmentResolution)
    (operator : Syntax.ValueAssignOp) (rhs : ExpressionId) (output : Ty) (next : Expr) (reasonAt : ExpressionId → Word) :
    SourceCoreLoops.assignValue (SourceCoreCompatibleDataMatches.loopPolicy values solved table diagnostics owner expression sourceCells definitions)
      fuel source scope site assignment operator rhs output next reasonAt =
    SourceCoreCompatibleDataPlaces.lower values values.checked.signatures expression fuel source scope site assignment operator
      (some rhs) output next reasonAt (diagnostics.placeReason owner site assignment.target.root none)
      (token table site assignment.target.root operator)
      (fun type => diagnostics.placeReason owner site assignment.target.root (some type)) := by
  cases operator <;> rfl

end Solcore.SourceSemantics.CoreLowering.GenericAssignmentDiagnostics

namespace Solcore.SourceSemantics.CoreLowering.GenericAssignmentStatements
open Core Frontend SourceInference SourceCoreCompatibleDataPlaces
open GenericAssignmentDiagnostics

theorem Head.reachable_of_token
    {values : ValuesContext} {source : TypedSource} {context : SourceSemantics.Context}
    {certificate : GenericExpressionMeaning.Certificate} {scope : Scope} {administrative : Core.Context}
    {definitions : DataEnvironment} {assignment : AssignmentResolution} {operator : Syntax.ValueAssignOp} {rhs : ExpressionId}
    (head : Head values source context certificate scope administrative definitions assignment operator rhs)
    {table : SourceCoreAssignmentFaultSites.Table} {first : Nat} {node : StatementNode}
    {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
    (same : head.invalid = token table (.occurrence node.id.occurrence) assignment.target.root operator)
    (included : ∀ reason word, OperandRep table reason word → faults reason word)
    (prepared : SourceCoreAssignmentFaultSites.prepare source first = .ok table)
    (member : Node.statement node ∈ source.nodes)
    (occurs : SourceCoreAssignmentFaultSites.Certificates.OperandAt node assignment operator)
    (rawProfile : operator = .equal ∨ assignment.target.type = .word ∨ assignment.target.type = .integer ∧ operator.wordOnly = false)
    (missing : ∀ {root resolved reason word count},
      CompatibleMixedRoute.FaultToken values.checked registry root head.prepared.steps resolved reason word count → faults reason word)
    (uninitialized : ∀ location, faults (.uninitializedLocation location) head.prepared.invalidProjection) :
    head.ReachableErrors registry faults :=
  ⟨missing, fun _ => uninitialized, same.symm ▸ prepared_operands_included included prepared member occurs rawProfile⟩

/-- One compiler traversal supplies both the emitted expression and its exact
operand token, then the actual prepared table supplies the reachable law. -/
theorem Head.of_prepared_policy
    {values : ValuesContext} {source : TypedSource} {context : SourceSemantics.Context}
    {certificate : GenericExpressionMeaning.Certificate} {reasonAt : ExpressionId → Word}
    {scope : Scope} {administrative : Core.Context} {definitions : DataEnvironment}
    {assignment : AssignmentResolution} {operator : Syntax.ValueAssignOp} {rhs : ExpressionId}
    {expression : SourceCoreFunctions.ExpressionLowerer} {fuel : Nat} {node : StatementNode}
    {next code : Expr} {output result : Ty}
    {solved : List SolvedRequirement} {table : SourceCoreAssignmentFaultSites.Table} {first : Nat}
    {diagnostics : SourceCoreDataPlaceFaultSites.Program} {owner : SourceSpecialization.SpecializationKey}
    {sourceCells : Option SourceCoreSourceCells.Allocator} {ambientDefinitions : Option DataEnvironment}
    {faults : FunctionCalls.FaultRep}
    (unique : NodeOccurrencesUnique source) (signatures : context.signatures = values.checked.signatures)
    (sourceTyped : ∀ binder, rootBinder source assignment.target.root = .ok binder →
      SourceProjectionsHaveType source context binder.scheme.body assignment.target.projections assignment.target.type)
    (writable : ∀ binder, rootBinder source assignment.target.root = .ok binder → WritableLocal context assignment.target.root binder.scheme.body)
    (rightTyped : ExpressionHasType source context rhs assignment.target.type)
    (rawProfile : operator = .equal ∨ assignment.target.type = .word ∨ assignment.target.type = .integer ∧ operator.wordOnly = false)
    (extract : ∀ id lowered, id ∈ rhs :: DataPlaceKeyOrder.sourceKeys assignment.target.projections →
      expression fuel source scope id reasonAt = .ok lowered → ∃ child,
      source.lookupExpression? id = some child ∧ certificate scope id lowered ∧
      HasType (SourceCoreLocalCell.coreContext scope ++ administrative) lowered.expression (LanguageResult.resultType lowered.type) definitions)
    (prepared : SourceCoreAssignmentFaultSites.prepare source first = .ok table)
    (member : Node.statement node ∈ source.nodes)
    (occurs : SourceCoreAssignmentFaultSites.Certificates.OperandAt node assignment operator)
    (included : ∀ reason word, OperandRep table reason word → faults reason word)
    (accepted : SourceCoreLoops.assignValue
      (SourceCoreCompatibleDataMatches.loopPolicy values solved table diagnostics owner expression sourceCells ambientDefinitions)
      fuel source scope (.occurrence node.id.occurrence) assignment operator rhs output next reasonAt = .ok code)
    (typed : HasType (SourceCoreLocalCell.coreContext scope ++ administrative) code result definitions) :
    ∃ head : Head values source context certificate scope administrative definitions assignment operator rhs,
      code = head.emit next output ∧
      head.invalid = token table (.occurrence node.id.occurrence) assignment.target.root operator ∧
      AssignmentOperandDiagnostics.OperandsLaw faults operator head.invalid := by
  rw [policy_assignment] at accepted
  have profile : operator = .equal ∨ SourceCoreRawMetadata.runtimeType assignment.target.type = .word ∨
      SourceCoreRawMetadata.runtimeType assignment.target.type = .integer ∧ operator.wordOnly = false := by
    rcases rawProfile with equal | word | ⟨integer, notWordOnly⟩
    · exact .inl equal
    · exact .inr (.inl (by rw [word]; rfl))
    · exact .inr (.inr ⟨by rw [integer]; rfl, notWordOnly⟩)
  obtain ⟨head, emitted, same⟩ := Head.of_lower_with_token unique signatures sourceTyped writable rightTyped profile extract accepted typed
  exact ⟨head, emitted, same, same.symm ▸ prepared_operands_included included prepared member occurs rawProfile⟩

end Solcore.SourceSemantics.CoreLowering.GenericAssignmentStatements
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.GenericAssignmentStatementMeaning
/-! Shared assignment composition consumes a typed expression meaning contract.
Concrete clients discharge that contract with their own expression Tree theorem.
Seven actual temporary values retain post-write typing and closure captures. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.GenericAssignmentStatements
open Core Frontend SourceInference GeneralHeap CompatiblePayload CompatibleEquality CompatibleHeap CoreProof
open SourceCoreCompatibleDataPlaces GenericExpressionMeaning

namespace Head
variable {values : ValuesContext} {source : TypedSource}
  {context : SourceSemantics.Context} {certificate : GenericExpressionMeaning.Certificate} {scope : Scope} {administrative : Core.Context}
  {ambient : AmbientDefinitions values.checked.catalog.definitions}
  (functions : FunctionModel values.checked.catalog ambient)
  {registry : SourceCoreRawMetadata.Registry} (extension : SourceCoreRawMetadata.Extends values.registry registry)
  (program : Program) (evidence : Dynamic.EvidenceEnvironment)
  {faults : FunctionCalls.FaultRep}
  (meaning : TypedGenericExpressionMeaning.Preserves (payloadModel values.checked registry functions)
    program context evidence source certificate faults)
  (reflection : TypedGenericExpressionMeaning.Reflects (payloadModel values.checked registry functions)
    program context evidence source certificate faults)
  {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
  (observations : FunctionObservations values.checked.catalog functions identities)
  {assignment : AssignmentResolution} {operator : Syntax.ValueAssignOp} {rhs : ExpressionId}
  (head : Head values source context certificate scope administrative ambient.definitions assignment operator rhs)
  {mapping : LocationMap} {world : StoreTyping} {environment : Dynamic.Environment}
  {canonical actual : Environment} {before : Dynamic.Heap} {store : Store} {actualContext : Core.Context} {ξ : Renaming}
  (environments : DataHeap.EnvRepresents (definitions := ambient.definitions) (storageCatalog values.checked.catalog)
    mapping world administrative scope environment canonical)
  (heaps : HeapRepresents values.checked registry functions mapping world before store)
  (locals : Dynamic.EnvironmentAgrees before context.locals environment)
  (agrees : ReadOnly.EnvironmentsAgree ξ canonical actual)
  (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)

include extension meaning faithful observations environments heaps locals agrees actualTyped in
theorem preserves_prefix {updated : Dynamic.Value} {after : Dynamic.Heap}
    (trace : Dynamic.SourcePlaceAssignment program context evidence source (Dynamic.AssignmentValueApplies operator)
      environment before assignment.target rhs updated after) :
    ∃ finalStore finalMap finalWorld slots,
      HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      slots.length = 7 ∧ RuntimeEnvironmentHasTypes finalWorld (slots ++ actual) (head.writtenContext actualContext) ambient.definitions ∧
      ∀ next output, ContinuationAgreement actual store ((head.emit next output).rename ξ)
        (slots ++ actual) finalStore (shift 7 (next.rename ξ)) := by
  rcases head with ⟨prepared, index, codes, leaf, lowered, node, invalid, shape, slot, writable, found, right, rightView, rightType, profile⟩
  cases shape with
  | bare empty layout =>
    obtain ⟨_, finalStore, finalMap, finalWorld, slots, _, finalHeaps, maps, worlds, frame, metadata, count, typed, continuation⟩ :=
      CompatibleBareAssignment.preserves_prefix layout empty extension meaning observations right found rightView rightType profile
        environments heaps locals agrees actualTyped slot writable trace invalid
    exact ⟨finalStore, finalMap, finalWorld, slots, finalHeaps, maps, worlds, frame, metadata, count, by simpa [Head.writtenContext, CompatibleRenamedPlaceSuccess.writtenContext, CompatibleBareAssignment.writtenContext, Prepared.optionalLeaf, SourceCoreCalls.packArguments, layout.sameType] using typed, continuation⟩
  | projected layout ordinary =>
    obtain ⟨_, finalStore, finalMap, finalWorld, _, finalHeaps, maps, worlds, frame, metadata, slots, count, typed, continuation⟩ :=
      CompatibleRenamedPlaceSuccess.preserves_prefix layout ordinary extension meaning faithful observations right found rightView rightType profile
        environments heaps locals agrees actualTyped slot writable trace invalid
    exact ⟨finalStore, finalMap, finalWorld, slots, finalHeaps, maps, worlds, frame, metadata, count, typed, continuation⟩

include extension meaning faithful observations environments heaps locals agrees actualTyped in
theorem preserves_fault_reachable (errors : head.ReachableErrors registry faults)
    {reason : Dynamic.SemanticFault} {after : Dynamic.Heap}
    (trace : Dynamic.SourcePlaceAssignmentFaults program context evidence source environment before assignment.target operator rhs reason after)
    (next : Expr) (output : Ty) :
    ∃ token finalStore finalMap finalWorld,
      Evaluates actual store ((head.emit next output).rename ξ) (.inLeft output (.word token)) finalStore ∧ faults reason token ∧
      HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after := by
  rcases head with ⟨prepared, index, codes, leaf, lowered, node, invalid, shape, slot, writable, found, right, rightView, rightType, profile⟩
  cases shape with
  | bare empty layout =>
    exact CompatibleBareAssignment.preserves_fault_reachable layout empty extension meaning observations right found rightView rightType profile
      environments heaps locals agrees actualTyped slot writable trace next output invalid errors.operands
  | projected layout ordinary =>
    exact CompatibleRenamedPlaceFaults.preserves layout ordinary extension meaning faithful observations
      errors.missing (errors.uninitialized layout.nonempty) right found rightView rightType profile environments heaps locals agrees actualTyped slot writable trace next output invalid

include extension meaning faithful observations environments heaps locals agrees actualTyped in
/-- Compatibility entry point retaining the original diagnostic receipt. -/
theorem preserves_fault (errors : head.Errors registry faults)
    {reason : Dynamic.SemanticFault} {after : Dynamic.Heap}
    (trace : Dynamic.SourcePlaceAssignmentFaults program context evidence source environment before assignment.target operator rhs reason after)
    (next : Expr) (output : Ty) :
    ∃ token finalStore finalMap finalWorld,
      Evaluates actual store ((head.emit next output).rename ξ) (.inLeft output (.word token)) finalStore ∧ faults reason token ∧
      HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after := by
  exact preserves_fault_reachable functions extension program evidence meaning faithful observations head environments heaps locals agrees actualTyped errors.reachable trace next output

include extension meaning reflection faithful observations environments heaps locals agrees actualTyped in
theorem reflects_reachable (functionTypes : FunctionRuntimeViews functions) (errors : head.ReachableErrors registry faults)
    {next : Expr} {output : Ty} {value : Value} {finalStore : Store}
    (completed : Evaluates actual store ((head.emit next output).rename ξ) value finalStore) :
    (∃ reason token after finalMap finalWorld,
      Dynamic.SourcePlaceAssignmentFaults program context evidence source environment before assignment.target operator rhs reason after ∧
      value = .inLeft output (.word token) ∧ faults reason token ∧
      HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after) ∨
    (∃ updated after written finalMap finalWorld slots,
      Dynamic.SourcePlaceAssignment program context evidence source (Dynamic.AssignmentValueApplies operator)
        environment before assignment.target rhs updated after ∧
      HeapRepresents values.checked registry functions finalMap finalWorld after written ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap written ∧ Dynamic.HeapMetadataExtend before after ∧
      slots.length = 7 ∧ RuntimeEnvironmentHasTypes finalWorld (slots ++ actual) (head.writtenContext actualContext) ambient.definitions ∧
      Evaluates (slots ++ actual) written (shift 7 (next.rename ξ)) value finalStore) := by
  rcases head with ⟨prepared, index, codes, leaf, lowered, node, invalid, shape, slot, writable, found, right, rightView, rightType, profile⟩
  cases shape with
  | bare empty layout =>
    have result := CompatibleBareAssignment.reflects_reachable layout empty extension reflection observations right found rightView rightType profile
      environments heaps locals agrees actualTyped slot writable errors.operands completed
    cases result with
    | fault trace same matched finalHeaps maps worlds frame metadata => exact .inl ⟨_, _, _, _, _, trace, same, matched, finalHeaps, maps, worlds, frame, metadata⟩
    | success trace _ finalHeaps maps worlds frame metadata count typed continuation =>
      exact .inr ⟨_, _, _, _, _, _, trace, finalHeaps, maps, worlds, frame, metadata, count, by simpa [Head.writtenContext, CompatibleRenamedPlaceSuccess.writtenContext, CompatibleBareAssignment.writtenContext, Prepared.optionalLeaf, SourceCoreCalls.packArguments, layout.sameType] using typed, continuation⟩
  | projected layout ordinary =>
    rcases CompatibleRenamedPlaceReflection.reflects layout ordinary extension reflection meaning functionTypes faithful observations
      errors.missing (errors.uninitialized layout.nonempty) right found rightView rightType profile environments heaps agrees actualTyped locals slot writable completed with
      ⟨_, _, _, _, _, trace, same, matched, finalHeaps, maps, worlds, frame, metadata⟩ |
      ⟨_, _, _, _, _, _, trace, finalHeaps, maps, worlds, frame, metadata, count, typed, continuation⟩
    · exact .inl ⟨_, _, _, _, _, trace, same, matched, finalHeaps, maps, worlds, frame, metadata⟩
    · exact .inr ⟨_, _, _, _, _, _, trace, finalHeaps, maps, worlds, frame, metadata, count, typed, continuation⟩
include extension meaning reflection faithful observations environments heaps locals agrees actualTyped in
/-- Compatibility entry point retaining the original diagnostic receipt. -/
theorem reflects (functionTypes : FunctionRuntimeViews functions) (errors : head.Errors registry faults)
    {next : Expr} {output : Ty} {value : Value} {finalStore : Store}
    (completed : Evaluates actual store ((head.emit next output).rename ξ) value finalStore) :
    (∃ reason token after finalMap finalWorld,
      Dynamic.SourcePlaceAssignmentFaults program context evidence source environment before assignment.target operator rhs reason after ∧
      value = .inLeft output (.word token) ∧ faults reason token ∧
      HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after) ∨
    (∃ updated after written finalMap finalWorld slots,
      Dynamic.SourcePlaceAssignment program context evidence source (Dynamic.AssignmentValueApplies operator)
        environment before assignment.target rhs updated after ∧
      HeapRepresents values.checked registry functions finalMap finalWorld after written ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap written ∧ Dynamic.HeapMetadataExtend before after ∧
      slots.length = 7 ∧ RuntimeEnvironmentHasTypes finalWorld (slots ++ actual) (head.writtenContext actualContext) ambient.definitions ∧
      Evaluates (slots ++ actual) written (shift 7 (next.rename ξ)) value finalStore) := by
  exact reflects_reachable functions extension program evidence meaning reflection faithful observations head environments heaps locals agrees actualTyped functionTypes errors.reachable completed

end Head
end Solcore.SourceSemantics.CoreLowering.GenericAssignmentStatements
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.GenericMatchChildren
/-! Finite children of the actual compatible match compiler. Requests retain
exact scopes, statement lists and generated code. The receipt is structural;
no child evaluation is stored. The enclosing recursive statement Tree adds a
source context and a positive recursive premise for each member. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.GenericMatchChildren
open Core Frontend SourceInference SourceCoreCompatibleDataMatches
open CompatibleMatchCertificates

structure Request where
  scope : Scope
  statements : List StatementId
  code : Expr

/-- A callback certificate that can contain only the retained finite children. -/
def Occurs (requests : List Request) : BodyCertificate :=
  fun scope statements code => ⟨scope, statements, code⟩ ∈ requests

def armRequests (scope : Scope) : List TypedMatchCase → List (Pattern × Expr) → List Request
  | arm :: cases, (pattern, code) :: arms =>
      ⟨armScope scope pattern, arm.body, code⟩ :: armRequests scope cases arms
  | _, _ => []

def fallbackRequests (scope : Scope) (fallback : Option (List StatementId)) (code : Expr) : List Request :=
  match fallback with
  | none => []
  | some statements => [⟨scope, statements, code⟩]

theorem Arms.mapBodies {compilation : SourceCoreCompatibleDataMatches.Context} {source : TypedSource}
    {site : StatementId} {scope : Scope} {expected : TypeSystem.Ty}
    {first second : BodyCertificate} {cases : List TypedMatchCase} {arms : List (Pattern × Expr)}
    (certified : Arms compilation source site scope expected first cases arms)
    (transport : ∀ scope statements code, first scope statements code → second scope statements code) :
    Arms compilation source site scope expected second cases arms := by
  induction certified with
  | nil => exact .nil
  | cons pattern typed body tail ih => exact .cons pattern typed (transport _ _ _ body) ih

theorem Fallback.mapBodies {first second : BodyCertificate} {scope : Scope} {type : Ty}
    {fallback : Option (List StatementId)} {code : Expr}
    (certified : Fallback first scope type fallback code)
    (transport : ∀ scope statements code, first scope statements code → second scope statements code) :
    Fallback second scope type fallback code := by
  cases certified with
  | none => exact .none
  | some body => exact .some (transport _ _ _ body)

theorem Arms.requests {compilation : SourceCoreCompatibleDataMatches.Context} {source : TypedSource}
    {site : StatementId} {scope : Scope} {expected : TypeSystem.Ty}
    {bodyCertificate : BodyCertificate} {cases : List TypedMatchCase} {arms : List (Pattern × Expr)}
    (certified : Arms compilation source site scope expected bodyCertificate cases arms) :
    Arms compilation source site scope expected (Occurs (armRequests scope cases arms)) cases arms ∧
      ∀ request ∈ armRequests scope cases arms, bodyCertificate request.scope request.statements request.code := by
  induction certified with
  | nil => exact ⟨.nil, by intro request member; cases member⟩
  | @cons arm cases pattern code arms patternCertificate typed body tail ih =>
    obtain ⟨tailCertified, members⟩ := ih
    constructor
    · apply Arms.cons patternCertificate typed
      · exact List.mem_cons_self
      · apply Arms.mapBodies tailCertified
        intro scope statements code member
        exact List.mem_cons_of_mem _ member
    · intro request member
      cases member with
      | head => exact body
      | tail _ member => exact members _ member

theorem Fallback.requests {bodyCertificate : BodyCertificate} {scope : Scope} {type : Ty}
    {fallback : Option (List StatementId)} {code : Expr}
    (certified : Fallback bodyCertificate scope type fallback code) :
    Fallback (Occurs (fallbackRequests scope fallback code)) scope type fallback code ∧
      ∀ request ∈ fallbackRequests scope fallback code, bodyCertificate request.scope request.statements request.code := by
  cases certified with
  | none => exact ⟨.none, by intro request member; cases member⟩
  | some body =>
    constructor
    · exact .some List.mem_cons_self
    · intro request member
      cases member with
      | head => exact body
      | tail _ member => cases member

theorem Arms.requests_length {compilation : SourceCoreCompatibleDataMatches.Context} {source : TypedSource}
    {site : StatementId} {scope : Scope} {expected : TypeSystem.Ty}
    {bodyCertificate : BodyCertificate} {cases : List TypedMatchCase} {arms : List (Pattern × Expr)}
    (certified : Arms compilation source site scope expected bodyCertificate cases arms) :
    (armRequests scope cases arms).length = cases.length := by
  induction certified with
  | nil => rfl
  | cons _ _ _ _ ih => exact congrArg Nat.succ ih

/-- Only the match's actual scrutinee occurrence needs an expression receipt. -/
theorem Certificate.mapExpressionAt
    {compilation : SourceCoreCompatibleDataMatches.Context} {source : TypedSource} {scope : Scope}
    {id : StatementId} {resolution : MatchResolution} {resultType : Ty} {internalReason : Word}
    {first second : ExpressionCertificate} {bodyCertificate : BodyCertificate} {code : Expr}
    (certificate : Certificate compilation source scope id resolution resultType internalReason first bodyCertificate code)
    (transport : ∀ lowered, first scope resolution.scrutinee lowered → second scope resolution.scrutinee lowered) :
    Certificate compilation source scope id resolution resultType internalReason second bodyCertificate code := by
  cases certificate with
  | matchWith read allowed form requirements hiddenOwned hiddenFresh scrutineeOwned scrutineeFound projection
      expression sameType armCertificates fallbackCertificate branchesCertified hiddenCompiled =>
    exact .matchWith read allowed form requirements hiddenOwned hiddenFresh scrutineeOwned scrutineeFound projection
      (transport _ expression) sameType armCertificates fallbackCertificate branchesCertified hiddenCompiled

/-- Every emitted arm and optional default remains in source order. Equal
requests are retained as duplicates; no set or lookup collapses occurrences. -/
theorem Certificate.finite_children
    {compilation : SourceCoreCompatibleDataMatches.Context} {source : TypedSource} {scope : Scope}
    {id : StatementId} {resolution : MatchResolution} {resultType : Ty} {internalReason : Word}
    {expressionCertificate : ExpressionCertificate} {bodyCertificate : BodyCertificate} {code : Expr}
    (certificate : Certificate compilation source scope id resolution resultType internalReason
      expressionCertificate bodyCertificate code) :
    ∃ requests,
      Certificate compilation source scope id resolution resultType internalReason expressionCertificate (Occurs requests) code ∧
      requests.length = resolution.cases.length + (if resolution.defaultBody.isSome then 1 else 0) ∧
      ∀ request ∈ requests, bodyCertificate request.scope request.statements request.code := by
  cases certificate with
  | @matchWith node statementType scrutineeNode type scrutinee arms fallback branches code
      read allowed form requirements hiddenOwned hiddenFresh scrutineeOwned scrutineeFound projection
      expression sameType armCertificates fallbackCertificate branchesCertified hiddenCompiled =>
    obtain ⟨retainedArms, armMembers⟩ := Arms.requests armCertificates
    obtain ⟨retainedFallback, fallbackMembers⟩ := Fallback.requests fallbackCertificate
    refine ⟨armRequests ((resolution.hiddenScrutinee, type) :: scope) resolution.cases arms ++
      fallbackRequests ((resolution.hiddenScrutinee, type) :: scope) resolution.defaultBody fallback, ?_, ?_, ?_⟩
    · apply Certificate.matchWith read allowed form requirements hiddenOwned hiddenFresh scrutineeOwned scrutineeFound projection expression sameType
      · apply Arms.mapBodies retainedArms
        intro scope statements code member
        exact List.mem_append_left _ member
      · apply Fallback.mapBodies retainedFallback
        intro scope statements code member
        exact List.mem_append_right _ member
      · exact branchesCertified
      · exact hiddenCompiled
    · have count := Arms.requests_length armCertificates
      rw [List.length_append, count]
      cases resolution.defaultBody <;> rfl
    · intro request member
      rcases List.mem_append.mp member with left | right
      · exact armMembers _ left
      · exact fallbackMembers _ right

/-- The finite certificate is extracted from the real callback invocations;
its child facts contain compiler equations, not semantic executions. -/
theorem finite_of_lower
    {compilation : SourceCoreCompatibleDataMatches.Context} {lowerExpression : ExpressionLowerer} {lowerBody : BodyLowerer}
    {fuel : Nat} {source : TypedSource} {scope : Scope} {id : StatementId}
    {resolution : MatchResolution} {resultType : Ty}
    {reasonAt : ExpressionId → Word} {internalReason : Word} {code : Expr}
    {expressionCertificate : ExpressionCertificate}
    (expressionExtract : ∀ childFuel result,
      lowerExpression childFuel source scope resolution.scrutinee reasonAt = .ok result →
      expressionCertificate scope resolution.scrutinee result)
    (accepted : lowerWithReasons compilation lowerExpression lowerBody fuel source scope id resolution
      resultType reasonAt internalReason = .ok code) :
    ∃ requests,
      Certificate compilation source scope id resolution resultType internalReason expressionCertificate (Occurs requests) code ∧
      requests.length = resolution.cases.length + (if resolution.defaultBody.isSome then 1 else 0) ∧
      ∀ request ∈ requests, ∃ childFuel,
        lowerBody childFuel source request.scope request.statements resultType reasonAt internalReason = .ok request.code := by
  have raw := certificate_of_lowerWithReasons
    (expressionCertificate := fun scope id lowered => ∃ childFuel,
      lowerExpression childFuel source scope id reasonAt = .ok lowered)
    (bodyCertificate := fun scope statements code => ∃ childFuel,
      lowerBody childFuel source scope statements resultType reasonAt internalReason = .ok code)
    (fun childFuel _ _ _ generated => ⟨childFuel, generated⟩)
    (fun childFuel _ _ _ generated => ⟨childFuel, generated⟩) accepted
  apply Certificate.finite_children (bodyCertificate := fun scope statements code => ∃ childFuel,
    lowerBody childFuel source scope statements resultType reasonAt internalReason = .ok code)
  exact Certificate.mapExpressionAt raw (fun lowered ⟨childFuel, generated⟩ => expressionExtract childFuel lowered generated)

/-- A selected arm/default exposes a member of the same finite request list.
No-branch fallthrough has no body child and is kept as its own alternative. -/
theorem selected_request {requests : List Request} {scope : Scope}
    {environment finalEnvironment : Dynamic.Environment} {heap finalHeap : Dynamic.Heap}
    {type : Ty} {selection : Dynamic.MatchCaseSelection} {finalScope : Scope} {code : Expr}
    (selected : DataMatchBranchPrefix.SelectedBody (Occurs requests) scope environment heap type
      selection finalScope finalEnvironment finalHeap code) :
    (selection = .noBranch ∧ finalScope = scope ∧ finalEnvironment = environment ∧
      finalHeap = heap ∧ code = LocalLoop.fallthrough type) ∨
    ∃ request ∈ requests, request.scope = finalScope ∧ request.code = code ∧
      ((∃ bindings, selection = .arm request.statements bindings) ∨ selection = .default request.statements) := by
  cases selected with
  | @arm statements bindings compiledBindings finalEnvironment finalHeap code binders allocated certified =>
    exact .inr ⟨⟨_, statements, code⟩, certified, rfl, rfl, .inl ⟨bindings, rfl⟩⟩
  | @default statements code certified =>
    exact .inr ⟨⟨scope, statements, code⟩, certified, rfl, rfl, .inr rfl⟩
  | noBranch => exact .inl ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- Source contexts are authenticated independently of native scope/type
projection. Several arms may share a request but have different source
contexts; every such source context remains a distinct child obligation. -/
inductive ContextFor (source : TypedSource) (parent : SourceSemantics.Context)
    (scrutineeType : TypeSystem.Ty) (cases : List TypedMatchCase)
    (fallback : Option (List StatementId)) (request : Request) : SourceSemantics.Context → Prop where
  | arm {arm binders arity context}
      (member : arm ∈ cases) (statements : request.statements = arm.body)
      (patternTyped : TypedMatchPatternHasType parent arm.pattern scrutineeType binders arity)
      (extended : BindersExtend source.owner parent binders context) :
      ContextFor source parent scrutineeType cases fallback request context
  | default (statements : fallback = some request.statements) :
      ContextFor source parent scrutineeType cases fallback request parent

/-- Independent pattern/body typing identifies the selected arm's context.
The actual request is compared only on its source statement list here; its
native scope/code remains the separate compiler receipt. -/
theorem ContextFor.selected_arm
    {source : TypedSource} {control : ControlContext} {parent : SourceSemantics.Context}
    {scrutineeType : TypeSystem.Ty} {cases : List TypedMatchCase} {facts : List BodyFacts}
    {fallback : Option (List StatementId)} {value : Dynamic.Value} {body : List StatementId}
    {bindings : List (TypedBinder × Dynamic.Value)} (request : Request)
    (sameBody : request.statements = body)
    (typed : MatchCasesHaveType source control parent scrutineeType cases facts)
    (selected : Dynamic.MatchCasesSelect parent value cases fallback (.arm body bindings)) :
    ∃ context finalContext bodyFacts,
      ContextFor source parent scrutineeType cases fallback request context ∧
      BindersExtend source.owner parent (bindings.map Prod.fst) context ∧
      StatementsHaveType source control context body finalContext bodyFacts ∧ bodyFacts ∈ facts := by
  cases selected with
  | head matched =>
    cases typed with
    | cons head tail =>
      cases head with
      | intro patternTyped extended bodyTyped =>
        exact ⟨_, _, _, .arm List.mem_cons_self sameBody patternTyped extended,
          DataMatchSourceScopes.PatternMatches.binders patternTyped matched ▸ extended,
          bodyTyped, List.mem_cons_self⟩
  | @tail arm rest _ _ notMatched selected =>
    cases typed with
    | cons head tail =>
      obtain ⟨context, finalContext, bodyFacts, child, extended, bodyTyped, member⟩ :=
        ContextFor.selected_arm request sameBody tail selected
      have lifted : ContextFor source parent scrutineeType (arm :: rest) fallback request context := by
        cases child with
        | arm member same typed extended => exact .arm (List.mem_cons_of_mem _ member) same typed extended
        | default same => exact .default same
      exact ⟨context, finalContext, bodyFacts, lifted, extended, bodyTyped, List.mem_cons_of_mem _ member⟩
termination_by cases.length


private theorem binder_context_unique {owner : Resolved.DeclarationId} {parent first second : SourceSemantics.Context}
    {binders : List TypedBinder} (left : BindersExtend owner parent binders first)
    (right : BindersExtend owner parent binders second) : first = second := by
  induction left generalizing second with
  | nil => cases right; rfl
  | cons head tail ih =>
    cases head
    cases right with
    | cons head tail => cases head; exact ih tail

theorem ContextFor.selected_arm_at
    {source : TypedSource} {control : ControlContext} {parent armContext : SourceSemantics.Context}
    {scrutineeType : TypeSystem.Ty} {cases : List TypedMatchCase} {facts : List BodyFacts}
    {fallback : Option (List StatementId)} {value : Dynamic.Value} {body : List StatementId}
    {bindings : List (TypedBinder × Dynamic.Value)} (request : Request)
    (sameBody : request.statements = body)
    (typed : MatchCasesHaveType source control parent scrutineeType cases facts)
    (selected : Dynamic.MatchCasesSelect parent value cases fallback (.arm body bindings))
    (extended : BindersExtend source.owner parent (bindings.map Prod.fst) armContext) :
    ContextFor source parent scrutineeType cases fallback request armContext := by
  obtain ⟨context, _, _, selectedContext, sameExtension, _, _⟩ :=
    ContextFor.selected_arm request sameBody typed selected
  exact binder_context_unique sameExtension extended ▸ selectedContext

theorem ContextFor.closed_fields
    {source : TypedSource} {parent child : SourceSemantics.Context}
    {scrutineeType : TypeSystem.Ty} {cases : List TypedMatchCase}
    {fallback : Option (List StatementId)} {request : Request}
    (selected : ContextFor source parent scrutineeType cases fallback request child) :
    child.signatures = parent.signatures ∧ child.typeVariables = parent.typeVariables ∧
      child.residualTypeVariables = parent.residualTypeVariables := by
  cases selected with
  | arm _ _ patternTyped extended =>
    clear patternTyped
    induction extended with
    | nil => exact ⟨rfl, rfl, rfl⟩
    | cons head tail ih => cases head; exact ih
  | default => exact ⟨rfl, rfl, rfl⟩

end Solcore.SourceSemantics.CoreLowering.GenericMatchChildren
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.GenericMatchScopedContexts
/-! Finite match requests retain their ordered source binder identities.
The source context still comes from independent pattern typing and lexical
extension. Scope identity transports source declaration lookup only; no native
payload typing or runtime execution follows from the identity list. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.GenericMatchChildren
open Core Frontend SourceInference
open SourceCoreCompatibleDataMatches

/-- Refines the source-only context relation by the actual child's scope IDs.
The hidden scope includes the scrutinee slot and the outer lexical scope. -/
inductive ScopedContextFor (source : TypedSource) (parent : SourceSemantics.Context)
    (hiddenIds : List Resolved.LocalId) (scrutineeType : TypeSystem.Ty)
    (cases : List TypedMatchCase) (fallback : Option (List StatementId))
    (request : Request) : SourceSemantics.Context → Prop where
  | arm {arm binders arity context}
      (member : arm ∈ cases) (statements : request.statements = arm.body)
      (patternTyped : TypedMatchPatternHasType parent arm.pattern scrutineeType binders arity)
      (extended : BindersExtend source.owner parent binders context)
      (scopeIds : request.scope.map Prod.fst = (binders.map (·.id)).reverse ++ hiddenIds) :
      ScopedContextFor source parent hiddenIds scrutineeType cases fallback request context
  | default (statements : fallback = some request.statements)
      (scopeIds : request.scope.map Prod.fst = hiddenIds) :
      ScopedContextFor source parent hiddenIds scrutineeType cases fallback request parent

theorem ScopedContextFor.forget
    {source : TypedSource} {parent child : SourceSemantics.Context}
    {hiddenIds : List Resolved.LocalId} {scrutineeType : TypeSystem.Ty}
    {cases : List TypedMatchCase} {fallback : Option (List StatementId)} {request : Request}
    (related : ScopedContextFor source parent hiddenIds scrutineeType cases fallback request child) :
    ContextFor source parent scrutineeType cases fallback request child := by
  cases related with
  | arm member statements typed extended _ => exact .arm member statements typed extended
  | default statements _ => exact .default statements

theorem ScopedContextFor.closed_fields
    {source : TypedSource} {parent child : SourceSemantics.Context}
    {hiddenIds : List Resolved.LocalId} {scrutineeType : TypeSystem.Ty}
    {cases : List TypedMatchCase} {fallback : Option (List StatementId)} {request : Request}
    (related : ScopedContextFor source parent hiddenIds scrutineeType cases fallback request child) :
    child.signatures = parent.signatures ∧ child.typeVariables = parent.typeVariables ∧
      child.residualTypeVariables = parent.residualTypeVariables :=
  related.forget.closed_fields

/-- Real marked arm allocation prepends the reversed ordered binder IDs. -/
theorem scope_binder_ids (bindings : List (TypedBinder × Ty)) (scope : Scope) :
    (bindings.foldl (fun scope binding => (binding.1.id, binding.2) :: scope) scope).map Prod.fst =
      (bindings.map (fun binding => binding.1.id)).reverse ++ scope.map Prod.fst := by
  induction bindings generalizing scope with
  | nil => rfl
  | cons binding rest ih =>
    rw [List.foldl_cons, ih]
    simp only [List.map_cons, List.reverse_cons, List.append_assoc, List.singleton_append]

/-- An actual compiled arm supplies the refined request at its real scope.
The full source binders are authenticated before retaining their IDs. -/
theorem ScopedContextFor.compiled_arm
    {compilation : CompatiblePatternCertificates.Compilation} {source : TypedSource}
    {parent child : SourceSemantics.Context} {scope : Scope} {site : StatementId}
    {scrutineeType : TypeSystem.Ty} {cases : List TypedMatchCase}
    {fallback : Option (List StatementId)} {arm : TypedMatchCase} {pattern : Pattern}
    {binders : List TypedBinder} {arity : Nat} (body : Expr)
    (member : arm ∈ cases)
    (certificate : CompatiblePatternCertificates.Certificate compilation source scope site arm.span
      scrutineeType arm.pattern pattern)
    (signatures : parent.signatures = compilation.signatures)
    (typed : TypedMatchPatternHasType parent arm.pattern scrutineeType binders arity)
    (extended : BindersExtend source.owner parent binders child) :
    ScopedContextFor source parent (scope.map Prod.fst) scrutineeType cases fallback
      ⟨CompatibleMatchCertificates.armScope scope pattern, arm.body, body⟩ child := by
  apply ScopedContextFor.arm member rfl typed extended
  rw [CompatibleMatchCertificates.armScope, scope_binder_ids]
  have ids := congrArg (List.map TypedBinder.id)
    (CompatiblePatternSourceBinders.Certificate.source_binders certificate signatures typed)
  simp only [List.map_map, Function.comp_def] at ids
  rw [ids]

/-- Native payload annotations may vary; the source declaration relation only
uses the ordered IDs. The hidden ID's source freshness remains explicit. -/
theorem ScopedContextFor.source_declarations
    {source : TypedSource} {parent child : SourceSemantics.Context} {scope : Scope}
    {site : StatementId} {node : StatementNode} {resolution : MatchResolution}
    {scrutineeType : TypeSystem.Ty} {request : Request}
    (found : source.lookupStatement? site = some node) (form : node.form = .matchWith resolution)
    (hidden : resolution.hiddenScrutinee ∉ (SourceCoreDataPlaces.declaredBinders source).map (·.id))
    (declarations : CompatibleExpressionReads.ScopeDeclarations source scope parent)
    (related : ScopedContextFor source parent (resolution.hiddenScrutinee :: scope.map Prod.fst)
      scrutineeType resolution.cases resolution.defaultBody request child) :
    CompatibleExpressionReads.ScopeDeclarations source request.scope child := by
  have hiddenDeclarations := CompatibleMatchArmScopes.scope_internal .unit hidden declarations
  cases related with
  | @arm arm binders arity context member statements typed extended sameIds =>
    let bindings : List (TypedBinder × Ty) := binders.map (fun binder => (binder, .unit))
    have sameBinders : bindings.map Prod.fst = binders := by simp [bindings, Function.comp_def]
    have members : ∀ binder ∈ bindings.map Prod.fst,
        binder ∈ SourceCoreDataPlaces.declaredBinders source := by
      rw [sameBinders]
      exact CompatibleMatchArmScopes.pattern_declarations found form member typed
    have bound := CompatibleMatchArmScopes.scope_binders (bindings := bindings)
      hiddenDeclarations members (sameBinders.symm ▸ extended)
    apply CompatibleMatchArmScopes.scope_ids (declarations := bound)
    rw [scope_binder_ids, sameIds]
    simp [bindings, List.map_map]
  | default statements sameIds =>
    exact CompatibleMatchArmScopes.scope_ids
      (first := (resolution.hiddenScrutinee, .unit) :: scope) sameIds.symm hiddenDeclarations

/-- Independent source selection supplies the arm context. The scope equation
comes separately from the actual selected allocation, not from a native type. -/
theorem ScopedContextFor.selected_arm
    {source : TypedSource} {control : ControlContext} {parent : SourceSemantics.Context}
    {hiddenIds : List Resolved.LocalId} {scrutineeType : TypeSystem.Ty}
    {cases : List TypedMatchCase} {facts : List BodyFacts} {fallback : Option (List StatementId)}
    {value : Dynamic.Value} {body : List StatementId} {bindings : List (TypedBinder × Dynamic.Value)}
    (request : Request) (sameBody : request.statements = body)
    (sameIds : request.scope.map Prod.fst = (bindings.map (fun binding => binding.1.id)).reverse ++ hiddenIds)
    (typed : MatchCasesHaveType source control parent scrutineeType cases facts)
    (selected : Dynamic.MatchCasesSelect parent value cases fallback (.arm body bindings)) :
    ∃ context finalContext bodyFacts,
      ScopedContextFor source parent hiddenIds scrutineeType cases fallback request context ∧
      BindersExtend source.owner parent (bindings.map Prod.fst) context ∧
      StatementsHaveType source control context body finalContext bodyFacts ∧ bodyFacts ∈ facts := by
  cases selected with
  | head matched =>
    cases typed with
    | cons head tail =>
      cases head with
      | intro patternTyped extended bodyTyped =>
        have binders := DataMatchSourceScopes.PatternMatches.binders patternTyped matched
        have ids := congrArg (fun xs => (xs.map TypedBinder.id).reverse ++ hiddenIds) binders
        simp only [List.map_map, Function.comp_def] at ids
        have ids := sameIds.trans ids
        exact ⟨_, _, _, .arm List.mem_cons_self sameBody patternTyped extended ids,
          binders ▸ extended, bodyTyped, List.mem_cons_self⟩
  | @tail arm rest _ _ notMatched selected =>
    cases typed with
    | cons head tail =>
      obtain ⟨context, finalContext, bodyFacts, child, extended, bodyTyped, member⟩ :=
        ScopedContextFor.selected_arm request sameBody sameIds tail selected
      have lifted : ScopedContextFor source parent hiddenIds scrutineeType (arm :: rest) fallback request context := by
        cases child with
        | arm member same typed extended ids => exact .arm (List.mem_cons_of_mem _ member) same typed extended ids
        | default same ids => exact .default same ids
      exact ⟨context, finalContext, bodyFacts, lifted, extended, bodyTyped, List.mem_cons_of_mem _ member⟩
termination_by cases.length

theorem ScopedContextFor.selected_arm_at
    {source : TypedSource} {control : ControlContext} {parent armContext : SourceSemantics.Context}
    {hiddenIds : List Resolved.LocalId} {scrutineeType : TypeSystem.Ty}
    {cases : List TypedMatchCase} {facts : List BodyFacts} {fallback : Option (List StatementId)}
    {value : Dynamic.Value} {body : List StatementId} {bindings : List (TypedBinder × Dynamic.Value)}
    (request : Request) (sameBody : request.statements = body)
    (sameIds : request.scope.map Prod.fst = (bindings.map (fun binding => binding.1.id)).reverse ++ hiddenIds)
    (typed : MatchCasesHaveType source control parent scrutineeType cases facts)
    (selected : Dynamic.MatchCasesSelect parent value cases fallback (.arm body bindings))
    (extended : BindersExtend source.owner parent (bindings.map Prod.fst) armContext) :
    ScopedContextFor source parent hiddenIds scrutineeType cases fallback request armContext := by
  obtain ⟨context, _, _, related, sameExtension, _, _⟩ :=
    ScopedContextFor.selected_arm request sameBody sameIds typed selected
  exact binder_context_unique sameExtension extended ▸ related

theorem selected_arm_ids
    {bodyCertificate : CompatibleMatchCertificates.BodyCertificate} {scope finalScope : Scope}
    {environment finalEnvironment : Dynamic.Environment} {heap finalHeap : Dynamic.Heap}
    {type : Ty} {statements : List StatementId} {bindings : List (TypedBinder × Dynamic.Value)} {body : Expr}
    (selected : DataMatchBranchPrefix.SelectedBody bodyCertificate scope environment heap type
      (.arm statements bindings) finalScope finalEnvironment finalHeap body) :
    finalScope.map Prod.fst = (bindings.map (fun binding => binding.1.id)).reverse ++ scope.map Prod.fst := by
  cases selected with
  | arm binders allocated certified =>
    rw [scope_binder_ids]
    have ids := congrArg (List.map TypedBinder.id) binders
    simp only [List.map_map, Function.comp_def] at ids
    rw [ids]

theorem selected_default_ids
    {bodyCertificate : CompatibleMatchCertificates.BodyCertificate} {scope finalScope : Scope}
    {environment finalEnvironment : Dynamic.Environment} {heap finalHeap : Dynamic.Heap}
    {type : Ty} {statements : List StatementId} {body : Expr}
    (selected : DataMatchBranchPrefix.SelectedBody bodyCertificate scope environment heap type
      (.default statements) finalScope finalEnvironment finalHeap body) :
    finalScope.map Prod.fst = scope.map Prod.fst := by
  cases selected
  rfl

private theorem instruction_ids (instructions : List MatchPatternInstruction) :
    (SourceCoreDataPlaces.instructionBinders instructions).map (·.id) =
      MatchPatternInstruction.binderIds instructions := by
  induction instructions with
  | nil => rfl
  | cons instruction rest ih =>
    cases instruction <;> simp [SourceCoreDataPlaces.instructionBinders, MatchPatternInstruction.binderIds] at ih ⊢ <;> exact ih

theorem typed_binder_ids {context : SourceSemantics.Context} {pattern : TypedMatchPattern}
    {type : TypeSystem.Ty} {binders : List TypedBinder} {arity : Nat}
    (typed : TypedMatchPatternHasType context pattern type binders arity) :
    binders.map (·.id) = pattern.binderIds := by
  rw [← CompatiblePatternSourceBinders.pattern_binders typed]
  cases resolution : pattern.resolution <;>
    simp only [SourceCoreDataPlaces.patternBinders, TypedMatchPattern.binderIds, resolution]
  all_goals try rfl
  all_goals exact instruction_ids _

theorem ScopedContextFor.compiled_arm_ids
    {compilation : CompatiblePatternCertificates.Compilation} {source : TypedSource}
    {parent child : SourceSemantics.Context} {scope : Scope} {site : StatementId}
    {scrutineeType : TypeSystem.Ty} {cases : List TypedMatchCase}
    {fallback : Option (List StatementId)} {arm : TypedMatchCase} {pattern : Pattern}
    {binders : List TypedBinder} {arity : Nat} (body : Expr)
    (member : arm ∈ cases)
    (certificate : CompatiblePatternCertificates.Certificate compilation source scope site arm.span
      scrutineeType arm.pattern pattern)
    (typed : TypedMatchPatternHasType parent arm.pattern scrutineeType binders arity)
    (extended : BindersExtend source.owner parent binders child) :
    ScopedContextFor source parent (scope.map Prod.fst) scrutineeType cases fallback
      ⟨CompatibleMatchCertificates.armScope scope pattern, arm.body, body⟩ child := by
  apply ScopedContextFor.arm member rfl typed extended
  rw [CompatibleMatchCertificates.armScope, scope_binder_ids,
    CompatibleMatchSelectionPrefix.certificate_binding_ids certificate, ← typed_binder_ids typed]

end Solcore.SourceSemantics.CoreLowering.GenericMatchChildren
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.GenericProjectedBitNotPreparedOrigins
/-! The unary head's preparation is tied to its exact layout site. Diagnostic
laws refer only to genuine reached missing/default and uninitialized phases. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleProjectedBitNotStatements
open Core Frontend SourceInference GeneralHeap CompatiblePayload
open SourceCoreCompatibleDataPlaces ProtectedPlaceReachedDiagnostics
universe u v
variable {values : ValuesContext} {source : TypedSource} {context : SourceSemantics.Context}
  {certificate : GenericExpressionMeaning.Certificate} {scope : Scope} {administrative : Core.Context}
  {definitions : DataEnvironment} {assignment : AssignmentResolution}

inductive Head.PreparedAt
    (head : Head values source context certificate scope administrative definitions assignment)
    (site : SourceCoreElaboration.ErrorSite) (fuel : Nat) (invalidProjection : Word)
    (missing : TypeSystem.Ty → Word) : Prop where
  | intro (siteEq : head.site = site) (route : Route)
      (described : describe values values.checked.signatures source site assignment = .ok route)
      (preparedBy : prepare values fuel route invalidProjection missing = .ok head.prepared) :
      head.PreparedAt site fuel invalidProjection missing

structure Head.ReachedErrors
    {ambient : AmbientDefinitions values.checked.catalog.definitions}
    (functions : FunctionModel values.checked.catalog ambient)
    {Records : Type v} (protocol : ProtectedStateTransition.Protocol.{u, v} Records)
    (head : Head values source context certificate scope administrative ambient.definitions assignment)
    (environment : Dynamic.Environment) {initialIndex : ProtectedStateTransition.Index}
    (initial : protocol.State initialIndex) (faults : FunctionCalls.FaultRep)
    {registry : SourceCoreRawMetadata.Registry} : Prop where
  missing : MissingFor values.checked registry functions protocol source head.site assignment.target
    head.prepared head.leaf initial faults
  uninitialized : UninitializedFor values.checked registry functions protocol environment assignment.target
    head.prepared initial faults

end Solcore.SourceSemantics.CoreLowering.CompatibleProjectedBitNotStatements
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.GenericMatchPreservation
/-! Forward finite match correspondence. Child obligations quantify over all
related initial states and finite independent child executions; no evaluator or
termination assumption is introduced. Source allocation determinism identifies
the cells built by the certified Core prefix with the given source trace. -/

set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.GenericMatchPreservation
open Core Frontend Frontend.SourceInference GeneralHeap CoreProof ReadOnly
open SourceCoreDataMatches DataMatchCertificates DataMatchBranchPrefix GenericMatchAllocation
open GenericMatchMeaning GenericLexicalContext

/-- Universal child expression preservation, including fault effects. -/
def ExpressionPreserves (compilation : DataPatternCertificates.Compilation)
    (model : GenericHeap.PayloadModel compilation.checked.catalog) (program : Program)
    (context : SourceSemantics.Context) (evidence : Dynamic.EvidenceEnvironment) (source : TypedSource)
    (certificate : ExpressionCertificate) (faults : FaultRep) : Prop :=
  ∀ {scope id lowered}, certificate scope id lowered →
  ∀ {node}, source.lookupExpression? id = some node →
  ∀ {mapping world administrativeContext environment canonical actual before store ξ outcome after},
    DataHeap.EnvRepresents compilation.checked.catalog mapping world administrativeContext scope environment canonical →
    GenericHeap.HeapRepresents model mapping world before store →
    Dynamic.EnvironmentAgrees before context.locals environment →
    EnvironmentsAgree ξ canonical actual →
    Dynamic.ExpressionEvaluatesOutcome program context evidence source environment before id outcome after →
    ∃ value finalStore finalMap finalWorld,
      Evaluates actual store (lowered.expression.rename ξ) value finalStore ∧
      ExpressionOutcomeRepresents compilation.checked.catalog compilation.signatures node.type lowered.type faults outcome value ∧
      GenericHeap.HeapRepresents model finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after

/-- Universal child statement preservation. Independent source static typing
supplies the selected lexical context; source execution supplies finiteness. -/
def BodyPreserves (compilation : DataPatternCertificates.Compilation)
    (model : GenericHeap.PayloadModel compilation.checked.catalog) (program : Program)
    (control : ControlContext) (evidence : Dynamic.EvidenceEnvironment) (source : TypedSource)
    (certificate : BodyCertificate) (resultSource : TypeSystem.Ty) (resultType : Ty) (faults : FaultRep) : Prop :=
  ∀ {scope statements code}, certificate scope statements code →
  ∀ {context staticFinal facts}, StatementsHaveType source control context statements staticFinal facts →
  ∀ {mapping world administrativeContext environment canonical actual before store ξ finalContext outcome after},
    DataHeap.EnvRepresents compilation.checked.catalog mapping world administrativeContext scope environment canonical →
    GenericHeap.HeapRepresents model mapping world before store →
    Dynamic.EnvironmentAgrees before context.locals environment →
    EnvironmentsAgree ξ canonical actual →
    Dynamic.StatementsExecuteOutcome program context evidence source environment before statements finalContext outcome after →
    ∃ value finalStore finalMap finalWorld,
      Evaluates actual store (code.rename ξ) value finalStore ∧
      OutcomeRepresents model finalMap finalWorld resultSource resultType faults outcome value ∧
      GenericHeap.HeapRepresents model finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after

private theorem allocations_same {before left right : Dynamic.Heap} {type : TypeSystem.Ty} {value : Option Dynamic.Value}
    {a b : Dynamic.Location} (first : Dynamic.Heap.Allocates before type value a left)
    (second : Dynamic.Heap.Allocates before type value b right) : left = right := by
  cases first; cases second; rfl

private theorem binders_same {environment a b : Dynamic.Environment} {before left right : Dynamic.Heap}
    {binders : List TypedBinder} {values : List Dynamic.Value}
    (first : Dynamic.BindersAllocate environment before binders values a left)
    (second : Dynamic.BindersAllocate environment before binders values b right) : a = b ∧ left = right := by
  induction first generalizing b right with
  | nil => cases second; exact ⟨rfl, rfl⟩
  | cons allocation rest ih =>
    cases second with
    | cons allocation' rest' =>
      cases allocation
      cases allocation'
      exact ih rest'

private theorem extensions_same {owner : Resolved.DeclarationId} {context a b : SourceSemantics.Context}
    {binders : List TypedBinder} (first : BindersExtend owner context binders a)
    (second : BindersExtend owner context binders b) : a = b := by
  induction first generalizing b with
  | nil => cases second; rfl
  | cons head tail ih =>
    cases second with
    | cons head' tail' =>
      cases head
      cases head'
      exact ih tail'

private theorem default_selected {context : SourceSemantics.Context} {value : Dynamic.Value}
    {cases : List TypedMatchCase} {fallback : Option (List StatementId)} {statements : List StatementId}
    (selected : Dynamic.MatchCasesSelect context value cases fallback (.default statements)) :
    fallback = some statements := by
  cases selected with
  | default => rfl
  | tail _ next => exact default_selected next
termination_by cases.length
decreasing_by simp_all

/-- A finite independent source match trace yields a finite evaluation of the
actual emitted match code. The source and Core allocate at their own lengths;
the final location map, world and administrative frame remain explicit. -/
theorem Certificate.preserves_trace
    {compilation : DataPatternCertificates.Compilation} {model : GenericHeap.PayloadModel compilation.checked.catalog}
    (includes : IncludesFinite compilation.signatures model)
    {program : Program} {context : SourceSemantics.Context} {control : ControlContext}
    {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource} {scope : Scope}
    {id : StatementId} {resolution : MatchResolution} {resultSource : TypeSystem.Ty} {resultType : Ty}
    {internalReason : Word} {expressionCertificate : ExpressionCertificate} {bodyCertificate : BodyCertificate}
    {faults : FaultRep} {code : Expr}
    (certificate : DataMatchCertificates.Certificate compilation source scope id resolution resultType internalReason
      expressionCertificate bodyCertificate code)
    (expressionMeaning : ExpressionPreserves compilation model program context evidence source expressionCertificate faults)
    (bodyMeaning : BodyPreserves compilation model program control evidence source bodyCertificate resultSource resultType faults)
    (valid : DataPatternLeaves.ContextValid compilation context) (unique : NodeOccurrencesUnique source)
    {scrutineeNode : ExpressionNode} (found : source.lookupExpression? resolution.scrutinee = some scrutineeNode)
    {caseFacts : List BodyFacts}
    (casesTyped : MatchCasesHaveType source control context scrutineeNode.type resolution.cases caseFacts)
    (defaultTyped : ∀ {statements}, resolution.defaultBody = some statements →
      ∃ finalContext facts, StatementsHaveType source control context statements finalContext facts)
    {mapping : LocationMap} {world : StoreTyping} {administrativeContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before after : Dynamic.Heap}
    {store : Store} {ξ : Renaming} {outcome : Dynamic.ControlOutcome}
    (environments : DataHeap.EnvRepresents compilation.checked.catalog mapping world administrativeContext scope environment canonical)
    (heaps : GenericHeap.HeapRepresents model mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (layout : EnvironmentsAgree ξ canonical actual)
    (trace : DataMatchSourceTrace.Trace program context evidence source environment before resolution outcome after) :
    ∃ value finalStore finalMap finalWorld,
      Evaluates actual store (code.rename ξ) value finalStore ∧
      OutcomeRepresents model finalMap finalWorld resultSource resultType faults outcome value ∧
      GenericHeap.HeapRepresents model finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after := by
  cases certificate with
  | @matchWith node statementType certifiedNode payload computation arms fallback read allowed form requirements
      hiddenOwned hiddenFresh scrutineeOwned scrutineeFound projection expression sameType armsCertified fallbackCertified =>
    have same := Option.some.inj (found.symm.trans scrutineeFound)
    subst certifiedNode
    cases trace with
    | scrutineeFault fault =>
      obtain ⟨value, finalStore, finalMap, finalWorld, coreEval, related, heapRep, maps, worlds, frame, metadata⟩ :=
        expressionMeaning expression found environments heaps locals layout (.fault fault)
      cases related with
      | fault represented =>
        refine ⟨_, finalStore, finalMap, finalWorld, ?_, .fault represented, heapRep, maps, worlds, frame, metadata⟩
        rw [LoopRenaming.letInitialized]
        exact LocalSequence.letInitialized_failure _ _ (by simpa only [← sameType] using coreEval)
    | patternFault contains evaluated allocated fault =>
      exact False.elim (GenericMatchSelection.Arms.not_pattern_fault armsCertified valid _ fault)
    | @arm sourceNode sourceValue middle hidden location statements bindings armContext armEnvironment bound
        innerFinal innerOutcome sourceAfter contains sourceEval sourceHidden selected sourceExtended sourceAllocated sourceBody =>
      have nodeEq : sourceNode = scrutineeNode := Option.some.inj
        ((lookupExpression?_complete unique contains).symm.trans found)
      subst sourceNode
      obtain ⟨value, middleStore, middleMap, middleWorld, coreEval, represented, middleRelated,
        firstMaps, firstWorlds, firstFrame, firstMetadata⟩ :=
        expressionMeaning expression found environments heaps locals layout (.value sourceEval)
      cases represented with
      | value represented =>
        obtain ⟨hiddenHeap, hiddenLocation, finalScope, selectedEnvironment, selectedHeap, selectedCanonical,
          selectedActual, selectedStore, selectedMap, selectedWorld, selectedEmbedding, body,
          hiddenAllocated, selectedAgain, selectedBody, selectedEnv, selectedRelated, secondMaps, secondWorlds,
          secondFrame, selectedLayout, agreement⟩ :=
          GenericMatchSelectedPrefix.selected_prefix includes hiddenFresh (DataPatternBindings.projected_raw projection)
            armsCertified fallbackCertified valid represented (environments.extend firstMaps firstWorlds)
            middleRelated layout coreEval selected
        have hiddenEq := allocations_same hiddenAllocated sourceHidden
        subst hiddenHeap
        cases selectedBody with
        | arm binders allocated bodyCertified =>
          obtain ⟨sameEnvironment, sameHeap⟩ := binders_same allocated sourceAllocated
          subst selectedEnvironment
          subst selectedHeap
          obtain ⟨staticContext, staticFinal, facts, extended, typed, _⟩ :=
            DataMatchSourceScopes.MatchCasesSelect.arm_scope casesTyped selected
          have sameContext := extensions_same extended sourceExtended
          subst staticContext
          obtain ⟨result, finalStore, finalMap, finalWorld, bodyEval, related, finalHeapRep,
            thirdMaps, thirdWorlds, thirdFrame, thirdMetadata⟩ :=
            bodyMeaning bodyCertified typed selectedEnv selectedRelated
              (binders_agree sourceExtended (arm_monomorphic casesTyped selected)
                (locals.mono (firstMetadata.trans (.of_allocation sourceHidden))) sourceAllocated)
              selectedLayout sourceBody
          exact ⟨result, finalStore, finalMap, finalWorld, agreement.wrap bodyEval, related.restore environment,
            finalHeapRep, firstMaps.trans (secondMaps.trans thirdMaps), firstWorlds.trans (secondWorlds.trans thirdWorlds),
            firstFrame.trans (secondFrame.trans thirdFrame),
            firstMetadata.trans ((Dynamic.HeapMetadataExtend.of_allocation sourceHidden).trans
              ((binders_metadata sourceAllocated).trans thirdMetadata))⟩
    | @default sourceNode sourceValue middle hidden location statements innerFinal innerOutcome sourceAfter
        contains sourceEval sourceHidden selected sourceBody =>
      have nodeEq : sourceNode = scrutineeNode := Option.some.inj
        ((lookupExpression?_complete unique contains).symm.trans found)
      subst sourceNode
      obtain ⟨value, middleStore, middleMap, middleWorld, coreEval, represented, middleRelated,
        firstMaps, firstWorlds, firstFrame, firstMetadata⟩ :=
        expressionMeaning expression found environments heaps locals layout (.value sourceEval)
      cases represented with
      | value represented =>
        obtain ⟨hiddenHeap, hiddenLocation, finalScope, selectedEnvironment, selectedHeap, selectedCanonical,
          selectedActual, selectedStore, selectedMap, selectedWorld, selectedEmbedding, body,
          hiddenAllocated, selectedAgain, selectedBody, selectedEnv, selectedRelated, secondMaps, secondWorlds,
          secondFrame, selectedLayout, agreement⟩ :=
          GenericMatchSelectedPrefix.selected_prefix includes hiddenFresh (DataPatternBindings.projected_raw projection)
            armsCertified fallbackCertified valid represented (environments.extend firstMaps firstWorlds)
            middleRelated layout coreEval selected
        have hiddenEq := allocations_same hiddenAllocated sourceHidden
        subst hiddenHeap
        cases selectedBody with
        | default bodyCertified =>
          obtain ⟨staticFinal, facts, typed⟩ := defaultTyped (default_selected selected)
          obtain ⟨result, finalStore, finalMap, finalWorld, bodyEval, related, finalHeapRep,
            thirdMaps, thirdWorlds, thirdFrame, thirdMetadata⟩ :=
            bodyMeaning bodyCertified typed selectedEnv selectedRelated
              (locals.mono (firstMetadata.trans (.of_allocation sourceHidden))) selectedLayout sourceBody
          exact ⟨result, finalStore, finalMap, finalWorld, agreement.wrap bodyEval, related.restore environment,
            finalHeapRep, firstMaps.trans (secondMaps.trans thirdMaps), firstWorlds.trans (secondWorlds.trans thirdWorlds),
            firstFrame.trans (secondFrame.trans thirdFrame),
            firstMetadata.trans ((Dynamic.HeapMetadataExtend.of_allocation sourceHidden).trans thirdMetadata)⟩
    | @noBranch sourceNode sourceValue middle hidden location contains sourceEval sourceHidden selected =>
      have nodeEq : sourceNode = scrutineeNode := Option.some.inj
        ((lookupExpression?_complete unique contains).symm.trans found)
      subst sourceNode
      obtain ⟨value, middleStore, middleMap, middleWorld, coreEval, represented, middleRelated,
        firstMaps, firstWorlds, firstFrame, firstMetadata⟩ :=
        expressionMeaning expression found environments heaps locals layout (.value sourceEval)
      cases represented with
      | value represented =>
        obtain ⟨hiddenHeap, hiddenLocation, finalScope, selectedEnvironment, selectedHeap, selectedCanonical,
          selectedActual, selectedStore, selectedMap, selectedWorld, selectedEmbedding, body,
          hiddenAllocated, selectedAgain, selectedBody, selectedEnv, selectedRelated, secondMaps, secondWorlds,
          secondFrame, selectedLayout, agreement⟩ :=
          GenericMatchSelectedPrefix.selected_prefix includes hiddenFresh (DataPatternBindings.projected_raw projection)
            armsCertified fallbackCertified valid represented (environments.extend firstMaps firstWorlds)
            middleRelated layout coreEval selected
        have hiddenEq := allocations_same hiddenAllocated sourceHidden
        subst hiddenHeap
        cases selectedBody
        exact ⟨_, selectedStore, selectedMap, selectedWorld, agreement.wrap (.inRight (.inLeft (.inLeft .unit))),
          .fallthrough environment, selectedRelated, firstMaps.trans secondMaps, firstWorlds.trans secondWorlds,
          firstFrame.trans secondFrame, firstMetadata.trans (.of_allocation sourceHidden)⟩

private theorem read_contains {checked : SourceCoreDataCatalog.Checked} {source : TypedSource} {id : StatementId}
    {node : StatementNode} {type : Ty}
    (read : SourceCoreGeneralTypes.readStatement checked source id = .ok (node, type)) : ContainsStatement source id node := by
  by_cases owned : id.occurrence.owner = source.owner
  · simp only [SourceCoreGeneralTypes.readStatement, owned, ne_eq, not_true_eq_false, ↓reduceIte,
      pure, Except.pure, bind, Except.bind] at read
    cases found : source.lookupStatement? id with
    | none => simp [found] at read
    | some selected =>
      simp only [found] at read
      cases projected : SourceCoreGeneralTypes.projectType checked (.occurrence id.occurrence) selected.type with
      | error => simp [projected] at read
      | ok projectedType =>
        simp only [projected, Except.ok.injEq, Prod.mk.injEq] at read
        rcases read with ⟨rfl, rfl⟩
        exact lookupStatement?_sound found
  · simp [SourceCoreGeneralTypes.readStatement, owned, bind, Except.bind] at read


/-- The independent statement-outcome judgment supplies the finite trace;
its view is derived using occurrence uniqueness rather than assumed. -/
theorem Certificate.preserves
    {compilation : DataPatternCertificates.Compilation} {model : GenericHeap.PayloadModel compilation.checked.catalog}
    (includes : IncludesFinite compilation.signatures model)
    {program : Program} {context : SourceSemantics.Context} {control : ControlContext}
    {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource} {scope : Scope}
    {id : StatementId} {resolution : MatchResolution} {resultSource : TypeSystem.Ty} {resultType : Ty}
    {internalReason : Word} {expressionCertificate : ExpressionCertificate} {bodyCertificate : BodyCertificate}
    {faults : FaultRep} {code : Expr}
    (certificate : DataMatchCertificates.Certificate compilation source scope id resolution resultType internalReason
      expressionCertificate bodyCertificate code)
    (expressionMeaning : ExpressionPreserves compilation model program context evidence source expressionCertificate faults)
    (bodyMeaning : BodyPreserves compilation model program control evidence source bodyCertificate resultSource resultType faults)
    (valid : DataPatternLeaves.ContextValid compilation context) (unique : NodeOccurrencesUnique source)
    {scrutineeNode : ExpressionNode} (found : source.lookupExpression? resolution.scrutinee = some scrutineeNode)
    {caseFacts : List BodyFacts}
    (casesTyped : MatchCasesHaveType source control context scrutineeNode.type resolution.cases caseFacts)
    (defaultTyped : ∀ {statements}, resolution.defaultBody = some statements →
      ∃ finalContext facts, StatementsHaveType source control context statements finalContext facts)
    {mapping : LocationMap} {world : StoreTyping} {administrativeContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before after : Dynamic.Heap}
    {store : Store} {ξ : Renaming} {outcome : Dynamic.ControlOutcome} {finalContext : SourceSemantics.Context}
    (environments : DataHeap.EnvRepresents compilation.checked.catalog mapping world administrativeContext scope environment canonical)
    (heaps : GenericHeap.HeapRepresents model mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (layout : EnvironmentsAgree ξ canonical actual)
    (executed : Dynamic.StatementExecutesOutcome program context evidence source environment before id finalContext outcome after) :
    ∃ value finalStore finalMap finalWorld,
      Evaluates actual store (code.rename ξ) value finalStore ∧
      OutcomeRepresents model finalMap finalWorld resultSource resultType faults outcome value ∧
      GenericHeap.HeapRepresents model finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after := by
  have view : DataMatchSourceTrace.Trace program context evidence source environment before resolution outcome after := by
    cases certificate with
    | matchWith read allowed form => exact (DataMatchSourceTrace.of_outcome unique (read_contains read) form executed).2
  exact Certificate.preserves_trace includes certificate expressionMeaning bodyMeaning valid unique found casesTyped
    defaultTyped environments heaps locals layout view

/-- Actual accepted match lowering preserves each independently finite source
outcome, under explicit universal child compiler correspondence theorems. -/
theorem lowerWithReasons_preserves
    {compilation : DataPatternCertificates.Compilation} {model : GenericHeap.PayloadModel compilation.checked.catalog}
    (includes : IncludesFinite compilation.signatures model)
    {program : Program} {context : SourceSemantics.Context} {control : ControlContext}
    {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource} {scope : Scope}
    {id : StatementId} {resolution : MatchResolution} {resultSource : TypeSystem.Ty} {resultType : Ty}
    {internalReason : Word} {reasonAt : ExpressionId → Word}
    {lowerExpression : ExpressionLowerer} {lowerBody : BodyLowerer} {fuel : Nat}
    {expressionCertificate : ExpressionCertificate} {bodyCertificate : BodyCertificate} {faults : FaultRep} {code : Expr}
    (expressionExtract : ∀ childFuel scope id result,
      lowerExpression childFuel source scope id reasonAt = .ok result → expressionCertificate scope id result)
    (bodyExtract : ∀ childFuel scope statements code,
      lowerBody childFuel source scope statements resultType reasonAt internalReason = .ok code →
      bodyCertificate scope statements code)
    (accepted : lowerWithReasons compilation lowerExpression lowerBody fuel source scope id resolution
      resultType reasonAt internalReason = .ok code)
    (expressionMeaning : ExpressionPreserves compilation model program context evidence source expressionCertificate faults)
    (bodyMeaning : BodyPreserves compilation model program control evidence source bodyCertificate resultSource resultType faults)
    (valid : DataPatternLeaves.ContextValid compilation context) (unique : NodeOccurrencesUnique source)
    {scrutineeNode : ExpressionNode} (found : source.lookupExpression? resolution.scrutinee = some scrutineeNode)
    {caseFacts : List BodyFacts}
    (casesTyped : MatchCasesHaveType source control context scrutineeNode.type resolution.cases caseFacts)
    (defaultTyped : ∀ {statements}, resolution.defaultBody = some statements →
      ∃ finalContext facts, StatementsHaveType source control context statements finalContext facts)
    {mapping : LocationMap} {world : StoreTyping} {administrativeContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before after : Dynamic.Heap}
    {store : Store} {ξ : Renaming} {outcome : Dynamic.ControlOutcome} {finalContext : SourceSemantics.Context}
    (environments : DataHeap.EnvRepresents compilation.checked.catalog mapping world administrativeContext scope environment canonical)
    (heaps : GenericHeap.HeapRepresents model mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (layout : EnvironmentsAgree ξ canonical actual)
    (executed : Dynamic.StatementExecutesOutcome program context evidence source environment before id finalContext outcome after) :
    ∃ value finalStore finalMap finalWorld,
      Evaluates actual store (code.rename ξ) value finalStore ∧
      OutcomeRepresents model finalMap finalWorld resultSource resultType faults outcome value ∧
      GenericHeap.HeapRepresents model finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after :=
  Certificate.preserves includes (certificate_of_lowerWithReasons expressionExtract bodyExtract accepted)
    expressionMeaning bodyMeaning valid unique found casesTyped defaultTyped environments heaps locals layout executed

end Solcore.SourceSemantics.CoreLowering.GenericMatchPreservation
end
