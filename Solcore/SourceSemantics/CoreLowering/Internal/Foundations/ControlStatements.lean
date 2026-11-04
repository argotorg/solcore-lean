import Solcore.SourceSemantics.CoreLowering.Internal.Foundations.BasicStatements
import Solcore.SourceSemantics.Ownership
import Solcore.Frontend.SourceCoreDataPlaces
import Solcore.SourceSemantics.CoreLowering.Internal.Foundations.LambdaViewsAndMarkedCaptures

/-!
# Statement trees and control statements

Tree certificates of basic statements, and the trees, certificates, meaning and bridge of control statements.
-/

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.BasicStatementTreeCertificates
/-! Extract a complete basic statement certificate from successful lowering.

The compiler checks binder ownership, monomorphism, scalar/product types and
freshness in its scope. The additional source-context invariant below supplies
well-formed ambient rigid binders and the identity correspondence needed to
transport freshness into both declarative lexical tables. It does not assume
source typing, a desired statement Tree, or any child evaluation.

This is a runtime correspondence theorem. It does not establish the complete
static SourceHasType judgment or the agreement of ambient local schemes with
the compiler scope. Supported expression coercions are empty, so their raw
types already equal their retained types. -/

set_option autoImplicit false

namespace Solcore.SourceSemantics.CoreLowering.BasicStatements

open Frontend Frontend.SourceInference TypeSystem LocalCell

/-- The source context and compiler scope have the same lexical identity
order, including the qualified-scheme table. Scheme payloads need not be
reconstructed to transport freshness. Runtime values and cell types are
related separately by `GeneralHeap.EnvRepresents` and `HeapRepresents`. -/
structure ScopeContextAligned (scope : SourceCoreLocalCell.Scope) (context : Context) : Prop where
  binders : TypeParameterBindersWellFormed context
  locals : context.locals.map Prod.fst = scope.map Prod.fst
  requirements : context.localSchemeRequirements.map Prod.fst = scope.map Prod.fst

namespace ScopeContextAligned

theorem empty (signatures : ProgramSignatures) :
    ScopeContextAligned [] (Context.ofSignatures signatures) := by
  constructor
  · simp [TypeParameterBindersWellFormed, Context.ofSignatures]
  · rfl
  · rfl

theorem bind {scope : SourceCoreLocalCell.Scope} {context : Context}
    (aligned : ScopeContextAligned scope context) (binder : TypedBinder) (type : Core.Ty) :
    ScopeContextAligned ((binder.id, type) :: scope)
      (context.withLocal binder.id binder.scheme binder.schemeRequirements) := by
  constructor
  · exact aligned.binders
  · simpa [Context.withLocal] using congrArg (List.cons binder.id) aligned.locals
  · simpa [Context.withLocal] using congrArg (List.cons binder.id) aligned.requirements

theorem fresh {scope : SourceCoreLocalCell.Scope} {context : Context} {id : Resolved.LocalId}
    (aligned : ScopeContextAligned scope context)
    (absent : scope.any (fun entry => decide (entry.1 = id)) = false) : LocalFresh context id := by
  have missing : id ∉ scope.map Prod.fst := by
    intro member
    obtain ⟨entry, member, equal⟩ := List.mem_map.mp member
    have present : scope.any (fun entry => decide (entry.1 = id)) = true := by
      apply List.any_eq_true.mpr
      exact ⟨entry, member, by simpa using equal⟩
    rw [absent] at present
    contradiction
  exact ⟨by simpa [aligned.locals] using missing,
    by simpa [aligned.requirements] using missing⟩

end ScopeContextAligned

theorem BinderCertificate.extends
    {source : TypedSource} {scope : SourceCoreLocalCell.Scope} {context : Context}
    {binder : TypedBinder} {type : Core.Ty}
    (certificate : BinderCertificate source scope binder type)
    (aligned : ScopeContextAligned scope context) :
    BinderExtends source.owner context binder
      (context.withLocal binder.id binder.scheme binder.schemeRequirements) := by
  have sourceScoped : ∀ {sourceType : Ty} {coreType : Core.Ty},
      TypeRepresents sourceType coreType → ∀ variables, TypeWellScoped context variables sourceType := by
    intro sourceType coreType types variables
    induction types with
    | unit => exact .builtin .unit
    | bool => exact .builtin .bool
    | word => exact .builtin .word
    | product _ _ left right => exact .product left right
  exact .intro {
    owned := certificate.owned
    scheme := {
      binders := aligned.binders
      quantified_nodup := by simp [certificate.monomorphic]
      body := sourceScoped certificate.types _
    }
    quantified_fresh := by simp [SchemeQuantifiersFresh, certificate.monomorphic]
    monomorphic_requirements_empty := fun _ => certificate.requirements
  } (aligned.fresh certificate.fresh)

private theorem bind_ok {α β ε : Type} {computation : Except ε α} {next : α → Except ε β}
    {result : β} (accepted : computation >>= next = .ok result) :
    ∃ value, computation = .ok value ∧ next value = .ok result := by
  cases computation with
  | error => cases accepted
  | ok value => exact ⟨value, rfl, accepted⟩

private theorem ensureType_ok
    {site : SourceCoreElaboration.ErrorSite} {expected actual : Core.Ty}
    (accepted : SourceCoreBasic.ensureType site expected actual = .ok ()) : expected = actual := by
  unfold SourceCoreBasic.ensureType at accepted
  split at accepted
  · assumption
  · cases accepted

/-- Every actually accepted basic statement list has a structural certificate.
Explicit returns need no facts about the unreachable remainder. Extraction is
bounded by the same traversal fuel and has no evaluation premises. -/
theorem tree_of_lowerStatements
    {fuel : Nat} {source : TypedSource} {scope : SourceCoreLocalCell.Scope}
    {context : Context} {statements : List StatementId} {resultType : Core.Ty}
    {reason : Core.Word} {expression : Core.Expr}
    (aligned : ScopeContextAligned scope context)
    (accepted : SourceCoreBasic.lowerStatements fuel source scope statements resultType reason = .ok expression) :
    ∃ depth, depth ≤ fuel ∧ Tree source reason scope context statements resultType expression depth := by
  induction fuel generalizing scope context statements expression with
  | zero =>
      cases statements with
      | nil =>
          simp only [SourceCoreBasic.lowerStatements] at accepted
          split at accepted
          · rename_i unitResult
            subst resultType
            cases accepted
            exact ⟨0, Nat.le_refl _, .nil⟩
          · cases accepted
      | cons => cases accepted
  | succ fuel ih =>
      cases statements with
      | nil =>
          simp only [SourceCoreBasic.lowerStatements] at accepted
          split at accepted
          · rename_i unitResult
            subst resultType
            cases accepted
            exact ⟨0, Nat.zero_le _, .nil⟩
          · cases accepted
      | cons id rest =>
          simp only [SourceCoreBasic.lowerStatements] at accepted
          obtain ⟨⟨node, type⟩, read, accepted⟩ := bind_ok accepted
          have metadata := (readStatement_certificate read).2
          cases form : node.form with
          | letDecl binder initializer =>
              simp only [form] at accepted
              obtain ⟨checkedUnit, checked, accepted⟩ := bind_ok accepted
              cases checkedUnit
              have unitType := ensureType_ok checked
              rw [← unitType] at metadata
              obtain ⟨payload, binding, accepted⟩ := bind_ok accepted
              have certificate := lowerBinder_certificate binding
              have extension := certificate.extends aligned
              cases initializer with
              | none =>
                  obtain ⟨body, compiledBody, accepted⟩ := bind_ok accepted
                  cases accepted
                  obtain ⟨depth, bound, tail⟩ := ih (aligned.bind binder payload) compiledBody
                  exact ⟨depth + 1, by omega, .letUninitialized metadata form certificate extension tail⟩
              | some initializer =>
                  obtain ⟨value, compiledValue, accepted⟩ := bind_ok accepted
                  obtain ⟨checkedUnit, checked, accepted⟩ := bind_ok accepted
                  cases checkedUnit
                  have same := ensureType_ok checked
                  obtain ⟨body, compiledBody, accepted⟩ := bind_ok accepted
                  cases accepted
                  obtain ⟨bodyDepth, bodyBound, tail⟩ := ih (aligned.bind binder payload) compiledBody
                  obtain ⟨valueDepth, valueBound, valueTree⟩ := BasicExpressions.tree_of_lowerExpression compiledValue
                  rw [← same] at valueTree
                  exact ⟨max valueDepth bodyDepth + 1, by omega,
                    .letInitialized metadata form certificate extension valueTree tail⟩
          | assignValue assignment operator value =>
              simp only [form] at accepted
              obtain ⟨checkedUnit, checked, accepted⟩ := bind_ok accepted
              cases checkedUnit
              have unitType := ensureType_ok checked
              rw [← unitType] at metadata
              obtain ⟨⟨index, payload⟩, target, accepted⟩ := bind_ok accepted
              obtain ⟨value, compiledValue, accepted⟩ := bind_ok accepted
              obtain ⟨checkedUnit, checked, accepted⟩ := bind_ok accepted
              cases checkedUnit
              have same := ensureType_ok checked
              obtain ⟨body, compiledBody, accepted⟩ := bind_ok accepted
              cases accepted
              obtain ⟨bodyDepth, bodyBound, tail⟩ := ih aligned compiledBody
              have targetCertificate := lowerAssignment_certificate target
              have equal := targetCertificate.equal
              subst operator
              obtain ⟨valueDepth, valueBound, valueTree⟩ := BasicExpressions.tree_of_lowerExpression compiledValue
              rw [← same] at valueTree
              exact ⟨max valueDepth bodyDepth + 1, by omega,
                .assign metadata form targetCertificate valueTree tail⟩
          | returnStmt value =>
              cases value with
              | none =>
                  simp only [form] at accepted
                  obtain ⟨checkedUnit, resultChecked, accepted⟩ := bind_ok accepted
                  cases checkedUnit
                  obtain ⟨checkedUnit, unitChecked, accepted⟩ := bind_ok accepted
                  cases checkedUnit
                  have resultSame := ensureType_ok resultChecked
                  have unitSame := ensureType_ok unitChecked
                  have resultUnit : resultType = .unit := resultSame.trans unitSame.symm
                  rw [← unitSame] at metadata
                  cases accepted
                  rw [resultUnit]
                  exact ⟨1, by omega, .returnUnit rest metadata form⟩
              | some value =>
                  simp only [form] at accepted
                  obtain ⟨checkedUnit, resultChecked, accepted⟩ := bind_ok accepted
                  cases checkedUnit
                  have resultSame := ensureType_ok resultChecked
                  rw [← resultSame] at metadata
                  obtain ⟨value, compiledValue, accepted⟩ := bind_ok accepted
                  obtain ⟨checkedUnit, checked, accepted⟩ := bind_ok accepted
                  cases checkedUnit
                  have same := ensureType_ok checked
                  cases accepted
                  obtain ⟨depth, bound, valueTree⟩ := BasicExpressions.tree_of_lowerExpression compiledValue
                  rw [← same] at valueTree
                  exact ⟨depth + 1, by omega, .returnValue rest metadata form valueTree⟩
          | expression value semicolon =>
              cases semicolon with
              | true =>
                  simp only [form, ↓reduceIte] at accepted
                  obtain ⟨checkedUnit, checked, accepted⟩ := bind_ok accepted
                  cases checkedUnit
                  have unitType := ensureType_ok checked
                  rw [← unitType] at metadata
                  obtain ⟨value, compiledValue, accepted⟩ := bind_ok accepted
                  obtain ⟨body, compiledBody, accepted⟩ := bind_ok accepted
                  cases accepted
                  obtain ⟨bodyDepth, bodyBound, tail⟩ := ih aligned compiledBody
                  obtain ⟨valueDepth, valueBound, valueTree⟩ := BasicExpressions.tree_of_lowerExpression compiledValue
                  exact ⟨max valueDepth bodyDepth + 1, by omega, .discard metadata form valueTree tail⟩
              | false =>
                  cases rest with
                  | cons => simp [form] at accepted
                  | nil =>
                      simp only [form, List.isEmpty_nil, Bool.false_eq_true, ↓reduceIte] at accepted
                      obtain ⟨checkedUnit, resultChecked, accepted⟩ := bind_ok accepted
                      cases checkedUnit
                      have resultSame := ensureType_ok resultChecked
                      rw [← resultSame] at metadata
                      obtain ⟨value, compiledValue, accepted⟩ := bind_ok accepted
                      obtain ⟨checkedUnit, checked, accepted⟩ := bind_ok accepted
                      cases checkedUnit
                      have same := ensureType_ok checked
                      cases accepted
                      obtain ⟨depth, bound, valueTree⟩ := BasicExpressions.tree_of_lowerExpression compiledValue
                      rw [← same] at valueTree
                      exact ⟨depth + 1, by omega, .tailExpression metadata form valueTree⟩
          | assignBitNot | ifThen | block | matchWith | forLoop | whileLoop | breakStmt | continueStmt =>
              simp [form] at accepted

/-- Actual successful basic lowering executes according to the independent
source semantics, even with administrative closures in the Core store. The
remaining premises describe the ambient context and initial representation;
no structural Tree or source execution is supplied by the caller. -/
theorem lowerStatements_run_preserves
    {fuel : Nat} {source : TypedSource} {scope : SourceCoreLocalCell.Scope}
    {context : Context} {statements : List StatementId} {type : Core.Ty}
    {reason : Core.Word} {code : Core.Expr}
    (aligned : ScopeContextAligned scope context) (unique : NodeOccurrencesUnique source)
    (accepted : SourceCoreBasic.lowerStatements fuel source scope statements type reason = .ok code)
    (program : Program) (evidence : Dynamic.EvidenceEnvironment)
    {mapping : GeneralHeap.LocationMap} {world : Core.StoreTyping} {administrativeContext : Core.Context}
    {environment : Dynamic.Environment} {heap : Dynamic.Heap}
    {coreEnvironment : Core.Environment} {store : Core.Store}
    (environments : GeneralHeap.EnvRepresents mapping world administrativeContext scope environment coreEnvironment)
    (heaps : GeneralHeap.HeapRepresents mapping world heap store) :
    Core.infer? (SourceCoreLocalCell.coreContext scope ++ administrativeContext) code =
      some (Core.LanguageResult.resultType type) ∧
    ∃ finalContext outcome after result finalStore finalMapping finalWorld required,
      Dynamic.FunctionStatementsExecuteOutcome program context evidence source environment heap
        statements finalContext outcome after ∧
      GeneralStatements.OutcomeRepresents finalMapping finalWorld administrativeContext reason type outcome result ∧
      GeneralHeap.HeapRepresents finalMapping finalWorld after finalStore ∧
      GeneralHeap.LocationMap.Extends mapping finalMapping ∧ Core.WorldExtends world finalWorld ∧
      GeneralHeap.EnvRepresents finalMapping finalWorld administrativeContext scope environment coreEnvironment ∧
      GeneralHeap.AdministrativePreserved mapping store finalMapping finalStore ∧
      (∀ runtimeFuel, required ≤ runtimeFuel → Core.runStateful runtimeFuel (.initial code coreEnvironment store) =
        .done result finalStore) ∧
      (∀ runtimeFuel actual actualStore, Core.runStateful runtimeFuel (.initial code coreEnvironment store) =
        .done actual actualStore → actual = result ∧ actualStore = finalStore) := by
  obtain ⟨depth, bound, tree⟩ := tree_of_lowerStatements aligned accepted
  exact (GeneralStatements.lower_run_preserves tree unique fuel bound program evidence environments heaps).2

end Solcore.SourceSemantics.CoreLowering.BasicStatements
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.SourceLetDeclarationFacts
/-! A concrete let and the same source's local identity ownership supply its
complete declaration and distinguish it from input parameters. These finite
inventory proofs are shared with the accepted-body binder analysis. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.SourceLetDeclarationFacts
open Core Frontend SourceInference

private theorem instruction_ids (instructions : List MatchPatternInstruction) :
    (SourceCoreDataPlaces.instructionBinders instructions).map (·.id) =
      patternInstructionBinderIds instructions := by
  induction instructions with
  | nil => rfl
  | cons item rest ih => cases item <;> simp [SourceCoreDataPlaces.instructionBinders,
      patternInstructionBinderIds] at ih ⊢ <;> exact ih

private theorem pattern_ids (pattern : TypedMatchPattern) :
    (SourceCoreDataPlaces.patternBinders pattern).map (·.id) = patternBinderIds pattern := by
  cases pattern with
  | mk source type resolution requirements =>
    cases resolution <;> simp [SourceCoreDataPlaces.patternBinders, patternBinderIds, instruction_ids]

private theorem for_ids (items : List ForItemForm) :
    (items.filterMap fun | .letDecl binder _ => some binder | _ => none).map (·.id) =
      items.flatMap forItemDefinedLocalIds := by
  induction items with
  | nil => rfl
  | cons item rest ih => cases item <;> simp [forItemDefinedLocalIds, ih]

private def nodeBinders (node : Node) : List TypedBinder :=
  match node with
  | .expression node => match node.form with
      | .lambda parameters _ _ => parameters
      | _ => []
  | .statement node => match node.form with
      | .letDecl binder _ => [binder]
      | .forLoop initial _ post _ => (initial ++ post).filterMap fun
          | .letDecl binder _ => some binder | _ => none
      | .matchWith resolution => resolution.cases.flatMap (fun arm => SourceCoreDataPlaces.patternBinders arm.pattern)
      | _ => []

private theorem node_ids (node : Node) :
    ((nodeBinders node).map (·.id)).Sublist node.definedLocalIds := by
  cases node with
  | expression node => cases form : node.form <;>
      simp [nodeBinders, form, Node.definedLocalIds, ExpressionForm.definedLocalIds]
  | statement node =>
      cases form : node.form <;>
        simp [nodeBinders, form, Node.definedLocalIds, StatementForm.definedLocalIds,
          for_ids]
      case matchWith resolution =>
        have same : (resolution.cases.flatMap (fun arm => SourceCoreDataPlaces.patternBinders arm.pattern)).map (·.id) =
            resolution.cases.flatMap (fun arm => arm.pattern.binderIds) := by
          simp [List.map_flatMap, pattern_ids]
        rw [same]
        exact List.sublist_cons_self _ _

private theorem nodes_ids (nodes : List Node) :
    ((nodes.flatMap nodeBinders).map (·.id)).Sublist (nodes.flatMap Node.definedLocalIds) := by
  induction nodes with
  | nil => exact .refl _
  | cons node rest ih =>
    simpa only [List.flatMap_cons, List.map_append] using (node_ids node).append ih

private theorem declared_ids (source : TypedSource) :
    ((SourceCoreDataPlaces.declaredBinders source).map (·.id)).Sublist (definedLocalIds source) := by
  have same : SourceCoreDataPlaces.declaredBinders source = source.inputs ++ source.nodes.flatMap nodeBinders := rfl
  rw [same, List.map_append, ← typedSourceDefinedLocalIds_eq_carrier]
  exact (List.Sublist.refl _).append (nodes_ids source.nodes)

private theorem filter_self {binders : List TypedBinder} {binder : TypedBinder}
    (unique : (binders.map (·.id)).Nodup) (member : binder ∈ binders) :
    binders.filter (fun other => decide (other.id = binder.id)) = [binder] := by
  induction binders with
  | nil => cases member
  | cons first rest ih =>
    obtain ⟨absent, restUnique⟩ := List.nodup_cons.mp unique
    rcases List.mem_cons.mp member with rfl | member
    · have none : rest.filter (fun other => decide (other.id = binder.id)) = [] := by
        apply List.filter_eq_nil_iff.mpr
        intro other found
        simp only [decide_eq_true_eq]
        intro equal
        exact absent (List.mem_map.mpr ⟨other, found, equal⟩)
      simp [none]
    · have different : first.id ≠ binder.id := by
        intro same
        exact absent (List.mem_map.mpr ⟨binder, member, same.symm⟩)
      simp [different, ih restUnique member]

theorem of_lookup {source : TypedSource} {id : StatementId} {node : StatementNode}
    {binder : TypedBinder} {initializer : Option ExpressionId}
    (ownership : LocalIdentityOwnership source)
    (found : source.lookupStatement? id = some node)
    (form : node.form = .letDecl binder initializer) :
    binder ∈ SourceCoreDataPlaces.declaredBinders source ∧
      (SourceCoreDataPlaces.declaredBinders source).filter
        (fun actual => decide (actual.id = binder.id)) = [binder] ∧
      source.inputs.any (fun input => decide (input.id = binder.id)) = false := by
  have member := (lookupStatement?_sound found).1
  have defined : binder ∈ nodeBinders (.statement node) := by simp [nodeBinders, form]
  have declared : binder ∈ SourceCoreDataPlaces.declaredBinders source :=
    List.mem_append_right _ (List.mem_flatMap.mpr ⟨.statement node, member, defined⟩)
  have filtered := filter_self ((declared_ids source).nodup ownership.unique) declared
  have inNodes : binder.id ∈ source.nodes.flatMap Node.definedLocalIds :=
    List.mem_flatMap.mpr ⟨.statement node, member,
      (node_ids (.statement node)).subset (List.mem_map.mpr ⟨binder, defined, rfl⟩)⟩
  have disjoint := (List.nodup_append.mp (show
      (source.inputs.map (·.id) ++ source.nodes.flatMap Node.definedLocalIds).Nodup from
      by simpa only [definedLocalIds, ← flatMapNodeDefinedLocalIds_eq_carrier] using ownership.unique)).2.2
  refine ⟨declared, filtered, ?_⟩
  apply Bool.eq_false_iff.mpr
  intro occurs
  obtain ⟨input, present, same⟩ := List.any_eq_true.mp occurs
  exact disjoint input.id (List.mem_map.mpr ⟨input, present, rfl⟩)
    binder.id inNodes (of_decide_eq_true same)

end Solcore.SourceSemantics.CoreLowering.SourceLetDeclarationFacts

namespace Solcore.SourceSemantics.CoreLowering.SourceLetDeclarationFacts
open Core Frontend SourceInference

theorem of_header_lookup {source : TypedSource} {id : StatementId} {node : StatementNode}
    {initial post : List ForItemForm} {condition : ExpressionId} {body : List StatementId}
    {binder : TypedBinder} {initializer : Option ExpressionId}
    (ownership : LocalIdentityOwnership source)
    (found : source.lookupStatement? id = some node)
    (form : node.form = .forLoop initial condition post body)
    (present : ForItemForm.letDecl binder initializer ∈ initial ++ post) :
    binder ∈ SourceCoreDataPlaces.declaredBinders source ∧
      (SourceCoreDataPlaces.declaredBinders source).filter
        (fun actual => decide (actual.id = binder.id)) = [binder] ∧
      source.inputs.any (fun input => decide (input.id = binder.id)) = false := by
  have member := (lookupStatement?_sound found).1
  have defined : binder ∈ nodeBinders (.statement node) := by
    simp only [nodeBinders, form]
    exact List.mem_filterMap.mpr ⟨.letDecl binder initializer, present, rfl⟩
  have declared : binder ∈ SourceCoreDataPlaces.declaredBinders source :=
    List.mem_append_right _ (List.mem_flatMap.mpr ⟨.statement node, member, defined⟩)
  have filtered := filter_self ((declared_ids source).nodup ownership.unique) declared
  have inNodes : binder.id ∈ source.nodes.flatMap Node.definedLocalIds :=
    List.mem_flatMap.mpr ⟨.statement node, member,
      (node_ids (.statement node)).subset (List.mem_map.mpr ⟨binder, defined, rfl⟩)⟩
  have disjoint := (List.nodup_append.mp (show
      (source.inputs.map (·.id) ++ source.nodes.flatMap Node.definedLocalIds).Nodup from
      by simpa only [definedLocalIds, ← flatMapNodeDefinedLocalIds_eq_carrier] using ownership.unique)).2.2
  refine ⟨declared, filtered, ?_⟩
  apply Bool.eq_false_iff.mpr
  intro occurs
  obtain ⟨input, present, same⟩ := List.any_eq_true.mp occurs
  exact disjoint input.id (List.mem_map.mpr ⟨input, present, rfl⟩)
    binder.id inNodes (of_decide_eq_true same)

end Solcore.SourceSemantics.CoreLowering.SourceLetDeclarationFacts
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.ControlStatementTree
/-! Static certificates for scoped control statements. Function lists and
nested lists differ only in their final-expression convention. The certificates
contain no child evaluation premise and preserve the actual reason provider. -/

set_option autoImplicit false

namespace Solcore.SourceSemantics.CoreLowering.ControlStatements

open Frontend Frontend.SourceInference TypeSystem LocalCell BasicStatements

/-- A finite control statement tree. `tailReturns` marks function sequencing;
nested blocks and conditional branches use ordinary statement sequencing. -/
inductive Tree (source : TypedSource) (reasonAt : ExpressionId → Core.Word) :
    SourceCoreLocalCell.Scope → Context → Bool → List StatementId → Core.Ty → Core.Expr → Prop where
  | nil {scope context tailReturns type} :
      Tree source reasonAt scope context tailReturns [] type (Core.LocalControl.fallthrough type)
  | letUninitialized
      {scope context middleContext tailReturns id rest node binder payloadType resultType body}
      (metadata : Metadata source id node .unit)
      (form : node.form = .letDecl binder none)
      (binding : BinderCertificate source scope binder payloadType)
      (extension : BinderExtends source.owner context binder middleContext)
      (tail : Tree source reasonAt ((binder.id, payloadType) :: scope) middleContext
        tailReturns rest resultType body) :
      Tree source reasonAt scope context tailReturns (id :: rest) resultType
        (Core.LocalSequence.letUninitialized payloadType body)
  | letInitialized
      {scope context middleContext tailReturns id rest node binder payloadType resultType
        initializer initializerCode body initializerDepth}
      (metadata : Metadata source id node .unit)
      (form : node.form = .letDecl binder (some initializer))
      (binding : BinderCertificate source scope binder payloadType)
      (extension : BinderExtends source.owner context binder middleContext)
      (value : ControlExpressions.Tree source scope reasonAt initializer payloadType initializerCode initializerDepth)
      (tail : Tree source reasonAt ((binder.id, payloadType) :: scope) middleContext
        tailReturns rest resultType body) :
      Tree source reasonAt scope context tailReturns (id :: rest) resultType
        (Core.LocalSequence.letInitialized (Core.LocalControl.controlType resultType) payloadType initializerCode body)
  | assign
      {scope context tailReturns id rest node assignment index payloadType resultType rhs rhsCode body rhsDepth}
      (metadata : Metadata source id node .unit)
      (form : node.form = .assignValue assignment .equal rhs)
      (target : AssignmentCertificate source scope assignment .equal index payloadType)
      (value : ControlExpressions.Tree source scope reasonAt rhs payloadType rhsCode rhsDepth)
      (tail : Tree source reasonAt scope context tailReturns rest resultType body) :
      Tree source reasonAt scope context tailReturns (id :: rest) resultType
        (Core.LocalSequence.assign (Core.LocalControl.controlType resultType) (.var index) rhsCode body)
  | discard
      {scope context tailReturns id rest node nodeType valueId valueType resultType valueCode body valueDepth semicolon}
      (metadata : Metadata source id node nodeType)
      (form : node.form = .expression valueId semicolon)
      (notTail : (!semicolon && tailReturns && rest.isEmpty) = false)
      (statementType : if semicolon then nodeType = .unit else nodeType = valueType)
      (value : ControlExpressions.Tree source scope reasonAt valueId valueType valueCode valueDepth)
      (tail : Tree source reasonAt scope context tailReturns rest resultType body) :
      Tree source reasonAt scope context tailReturns (id :: rest) resultType
        (Core.LocalSequence.discard (Core.LocalControl.controlType resultType) valueCode body)
  | returnValue
      {scope context tailReturns id node valueId resultType valueCode valueDepth}
      (rest : List StatementId)
      (metadata : Metadata source id node resultType)
      (form : node.form = .returnStmt (some valueId))
      (value : ControlExpressions.Tree source scope reasonAt valueId resultType valueCode valueDepth) :
      Tree source reasonAt scope context tailReturns (id :: rest) resultType
        (Core.LocalControl.returnValue resultType valueCode)
  | returnUnit {scope context tailReturns id node}
      (rest : List StatementId)
      (metadata : Metadata source id node .unit)
      (form : node.form = .returnStmt none) :
      Tree source reasonAt scope context tailReturns (id :: rest) .unit (Core.LocalControl.returned .unit)
  | tailExpression
      {scope context id node valueId resultType valueCode valueDepth}
      (metadata : Metadata source id node resultType)
      (form : node.form = .expression valueId false)
      (value : ControlExpressions.Tree source scope reasonAt valueId resultType valueCode valueDepth) :
      Tree source reasonAt scope context true [id] resultType (Core.LocalControl.returnValue resultType valueCode)
  | block
      {scope context tailReturns id rest node nodeType statements resultType blockCode body}
      (metadata : Metadata source id node nodeType)
      (form : node.form = .block statements)
      (block : Tree source reasonAt scope context false statements resultType blockCode)
      (tail : Tree source reasonAt scope context tailReturns rest resultType body) :
      Tree source reasonAt scope context tailReturns (id :: rest) resultType
        (Core.LocalControl.sequence resultType blockCode body)
  | ifThen
      {scope context tailReturns id rest node nodeType condition thenBody elseBody resultType
        conditionCode thenCode elseCode body conditionDepth}
      (metadata : Metadata source id node nodeType)
      (form : node.form = .ifThen condition thenBody elseBody)
      (conditionTree : ControlExpressions.Tree source scope reasonAt condition .bool conditionCode conditionDepth)
      (thenTree : Tree source reasonAt scope context false thenBody resultType thenCode)
      (elseTree : Tree source reasonAt scope context false (elseBody.getD []) resultType elseCode)
      (tail : Tree source reasonAt scope context tailReturns rest resultType body) :
      Tree source reasonAt scope context tailReturns (id :: rest) resultType
        (Core.LocalControl.sequence resultType
          (Core.LocalControl.conditional resultType conditionCode thenCode elseCode) body)

theorem Tree.heapEffects
    {source : TypedSource} {reasonAt : ExpressionId → Core.Word} {scope : SourceCoreLocalCell.Scope}
    {context : Context} {tailReturns : Bool} {statements : List StatementId} {type : Core.Ty} {code : Core.Expr}
    (tree : Tree source reasonAt scope context tailReturns statements type code) : Core.HeapEffects.Expression code := by
  induction tree with
  | nil => exact .inRight (.inLeft .unit)
  | returnUnit => exact .inRight (.inRight .unit)
  | returnValue _ _ _ value | tailExpression _ _ value =>
      exact .caseE (.of_readOnly (GeneralExpressions.Control.readOnly value)) (.inLeft .var)
        (.inRight (.inRight .var))
  | letUninitialized _ _ _ _ _ tail => exact .letE (.newCell (.inLeft .unit)) tail
  | letInitialized _ _ _ _ value _ tail =>
      exact .caseE (.of_readOnly (GeneralExpressions.Control.readOnly value)) (.inLeft .var)
        (.letE (.newCell (.inRight .var)) (tail.weakenAt 1))
  | assign _ _ _ value _ tail =>
      exact .letE .var
        (.caseE ((Core.HeapEffects.Expression.of_readOnly (GeneralExpressions.Control.readOnly value)).weakenAt 0)
          (.inLeft .var) (.letE (.storeCell .var (.inRight .var)) (((tail.weakenAt 0).weakenAt 0).weakenAt 0)))
  | discard _ _ _ _ value _ tail =>
      exact .caseE (.of_readOnly (GeneralExpressions.Control.readOnly value)) (.inLeft .var) (tail.weakenAt 0)
  | block _ _ _ _ block tail =>
      exact .caseE block (.inLeft .var)
        (.caseE .var ((tail.weakenAt 0).weakenAt 0) (.inRight (.inRight .var)))
  | ifThen _ _ condition _ _ _ thenTree elseTree tail =>
      exact .caseE
        (.caseE (.of_readOnly (GeneralExpressions.Control.readOnly condition)) (.inLeft .var)
          (.ifE .var (thenTree.weakenAt 0) (elseTree.weakenAt 0))) (.inLeft .var)
        (.caseE .var ((tail.weakenAt 0).weakenAt 0) (.inRight (.inRight .var)))

theorem Tree.hasType
    {source : TypedSource} {reasonAt : ExpressionId → Core.Word} {scope : SourceCoreLocalCell.Scope}
    {context : Context} {tailReturns : Bool} {statements : List StatementId} {type : Core.Ty} {code : Core.Expr}
    (tree : Tree source reasonAt scope context tailReturns statements type code)
    (wellFormed : Core.Ty.WellFormed [] type) :
    Core.HasType (SourceCoreLocalCell.coreContext scope) code (Core.LocalControl.resultType type) := by
  induction tree with
  | nil => exact Core.LocalControl.fallthrough_hasType wellFormed
  | returnUnit => exact Core.LocalControl.returned_hasType .unit
  | returnValue _ _ _ value | tailExpression _ _ value =>
      exact Core.LocalControl.returnValue_hasType wellFormed value.hasType
  | letUninitialized _ _ binding _ _ tail =>
      exact Core.LocalSequence.letUninitialized_hasType (binding.types.wellFormed []) (tail wellFormed)
  | letInitialized _ _ _ _ value _ tail =>
      exact Core.LocalSequence.letInitialized_hasType (.sum .unit wellFormed) value.hasType (tail wellFormed)
  | assign _ _ target value _ tail =>
      exact Core.LocalSequence.assign_hasType (.sum .unit wellFormed)
        (.var (SourceCoreLocalCell.lookup?_context target.slot)) value.hasType (tail wellFormed)
  | discard _ _ _ _ value _ tail =>
      exact Core.LocalSequence.discard_hasType (.sum .unit wellFormed) value.hasType (tail wellFormed)
  | block _ _ _ _ block tail => exact Core.LocalControl.sequence_hasType wellFormed (block wellFormed) (tail wellFormed)
  | ifThen _ _ condition _ _ _ thenTree elseTree tail =>
      exact Core.LocalControl.sequence_hasType wellFormed
        (Core.LocalControl.conditional_hasType wellFormed condition.hasType (thenTree wellFormed) (elseTree wellFormed))
        (tail wellFormed)

end Solcore.SourceSemantics.CoreLowering.ControlStatements
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.ControlStatementCertificates
/-! Extract scoped control statement trees from the actual successful compiler.
The ambient context/scope alignment and unique source occurrences are static
premises. Neither child trees nor source/Core evaluations are assumed. -/

set_option autoImplicit false

namespace Solcore.SourceSemantics.CoreLowering.ControlStatements

open Frontend Frontend.SourceInference TypeSystem LocalCell BasicStatements

private theorem bind_ok {α β ε : Type} {computation : Except ε α} {next : α → Except ε β}
    {result : β} (accepted : computation >>= next = .ok result) :
    ∃ value, computation = .ok value ∧ next value = .ok result := by
  cases computation with
  | error => cases accepted
  | ok value => exact ⟨value, rfl, accepted⟩

private theorem ensureType_ok
    {site : SourceCoreElaboration.ErrorSite} {expected actual : Core.Ty}
    (accepted : SourceCoreBasic.ensureType site expected actual = .ok ()) : expected = actual := by
  unfold SourceCoreBasic.ensureType at accepted
  split at accepted
  · assumption
  · cases accepted

/-- Function and nested-list tail conventions are both recovered from
successful lowering. Branch/block binders remain local to their child tree. -/
theorem tree_of_lowerFlowStatements
    {fuel : Nat} {source : TypedSource} {scope : SourceCoreLocalCell.Scope}
    {context : Context} {statements : List StatementId} {resultType : Core.Ty}
    {reasonAt : ExpressionId → Core.Word} {tailReturns : Bool} {code : Core.Expr}
    (aligned : ScopeContextAligned scope context) (unique : NodeOccurrencesUnique source)
    (accepted : SourceCoreControl.lowerFlowStatementsWithReasons fuel source scope statements
      resultType reasonAt tailReturns = .ok code) :
    Tree source reasonAt scope context tailReturns statements resultType code := by
  induction fuel generalizing scope context statements code tailReturns with
  | zero =>
      cases statements with
      | nil => cases accepted; exact .nil
      | cons => cases accepted
  | succ fuel ih =>
      cases statements with
      | nil => cases accepted; exact .nil
      | cons id rest =>
          simp only [SourceCoreControl.lowerFlowStatementsWithReasons,
            SourceCoreControl.lowerFlowStatementsWithExpression] at accepted
          obtain ⟨⟨node, type⟩, read, accepted⟩ := bind_ok accepted
          have metadata := (readStatement_certificate read).2
          cases form : node.form with
          | letDecl binder initializer =>
              simp only [form] at accepted
              obtain ⟨checkedUnit, checked, accepted⟩ := bind_ok accepted
              cases checkedUnit
              rw [← ensureType_ok checked] at metadata
              obtain ⟨payload, binding, accepted⟩ := bind_ok accepted
              have certificate := lowerBinder_certificate binding
              have extension := certificate.extends aligned
              cases initializer with
              | none =>
                  obtain ⟨body, compiledBody, accepted⟩ := bind_ok accepted
                  cases accepted
                  exact .letUninitialized metadata form certificate extension
                    (ih (aligned.bind binder payload) compiledBody)
              | some initializer =>
                  obtain ⟨value, compiledValue, accepted⟩ := bind_ok accepted
                  obtain ⟨checkedUnit, checked, accepted⟩ := bind_ok accepted
                  cases checkedUnit
                  obtain ⟨body, compiledBody, accepted⟩ := bind_ok accepted
                  cases accepted
                  obtain ⟨_, _, valueTree⟩ := ControlExpressions.tree_of_lowerExpression unique compiledValue
                  rw [← ensureType_ok checked] at valueTree
                  exact .letInitialized metadata form certificate extension valueTree
                    (ih (aligned.bind binder payload) compiledBody)
          | assignValue assignment operator rhs =>
              simp only [form] at accepted
              obtain ⟨checkedUnit, checked, accepted⟩ := bind_ok accepted
              cases checkedUnit
              rw [← ensureType_ok checked] at metadata
              obtain ⟨⟨index, payload⟩, target, accepted⟩ := bind_ok accepted
              obtain ⟨value, compiledValue, accepted⟩ := bind_ok accepted
              obtain ⟨checkedUnit, checked, accepted⟩ := bind_ok accepted
              cases checkedUnit
              obtain ⟨body, compiledBody, accepted⟩ := bind_ok accepted
              cases accepted
              have targetCertificate := lowerAssignment_certificate target
              have equal := targetCertificate.equal
              subst operator
              obtain ⟨_, _, valueTree⟩ := ControlExpressions.tree_of_lowerExpression unique compiledValue
              rw [← ensureType_ok checked] at valueTree
              exact .assign metadata form targetCertificate valueTree (ih aligned compiledBody)
          | returnStmt value =>
              cases value with
              | none =>
                  simp only [form] at accepted
                  obtain ⟨checkedUnit, resultChecked, accepted⟩ := bind_ok accepted
                  cases checkedUnit
                  obtain ⟨checkedUnit, unitChecked, accepted⟩ := bind_ok accepted
                  cases checkedUnit
                  have resultUnit : resultType = .unit :=
                    (ensureType_ok resultChecked).trans (ensureType_ok unitChecked).symm
                  rw [← ensureType_ok unitChecked] at metadata
                  cases accepted
                  rw [resultUnit]
                  exact .returnUnit rest metadata form
              | some value =>
                  simp only [form] at accepted
                  obtain ⟨checkedUnit, resultChecked, accepted⟩ := bind_ok accepted
                  cases checkedUnit
                  rw [← ensureType_ok resultChecked] at metadata
                  obtain ⟨value, compiledValue, accepted⟩ := bind_ok accepted
                  obtain ⟨checkedUnit, checked, accepted⟩ := bind_ok accepted
                  cases checkedUnit
                  cases accepted
                  obtain ⟨_, _, valueTree⟩ := ControlExpressions.tree_of_lowerExpression unique compiledValue
                  rw [← ensureType_ok checked] at valueTree
                  exact .returnValue rest metadata form valueTree
          | expression value semicolon =>
              simp only [form] at accepted
              obtain ⟨value, compiledValue, accepted⟩ := bind_ok accepted
              obtain ⟨_, _, valueTree⟩ := ControlExpressions.tree_of_lowerExpression unique compiledValue
              split at accepted
              · rename_i isTail
                have shape : semicolon = false ∧ tailReturns = true ∧ rest = [] := by
                  cases semicolon <;> cases tailReturns <;> cases rest <;> simp_all
                obtain ⟨checkedUnit, resultChecked, accepted⟩ := bind_ok accepted
                cases checkedUnit
                rw [← ensureType_ok resultChecked] at metadata
                obtain ⟨checkedUnit, checked, accepted⟩ := bind_ok accepted
                cases checkedUnit
                cases accepted
                rw [← ensureType_ok checked] at valueTree
                rcases shape with ⟨rfl, rfl, rfl⟩
                exact .tailExpression metadata form valueTree
              · rename_i notTail
                have notTail : (!semicolon && tailReturns && rest.isEmpty) = false := by simpa using notTail
                cases semicolon with
                | true =>
                    obtain ⟨checkedUnit, checked, accepted⟩ := bind_ok accepted
                    cases checkedUnit
                    obtain ⟨body, compiledBody, accepted⟩ := bind_ok accepted
                    cases accepted
                    exact .discard metadata form notTail (ensureType_ok checked).symm
                      valueTree (ih aligned compiledBody)
                | false =>
                    obtain ⟨checkedUnit, checked, accepted⟩ := bind_ok accepted
                    cases checkedUnit
                    obtain ⟨body, compiledBody, accepted⟩ := bind_ok accepted
                    cases accepted
                    exact .discard metadata form notTail (ensureType_ok checked)
                      valueTree (ih aligned compiledBody)
          | block statements =>
              simp only [form] at accepted
              obtain ⟨block, compiledBlock, accepted⟩ := bind_ok accepted
              obtain ⟨body, compiledBody, accepted⟩ := bind_ok accepted
              cases accepted
              exact .block metadata form (ih aligned compiledBlock) (ih aligned compiledBody)
          | ifThen condition thenBody elseBody =>
              simp only [form] at accepted
              obtain ⟨condition, compiledCondition, accepted⟩ := bind_ok accepted
              obtain ⟨checkedUnit, checked, accepted⟩ := bind_ok accepted
              cases checkedUnit
              obtain ⟨thenBranch, compiledThen, accepted⟩ := bind_ok accepted
              obtain ⟨_, _, conditionTree⟩ := ControlExpressions.tree_of_lowerExpression unique compiledCondition
              rw [← ensureType_ok checked] at conditionTree
              cases elseBody with
              | none =>
                  obtain ⟨elseBranch, compiledElse, accepted⟩ := bind_ok accepted
                  cases compiledElse
                  obtain ⟨body, compiledBody, accepted⟩ := bind_ok accepted
                  cases accepted
                  exact .ifThen metadata form conditionTree (ih aligned compiledThen) .nil (ih aligned compiledBody)
              | some statements =>
                  obtain ⟨elseBranch, compiledElse, accepted⟩ := bind_ok accepted
                  obtain ⟨body, compiledBody, accepted⟩ := bind_ok accepted
                  cases accepted
                  exact .ifThen metadata form conditionTree (ih aligned compiledThen)
                    (ih aligned compiledElse) (ih aligned compiledBody)
          | assignBitNot | matchWith | forLoop | whileLoop | breakStmt | continueStmt =>
              simp [form] at accepted

/-- The actual function compiler supplies its complete flow tree and the
precise finish expression, including Unit/non-Unit fallthrough handling. -/
theorem tree_of_lowerStatements
    {fuel : Nat} {source : TypedSource} {scope : SourceCoreLocalCell.Scope}
    {context : Context} {statements : List StatementId} {resultType : Core.Ty}
    {reasonAt : ExpressionId → Core.Word} {fellThroughReason : Core.Word} {code : Core.Expr}
    (aligned : ScopeContextAligned scope context) (unique : NodeOccurrencesUnique source)
    (accepted : SourceCoreControl.lowerStatementsWithReasons fuel source scope statements
      resultType reasonAt fellThroughReason = .ok code) :
    ∃ flow, code = Core.LocalControl.finish resultType flow
        (if resultType = .unit then Core.LanguageResult.success .unit
         else Core.LanguageResult.failure resultType (.word fellThroughReason)) ∧
      Tree source reasonAt scope context true statements resultType flow := by
  unfold SourceCoreControl.lowerStatementsWithReasons at accepted
  obtain ⟨flow, compiledFlow, accepted⟩ := bind_ok accepted
  cases accepted
  exact ⟨flow, rfl, tree_of_lowerFlowStatements aligned unique compiledFlow⟩

end Solcore.SourceSemantics.CoreLowering.ControlStatements
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.ControlStatementMeaning
/-! Whole scoped-control correspondence over mapped source cells and arbitrary
typed administrative cells. All child evaluations follow from the static tree;
blocks restore lexical environments while retaining heap changes. -/

set_option autoImplicit false

namespace Solcore.SourceSemantics.CoreLowering.ControlStatements

open Frontend Frontend.SourceInference TypeSystem LocalCell BasicStatements

/-- Select the independent list judgment used by the source language. -/
def Executes (tailReturns : Bool) (program : Program) (context : Context)
    (evidence : Dynamic.EvidenceEnvironment) (source : TypedSource)
    (environment : Dynamic.Environment) (before : Dynamic.Heap) (statements : List StatementId)
    (finalContext : Context) (outcome : Dynamic.ControlOutcome) (after : Dynamic.Heap) : Prop :=
  if tailReturns then
    Dynamic.FunctionStatementsExecuteOutcome program context evidence source environment before
      statements finalContext outcome after
  else Dynamic.StatementsExecuteOutcome program context evidence source environment before
      statements finalContext outcome after

/-- The control envelope contains fallthrough, return, or the provider token
of an uninitialized read. Source fault locations and Core locations remain
separate. The expression-level provenance is retained as an explicit witness. -/
inductive OutcomeRepresents (program : Program) (evidence : Dynamic.EvidenceEnvironment)
    (source : TypedSource) (mapping : GeneralHeap.LocationMap) (world : Core.StoreTyping)
    (administrativeContext : Core.Context) (reasonAt : ExpressionId → Core.Word) (type : Core.Ty) :
    Dynamic.ControlOutcome → Core.Value → Prop where
  | fallthrough {scope environment coreEnvironment}
      (environments : GeneralHeap.EnvRepresents mapping world administrativeContext scope environment coreEnvironment) :
      OutcomeRepresents program evidence source mapping world administrativeContext reasonAt type
        (.fallthrough environment) (.inRight .word (.inLeft type .unit))
  | returned (value : SourceStagedValue.Value) (typed : SourceStagedValue.coreType value = type) :
      OutcomeRepresents program evidence source mapping world administrativeContext reasonAt type
        (.returned (StagedValue.toSource value)) (.inRight .word (.inRight .unit (SourceStagedValue.toCore value)))
  | uninitialized (site : ExpressionId) (location : Dynamic.Location)
      {context : Context} {environment : Dynamic.Environment} {heap : Dynamic.Heap} {root : ExpressionId}
      (origin : ControlExpressions.UninitializedAt program context evidence source environment heap root site location) :
      OutcomeRepresents program evidence source mapping world administrativeContext reasonAt type
        (.fault (.uninitializedLocation location)) (.inLeft (Core.LocalControl.controlType type) (.word (reasonAt site)))

private theorem nil_executes (tailReturns : Bool) (program : Program) (context : Context)
    (evidence : Dynamic.EvidenceEnvironment) (source : TypedSource)
    (environment : Dynamic.Environment) (heap : Dynamic.Heap) :
    Executes tailReturns program context evidence source environment heap [] context (.fallthrough environment) heap := by
  cases tailReturns <;> exact .control .nil

private theorem fault_head
    {program : Program} {context : Context} {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource}
    {environment : Dynamic.Environment} {before after : Dynamic.Heap} {id : StatementId}
    {reason : Dynamic.SemanticFault} (tailReturns : Bool) (rest : List StatementId)
    (fault : Dynamic.StatementFaults program context evidence source environment before id reason after) :
    Executes tailReturns program context evidence source environment before (id :: rest) context (.fault reason) after := by
  cases tailReturns with
  | false => exact .fault (.head fault)
  | true => cases rest with
    | nil => exact .fault (.singleton fault)
    | cons => exact .fault (.head fault)

private theorem terminal_head
    {program : Program} {context finalContext : Context} {evidence : Dynamic.EvidenceEnvironment}
    {source : TypedSource} {environment : Dynamic.Environment} {before after : Dynamic.Heap}
    {id : StatementId} {node : StatementNode} {outcome : Dynamic.ControlOutcome}
    (tailReturns : Bool) (rest : List StatementId) (contains : ContainsStatement source id node)
    (notTail : ∀ expression, node.form ≠ .expression expression false)
    (head : Dynamic.StatementExecutes program context evidence source environment before id finalContext outcome after)
    (terminal : Dynamic.TerminalControl outcome) :
    Executes tailReturns program context evidence source environment before (id :: rest) finalContext outcome after := by
  cases tailReturns with
  | false => exact .control (.terminal head terminal)
  | true => cases rest with
    | nil => exact .control (.singleton contains notTail head)
    | cons => exact .control (.terminal head terminal)

private theorem prepend
    {program : Program} {context middleContext finalContext : Context}
    {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource}
    {environment nextEnvironment : Dynamic.Environment} {before middle after : Dynamic.Heap}
    {id : StatementId} {rest : List StatementId} {node : StatementNode}
    {outcome : Dynamic.ControlOutcome} {tailReturns : Bool}
    (contains : ContainsStatement source id node)
    (notTail : tailReturns = true → rest = [] → ∀ expression, node.form ≠ .expression expression false)
    (head : Dynamic.StatementExecutes program context evidence source environment before id
      middleContext (.fallthrough nextEnvironment) middle)
    (tail : Executes tailReturns program middleContext evidence source nextEnvironment middle
      rest finalContext outcome after) :
    Executes tailReturns program context evidence source environment before (id :: rest) finalContext outcome after := by
  cases tailReturns with
  | false => cases tail with
    | control execute => exact .control (.cons head execute)
    | fault fault => exact .fault (.tail head fault)
  | true => cases rest with
    | nil =>
        cases tail with
        | control execute => cases execute; exact .control (.singleton contains (notTail rfl rfl) head)
        | fault fault => cases fault
    | cons => cases tail with
      | control execute => exact .control (.cons head execute)
      | fault fault => exact .fault (.tail head fault)

private theorem scoped_block
    {program : Program} {context finalContext : Context} {evidence : Dynamic.EvidenceEnvironment}
    {source : TypedSource} {environment : Dynamic.Environment} {before after : Dynamic.Heap}
    {id : StatementId} {node : StatementNode} {statements : List StatementId} {outcome : Dynamic.ControlOutcome}
    (contains : ContainsStatement source id node) (form : node.form = .block statements)
    (evaluated : Executes false program context evidence source environment before statements finalContext outcome after) :
    Dynamic.StatementExecutesOutcome program context evidence source environment before id context
      (Dynamic.restoreControl environment outcome) after := by
  cases evaluated with
  | control execute => exact .control (.block contains form execute)
  | fault fault => exact .fault (.block contains form fault)

private theorem scoped_if_true
    {program : Program} {context finalContext : Context} {evidence : Dynamic.EvidenceEnvironment}
    {source : TypedSource} {environment : Dynamic.Environment} {before middle after : Dynamic.Heap}
    {id : StatementId} {node : StatementNode} {condition : ExpressionId} {thenBody : List StatementId}
    {elseBody : Option (List StatementId)} {outcome : Dynamic.ControlOutcome}
    (contains : ContainsStatement source id node) (form : node.form = .ifThen condition thenBody elseBody)
    (conditionEvaluated : Dynamic.ExpressionEvaluates program context evidence source environment before condition (.bool true) middle)
    (evaluated : Executes false program context evidence source environment middle thenBody finalContext outcome after) :
    Dynamic.StatementExecutesOutcome program context evidence source environment before id context
      (Dynamic.restoreControl environment outcome) after := by
  cases evaluated with
  | control execute => exact .control (.ifTrue contains form conditionEvaluated execute)
  | fault fault => exact .fault (.ifTrueBody contains form conditionEvaluated fault)

private theorem scoped_if_false
    {program : Program} {context finalContext : Context} {evidence : Dynamic.EvidenceEnvironment}
    {source : TypedSource} {environment : Dynamic.Environment} {before middle after : Dynamic.Heap}
    {id : StatementId} {node : StatementNode} {condition : ExpressionId} {thenBody : List StatementId}
    {elseBody : Option (List StatementId)} {outcome : Dynamic.ControlOutcome}
    (contains : ContainsStatement source id node) (form : node.form = .ifThen condition thenBody elseBody)
    (conditionEvaluated : Dynamic.ExpressionEvaluates program context evidence source environment before condition (.bool false) middle)
    (evaluated : Executes false program context evidence source environment middle (elseBody.getD []) finalContext outcome after) :
    Dynamic.StatementExecutesOutcome program context evidence source environment before id context
      (Dynamic.restoreControl environment outcome) after := by
  cases elseBody with
  | none =>
      cases evaluated with
      | control execute => cases execute; exact .control (.ifFalseWithoutElse contains form conditionEvaluated)
      | fault fault => cases fault
  | some statements =>
      cases evaluated with
      | control execute => exact .control (.ifFalseWithElse contains form conditionEvaluated execute)
      | fault fault => exact .fault (.ifFalseBody contains form conditionEvaluated fault)

private theorem weaken_three {environment : Core.Environment} {store finalStore : Core.Store}
    {expression : Core.Expr} {result : Core.Value}
    (restricted : Core.HeapEffects.Expression expression)
    (evaluation : Core.Evaluates environment store expression result finalStore) (reference value : Core.Value) :
    Core.Evaluates (.unit :: value :: reference :: environment) store
      (((expression.weakenAt 0).weakenAt 0).weakenAt 0) result finalStore :=
  (((restricted.weakenAt 0).weakenAt 0).evaluation_weakenAt_zero
    ((restricted.weakenAt 0).evaluation_weakenAt_zero
      (restricted.evaluation_weakenAt_zero evaluation reference) value) .unit)

private theorem cellsWrite_set {cells : List Dynamic.Cell} {index : Nat}
    {previous : Dynamic.Cell} (selected : Dynamic.Heap.CellAt cells index previous)
    (replacement : Dynamic.Cell) :
    Dynamic.Heap.CellsWrite cells index replacement (cells.set index replacement) := by
  induction selected with
  | head => exact .head
  | tail _ ih => exact .tail ih

/-- Basic expression RHS evaluation leaves its heap unchanged. The captured
source location and independently mapped Core location identify the same cell. -/
private theorem equal_assignment
    {program : Program} {context : Context} {evidence : Dynamic.EvidenceEnvironment}
    {source : TypedSource} {scope : SourceCoreLocalCell.Scope}
    {environment : Dynamic.Environment} {coreEnvironment : Core.Environment}
    {heap : Dynamic.Heap} {store : Core.Store} {world : Core.StoreTyping}
    {mapping : GeneralHeap.LocationMap} {administrativeContext : Core.Context}
    {target : PlaceResolution} {rhs : ExpressionId} {index : Nat} {payloadType : Core.Ty}
    (environments : GeneralHeap.EnvRepresents mapping world administrativeContext scope environment coreEnvironment)
    (heaps : GeneralHeap.HeapRepresents mapping world heap store)
    (slot : SourceCoreLocalCell.lookup? scope target.root = some (index, payloadType))
    (bare : target.projections = []) (value : SourceStagedValue.Value)
    (valueType : SourceStagedValue.coreType value = payloadType)
    (rhsEvaluated : Dynamic.ExpressionEvaluates program context evidence source environment
      heap rhs (StagedValue.toSource value) heap) :
    ∃ (coreLocation : Core.Location) (after : Dynamic.Heap) (finalStore : Core.Store),
      Dynamic.SourcePlaceAssignment program context evidence source
        (Dynamic.AssignmentValueApplies .equal) environment heap target rhs (StagedValue.toSource value) after ∧
      coreEnvironment[index]? = some (.cellRef (Core.OptionalCell.cellType payloadType) coreLocation) ∧
      (∃ oldValue, store.read? coreLocation = some oldValue) ∧
      store.write? coreLocation (.inRight .unit (SourceStagedValue.toCore value)) = some finalStore ∧
      GeneralHeap.HeapRepresents mapping world after finalStore ∧
      GeneralHeap.EnvRepresents mapping world administrativeContext scope environment coreEnvironment ∧
      GeneralHeap.AdministrativePreserved mapping store mapping finalStore := by
  obtain ⟨location, coreLocation, cell, stored, lookup, coreLookup, reference, read, coreRead, represented⟩ :=
    environments.lookup_heap heaps slot
  let replacement : Dynamic.Cell := { cell with value := some (StagedValue.toSource value) }
  let after : Dynamic.Heap := ⟨heap.cells.set location.index replacement⟩
  have sourceWrite : Dynamic.Heap.Writes heap location (some (StagedValue.toSource value)) after := by
    cases read with
    | intro selected => exact .intro (.intro selected) (cellsWrite_set selected replacement)
  obtain ⟨finalStore, written, heapRelated⟩ := heaps.write_initialized reference value valueType sourceWrite
  let captured : Dynamic.ResolvedPlace := {
    location, rootType := cell.type, valueType := target.type, projections := [], selected := cell.value
  }
  have resolved : Dynamic.SourcePlaceResolves program context evidence source environment heap target captured heap := by
    apply Dynamic.SourcePlaceResolves.intro lookup read
    · rw [bare]; exact .nil
    · exact read
    · exact represented.rootInitialValue
    · exact .nil
  exact ⟨coreLocation, after, finalStore,
    .intro resolved rhsEvaluated
      (.intro read rfl represented.rootInitialValue (.leaf (.equal cell.value (StagedValue.toSource value))) sourceWrite),
    coreLookup, ⟨stored, coreRead⟩, written, heapRelated, environments,
    GeneralHeap.AdministrativePreserved.write (List.mem_of_getElem? reference.mapped) written⟩


/-- Finite whole-list correspondence, including extensions of both location
representations and preservation of installed administrative cells. -/
def Result (tailReturns : Bool) (program : Program) (context : Context)
    (evidence : Dynamic.EvidenceEnvironment) (source : TypedSource)
    (reasonAt : ExpressionId → Core.Word) (type : Core.Ty) (statements : List StatementId)
    (environment : Dynamic.Environment) (heap : Dynamic.Heap)
    (coreEnvironment : Core.Environment) (store : Core.Store) (code : Core.Expr)
    (mapping : GeneralHeap.LocationMap) (world : Core.StoreTyping) (administrativeContext : Core.Context) : Prop :=
  ∃ finalContext outcome after result finalStore finalMapping finalWorld,
    Executes tailReturns program context evidence source environment heap statements finalContext outcome after ∧
    OutcomeRepresents program evidence source finalMapping finalWorld administrativeContext reasonAt type outcome result ∧
    Core.Evaluates coreEnvironment store code result finalStore ∧
    GeneralHeap.HeapRepresents finalMapping finalWorld after finalStore ∧
    GeneralHeap.LocationMap.Extends mapping finalMapping ∧ Core.WorldExtends world finalWorld ∧
    GeneralHeap.AdministrativePreserved mapping store finalMapping finalStore

private theorem scoped_sequence
    {program : Program} {context : Context} {evidence : Dynamic.EvidenceEnvironment}
    {source : TypedSource} {scope : SourceCoreLocalCell.Scope} {reasonAt : ExpressionId → Core.Word}
    {type : Core.Ty} {tailReturns : Bool} {id : StatementId} {node : StatementNode} {rest : List StatementId}
    {environment : Dynamic.Environment} {heap middleHeap : Dynamic.Heap}
    {coreEnvironment : Core.Environment} {store middleStore : Core.Store}
    {mapping middleMapping : GeneralHeap.LocationMap} {world middleWorld : Core.StoreTyping}
    {administrativeContext : Core.Context} {computation next : Core.Expr}
    {outcome : Dynamic.ControlOutcome} {result : Core.Value}
    (contains : ContainsStatement source id node)
    (notTail : ∀ expression, node.form ≠ .expression expression false)
    (environments : GeneralHeap.EnvRepresents mapping world administrativeContext scope environment coreEnvironment)
    (head : Dynamic.StatementExecutesOutcome program context evidence source environment heap id context
      (Dynamic.restoreControl environment outcome) middleHeap)
    (related : OutcomeRepresents program evidence source middleMapping middleWorld administrativeContext reasonAt type outcome result)
    (coreHead : Core.Evaluates coreEnvironment store computation result middleStore)
    (heaps : GeneralHeap.HeapRepresents middleMapping middleWorld middleHeap middleStore)
    (mapsExtended : GeneralHeap.LocationMap.Extends mapping middleMapping)
    (worldsExtended : Core.WorldExtends world middleWorld)
    (frame : GeneralHeap.AdministrativePreserved mapping store middleMapping middleStore)
    (nextRestricted : Core.HeapEffects.Expression next)
    (tail : GeneralHeap.EnvRepresents middleMapping middleWorld administrativeContext scope environment coreEnvironment →
      Result tailReturns program context evidence source reasonAt type rest environment middleHeap
        coreEnvironment middleStore next middleMapping middleWorld administrativeContext) :
    Result tailReturns program context evidence source reasonAt type (id :: rest) environment heap
      coreEnvironment store (Core.LocalControl.sequence type computation next) mapping world administrativeContext := by
  cases related with
  | fallthrough branchEnvironments =>
      cases head with
      | control head =>
          obtain ⟨finalContext, finalOutcome, after, finalValue, finalStore, finalMapping, finalWorld,
            tailSource, tailRelated, tailCore, finalHeaps, finalMaps, finalWorlds, tailFrame⟩ :=
            tail (environments.extend mapsExtended worldsExtended)
          have shifted := (nextRestricted.weakenAt 0).evaluation_weakenAt_zero
            (nextRestricted.evaluation_weakenAt_zero tailCore (.inLeft type .unit)) .unit
          exact ⟨_, _, _, _, _, _, _, prepend contains (fun _ _ => notTail) head tailSource,
            tailRelated, Core.LocalControl.sequence_fallthrough type coreHead shifted, finalHeaps,
            mapsExtended.trans finalMaps, worldsExtended.trans finalWorlds, frame.trans tailFrame⟩
  | returned value typed =>
      cases head with
      | control head =>
          exact ⟨_, _, _, _, _, _, _, terminal_head tailReturns rest contains notTail head (.returned _),
            .returned value typed, Core.LocalControl.sequence_returned type coreHead,
            heaps, mapsExtended, worldsExtended, frame⟩
  | uninitialized site location origin =>
      cases head with
      | control head =>
          exact ⟨_, _, _, _, _, _, _, terminal_head tailReturns rest contains notTail head (.fault _),
            .uninitialized site location origin, Core.LocalControl.sequence_failure type coreHead,
            heaps, mapsExtended, worldsExtended, frame⟩
      | fault fault =>
          exact ⟨_, _, _, _, _, _, _, fault_head tailReturns rest fault, .uninitialized site location origin,
            Core.LocalControl.sequence_failure type coreHead, heaps, mapsExtended, worldsExtended, frame⟩

/-- A static certificate determines a finite source execution and matching
Core execution for this loop-free fragment. No child evaluation is assumed. -/
theorem Tree.preserves
    {source : TypedSource} {reasonAt : ExpressionId → Core.Word} {scope : SourceCoreLocalCell.Scope}
    {context : Context} {tailReturns : Bool} {statements : List StatementId} {type : Core.Ty} {code : Core.Expr}
    (tree : Tree source reasonAt scope context tailReturns statements type code)
    (program : Program) (evidence : Dynamic.EvidenceEnvironment)
    {environment : Dynamic.Environment} {heap : Dynamic.Heap}
    {coreEnvironment : Core.Environment} {store : Core.Store} {world : Core.StoreTyping}
    {mapping : GeneralHeap.LocationMap} {administrativeContext : Core.Context}
    (environments : GeneralHeap.EnvRepresents mapping world administrativeContext scope environment coreEnvironment)
    (heaps : GeneralHeap.HeapRepresents mapping world heap store) :
    Result tailReturns program context evidence source reasonAt type statements environment heap
      coreEnvironment store code mapping world administrativeContext := by
  induction tree generalizing environment heap coreEnvironment store world mapping with
  | @nil scope context tailReturns type =>
      exact ⟨_, _, _, _, _, _, _, nil_executes tailReturns program context evidence source environment heap,
        .fallthrough environments, Core.LocalControl.fallthrough_evaluates type coreEnvironment store,
        heaps, .refl _, .refl _, .refl _ _⟩
  | @returnUnit scope context tailReturns id node rest metadata form =>
      exact ⟨_, _, _, _, _, _, _, terminal_head tailReturns rest metadata.contains
        (by intro expression; rw [form]; intro impossible; cases impossible)
        (.returnUnit metadata.contains form) (.returned _), .returned .unit rfl,
        Core.LocalControl.returned_evaluates .unit, heaps, .refl _, .refl _, .refl _ _⟩
  | @returnValue scope context tailReturns id node valueId resultType valueCode valueDepth rest metadata form value =>
      obtain ⟨sourceOutcome, result, sourceEvaluation, related, coreEvaluation⟩ :=
        GeneralExpressions.Control.preserves value program context evidence environments heaps
      cases related with
      | value staged typed =>
          cases sourceEvaluation with
          | value sourceEvaluation =>
              exact ⟨_, _, _, _, _, _, _, terminal_head tailReturns rest metadata.contains
                (by intro expression; rw [form]; intro impossible; cases impossible)
                (.returnValue metadata.contains form sourceEvaluation) (.returned _), .returned staged typed,
                Core.LocalControl.returnValue_success resultType coreEvaluation, heaps, .refl _, .refl _, .refl _ _⟩
      | uninitialized site location origin =>
          cases sourceEvaluation with
          | fault sourceFault =>
              exact ⟨_, _, _, _, _, _, _, fault_head tailReturns rest
                (.returnValue metadata.contains form sourceFault), .uninitialized site location origin,
                Core.LocalControl.returnValue_failure resultType coreEvaluation, heaps, .refl _, .refl _, .refl _ _⟩
  | @tailExpression scope context id node valueId resultType valueCode valueDepth metadata form value =>
      obtain ⟨sourceOutcome, result, sourceEvaluation, related, coreEvaluation⟩ :=
        GeneralExpressions.Control.preserves value program context evidence environments heaps
      cases related with
      | value staged typed =>
          cases sourceEvaluation with
          | value sourceEvaluation =>
              exact ⟨_, _, _, _, _, _, _, .control (.tailExpression metadata.contains form sourceEvaluation),
                .returned staged typed, Core.LocalControl.returnValue_success resultType coreEvaluation,
                heaps, .refl _, .refl _, .refl _ _⟩
      | uninitialized site location origin =>
          cases sourceEvaluation with
          | fault sourceFault =>
              exact ⟨_, _, _, _, _, _, _, .fault (.tailExpression metadata.contains form sourceFault),
                .uninitialized site location origin, Core.LocalControl.returnValue_failure resultType coreEvaluation,
                heaps, .refl _, .refl _, .refl _ _⟩
  | @letUninitialized scope context middleContext tailReturns id rest node binder payloadType resultType body
      metadata form binding extension tail ih =>
      have allocated : Dynamic.Heap.Allocates heap binder.scheme.body none
          ⟨heap.cells.length⟩ ⟨heap.cells ++ [{ type := binder.scheme.body, value := none }]⟩ := .append
      obtain ⟨nextEnvironments, nextHeaps⟩ := environments.bind heaps (.uninitialized binding.types) allocated
      obtain ⟨finalContext, outcome, after, result, finalStore, finalMapping, finalWorld,
        tailSource, tailRelated, tailCore, finalHeaps, mapsExtended, extended, tailFrame⟩ := ih nextEnvironments nextHeaps
      have sourceExecution := prepend metadata.contains
        (by intros _ _ expression; rw [form]; intro impossible; cases impossible)
        (.letUninitialized metadata.contains form binding.monomorphic extension allocated) tailSource
      exact ⟨_, _, _, _, _, _, _, sourceExecution, tailRelated,
        Core.LocalSequence.letUninitialized_evaluates payloadType tailCore, finalHeaps,
        GeneralHeap.LocationMap.Extends.trans ⟨_, rfl⟩ mapsExtended,
        (Core.WorldExtends.trans ⟨_, rfl⟩ extended),
        GeneralHeap.AdministrativePreserved.trans (GeneralHeap.AdministrativePreserved.allocate _ _ _) tailFrame⟩
  | @letInitialized scope context middleContext tailReturns id rest node binder payloadType resultType
      initializer initializerCode body initializerDepth metadata form binding extension value tail ih =>
      obtain ⟨sourceOutcome, result, sourceEvaluation, related, coreEvaluation⟩ :=
        GeneralExpressions.Control.preserves value program context evidence environments heaps
      cases related with
      | value staged typed =>
          cases sourceEvaluation with
          | value sourceEvaluation =>
              have binderType : binder.scheme.body = SourceStagedValue.sourceType staged :=
                binding.types.source_unique (typed ▸ stagedTypes staged)
              have allocated : Dynamic.Heap.Allocates heap binder.scheme.body (some (StagedValue.toSource staged))
                  ⟨heap.cells.length⟩
                  ⟨heap.cells ++ [{ type := binder.scheme.body, value := some (StagedValue.toSource staged) }]⟩ := .append
              have cell : CellRepresents
                  { type := binder.scheme.body, value := some (StagedValue.toSource staged) }
                  (.inRight .unit (SourceStagedValue.toCore staged)) payloadType := by
                rw [binderType, ← typed]
                exact .initialized staged
              obtain ⟨nextEnvironments, nextHeaps⟩ := environments.bind heaps cell allocated
              obtain ⟨finalContext, outcome, after, result, finalStore, finalMapping, finalWorld,
                tailSource, tailRelated, tailCore, finalHeaps, mapsExtended, extended, tailFrame⟩ := ih nextEnvironments nextHeaps
              have shifted := tail.heapEffects.evaluation_weakenAt tailCore 1 (SourceStagedValue.toCore staged)
              simp only [Core.Environment.insertAt] at shifted
              have sourceExecution := prepend metadata.contains
                (by intros _ _ expression; rw [form]; intro impossible; cases impossible)
                (.letInitialized metadata.contains form sourceEvaluation binding.monomorphic extension allocated) tailSource
              exact ⟨_, _, _, _, _, _, _, sourceExecution, tailRelated,
                Core.LocalSequence.letInitialized_success (Core.LocalControl.controlType resultType) payloadType coreEvaluation shifted,
                finalHeaps, GeneralHeap.LocationMap.Extends.trans ⟨_, rfl⟩ mapsExtended,
                (Core.WorldExtends.trans ⟨_, rfl⟩ extended),
                GeneralHeap.AdministrativePreserved.trans (GeneralHeap.AdministrativePreserved.allocate _ _ _) tailFrame⟩
      | uninitialized site location origin =>
          cases sourceEvaluation with
          | fault sourceFault =>
              exact ⟨_, _, _, _, _, _, _, fault_head tailReturns rest
                (.letInitializer metadata.contains form binding.monomorphic sourceFault), .uninitialized site location origin,
                Core.LocalSequence.letInitialized_failure (Core.LocalControl.controlType resultType) payloadType coreEvaluation,
                heaps, .refl _, .refl _, .refl _ _⟩
  | @discard scope context tailReturns id rest node nodeType valueId valueType resultType valueCode body valueDepth semicolon
      metadata form notTail statementType value tail ih =>
      obtain ⟨sourceOutcome, result, sourceEvaluation, related, coreEvaluation⟩ :=
        GeneralExpressions.Control.preserves value program context evidence environments heaps
      cases related with
      | value staged typed =>
          cases sourceEvaluation with
          | value sourceEvaluation =>
              obtain ⟨finalContext, outcome, after, result, finalStore, finalMapping, finalWorld,
                tailSource, tailRelated, tailCore, finalHeaps, mapsExtended, extended, tailFrame⟩ := ih environments heaps
              have notTailForm : tailReturns = true → rest = [] → ∀ expression, node.form ≠ .expression expression false := by
                intro isFunction empty expression same
                rw [form] at same
                cases same
                simp [isFunction, empty] at notTail
              have sourceExecution := prepend metadata.contains notTailForm
                (.expression metadata.contains form sourceEvaluation) tailSource
              exact ⟨_, _, _, _, _, _, _, sourceExecution, tailRelated,
                Core.LocalSequence.discard_success (Core.LocalControl.controlType resultType) coreEvaluation
                  (tail.heapEffects.evaluation_weakenAt_zero tailCore (SourceStagedValue.toCore staged)),
                finalHeaps, mapsExtended, extended, tailFrame⟩
      | uninitialized site location origin =>
          cases sourceEvaluation with
          | fault sourceFault =>
              exact ⟨_, _, _, _, _, _, _, fault_head tailReturns rest (.expression metadata.contains form sourceFault),
                .uninitialized site location origin,
                Core.LocalSequence.discard_failure (Core.LocalControl.controlType resultType) coreEvaluation,
                heaps, .refl _, .refl _, .refl _ _⟩
  | @assign scope context tailReturns id rest node assignment index payloadType resultType rhs rhsCode body rhsDepth
      metadata form target value tail ih =>
      obtain ⟨sourceOutcome, result, sourceEvaluation, related, coreEvaluation⟩ :=
        GeneralExpressions.Control.preserves value program context evidence environments heaps
      cases related with
      | value staged typed =>
          cases sourceEvaluation with
          | value sourceEvaluation =>
              obtain ⟨coreLocation, updatedHeap, updatedStore, assignmentSource, lookup, ⟨oldValue, readable⟩,
                written, updatedHeaps, updatedEnvironments, updatedFrame⟩ := equal_assignment environments heaps
                  target.slot target.bare staged typed sourceEvaluation
              obtain ⟨finalContext, outcome, after, result, finalStore, finalMapping, finalWorld,
                tailSource, tailRelated, tailCore, finalHeaps, mapsExtended, extended, tailFrame⟩ := ih updatedEnvironments updatedHeaps
              have rhsShifted := (GeneralExpressions.Control.readOnly value).evaluation_weakenAt_zero coreEvaluation
                (.cellRef (Core.OptionalCell.cellType payloadType) coreLocation)
              have shifted := weaken_three tail.heapEffects tailCore
                (.cellRef (Core.OptionalCell.cellType payloadType) coreLocation) (SourceStagedValue.toCore staged)
              have sourceExecution := prepend metadata.contains
                (by intros _ _ expression; rw [form]; intro impossible; cases impossible)
                (.assignValue metadata.contains form assignmentSource) tailSource
              exact ⟨_, _, _, _, _, _, _, sourceExecution, tailRelated,
                Core.LocalSequence.assign_success (Core.LocalControl.controlType resultType) (.var lookup)
                  rhsShifted readable written shifted, finalHeaps, mapsExtended, extended, updatedFrame.trans tailFrame⟩
      | uninitialized site location origin =>
          cases sourceEvaluation with
          | fault sourceFault =>
              obtain ⟨targetLocation, coreTarget, cell, current, sourceLookup, coreLookup, _, read, _, cellRelated⟩ :=
                environments.lookup_heap heaps target.slot
              let captured : Dynamic.ResolvedPlace := {
                location := targetLocation, rootType := cell.type, valueType := assignment.target.type,
                projections := [], selected := cell.value
              }
              have resolved : Dynamic.SourcePlaceResolves program context evidence source environment
                  heap assignment.target captured heap := by
                apply Dynamic.SourcePlaceResolves.intro sourceLookup read
                · rw [target.bare]; exact .nil
                · exact read
                · exact cellRelated.rootInitialValue
                · exact .nil
              have rhsShifted := (GeneralExpressions.Control.readOnly value).evaluation_weakenAt_zero coreEvaluation
                (.cellRef (Core.OptionalCell.cellType payloadType) coreTarget)
              exact ⟨_, _, _, _, _, _, _, fault_head tailReturns rest
                (.assignValue metadata.contains form (.rhs resolved sourceFault)), .uninitialized site location origin,
                Core.LocalSequence.assign_failure (Core.LocalControl.controlType resultType) (.var coreLookup) rhsShifted,
                heaps, .refl _, .refl _, .refl _ _⟩
  | @block scope context tailReturns id rest node nodeType statements resultType blockCode body
      metadata form block tail blockIH tailIH =>
      obtain ⟨finalContext, outcome, after, result, finalStore, finalMapping, finalWorld,
        blockSource, blockRelated, blockCore, finalHeaps, mapsExtended, extended, frame⟩ := blockIH environments heaps
      exact scoped_sequence metadata.contains (by intro expression; rw [form]; intro impossible; cases impossible)
        environments (scoped_block metadata.contains form blockSource) blockRelated blockCore finalHeaps mapsExtended extended frame
        tail.heapEffects (fun nextEnvironments => tailIH nextEnvironments finalHeaps)
  | @ifThen scope context tailReturns id rest node nodeType condition thenBody elseBody resultType
      conditionCode thenCode elseCode body conditionDepth metadata form conditionTree thenTree elseTree tail thenIH elseIH tailIH =>
      obtain ⟨sourceOutcome, result, sourceEvaluation, related, coreEvaluation⟩ :=
        GeneralExpressions.Control.preserves conditionTree program context evidence environments heaps
      cases related with
      | value staged typed =>
          cases staged with
          | bool boolean =>
              cases sourceEvaluation with
              | value sourceEvaluation =>
                  cases boolean with
                  | true =>
                      obtain ⟨finalContext, outcome, after, result, finalStore, finalMapping, finalWorld,
                        branchSource, branchRelated, branchCore, finalHeaps, mapsExtended, extended, frame⟩ := thenIH environments heaps
                      have conditionalCore := Core.LocalControl.conditional_true (elseBranch := elseCode) resultType coreEvaluation
                        (thenTree.heapEffects.evaluation_weakenAt_zero branchCore (.bool true))
                      exact scoped_sequence metadata.contains (by intro expression; rw [form]; intro impossible; cases impossible)
                        environments (scoped_if_true metadata.contains form sourceEvaluation branchSource) branchRelated conditionalCore
                        finalHeaps mapsExtended extended frame tail.heapEffects (fun nextEnvironments => tailIH nextEnvironments finalHeaps)
                  | false =>
                      obtain ⟨finalContext, outcome, after, result, finalStore, finalMapping, finalWorld,
                        branchSource, branchRelated, branchCore, finalHeaps, mapsExtended, extended, frame⟩ := elseIH environments heaps
                      have conditionalCore := Core.LocalControl.conditional_false (thenBranch := thenCode) resultType coreEvaluation
                        (elseTree.heapEffects.evaluation_weakenAt_zero branchCore (.bool false))
                      exact scoped_sequence metadata.contains (by intro expression; rw [form]; intro impossible; cases impossible)
                        environments (scoped_if_false metadata.contains form sourceEvaluation branchSource) branchRelated conditionalCore
                        finalHeaps mapsExtended extended frame tail.heapEffects (fun nextEnvironments => tailIH nextEnvironments finalHeaps)
          | unit | word | product => cases typed
      | uninitialized site location origin =>
          cases sourceEvaluation with
          | fault sourceFault =>
              exact ⟨_, _, _, _, _, _, _, fault_head tailReturns rest (.ifCondition metadata.contains form sourceFault),
                .uninitialized site location origin,
                Core.LocalControl.sequence_failure resultType (Core.LocalControl.conditional_failure resultType coreEvaluation),
                heaps, .refl _, .refl _, .refl _ _⟩

/-- The function boundary preserves the source fallthrough outcome explicitly.
For non-Unit results the compiler emits its supplied missing-return token; it
does not turn that source outcome into an invented semantic fault. -/
inductive FinishedOutcomeRepresents (program : Program) (evidence : Dynamic.EvidenceEnvironment)
    (source : TypedSource) (mapping : GeneralHeap.LocationMap) (world : Core.StoreTyping)
    (administrativeContext : Core.Context) (reasonAt : ExpressionId → Core.Word) (fellThroughReason : Core.Word) :
    Core.Ty → Dynamic.ControlOutcome → Core.Value → Prop where
  | unitFallthrough {scope environment coreEnvironment}
      (environments : GeneralHeap.EnvRepresents mapping world administrativeContext scope environment coreEnvironment) :
      FinishedOutcomeRepresents program evidence source mapping world administrativeContext reasonAt fellThroughReason
        .unit (.fallthrough environment) (.inRight .word .unit)
  | missingReturn {scope environment coreEnvironment type} (nonUnit : type ≠ .unit)
      (environments : GeneralHeap.EnvRepresents mapping world administrativeContext scope environment coreEnvironment) :
      FinishedOutcomeRepresents program evidence source mapping world administrativeContext reasonAt fellThroughReason
        type (.fallthrough environment) (.inLeft type (.word fellThroughReason))
  | returned (value : SourceStagedValue.Value) {type : Core.Ty} (typed : SourceStagedValue.coreType value = type) :
      FinishedOutcomeRepresents program evidence source mapping world administrativeContext reasonAt fellThroughReason
        type (.returned (StagedValue.toSource value)) (.inRight .word (SourceStagedValue.toCore value))
  | uninitialized (site : ExpressionId) (location : Dynamic.Location) (type : Core.Ty)
      {context : Context} {environment : Dynamic.Environment} {heap : Dynamic.Heap} {root : ExpressionId}
      (origin : ControlExpressions.UninitializedAt program context evidence source environment heap root site location) :
      FinishedOutcomeRepresents program evidence source mapping world administrativeContext reasonAt fellThroughReason
        type (.fault (.uninitializedLocation location)) (.inLeft type (.word (reasonAt site)))

/-- The fallback used by the existing executable function compiler. -/
def fallback (type : Core.Ty) (fellThroughReason : Core.Word) : Core.Expr :=
  if type = .unit then Core.LanguageResult.success .unit
  else Core.LanguageResult.failure type (.word fellThroughReason)

theorem Tree.finish_preserves
    {source : TypedSource} {reasonAt : ExpressionId → Core.Word} {scope : SourceCoreLocalCell.Scope}
    {context : Context} {statements : List StatementId} {type : Core.Ty} {flow : Core.Expr}
    (tree : Tree source reasonAt scope context true statements type flow)
    (fellThroughReason : Core.Word) (program : Program) (evidence : Dynamic.EvidenceEnvironment)
    {environment : Dynamic.Environment} {heap : Dynamic.Heap}
    {coreEnvironment : Core.Environment} {store : Core.Store} {world : Core.StoreTyping}
    {mapping : GeneralHeap.LocationMap} {administrativeContext : Core.Context}
    (environments : GeneralHeap.EnvRepresents mapping world administrativeContext scope environment coreEnvironment)
    (heaps : GeneralHeap.HeapRepresents mapping world heap store) :
    ∃ finalContext outcome after result finalStore finalMapping finalWorld,
      Dynamic.FunctionStatementsExecuteOutcome program context evidence source environment heap statements finalContext outcome after ∧
      FinishedOutcomeRepresents program evidence source finalMapping finalWorld administrativeContext reasonAt fellThroughReason
        type outcome result ∧
      Core.Evaluates coreEnvironment store (Core.LocalControl.finish type flow (fallback type fellThroughReason)) result finalStore ∧
      GeneralHeap.HeapRepresents finalMapping finalWorld after finalStore ∧
      GeneralHeap.LocationMap.Extends mapping finalMapping ∧ Core.WorldExtends world finalWorld ∧
      GeneralHeap.AdministrativePreserved mapping store finalMapping finalStore := by
  obtain ⟨finalContext, outcome, after, result, finalStore, finalMapping, finalWorld,
    sourceEvaluation, related, coreEvaluation, finalHeaps, mapsExtended, worldsExtended, frame⟩ :=
    tree.preserves program evidence environments heaps
  cases related with
  | fallthrough finalEnvironments =>
      by_cases unitType : type = .unit
      · subst type
        refine ⟨_, _, _, _, _, _, _, sourceEvaluation, .unitFallthrough finalEnvironments,
          Core.LocalControl.finish_fallthrough .unit coreEvaluation ?_, finalHeaps, mapsExtended, worldsExtended, frame⟩
        simp only [fallback, ↓reduceIte, Core.LanguageResult.success, Core.Expr.weakenAt]
        exact .inRight .unit
      · refine ⟨_, _, _, _, _, _, _, sourceEvaluation, .missingReturn unitType finalEnvironments,
          Core.LocalControl.finish_fallthrough type coreEvaluation ?_, finalHeaps, mapsExtended, worldsExtended, frame⟩
        simp only [fallback, unitType, ↓reduceIte, Core.LanguageResult.failure, Core.Expr.weakenAt]
        exact .inLeft .word
  | returned value typed =>
      exact ⟨_, _, _, _, _, _, _, sourceEvaluation, .returned value typed,
        Core.LocalControl.finish_returned type coreEvaluation, finalHeaps, mapsExtended, worldsExtended, frame⟩
  | uninitialized site location origin =>
      exact ⟨_, _, _, _, _, _, _, sourceEvaluation, .uninitialized site location type origin,
        Core.LocalControl.finish_failure type coreEvaluation, finalHeaps, mapsExtended, worldsExtended, frame⟩

theorem Tree.hasType_with_administrative
    {source : TypedSource} {reasonAt : ExpressionId → Core.Word} {scope : SourceCoreLocalCell.Scope}
    {context : Context} {tailReturns : Bool} {statements : List StatementId} {type : Core.Ty} {flow : Core.Expr}
    (tree : Tree source reasonAt scope context tailReturns statements type flow)
    (wellFormed : Core.Ty.WellFormed [] type) (administrativeContext : Core.Context) :
    Core.HasType (SourceCoreLocalCell.coreContext scope ++ administrativeContext) flow (Core.LocalControl.resultType type) := by
  have respects : Core.Renaming.Respects Core.Renaming.id (SourceCoreLocalCell.coreContext scope)
      (SourceCoreLocalCell.coreContext scope ++ administrativeContext) := by
    intro index foundType found
    change (SourceCoreLocalCell.coreContext scope ++ administrativeContext)[index]? = some foundType
    rw [List.getElem?_append_left (List.getElem?_eq_some_iff.mp found).1]
    exact found
  simpa using (tree.hasType wellFormed).rename respects

theorem Tree.finish_hasType
    {source : TypedSource} {reasonAt : ExpressionId → Core.Word} {scope : SourceCoreLocalCell.Scope}
    {context : Context} {statements : List StatementId} {type : Core.Ty} {flow : Core.Expr}
    (tree : Tree source reasonAt scope context true statements type flow)
    (wellFormed : Core.Ty.WellFormed [] type) (administrativeContext : Core.Context) (fellThroughReason : Core.Word) :
    Core.HasType (SourceCoreLocalCell.coreContext scope ++ administrativeContext)
      (Core.LocalControl.finish type flow (fallback type fellThroughReason)) (Core.LanguageResult.resultType type) := by
  apply Core.LocalControl.finish_hasType wellFormed (tree.hasType_with_administrative wellFormed administrativeContext)
  unfold fallback
  split
  · rename_i unitType
    subst type
    exact Core.LanguageResult.success_hasType .unit
  · exact Core.LanguageResult.failure_hasType wellFormed .word

end Solcore.SourceSemantics.CoreLowering.ControlStatements
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.ControlStatementBridge
/-! Actual accepted scoped-control lowering implies independent source/Core
correspondence. Static certificates and all child evaluations are extracted,
not supplied by the caller. This is the finite, loop-free scalar/product
profile; its administrative heap may contain recursive closures. -/

set_option autoImplicit false

namespace Solcore.SourceSemantics.CoreLowering.ControlStatements

open Frontend Frontend.SourceInference BasicStatements

theorem lowerFlowStatements_run_preserves
    {fuel : Nat} {source : TypedSource} {scope : SourceCoreLocalCell.Scope}
    {context : Context} {statements : List StatementId} {type : Core.Ty}
    {reasonAt : ExpressionId → Core.Word} {tailReturns : Bool} {code : Core.Expr}
    (aligned : ScopeContextAligned scope context) (unique : NodeOccurrencesUnique source)
    (accepted : SourceCoreControl.lowerFlowStatementsWithReasons fuel source scope statements type reasonAt tailReturns = .ok code)
    (wellFormed : Core.Ty.WellFormed [] type) (program : Program) (evidence : Dynamic.EvidenceEnvironment)
    {environment : Dynamic.Environment} {heap : Dynamic.Heap}
    {coreEnvironment : Core.Environment} {store : Core.Store} {world : Core.StoreTyping}
    {mapping : GeneralHeap.LocationMap} {administrativeContext : Core.Context}
    (environments : GeneralHeap.EnvRepresents mapping world administrativeContext scope environment coreEnvironment)
    (heaps : GeneralHeap.HeapRepresents mapping world heap store) :
    Core.infer? (SourceCoreLocalCell.coreContext scope ++ administrativeContext) code = some (Core.LocalControl.resultType type) ∧
    ∃ finalContext outcome after result finalStore finalMapping finalWorld required,
      Executes tailReturns program context evidence source environment heap statements finalContext outcome after ∧
      OutcomeRepresents program evidence source finalMapping finalWorld administrativeContext reasonAt type outcome result ∧
      GeneralHeap.HeapRepresents finalMapping finalWorld after finalStore ∧
      GeneralHeap.LocationMap.Extends mapping finalMapping ∧ Core.WorldExtends world finalWorld ∧
      GeneralHeap.EnvRepresents finalMapping finalWorld administrativeContext scope environment coreEnvironment ∧
      GeneralHeap.AdministrativePreserved mapping store finalMapping finalStore ∧
      (∀ runtimeFuel, required ≤ runtimeFuel → Core.runStateful runtimeFuel (.initial code coreEnvironment store) = .done result finalStore) ∧
      (∀ runtimeFuel actual actualStore, Core.runStateful runtimeFuel (.initial code coreEnvironment store) = .done actual actualStore →
        actual = result ∧ actualStore = finalStore) := by
  have tree := tree_of_lowerFlowStatements aligned unique accepted
  obtain ⟨finalContext, outcome, after, result, finalStore, finalMapping, finalWorld,
    sourceExecution, related, coreExecution, finalHeaps, mapsExtended, worldsExtended, frame⟩ :=
    tree.preserves program evidence environments heaps
  obtain ⟨required, completes⟩ := Core.evaluation_runStateful_complete_with_sufficient_fuel coreExecution
  refine ⟨Core.infer_complete (tree.hasType_with_administrative wellFormed administrativeContext),
    finalContext, outcome, after, result, finalStore, finalMapping, finalWorld, required,
    sourceExecution, related, finalHeaps, mapsExtended, worldsExtended,
    environments.extend mapsExtended worldsExtended, frame, completes, ?_⟩
  intro runtimeFuel actual actualStore completed
  exact Core.evaluation_deterministic (Core.runStateful_evaluation_sound completed) coreExecution

/-- The executable function compiler's finished result agrees with source
execution. The relation distinguishes ordinary returns, Unit fallthrough,
non-Unit missing returns, and the provider token of uninitialized reads. -/
theorem lowerStatements_run_preserves
    {fuel : Nat} {source : TypedSource} {scope : SourceCoreLocalCell.Scope}
    {context : Context} {statements : List StatementId} {type : Core.Ty}
    {reasonAt : ExpressionId → Core.Word} {fellThroughReason : Core.Word} {code : Core.Expr}
    (aligned : ScopeContextAligned scope context) (unique : NodeOccurrencesUnique source)
    (accepted : SourceCoreControl.lowerStatementsWithReasons fuel source scope statements type reasonAt fellThroughReason = .ok code)
    (wellFormed : Core.Ty.WellFormed [] type) (program : Program) (evidence : Dynamic.EvidenceEnvironment)
    {environment : Dynamic.Environment} {heap : Dynamic.Heap}
    {coreEnvironment : Core.Environment} {store : Core.Store} {world : Core.StoreTyping}
    {mapping : GeneralHeap.LocationMap} {administrativeContext : Core.Context}
    (environments : GeneralHeap.EnvRepresents mapping world administrativeContext scope environment coreEnvironment)
    (heaps : GeneralHeap.HeapRepresents mapping world heap store) :
    Core.infer? (SourceCoreLocalCell.coreContext scope ++ administrativeContext) code = some (Core.LanguageResult.resultType type) ∧
    ∃ finalContext outcome after result finalStore finalMapping finalWorld required,
      Dynamic.FunctionStatementsExecuteOutcome program context evidence source environment heap statements finalContext outcome after ∧
      FinishedOutcomeRepresents program evidence source finalMapping finalWorld administrativeContext reasonAt fellThroughReason
        type outcome result ∧
      GeneralHeap.HeapRepresents finalMapping finalWorld after finalStore ∧
      GeneralHeap.LocationMap.Extends mapping finalMapping ∧ Core.WorldExtends world finalWorld ∧
      GeneralHeap.EnvRepresents finalMapping finalWorld administrativeContext scope environment coreEnvironment ∧
      GeneralHeap.AdministrativePreserved mapping store finalMapping finalStore ∧
      (∀ runtimeFuel, required ≤ runtimeFuel → Core.runStateful runtimeFuel (.initial code coreEnvironment store) = .done result finalStore) ∧
      (∀ runtimeFuel actual actualStore, Core.runStateful runtimeFuel (.initial code coreEnvironment store) = .done actual actualStore →
        actual = result ∧ actualStore = finalStore) := by
  obtain ⟨flow, same, tree⟩ := tree_of_lowerStatements aligned unique accepted
  change code = Core.LocalControl.finish type flow (fallback type fellThroughReason) at same
  subst code
  obtain ⟨finalContext, outcome, after, result, finalStore, finalMapping, finalWorld,
    sourceExecution, related, coreExecution, finalHeaps, mapsExtended, worldsExtended, frame⟩ :=
    tree.finish_preserves fellThroughReason program evidence environments heaps
  obtain ⟨required, completes⟩ := Core.evaluation_runStateful_complete_with_sufficient_fuel coreExecution
  refine ⟨Core.infer_complete (tree.finish_hasType wellFormed administrativeContext fellThroughReason),
    finalContext, outcome, after, result, finalStore, finalMapping, finalWorld, required,
    sourceExecution, related, finalHeaps, mapsExtended, worldsExtended,
    environments.extend mapsExtended worldsExtended, frame, completes, ?_⟩
  intro runtimeFuel actual actualStore completed
  exact Core.evaluation_deterministic (Core.runStateful_evaluation_sound completed) coreExecution

end Solcore.SourceSemantics.CoreLowering.ControlStatements
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.SourceStagedIntegerStatementsMeaning
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace Solcore.SourceSemantics.CoreLowering.SourceStagedIntegerStatementsMeaning
open Solcore Solcore.Frontend Solcore.Frontend.SourceInference
open Solcore.SourceSemantics Solcore.SourceSemantics.CoreLowering
open SourceCoreElaboration SourceCoreElaboration.Internal SourceStagedClosedEvaluationMeaning

def bindingId (binding : Staged.Binding) : Resolved.LocalId := by
  cases binding with
  | mk binder _ => exact binder.id

theorem lookup_cons (binding : Staged.Binding) (actual : Staged.Environment) (id : Resolved.LocalId) :
    Staged.lookup (binding :: actual) id =
      if bindingId binding = id then some binding else Staged.lookup actual id := by
  change List.find? (fun item => decide (bindingId item = id)) (binding :: actual) =
    if bindingId binding = id then some binding else List.find? (fun item => decide (bindingId item = id)) actual
  by_cases same : bindingId binding = id <;> simp [List.find?, same]

/-- The actual first-match Integer environment tracks the independently
allocated source cell, including lexical shadowing and all old heap cells. -/
theorem EnvironmentRep.bind {actual : Staged.Environment} {environment : Dynamic.Environment}
    {heap : Dynamic.Heap} (binding : Staged.Binding)
    (related : EnvironmentRep actual environment heap)
    {afterEnvironment : Dynamic.Environment} {after : Dynamic.Heap}
    (allocated : Dynamic.Binds environment heap (bindingId binding) .integer
      (some (.integer (bindingValue binding))) afterEnvironment after) :
    EnvironmentRep (binding :: actual) afterEnvironment after := by
  cases allocated with
  | intro allocation =>
    intro id selected found
    rw [lookup_cons] at found
    split at found
    · rename_i same
      have identical := Option.some.inj found
      cases identical
      exact ⟨_, _, same ▸ Dynamic.Environment.LooksUp.head, allocation.reads_new, rfl, rfl⟩
    · rename_i different
      obtain ⟨location, cell, lookup, read, ordinary, value⟩ := related id selected found
      exact ⟨location, cell, .tail different lookup, allocation.preserves_read read, ordinary, value⟩


/-- An actual immutable staged Integer cell carries no generalized closure. -/
def integerCell (value : Int) : Dynamic.Cell :=
  { type := .integer, value := some (.integer value) }

/-- Complete original heap and exact source-ordered appended Integer cells.
This is an allocation invariant, not an escape or whole-pass erasure law. -/
def Extends (before after : Dynamic.Heap) (values : List Int) : Prop :=
  after.cells = before.cells ++ values.map integerCell

namespace Extends

theorem refl (heap : Dynamic.Heap) : Extends heap heap [] := by
  simp [Extends]

theorem trans {before middle after : Dynamic.Heap} {left right : List Int}
    (first : Extends before middle left) (second : Extends middle after right) :
    Extends before after (left ++ right) := by
  simp only [Extends, List.map_append] at *
  rw [second, first, List.append_assoc]

theorem allocate {before middle after : Dynamic.Heap} {values : List Int}
    (extension : Extends before middle values) {value : Int} {location : Dynamic.Location}
    (allocated : Dynamic.Heap.Allocates middle .integer (some (.integer value)) location after) :
    Extends before after (values ++ [value]) := by
  cases allocated
  simpa only [Extends, List.map_append, List.map_cons, List.map_nil,
    List.append_assoc, integerCell] using congrArg (fun cells => cells ++ [integerCell value]) extension

theorem bind {before middle after : Dynamic.Heap} {values : List Int}
    (extension : Extends before middle values) {environment finalEnvironment : Dynamic.Environment}
    {id : Resolved.LocalId} {value : Int}
    (bound : Dynamic.Binds environment middle id .integer (some (.integer value)) finalEnvironment after) :
    Extends before after (values ++ [value]) := by
  cases bound with
  | intro allocated => exact extension.allocate allocated

theorem preserves_read {before after : Dynamic.Heap} {values : List Int}
    (extension : Extends before after values) {location : Dynamic.Location} {cell : Dynamic.Cell}
    (read : Dynamic.Heap.Reads before location cell) : Dynamic.Heap.Reads after location cell := by
  cases read with
  | intro selected =>
      constructor
      rw [extension]
      exact selected.append_left

theorem length_eq {before after : Dynamic.Heap} {values : List Int}
    (extension : Extends before after values) : after.cells.length = before.cells.length + values.length := by
  change after.cells = before.cells ++ values.map integerCell at extension
  rw [extension, List.length_append, List.length_map]

end Extends

/-- Static lexical extensions on the exact accepted tree, with no execution law. -/
inductive BindingsFormed (solved : List SolvedRequirement) (source : TypedSource) :
    Solcore.SourceSemantics.Context → {actual : Staged.Environment} → {execute : Bool} → {fuel : Nat} →
    {roots : List StatementId} → {result : StagedIntegerEvaluation} →
    Staged.Statements.Checked solved source actual execute fuel roots result → Prop where
  | letValue {actual : Staged.Environment} {execute : Bool} {fuel : Nat}
      {statement : StatementId} {rest : List StatementId} {node : StatementNode}
      {binder : TypedBinder} {initializer : ExpressionId} {initial result : StagedIntegerEvaluation}
      {context next : Solcore.SourceSemantics.Context}
      (found : source.lookupStatement? statement = some node)
      (form : node.form = .letDecl binder (some initializer))
      (nodeType : node.type = .unit) (fresh : _)
      (owned : binder.id.owner = source.owner) (mono : binder.scheme.quantified = [])
      (binderType : binder.scheme.body = .integer)
      (initialChecked : Staged.IntegerChecked solved source actual execute fuel initializer initial)
      (bodyChecked : Staged.Statements.Checked solved source (Staged.Statements.bind binder initial.value :: actual) execute fuel rest result)
      (extension : BinderExtends source.owner context binder next)
      (bodyFormed : BindingsFormed solved source next bodyChecked) :
      BindingsFormed solved source context (.letValue found form nodeType fresh owned mono binderType initialChecked bodyChecked)
  | returnValue {actual : Staged.Environment} {execute : Bool} {fuel : Nat}
      {statement : StatementId} {node : StatementNode} {value : ExpressionId}
      {result : StagedIntegerEvaluation} {context : Solcore.SourceSemantics.Context}
      (found : source.lookupStatement? statement = some node)
      (form : node.form = .returnStmt (some value)) (nodeType : node.type = .integer)
      (valueChecked : Staged.IntegerChecked solved source actual execute fuel value result) :
      BindingsFormed solved source context (.returnValue found form nodeType valueChecked)
  | conditional {actual : Staged.Environment} {execute : Bool} {fuel : Nat}
      {statement : StatementId} {node : StatementNode} {condition : ExpressionId}
      {yes no : List StatementId} {guard : StagedBoolEvaluation} {left right : StagedIntegerEvaluation}
      {context : Solcore.SourceSemantics.Context}
      (found : source.lookupStatement? statement = some node)
      (form : node.form = .ifThen condition yes (some no)) (nodeType : node.type = .integer)
      (conditionChecked : Staged.BoolChecked solved source actual execute fuel condition guard)
      (thenChecked : Staged.Statements.Checked solved source actual (execute && guard.value) fuel yes left)
      (elseChecked : Staged.Statements.Checked solved source actual (execute && !guard.value) fuel no right)
      (thenFormed : BindingsFormed solved source context thenChecked)
      (elseFormed : BindingsFormed solved source context elseChecked) :
      BindingsFormed solved source context (.conditional found form nodeType conditionChecked thenChecked elseChecked)
  | block {actual : Staged.Environment} {execute : Bool} {fuel : Nat}
      {statement : StatementId} {node : StatementNode} {body : List StatementId}
      {result : StagedIntegerEvaluation} {context : Solcore.SourceSemantics.Context}
      (found : source.lookupStatement? statement = some node)
      (form : node.form = .block body) (nodeType : node.type = .integer)
      (bodyChecked : Staged.Statements.Checked solved source actual execute fuel body result)
      (bodyFormed : BindingsFormed solved source context bodyChecked) :
      BindingsFormed solved source context (.block found form nodeType bodyChecked)

/-- A lexical binder changes no assumptions or rule catalog used by a
consumed numeric implementation row. -/
theorem usedValid_extend {context next : Solcore.SourceSemantics.Context} {owner : Resolved.DeclarationId}
    {binder : TypedBinder} {solved : List SolvedRequirement} {used : List RequirementId}
    (extension : BinderExtends owner context binder next)
    (valid : UsedValid context solved used) : UsedValid next solved used := by
  cases extension
  intro row proof member consumed evidence
  cases valid row proof member consumed evidence with
  | intro authenticated => exact .intro authenticated


namespace StaticViews
open Solcore Solcore.Frontend Solcore.Frontend.SourceInference
open Solcore.SourceSemantics Solcore.SourceSemantics.CoreLowering
open SourceCoreElaboration SourceCoreElaboration.Internal

theorem checked_nonempty {solved source environment execute fuel statements result}
    (checked : Staged.Statements.Checked solved source environment execute fuel statements result) :
    statements ≠ [] := by
  cases checked <;> simp

theorem typed_cons {source control context final statement tail facts}
    (typed : StatementsHaveType source control context (statement :: tail) final facts)
    (nonempty : tail ≠ []) :
    ∃ middle headFacts tailFacts,
      StatementHasType source control context statement middle headFacts ∧
      StatementsHaveType source control middle tail final tailFacts := by
  cases typed with
  | singleton head => exact False.elim (nonempty rfl)
  | cons head rest => exact ⟨_, _, _, head, rest⟩

theorem typed_singleton {source control context final statement facts}
    (typed : StatementsHaveType source control context [statement] final facts) :
    ∃ headFacts, StatementHasType source control context statement final headFacts := by
  cases typed with
  | singleton head => exact ⟨_, head⟩

private theorem statement_shape {source : TypedSource} {id : StatementId} {node : StatementNode}
    {form : StatementForm} (unique : NodeOccurrencesUnique source)
    (found : source.lookupStatement? id = some node) (sameForm : node.form = form) :
    ∀ other, ContainsStatement source id other → other.form = form := by
  intro other contains
  have same : other = node := Option.some.inj
    ((lookupStatement?_complete unique contains).symm.trans found)
  exact same ▸ sameForm

theorem typed_let {source control context final id facts node binder initializer}
    (unique : NodeOccurrencesUnique source)
    (found : source.lookupStatement? id = some node)
    (form : node.form = .letDecl binder (some initializer))
    (_mono : binder.scheme.quantified = [])
    (typed : StatementHasType source control context id final facts) :
    BinderExtends source.owner context binder final := by
  have shape := statement_shape unique found form
  clear found form
  cases typed <;> have actualForm := shape _ (by assumption) <;> simp_all

theorem typed_if {source control context final id facts node condition yes no}
    (unique : NodeOccurrencesUnique source)
    (found : source.lookupStatement? id = some node)
    (form : node.form = .ifThen condition yes (some no))
    (typed : StatementHasType source control context id final facts) :
    ∃ yesFinal noFinal yesFacts noFacts,
      StatementsHaveType source control context yes yesFinal yesFacts ∧
      StatementsHaveType source control context no noFinal noFacts := by
  have shape := statement_shape unique found form
  clear found form
  cases typed <;> have actualForm := shape _ (by assumption) <;> simp_all
  exact ⟨⟨_, _, by assumption⟩, ⟨_, _, by assumption⟩⟩

theorem typed_block {source control context final id facts node statements}
    (unique : NodeOccurrencesUnique source)
    (found : source.lookupStatement? id = some node)
    (form : node.form = .block statements)
    (typed : StatementHasType source control context id final facts) :
    ∃ innerFinal innerFacts,
      StatementsHaveType source control context statements innerFinal innerFacts := by
  have shape := statement_shape unique found form
  clear found form
  cases typed <;> have actualForm := shape _ (by assumption) <;> simp_all
  exact ⟨_, _, by assumption⟩

end StaticViews

/-- Independent source typing supplies every lexical extension in the actual
checked tree, including branches validated without execution. -/
theorem bindingsFormed_of_typing {solved : List SolvedRequirement} {source : TypedSource}
    {actual : Staged.Environment} {execute : Bool} {fuel : Nat}
    {roots : List StatementId} {result : StagedIntegerEvaluation}
    (checked : Staged.Statements.Checked solved source actual execute fuel roots result)
    (unique : NodeOccurrencesUnique source) {control : ControlContext}
    {context final : Solcore.SourceSemantics.Context} {facts : BodyFacts}
    (typed : StatementsHaveType source control context roots final facts) :
    BindingsFormed solved source context checked := by
  induction checked generalizing context final facts with
  | letValue found form nodeType fresh owned mono binderType initial body ih =>
      obtain ⟨next, headFacts, tailFacts, head, tail⟩ := StaticViews.typed_cons typed (StaticViews.checked_nonempty body)
      exact .letValue found form nodeType fresh owned mono binderType initial body
        (StaticViews.typed_let unique found form mono head) (ih tail)
  | returnValue found form nodeType value => exact .returnValue found form nodeType value
  | conditional found form nodeType condition yes no ihYes ihNo =>
      obtain ⟨headFacts, head⟩ := StaticViews.typed_singleton typed
      obtain ⟨yesFinal, noFinal, yesFacts, noFacts, yesTyped, noTyped⟩ := StaticViews.typed_if unique found form head
      exact .conditional found form nodeType condition yes no (ihYes yesTyped) (ihNo noTyped)
  | block found form nodeType body ih =>
      obtain ⟨headFacts, head⟩ := StaticViews.typed_singleton typed
      obtain ⟨inner, innerFacts, bodyTyped⟩ := StaticViews.typed_block unique found form head
      exact .block found form nodeType body (ih bodyTyped)

/-- Actual execution follows only the selected branch. It preserves every
initial cell and records the exact ordered suffix of allocated Integer cells. -/
theorem formed_meaning {solved : List SolvedRequirement} {source : TypedSource}
    {actual : Staged.Environment} {execute : Bool} {fuel : Nat}
    {roots : List StatementId} {result : StagedIntegerEvaluation}
    {checked : Staged.Statements.Checked solved source actual execute fuel roots result}
    {context : Solcore.SourceSemantics.Context}
    (formed : BindingsFormed solved source context checked) {program : Program}
    {evidence : Dynamic.EvidenceEnvironment} {environment : Dynamic.Environment} {before : Dynamic.Heap}
    (executed : execute = true) (ledger : context.solvedRequirements = solved)
    (environments : EnvironmentRep actual environment before)
    (valid : UsedValid context solved result.consumedRequirements) :
    ∃ final after added,
      Dynamic.StatementsExecute program context evidence source environment before roots final
        (.returned (.integer result.value)) after ∧ Extends before after added := by
  induction formed generalizing environment before with
  | @letValue actual execute fuel statement rest node binder initializer initial result context next found form nodeType fresh owned mono binderType initialChecked bodyChecked extension bodyFormed ih =>
      cases executed
      have initialValid : UsedValid context solved initial.consumedRequirements := valid.mono (by
        intro id member; exact List.mem_append_left _ member)
      have initialEval := (SourceStagedClosedEvaluationMeaning.checked_meaning (program := program) (evidence := evidence) ledger environments fuel).1 initialChecked initialValid
      let location : Dynamic.Location := ⟨before.cells.length⟩
      let middle : Dynamic.Heap := ⟨before.cells ++ [integerCell initial.value]⟩
      let nextEnvironment : Dynamic.Environment := (binder.id, location) :: environment
      have allocation : Dynamic.Heap.Allocates before .integer (some (.integer initial.value)) location middle := .append
      have binding : Dynamic.Binds environment before (bindingId (Staged.Statements.bind binder initial.value)) .integer
          (some (.integer (bindingValue (Staged.Statements.bind binder initial.value)))) nextEnvironment middle := by
        simpa only [bindingId, bindingValue, Staged.Statements.bind] using Dynamic.Binds.intro allocation
      have nextEnvironments := EnvironmentRep.bind (Staged.Statements.bind binder initial.value) environments binding
      have nextLedger := extension.context_fields.2.2.2.2.trans ledger
      have tailValid := usedValid_extend extension (valid.mono (by
        intro id member; exact List.mem_append_right _ member))
      obtain ⟨final, after, added, tailEval, cells⟩ := ih rfl nextLedger nextEnvironments tailValid
      have declaredAllocation : Dynamic.Heap.Allocates before binder.scheme.body
          (some (.integer initial.value)) location middle := by rw [binderType]; exact allocation
      have headEval : Dynamic.StatementExecutes program context evidence source environment before statement next
          (.fallthrough nextEnvironment) middle :=
        .letInitialized (lookupStatement?_sound found) form initialEval mono extension declaredAllocation
      exact ⟨final, after, [initial.value] ++ added, .cons headEval tailEval,
        (Extends.refl before).allocate allocation |>.trans cells⟩
  | returnValue found form nodeType valueChecked =>
      cases executed
      have evaluated := (SourceStagedClosedEvaluationMeaning.checked_meaning (program := program) (evidence := evidence) ledger environments _).1 valueChecked valid
      exact ⟨_, before, [], .terminal (.returnValue (lookupStatement?_sound found) form evaluated) (.returned _), Extends.refl before⟩
  | @conditional actual execute fuel statement node condition yes no guard left right context found form nodeType conditionChecked thenChecked elseChecked thenFormed elseFormed ihYes ihNo =>
      cases executed
      have guardValid : UsedValid context solved guard.consumedRequirements := valid.mono (by
        intro id member; exact List.mem_append_left _ (List.mem_append_left _ member))
      have guardEval := (SourceStagedClosedEvaluationMeaning.checked_meaning (program := program) (evidence := evidence) ledger environments fuel).2.2 conditionChecked guardValid
      cases truth : guard.value with
      | false =>
          have branchValid : UsedValid context solved right.consumedRequirements := valid.mono (by
            intro id member; exact List.mem_append_right _ member)
          obtain ⟨final, after, added, branchEval, cells⟩ := ihNo (by simp [truth]) ledger environments branchValid
          have headEval := Dynamic.StatementExecutes.ifFalseWithElse (lookupStatement?_sound found) form (by simpa only [truth] using guardEval) branchEval
          refine ⟨context, after, added, ?_, cells⟩
          simpa only [truth, Bool.false_eq_true, ↓reduceIte, Dynamic.restoreControl] using Dynamic.StatementsExecute.terminal headEval (.returned _)
      | true =>
          have branchValid : UsedValid context solved left.consumedRequirements := valid.mono (by
            intro id member; exact List.mem_append_left _ (List.mem_append_right _ member))
          obtain ⟨final, after, added, branchEval, cells⟩ := ihYes (by simp [truth]) ledger environments branchValid
          have headEval := Dynamic.StatementExecutes.ifTrue (lookupStatement?_sound found) form (by simpa only [truth] using guardEval) branchEval
          refine ⟨context, after, added, ?_, cells⟩
          simpa only [truth, ↓reduceIte, Dynamic.restoreControl] using Dynamic.StatementsExecute.terminal headEval (.returned _)
  | @block actual execute fuel statement node body result context found form nodeType bodyChecked bodyFormed ih =>
      obtain ⟨final, after, added, bodyEval, cells⟩ := ih executed ledger environments valid
      have headEval := Dynamic.StatementExecutes.block (lookupStatement?_sound found) form bodyEval
      refine ⟨context, after, added, ?_, cells⟩
      simpa only [Dynamic.restoreControl] using Dynamic.StatementsExecute.terminal headEval (.returned _)

end Solcore.SourceSemantics.CoreLowering.SourceStagedIntegerStatementsMeaning

set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.SourceStagedIntegerStatementsMeaning
open Solcore Solcore.Frontend Solcore.Frontend.SourceCoreElaboration.Internal
open Solcore.SourceSemantics
open Solcore.SourceSemantics.CoreLowering.SourceStagedClosedEvaluationMeaning

private theorem lookup_bind (binder : SourceInference.TypedBinder) (value : Int)
    (actual : Staged.Environment) (id : Resolved.LocalId) :
    Staged.lookup (Staged.Statements.bind binder value :: actual) id =
      if binder.id = id then some (Staged.Statements.bind binder value)
      else Staged.lookup actual id := by
  change List.find? _ (Staged.Statements.bind binder value :: actual) = _
  by_cases same : binder.id = id <;> simp [List.find?, Staged.Statements.bind, same] <;> rfl

/-- Inputs are allocated in the original compiler order. The source environment
places later inputs first; freshness in the actual receipt preserves every
previous input lookup despite this reversal. -/
theorem allocate_seen {source : SourceInference.TypedSource} {seen : List Resolved.LocalId}
    {binders : List SourceInference.TypedBinder} {values : List Int} {actual : Staged.Environment}
    (checked : Staged.Statements.InputsChecked source seen binders values actual)
    (environment : Dynamic.Environment) (before : Dynamic.Heap) :
    ∃ finalEnvironment after,
      Dynamic.BindersAllocate environment before binders (values.map Dynamic.Value.integer) finalEnvironment after ∧
      EnvironmentRep actual finalEnvironment after ∧
      after.cells = before.cells ++ values.map integerCell ∧
      (∀ id, id ∈ seen → ∀ location, Dynamic.Environment.LooksUp environment id location →
        Dynamic.Environment.LooksUp finalEnvironment id location) := by
  induction checked generalizing environment before with
  | nil seen =>
    refine ⟨environment, before, .nil environment before, EnvironmentRep.empty environment before, ?_, ?_⟩
    · simp
    · intro id member location found; exact found
  | @cons seen binder rest value values actual owned fresh mono typed tail ih =>
    let location : Dynamic.Location := ⟨before.cells.length⟩
    let middle : Dynamic.Heap := ⟨before.cells ++ [integerCell value]⟩
    have allocate : Dynamic.Heap.Allocates before .integer (some (.integer value)) location middle := .append
    have allocate' : Dynamic.Heap.Allocates before binder.scheme.body (some (.integer value)) location middle := by
      rw [typed]; exact allocate
    obtain ⟨finalEnvironment, after, allocated, represented, cells, preserved⟩ :=
      ih ((binder.id, location) :: environment) middle
    refine ⟨finalEnvironment, after, .cons allocate' allocated, ?_, ?_, ?_⟩
    · intro id binding found
      rw [lookup_bind] at found
      split at found
      · rename_i same
        have sameBinding := Option.some.inj found
        cases sameBinding
        refine ⟨location, integerCell value, ?_, ?_, rfl, rfl⟩
        · exact same ▸ preserved binder.id (by simp) location .head
        · cases allocate.reads_new with
          | intro selected =>
            constructor
            rw [cells]
            exact selected.append_left
      · exact represented id binding found
    · simpa only [middle, List.map_cons, List.append_assoc, List.singleton_append] using cells
    · intro id member oldLocation found
      have different : binder.id ≠ id := by
        intro same
        exact fresh (same ▸ member)
      exact preserved id (by simp [member]) oldLocation (.tail different found)

/-- An accepted input environment has a source allocation from the empty
lexical environment and preserves every original heap cell. -/
theorem allocate {source : SourceInference.TypedSource}
    {binders : List SourceInference.TypedBinder} {values : List Int} {actual : Staged.Environment}
    (checked : Staged.Statements.InputsChecked source [] binders values actual)
    (before : Dynamic.Heap) :
    ∃ environment after,
      Dynamic.BindersAllocate [] before binders (values.map Dynamic.Value.integer) environment after ∧
      EnvironmentRep actual environment after ∧
      after.cells = before.cells ++ values.map integerCell := by
  obtain ⟨environment, after, allocated, represented, cells, _⟩ := allocate_seen checked [] before
  exact ⟨environment, after, allocated, represented, cells⟩

end Solcore.SourceSemantics.CoreLowering.SourceStagedIntegerStatementsMeaning

namespace Solcore.SourceSemantics.CoreLowering.SourceStagedIntegerStatementsMeaning
open Frontend SourceInference SourceCoreElaboration SourceCoreElaboration.Internal
open SourceStagedClosedEvaluationMeaning

/-- Actual acceptance and independent source typing provide the required lexical
extensions. Execution appends only the Integer cells allocated by selected lets. -/
theorem statements_of_accepted
    {program : Program} {context finalTyped : Context} {evidence : Dynamic.EvidenceEnvironment}
    {source : TypedSource} {solved : List SolvedRequirement} {actual : Staged.Environment}
    {environment : Dynamic.Environment} {before : Dynamic.Heap} {fuel : Nat}
    {site : ErrorSite} {reason : ErrorReason} {roots : List StatementId}
    {result : StagedIntegerEvaluation} {control : ControlContext} {facts : BodyFacts}
    (accepted : Staged.Statements.evaluate solved source actual true fuel site reason roots = .ok result)
    (unique : NodeOccurrencesUnique source)
    (typed : StatementsHaveType source control context roots finalTyped facts)
    (ledger : context.solvedRequirements = solved)
    (environments : EnvironmentRep actual environment before)
    (valid : UsedValid context solved result.consumedRequirements) :
    Staged.Statements.Checked solved source actual true fuel roots result ∧
      ∃ final after added,
        Dynamic.StatementsExecute program context evidence source environment before roots final
          (.returned (.integer result.value)) after ∧ Extends before after added := by
  have checked := Staged.Statements.checked accepted
  exact ⟨checked, formed_meaning (bindingsFormed_of_typing checked unique typed) rfl ledger environments valid⟩

private theorem roots_filterMap {roots : List StatementId} {sourceRoots : List NodeId}
    (same : roots.map NodeId.statement = sourceRoots) :
    (sourceRoots.filterMap fun root => match root with
      | .statement statement => some statement | .expression _ => none) = roots := by
  subst sourceRoots
  induction roots with
  | nil => rfl
  | cons head tail ih => simpa using congrArg (List.cons head) ih

/-- The public reject-calls function evaluator supplies its full validation
receipt and a source execution from the actual ordered input allocation. The
whole original heap remains, followed by inputs and selected let allocations.
This statement does not identify those source-only cells with an erased runtime heap. -/
theorem evaluateStagedIntegerFunction_sound
    {function : CheckedFunction} {arguments : List Int} {value : Int}
    {program : Program} {context : Context} {evidence : Dynamic.EvidenceEnvironment}
    {before : Dynamic.Heap} {facts : BodyFacts}
    (accepted : evaluateStagedIntegerFunction function arguments = .ok value)
    (unique : NodeOccurrencesUnique function.typedBody)
    (typed : BodyHasType function.typedBody context .integer facts)
    (ledger : context.solvedRequirements = function.solvedRequirements)
    (valid : UsedValid context function.solvedRequirements (function.solvedRequirements.map (·.id))) :
    Staged.Statements.FunctionChecked function arguments value ∧
      ∃ environment bound roots final after added,
        roots.map NodeId.statement = function.typedBody.roots ∧
        Dynamic.BindersAllocate [] before function.typedBody.inputs
          (arguments.map Dynamic.Value.integer) environment bound ∧
        Dynamic.StatementsExecute program context evidence function.typedBody environment bound roots final
          (.returned (.integer value)) after ∧ Extends before after (arguments ++ added) := by
  have checked := Staged.Statements.function_checked accepted
  refine ⟨checked, ?_⟩
  cases checked with
  | intro owned arity inferred type inputs roots statements returned reconciled =>
      rename_i actual sourceRoots result
      obtain ⟨environment, bound, allocated, represented, inputCells⟩ := allocate inputs before
      obtain ⟨finalTyped, typed, rootKinds, completes⟩ := typed
      have typed' := (roots_filterMap roots) ▸ typed
      have formed := bindingsFormed_of_typing statements unique typed'
      have used : UsedValid context function.solvedRequirements result.consumedRequirements := by
        intro row proof member consumed actual
        exact valid row proof member (List.mem_map.mpr ⟨row, member, rfl⟩) actual
      obtain ⟨final, after, added, executed, cells⟩ := formed_meaning (program := program)
        (evidence := evidence) formed rfl ledger represented used
      refine ⟨environment, bound, _, final, after, added, roots, allocated, ?_, ?_⟩
      · simpa only [returned] using executed
      · exact (show Extends before bound arguments from inputCells).trans cells

end Solcore.SourceSemantics.CoreLowering.SourceStagedIntegerStatementsMeaning
end
