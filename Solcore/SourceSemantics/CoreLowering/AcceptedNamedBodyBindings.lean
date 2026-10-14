import Solcore.SourceSemantics.CoreLowering.AcceptedNamedBodySyntax
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedHeaderSourceTyping
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPreparedHeaderPolicies

/-! Original source ownership and statement typing authenticate binders in the
accepted compiler flow. Generalized locals remain an explicit retained boundary. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2400000
namespace Solcore.SourceSemantics.CoreLowering.AcceptedNamedBodyBindings
open Core Frontend SourceInference
open AcceptedNamedBodyFlow

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

private theorem node_receipt {source : TypedSource} {node : StatementNode}
    {binder : TypedBinder}
    (ownership : LocalIdentityOwnership source)
    (member : Node.statement node ∈ source.nodes)
    (defined : binder ∈ nodeBinders (.statement node))
    (mono : binder.scheme.quantified = []) (requirements : binder.schemeRequirements = []) :
    RecursiveNamedStatementSyntaxFacts.BinderReceipt source binder := by
  have declared : binder ∈ SourceCoreDataPlaces.declaredBinders source := by
    apply List.mem_append_right
    exact List.mem_flatMap.mpr ⟨.statement node, member, defined⟩
  have idMem : binder.id ∈ definedLocalIds source :=
    (declared_ids source).subset (List.mem_map.mpr ⟨binder, declared, rfl⟩)
  have owned := ownership.owned binder.id idMem
  have filtered := filter_self ((declared_ids source).nodup ownership.unique) declared
  have inNodes : binder.id ∈ source.nodes.flatMap Node.definedLocalIds := by
    exact List.mem_flatMap.mpr ⟨.statement node, member, (node_ids (.statement node)).subset (List.mem_map.mpr ⟨binder, defined, rfl⟩)⟩
  have disjoint := (List.nodup_append.mp (show
    (source.inputs.map (·.id) ++ source.nodes.flatMap Node.definedLocalIds).Nodup from
    by simpa only [definedLocalIds, ← flatMapNodeDefinedLocalIds_eq_carrier] using ownership.unique)).2.2
  refine ⟨?_, mono, ?_⟩
  · simp [SourceCoreDataPlaces.rootBinder, owned, filtered, mono, requirements, pure, Except.pure]
  · apply Bool.eq_false_iff.mpr
    intro found
    obtain ⟨input, present, same⟩ := List.any_eq_true.mp found
    exact disjoint input.id (List.mem_map.mpr ⟨input, present, rfl⟩)
      binder.id inNodes (of_decide_eq_true same)

private theorem let_receipt {source : TypedSource} {node : StatementNode}
    {binder : TypedBinder} {initializer : Option ExpressionId}
    (ownership : LocalIdentityOwnership source) (member : Node.statement node ∈ source.nodes)
    (form : node.form = .letDecl binder initializer)
    (mono : binder.scheme.quantified = []) (requirements : binder.schemeRequirements = []) :
    RecursiveNamedStatementSyntaxFacts.BinderReceipt source binder :=
  node_receipt ownership member (by simp [nodeBinders, form]) mono requirements

private theorem items_receipts {policy : SourceCoreLoops.Policy} {source : TypedSource}
    {site : SourceCoreElaboration.ErrorSite} {result : Ty} {reasonAt : ExpressionId → Word}
    {next : SourceCoreLocalCell.Scope → Except SourceCoreBasic.Error Expr} {finalScope : SourceCoreLocalCell.Scope}
    {finish : Expr} {fuel scope items code} {node : StatementNode}
    (tree : Items policy source site result reasonAt next finalScope finish fuel scope items code)
    (ownership : LocalIdentityOwnership source) (member : Node.statement node ∈ source.nodes)
    (defined : ∀ binder initializer, ForItemForm.letDecl binder initializer ∈ items → binder ∈ nodeBinders (.statement node))
    {control : ControlContext} {context final : SourceSemantics.Context}
    (typed : ForItemsHaveType source control context items final)
    (monomorphic : ∀ binding ∈ tree.bindings, binding.binder.scheme.quantified = []) :
    ∀ binding ∈ tree.bindings, RecursiveNamedStatementSyntaxFacts.BinderReceipt source binding.binder := by
  induction tree generalizing context final with
  | nil => simp [Items.bindings]
  | absent projected remaining allocated ih =>
    cases typed with
    | cons head tail =>
      cases head with
      | letUninitialized mono _ extension =>
        have receipt := node_receipt ownership member (defined _ _ List.mem_cons_self) mono
          (by cases extension with | intro wellFormed _ => exact wellFormed.monomorphic_requirements_empty mono)
        intro binding present
        rcases List.mem_cons.mp present with rfl | present
        · exact receipt
        · exact ih (fun b e p => defined b e (List.mem_cons_of_mem _ p)) tail
            (fun b p => monomorphic b (List.mem_cons_of_mem _ p)) binding present
  | initialized projected child generated childType remaining allocated ih =>
    have mono := monomorphic ⟨_, _, _, projected⟩ (by simp [Items.bindings])
    cases typed with
    | cons head tail =>
      cases head with
      | letInitialized value _ _ extension =>
        have receipt := node_receipt ownership member (defined _ _ List.mem_cons_self) mono
          (by cases extension with | intro wellFormed _ => exact wellFormed.monomorphic_requirements_empty mono)
        intro binding present
        rcases List.mem_cons.mp present with rfl | present
        · exact receipt
        · exact ih (fun b e p => defined b e (List.mem_cons_of_mem _ p)) tail
            (fun b p => monomorphic b (List.mem_cons_of_mem _ p)) binding present
      | letInitializedGeneralized poly _ _ _ _ => exact False.elim (poly mono)
  | discard _ _ remaining ih | assigning remaining _ ih | assigned remaining _ _ ih =>
    cases typed with
    | cons head tail =>
      exact ih (fun b e p => defined b e (List.mem_cons_of_mem _ p)) tail monomorphic

private theorem head_tail {source : TypedSource} {control : ControlContext}
    {context final : SourceSemantics.Context} {id : StatementId} {rest : List StatementId} {facts : BodyFacts}
    (typed : StatementsHaveType source control context (id :: rest) final facts) :
    ∃ middle headFacts tailFacts, StatementHasType source control context id middle headFacts ∧
      StatementsHaveType source control middle rest final tailFacts := by
  cases typed with
  | singleton head => exact ⟨_, _, _, head, .nil _ _⟩
  | cons head tail => exact ⟨_, _, _, head, tail⟩

private theorem form_at {source : TypedSource} {control : ControlContext}
    {context final : SourceSemantics.Context} {id : StatementId} {facts : StatementFacts} {node : StatementNode}
    (unique : NodeOccurrencesUnique source) (found : source.lookupStatement? id = some node)
    (typed : StatementHasType source control context id final facts) :
    Dynamic.StatementHasType.FormTyping source control context node.form final := by
  obtain ⟨actual, contains, original⟩ := Dynamic.StatementHasType.formTyping typed
  cases Option.some.inj ((lookupStatement?_complete unique contains).symm.trans found)
  exact original

/-- Every actual monomorphic let in the accepted flow has one original declaration.
The source typing derivation supplies its binder requirements; whole-source
ownership prevents any collision with inputs or another retained declaration. -/
theorem of_monomorphic {policy : SourceCoreLoops.Policy} {checked : SourceCoreCompatibleCatalog.Checked}
    {source : TypedSource} {result : Ty} {reasonAt : ExpressionId → Word} {mode : Bool} {escaped : Word}
    {fuel : Nat} {scope : SourceCoreLocalCell.Scope} {statements : List StatementId} {code : Expr}
    (tree : Tree policy source result reasonAt mode escaped fuel scope statements code)
    (readPolicy : policy.readStatement = SourceCoreCompatibleDataExpressions.readStatement checked)
    (unique : NodeOccurrencesUnique source) (ownership : LocalIdentityOwnership source)
    {control : ControlContext} {context final : SourceSemantics.Context} {facts : BodyFacts}
    (typed : StatementsHaveType source control context statements final facts)
    (monomorphic : ∀ binding ∈ tree.bindings, binding.binder.scheme.quantified = []) :
    ∀ binding ∈ tree.bindings, RecursiveNamedStatementSyntaxFacts.BinderReceipt source binding.binder := by
  induction tree generalizing control context final facts with
  | nil | returning | returnUnit | boundary | forBoundary | breaking | continuing =>
      intro binding member
      simp only [Tree.bindings, List.not_mem_nil] at member
  | initialized read form statementType projected child generated childType remaining allocated ih =>
      have found := read_found (readPolicy ▸ read)
      obtain ⟨_, _, _, head, tail⟩ := head_tail typed
      have original := form_at unique found head
      rw [form] at original
      have mono := monomorphic ⟨_, _, _, projected⟩ (by simp [Tree.bindings])
      have requirements : _ := original
      cases requirements with
      | letInitialized _ _ extension =>
        have receipt := let_receipt ownership (lookupStatement?_sound found).1 form mono
          (by cases extension with | intro wellFormed _ => exact wellFormed.monomorphic_requirements_empty mono)
        intro binding member
        rcases List.mem_cons.mp member with rfl | member
        · exact receipt
        · exact ih tail (fun next present => monomorphic next (List.mem_cons_of_mem _ present)) binding member
      | letInitializedGeneralized poly _ _ _ _ => exact False.elim (poly mono)
  | absent read form statementType projected remaining allocated ih =>
      have found := read_found (readPolicy ▸ read)
      obtain ⟨_, _, _, head, tail⟩ := head_tail typed
      have original := form_at unique found head
      rw [form] at original
      cases original with
      | letUninitialized mono extension =>
        have receipt := let_receipt ownership (lookupStatement?_sound found).1 form mono
          (by cases extension with | intro wellFormed _ => exact wellFormed.monomorphic_requirements_empty mono)
        intro binding member
        rcases List.mem_cons.mp member with rfl | member
        · exact receipt
        · exact ih tail (fun next present => monomorphic next (List.mem_cons_of_mem _ present)) binding member

  | assigning _ _ _ _ _ ih | assigned _ _ _ _ _ _ ih | discard _ _ _ _ _ _ ih =>
      obtain ⟨_, _, _, _, tail⟩ := head_tail typed
      exact ih tail monomorphic
  | block read form inner remaining innerIH tailIH =>
      have found := read_found (readPolicy ▸ read)
      obtain ⟨_, _, _, head, tail⟩ := head_tail typed
      have original := form_at unique found head
      rw [form] at original
      cases original with
      | block body =>
        intro binding member
        rcases List.mem_append.mp member with member | member
        · exact innerIH body
            (fun next present => monomorphic next (List.mem_append_left _ present)) binding member
        · exact tailIH tail
            (fun next present => monomorphic next (List.mem_append_right _ present)) binding member
  | conditional read form _ _ _ left right remaining leftIH rightIH tailIH =>
      have found := read_found (readPolicy ▸ read)
      obtain ⟨_, _, _, head, tail⟩ := head_tail typed
      have original := form_at unique found head
      rw [form] at original
      cases original with
      | ifWithoutElse condition body =>
        have first := leftIH body
          (fun binding member => monomorphic binding (by simp [Tree.bindings, member]))
        have second := rightIH (.nil control context)
          (fun binding member => monomorphic binding (by simp [Tree.bindings, member]))
        have next := tailIH tail
          (fun binding member => monomorphic binding (by simp [Tree.bindings, member]))
        intro binding member
        simp only [Tree.bindings, List.mem_append] at member
        rcases member with (member | member) | member
        · exact first binding member
        · exact second binding member
        · exact next binding member
      | ifWithElse condition firstBody secondBody =>
        have first := leftIH firstBody
          (fun binding member => monomorphic binding (by simp [Tree.bindings, member]))
        have second := rightIH secondBody
          (fun binding member => monomorphic binding (by simp [Tree.bindings, member]))
        have next := tailIH tail
          (fun binding member => monomorphic binding (by simp [Tree.bindings, member]))
        intro binding member
        simp only [Tree.bindings, List.mem_append] at member
        rcases member with (member | member) | member
        · exact first binding member
        · exact second binding member
        · exact next binding member
  | whileLoop read form _ _ _ _ inner remaining innerIH tailIH =>
      have found := read_found (readPolicy ▸ read)
      obtain ⟨_, _, _, head, tail⟩ := head_tail typed
      have original := form_at unique found head
      rw [form] at original
      cases original with
      | whileLoop _ body =>
        intro binding member
        rcases List.mem_append.mp member with member | member
        · exact innerIH (control := control.enterLoop) body
            (fun next present => monomorphic next (List.mem_append_left _ present)) binding member
        · exact tailIH tail
            (fun next present => monomorphic next (List.mem_append_right _ present)) binding member

  | forLoop read form _ _ _ _ initial inner after remaining innerIH tailIH =>
      have found := read_found (readPolicy ▸ read)
      obtain ⟨_, _, _, head, tail⟩ := head_tail typed
      have original := form_at unique found head
      rw [form] at original
      cases original with
      | forLoop initTyped condition body postTyped =>
        have initialBindings := items_receipts initial ownership (lookupStatement?_sound found).1
          (fun binder expression present => by
            simp only [nodeBinders, form, List.filterMap_append, List.mem_append]
            exact .inl (List.mem_filterMap.mpr ⟨_, present, rfl⟩)) initTyped
          (fun binding member => monomorphic binding (by simp [Tree.bindings, member]))
        have inside := innerIH body
          (fun binding member => monomorphic binding (by simp [Tree.bindings, member]))
        have postBindings := items_receipts after ownership (lookupStatement?_sound found).1
          (fun binder expression present => by
            simp only [nodeBinders, form, List.filterMap_append, List.mem_append]
            exact .inr (List.mem_filterMap.mpr ⟨_, present, rfl⟩)) postTyped
          (fun binding member => monomorphic binding (by simp [Tree.bindings, member]))
        have next := tailIH tail
          (fun binding member => monomorphic binding (by simp [Tree.bindings, member]))
        intro binding member
        simp only [Tree.bindings, List.mem_append] at member
        rcases member with ((member | member) | member) | member
        · exact initialBindings binding member
        · exact inside binding member
        · exact postBindings binding member
        · exact next binding member

/-- The only unresolved binding condition is exposed on an actual accepted
binding, retaining its original scope, payload and contextual projection. -/
theorem of_tree {policy : SourceCoreLoops.Policy} {checked : SourceCoreCompatibleCatalog.Checked}
    {source : TypedSource} {result : Ty} {reasonAt : ExpressionId → Word} {mode : Bool} {escaped : Word}
    {fuel : Nat} {scope : SourceCoreLocalCell.Scope} {statements : List StatementId} {code : Expr}
    (tree : Tree policy source result reasonAt mode escaped fuel scope statements code)
    (readPolicy : policy.readStatement = SourceCoreCompatibleDataExpressions.readStatement checked)
    (unique : NodeOccurrencesUnique source) (ownership : LocalIdentityOwnership source)
    {control : ControlContext} {context final : SourceSemantics.Context} {facts : BodyFacts}
    (typed : StatementsHaveType source control context statements final facts) :
    (∀ binding ∈ tree.bindings, RecursiveNamedStatementSyntaxFacts.BinderReceipt source binding.binder) ∨
      ∃ binding ∈ tree.bindings, binding.binder.scheme.quantified ≠ [] := by
  classical
  by_cases mono : ∀ binding ∈ tree.bindings, binding.binder.scheme.quantified = []
  · exact .inl (of_monomorphic tree readPolicy unique ownership typed mono)
  · apply Or.inr
    apply Classical.byContradiction
    intro none
    apply mono
    intro binding member
    apply Classical.byContradiction
    intro quantified
    exact none ⟨binding, member, quantified⟩

/-- Header attribution supplies the genuine instantiated source ownership and
statement typing. No declaration, statement-shape or body-execution callback
is an input to the binding extraction. -/
theorem of_header {compiled : SourceCoreUnifiedCompilation.Compiled}
    {row : SourceSpecialization.SpecializedFunction}
    (prepared : RecursiveNamedPublicSpecializationMeaning.Prepared compiled row)
    {instantiation : DeclarationInstantiation}
    {header : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram)}
    (aligned : RecursiveNamedPreparedHeaders.Prepared.HeaderAt prepared instantiation header)
    (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
    {flow : Expr}
    (tree : Tree header.policy header.function.source header.output header.reasonAt true header.escaped
      header.fuel (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2))) header.function.body flow) :
    (∀ binding ∈ tree.bindings, RecursiveNamedStatementSyntaxFacts.BinderReceipt header.function.source binding.binder) ∨
      ∃ binding ∈ tree.bindings, binding.binder.scheme.quantified ≠ [] := by
  obtain ⟨facts, certified⟩ := RecursiveNamedHeaderSourceTyping.certificate header wellFormed
  have ownership : LocalIdentityOwnership header.function.source := by
    rw [header.frame.source]
    exact certified.local_identity_ownership
  obtain ⟨final, facts, typed, _⟩ := RecursiveNamedHeaderSourceTyping.statements header wellFormed
  exact of_tree tree (RecursiveNamedPreparedHeaderPolicies.Prepared.header_read prepared aligned)
    header.unique ownership typed

end Solcore.SourceSemantics.CoreLowering.AcceptedNamedBodyBindings
