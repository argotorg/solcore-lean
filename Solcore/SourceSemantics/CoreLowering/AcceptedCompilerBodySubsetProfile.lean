import Solcore.SourceSemantics.CoreLowering.AcceptedCompilerBodyProfile

/-! Flat statement membership closes an actual inner compiler tree. The checked
set excludes unrelated outer statements and retains every loop child and root. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2400000
namespace Solcore.SourceSemantics.CoreLowering.AcceptedCompilerBodySubsetProfile
open Core Frontend SourceInference AcceptedNamedBodyFlow
open AcceptedCompilerBodyProfile (StatementReady HasReturn returns)

/-- Membership is computed from original forms and expression operands. -/
def ids (source : TypedSource) (expressions : List ExpressionId) : List StatementId :=
  source.nodes.filterMap fun node => match node with
    | .expression _ => none
    | .statement statement =>
        if (AcceptedCompilerBodyProfile.statement? source (fun id => id ∈ expressions) statement).isSome then
          some statement.id else none

def LoopEdges (source : TypedSource) (expressions : List ExpressionId) (node : StatementNode) : Prop :=
  match node.form with
  | .block body | .whileLoop _ body => ∀ id ∈ body, id ∈ ids source expressions
  | .ifThen _ left right =>
      (∀ id ∈ left, id ∈ ids source expressions) ∧
      (∀ id ∈ right.getD [], id ∈ ids source expressions)
  | _ => True

def NodeReady (source : TypedSource) (expressions : List ExpressionId) (id : StatementId) : Prop :=
  ∃ node, source.lookupStatement? id = some node ∧
    StatementReady source (fun expression => expression ∈ expressions) node ∧ LoopEdges source expressions node

structure Profile (source : TypedSource) (expressions : List ExpressionId) (roots : List StatementId) : Prop where
  nodes : ∀ id ∈ ids source expressions, NodeReady source expressions id
  rootMembers : ∀ id ∈ roots, id ∈ ids source expressions
  returns : HasReturn source roots

private def allProof? {α : Type} (predicate : α → Prop)
    (check : (item : α) → Option (PLift (predicate item))) :
    (items : List α) → Option (PLift (∀ item ∈ items, predicate item))
  | [] => some ⟨by intro item member; cases member⟩
  | first :: rest => do
      let ⟨head⟩ ← check first
      let ⟨tail⟩ ← allProof? predicate check rest
      pure ⟨by
        intro item member
        rcases List.mem_cons.mp member with same | member
        · exact same ▸ head
        · exact tail item member⟩

private def edges? (source : TypedSource) (expressions : List ExpressionId) (node : StatementNode) :
    Option (PLift (LoopEdges source expressions node)) := by
  cases form : node.form
  case block body =>
    exact if closed : body.all (fun id => decide (id ∈ ids source expressions)) = true then
      some ⟨by
        simp only [LoopEdges, form]
        exact fun id member => of_decide_eq_true (List.all_eq_true.mp closed id member)⟩ else none
  case ifThen condition left right =>
    exact if first : left.all (fun id => decide (id ∈ ids source expressions)) = true then
      if second : (right.getD []).all (fun id => decide (id ∈ ids source expressions)) = true then
        some ⟨by
          simp only [LoopEdges, form]
          exact ⟨fun id member => of_decide_eq_true (List.all_eq_true.mp first id member),
            fun id member => of_decide_eq_true (List.all_eq_true.mp second id member)⟩⟩ else none
    else none
  case whileLoop condition body =>
    exact if closed : body.all (fun id => decide (id ∈ ids source expressions)) = true then
      some ⟨by
        simp only [LoopEdges, form]
        exact fun id member => of_decide_eq_true (List.all_eq_true.mp closed id member)⟩ else none
  all_goals exact some ⟨by simp only [LoopEdges, form]⟩

private def node? (source : TypedSource) (expressions : List ExpressionId) (id : StatementId) :
    Option (PLift (NodeReady source expressions id)) := do
  match found : source.lookupStatement? id with
  | none => none
  | some node =>
    let ⟨ready⟩ ← AcceptedCompilerBodyProfile.statement? source (fun expression => expression ∈ expressions) node
    let ⟨edges⟩ ← edges? source expressions node
    pure ⟨⟨node, found, ready, edges⟩⟩

/-- Every chosen original node, loop body and initial body root is checked.
No recursive body grammar is an input or a result of this finite check. -/
def validate (source : TypedSource) (expressions : List ExpressionId) (roots : List StatementId) :
    Option (PLift (Profile source expressions roots)) := do
  let ⟨nodes⟩ ← allProof? (NodeReady source expressions) (node? source expressions) (ids source expressions)
  if present : roots.all (fun id => decide (id ∈ ids source expressions)) = true then
    let ⟨returns⟩ ← AcceptedCompilerBodyProfile.hasReturn? source roots
    pure ⟨⟨nodes, fun id member => of_decide_eq_true (List.all_eq_true.mp present id member), returns⟩⟩
  else none

theorem Profile.at {source : TypedSource} {expressions : List ExpressionId} {roots : List StatementId}
    (profile : Profile source expressions roots) {id : StatementId} {node : StatementNode}
    (present : id ∈ ids source expressions) (found : source.lookupStatement? id = some node) :
    StatementReady source (fun expression => expression ∈ expressions) node ∧ LoopEdges source expressions node := by
  obtain ⟨actual, lookup, ready⟩ := profile.nodes id present
  cases Option.some.inj (lookup.symm.trans found)
  exact ready

private theorem expanded_of_ready {source : TypedSource} {expressions : List ExpressionId}
    {node : StatementNode} (ready : StatementReady source (fun id => id ∈ expressions) node) :
    expanded node.form = true := by
  cases form : node.form <;> simp_all [StatementReady, AcceptedNamedBodyFlow.expanded]

private theorem facts_general {policy : SourceCoreLoops.Policy} {checked : SourceCoreCompatibleCatalog.Checked}
    {source : TypedSource} {result : Ty} {reasonAt : ExpressionId → Word}
    {mode : Bool} {escaped : Word} {fuel : Nat} {scope : SourceCoreLocalCell.Scope}
    {statements originalRoots : List StatementId} {code : Expr} {expressionIds : List ExpressionId}
    (tree : Tree policy source result reasonAt mode escaped fuel scope statements code)
    (readPolicy : policy.readStatement = SourceCoreCompatibleDataExpressions.readStatement checked)
    (profile : Profile source expressionIds originalRoots) (ready : tree.Ready)
    (present : ∀ id ∈ statements, id ∈ ids source expressionIds)
    (finish : mode = false ∨ HasReturn source statements) :
    tree.closed = true ∧
      (∀ binding ∈ tree.bindings, binding.binder.scheme.quantified = []) ∧
      (∀ child ∈ tree.children, child.expression ∈ expressionIds) := by
  induction tree with
  | @nil actualMode _ _ _ =>
      have modeFalse : actualMode = false := by
        rcases finish with same | ⟨id, member, _⟩
        · exact same
        · cases member
      simp [Tree.closed, Tree.bindings, Tree.children, modeFalse]
  | returning read form statementType child generated childType =>
      have original := (profile.at (present _ List.mem_cons_self) (read_found (readPolicy ▸ read))).1
      simp only [StatementReady, form] at original
      exact ⟨rfl, by simp [Tree.bindings], by simpa [Tree.children] using original⟩
  | returnUnit => simp [Tree.closed, Tree.bindings, Tree.children]
  | initialized read form statementType projected child generated childType remaining allocated ih =>
      have found := read_found (readPolicy ▸ read)
      have original := (profile.at (present _ List.mem_cons_self) found).1
      simp only [StatementReady, form, Option.toList_some, List.mem_singleton] at original
      have next := ih ready (fun id member => present id (List.mem_cons_of_mem _ member)) (finish.elim Or.inl (fun h => Or.inr (h.tail found (by simp [form, returns]))))
      refine ⟨next.1, ?_, ?_⟩
      · intro binding member
        rcases List.mem_cons.mp member with rfl | member
        · exact original.1
        · exact next.2.1 binding member
      · intro actual member
        rcases List.mem_cons.mp member with rfl | member
        · exact original.2 _ rfl
        · exact next.2.2 actual member
  | absent read form statementType projected remaining allocated ih =>
      have found := read_found (readPolicy ▸ read)
      have original := (profile.at (present _ List.mem_cons_self) found).1
      simp only [StatementReady, form] at original
      have next := ih ready (fun id member => present id (List.mem_cons_of_mem _ member)) (finish.elim Or.inl (fun h => Or.inr (h.tail found (by simp [form, returns]))))
      refine ⟨next.1, ?_, next.2.2⟩
      intro binding member
      rcases List.mem_cons.mp member with rfl | member
      · exact original.1
      · exact next.2.1 binding member
  | assigning read form statementType remaining assigned ih =>
      have original := (profile.at (present _ List.mem_cons_self) (read_found (readPolicy ▸ read))).1
      simp only [StatementReady, form] at original
      exact False.elim (ready.1 original.1)
  | assigned read form statementType remaining receipt targetType ih =>
      have found := read_found (readPolicy ▸ read)
      have original := (profile.at (present _ List.mem_cons_self) found).1
      simp only [StatementReady, form] at original
      have next := ih ready (fun id member => present id (List.mem_cons_of_mem _ member)) (finish.elim Or.inl (fun h => Or.inr (h.tail found (by simp [form, returns]))))
      refine ⟨next.1, next.2.1, ?_⟩
      intro actual member
      rcases List.mem_cons.mp member with rfl | member
      · exact original.2
      · exact next.2.2 actual member
  | discard read form child generated statementType remaining tailIH =>
      have found := read_found (readPolicy ▸ read)
      have original := (profile.at (present _ List.mem_cons_self) found).1
      simp only [StatementReady, form] at original
      have next := tailIH ready (fun id member => present id (List.mem_cons_of_mem _ member)) (finish.elim Or.inl (fun h => Or.inr (h.tail found (by simp [form, returns]))))
      refine ⟨next.1, next.2.1, ?_⟩
      intro actual member
      rcases List.mem_cons.mp member with rfl | member
      · exact original.2
      · exact next.2.2 actual member
  | block read form inner remaining innerIH tailIH =>
      have found := read_found (readPolicy ▸ read)
      have edges := (profile.at (present _ List.mem_cons_self) found).2
      simp only [LoopEdges, form] at edges
      have inside := innerIH ready.1 edges (Or.inl rfl)
      have next := tailIH ready.2 (fun id member => present id (List.mem_cons_of_mem _ member)) (finish.elim Or.inl (fun h => Or.inr (h.tail found (by simp [form, returns]))))
      refine ⟨by simp only [Tree.closed, inside.1, next.1, Bool.and_true], ?_, ?_⟩
      · intro binding member
        rcases List.mem_append.mp member with member | member
        · exact inside.2.1 binding member
        · exact next.2.1 binding member
      · intro actual member
        rcases List.mem_append.mp member with member | member
        · exact inside.2.2 actual member
        · exact next.2.2 actual member
  | conditional read form child generated conditionType left right remaining leftIH rightIH tailIH =>
      have found := read_found (readPolicy ▸ read)
      have original := (profile.at (present _ List.mem_cons_self) found).1
      simp only [StatementReady, form] at original
      have edges := (profile.at (present _ List.mem_cons_self) found).2
      simp only [LoopEdges, form] at edges
      have first := leftIH ready.1 edges.1 (Or.inl rfl)
      have second := rightIH ready.2.1 edges.2 (Or.inl rfl)
      have next := tailIH ready.2.2 (fun id member => present id (List.mem_cons_of_mem _ member)) (finish.elim Or.inl (fun h => Or.inr (h.tail found (by simp [form, returns]))))
      refine ⟨by simp [Tree.closed, original.1, first.1, second.1, next.1], ?_, ?_⟩
      · intro binding member
        simp only [Tree.bindings, List.mem_append] at member
        rcases member with (member | member) | member
        · exact first.2.1 binding member
        · exact second.2.1 binding member
        · exact next.2.1 binding member
      · intro actual member
        rcases List.mem_cons.mp member with rfl | member
        · exact original.2
        · simp only [List.mem_append] at member
          rcases member with (member | member) | member
          · exact first.2.2 actual member
          · exact second.2.2 actual member
          · exact next.2.2 actual member
  | whileLoop read form statementType child generated conditionType inner remaining innerIH tailIH =>
      have found := read_found (readPolicy ▸ read)
      have original := (profile.at (present _ List.mem_cons_self) found).1
      simp only [StatementReady, form] at original
      have edges := (profile.at (present _ List.mem_cons_self) found).2
      simp only [LoopEdges, form] at edges
      have inside := innerIH ready.1 edges (Or.inl rfl)
      have next := tailIH ready.2 (fun id member => present id (List.mem_cons_of_mem _ member)) (finish.elim Or.inl (fun h => Or.inr (h.tail found (by simp [form, returns]))))
      refine ⟨by simp only [Tree.closed, inside.1, next.1, Bool.and_true], ?_, ?_⟩
      · intro binding member
        rcases List.mem_append.mp member with member | member
        · exact inside.2.1 binding member
        · exact next.2.1 binding member
      · intro actual member
        rcases List.mem_cons.mp member with rfl | member
        · exact original
        · rcases List.mem_append.mp member with member | member
          · exact inside.2.2 actual member
          · exact next.2.2 actual member
  | boundary read outside accepted =>
      have checked := (profile.at (present _ List.mem_cons_self) (read_found (readPolicy ▸ read))).1
      have original := expanded_of_ready checked
      rw [outside] at original
      cases original

/-- Actual compiler recursion supplies the body shape and lexical bindings.
The finite subset check identifies only original nodes and operand membership. -/
theorem Profile.facts {source : TypedSource} {expressions : List ExpressionId} {statements : List StatementId}
    (profile : Profile source expressions statements)
    {policy : SourceCoreLoops.Policy} {checked : SourceCoreCompatibleCatalog.Checked}
    {result : Ty} {reasonAt : ExpressionId → Word} {escaped : Word} {fuel : Nat}
    {scope : SourceCoreLocalCell.Scope} {code : Expr}
    (tree : Tree policy source result reasonAt true escaped fuel scope statements code)
    (readPolicy : policy.readStatement = SourceCoreCompatibleDataExpressions.readStatement checked)
    (ready : tree.Ready) :
    tree.closed = true ∧
      (∀ binding ∈ tree.bindings, binding.binder.scheme.quantified = []) ∧
      (∀ child ∈ tree.children, child.expression ∈ expressions) :=
  facts_general tree readPolicy profile ready profile.rootMembers (.inr profile.returns)

end Solcore.SourceSemantics.CoreLowering.AcceptedCompilerBodySubsetProfile
