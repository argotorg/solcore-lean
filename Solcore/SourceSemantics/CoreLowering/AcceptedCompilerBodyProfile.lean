import Solcore.SourceSemantics.CoreLowering.AcceptedNamedBodySyntax

/-! Flat facts about original statement nodes close the refined compiler tree.
The tree supplies recursion, actual child actions and lexical scopes. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2400000
namespace Solcore.SourceSemantics.CoreLowering.AcceptedCompilerBodyProfile
open Core Frontend SourceInference AcceptedNamedBodyFlow

def returns : StatementForm → Bool
  | .returnStmt _ => true
  | _ => false

def HasReturn (source : TypedSource) (statements : List StatementId) : Prop :=
  ∃ id ∈ statements, ∃ node, source.lookupStatement? id = some node ∧ returns node.form = true

/-- These conditions inspect one original node and its immediate operands. -/
def StatementReady (source : TypedSource) (reached : ExpressionId → Prop)
    (node : StatementNode) : Prop :=
  match node.form with
  | .returnStmt none => True
  | .returnStmt (some expression) => reached expression
  | .letDecl binder initializer =>
      binder.scheme.quantified = [] ∧ ∀ expression ∈ initializer.toList, reached expression
  | .assignValue assignment operator expression => Assignable source assignment operator ∧ reached expression
  | .whileLoop condition _ => reached condition
  | _ => False

structure Profile (source : TypedSource) (reached : ExpressionId → Prop) : Prop where
  nodes : ∀ node, Node.statement node ∈ source.nodes → StatementReady source reached node

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

def assignment? (source : TypedSource) (assignment : AssignmentResolution)
    (operator : Solcore.Syntax.ValueAssignOp) : Option (PLift (Assignable source assignment operator)) := do
  if equal : operator = .equal then
    if bare : assignment.target.projections = [] then
      match found : SourceCoreDataPlaces.rootBinder source assignment.target.root with
      | .error _ => none
      | .ok binder =>
        if typed : binder.scheme.body = assignment.target.type then
          some ⟨⟨equal, bare, by
            intro actual accepted
            cases Except.ok.inj (found.symm.trans accepted)
            exact typed⟩⟩
        else none
    else none
  else none

def statement? (source : TypedSource) (reached : ExpressionId → Prop) [DecidablePred reached]
    (node : StatementNode) : Option (PLift (StatementReady source reached node)) := by
  cases form : node.form
  case returnStmt value =>
    cases value with
    | none => exact some ⟨by simp only [StatementReady, form]⟩
    | some expression =>
      exact if present : reached expression then some ⟨by simpa only [StatementReady, form] using present⟩ else none
  case letDecl binder initializer =>
    exact if mono : binder.scheme.quantified = [] then do
      let ⟨children⟩ ← allProof? reached (fun expression =>
        if present : reached expression then some ⟨present⟩ else none) initializer.toList
      pure ⟨by simpa only [StatementReady, form] using And.intro mono children⟩
    else none
  case assignValue assignment operator expression =>
    exact do
      let ⟨target⟩ ← assignment? source assignment operator
      if present : reached expression then
        pure ⟨by simpa only [StatementReady, form] using And.intro target present⟩
      else none
  case whileLoop condition body =>
    exact if present : reached condition then some ⟨by simpa only [StatementReady, form] using present⟩ else none
  all_goals exact none

/-- Every original statement node is inspected once. Expression membership
and assignment layout checks are finite data tests. -/
def validate (source : TypedSource) (reached : ExpressionId → Prop) [DecidablePred reached] :
    Option (PLift (Profile source reached)) := do
  let ⟨nodes⟩ ← allProof?
    (fun node => ∀ statement, node = Node.statement statement → StatementReady source reached statement)
    (fun node => match node with
      | .expression _ => some ⟨by intro statement impossible; cases impossible⟩
      | .statement statement => do
        let ⟨ready⟩ ← statement? source reached statement
        pure ⟨by intro actual same; cases same; exact ready⟩) source.nodes
  pure ⟨⟨fun node member => nodes _ member node rfl⟩⟩

/-- The return check is a flat search through the original outer roots. -/
def hasReturn? (source : TypedSource) : (statements : List StatementId) → Option (PLift (HasReturn source statements))
  | [] => none
  | id :: rest =>
    let tail : Option (PLift (HasReturn source (id :: rest))) := do
      let ⟨next⟩ ← hasReturn? source rest
      pure ⟨by
        obtain ⟨actual, member, node, found, returned⟩ := next
        exact ⟨actual, List.mem_cons_of_mem _ member, node, found, returned⟩⟩
    match found : source.lookupStatement? id with
    | none => tail
    | some node =>
      if returned : returns node.form = true then some ⟨⟨id, List.mem_cons_self, node, found, returned⟩⟩
      else tail

theorem Profile.at {source : TypedSource} {reached : ExpressionId → Prop}
    (profile : Profile source reached) {id : StatementId} {node : StatementNode}
    (found : source.lookupStatement? id = some node) : StatementReady source reached node :=
  profile.nodes node (lookupStatement?_sound found).1

theorem HasReturn.tail {source : TypedSource} {id : StatementId} {rest : List StatementId}
    {node : StatementNode} (found : source.lookupStatement? id = some node)
    (continues : returns node.form = false) (present : HasReturn source (id :: rest)) :
    HasReturn source rest := by
  obtain ⟨actual, member, original, lookup, returned⟩ := present
  rcases List.mem_cons.mp member with same | member
  · subst actual
    cases Option.some.inj (found.symm.trans lookup)
    rw [continues] at returned
    cases returned
  · exact ⟨actual, member, original, lookup, returned⟩

private theorem StatementReady.expanded {source : TypedSource} {reached : ExpressionId → Prop}
    {node : StatementNode} (ready : StatementReady source reached node) : expanded node.form = true := by
  cases form : node.form <;> simp_all [StatementReady, AcceptedNamedBodyFlow.expanded]

/-- The outer sequence retains a return occurrence; loop bodies use their
actual false mode and can end normally. No source-body shape is supplied. -/
theorem facts {policy : SourceCoreLoops.Policy} {checked : SourceCoreCompatibleCatalog.Checked}
    {source : TypedSource} {result : Ty} {reasonAt : ExpressionId → Word}
    {mode : Bool} {escaped : Word} {fuel : Nat} {scope : SourceCoreLocalCell.Scope}
    {statements : List StatementId} {code : Expr} {reached : ExpressionId → Prop}
    (tree : Tree policy source result reasonAt mode escaped fuel scope statements code)
    (readPolicy : policy.readStatement = SourceCoreCompatibleDataExpressions.readStatement checked)
    (profile : Profile source reached) (ready : tree.Ready)
    (finish : mode = false ∨ HasReturn source statements) :
    tree.closed = true ∧
      (∀ binding ∈ tree.bindings, binding.binder.scheme.quantified = []) ∧
      (∀ child ∈ tree.children, reached child.expression) := by
  induction tree with
  | @nil actualMode _ _ _ =>
      have modeFalse : actualMode = false := by
        rcases finish with same | ⟨id, member, _⟩
        · exact same
        · cases member
      simp [Tree.closed, Tree.bindings, Tree.children, modeFalse]
  | returning read form statementType child generated childType =>
      have original := profile.at (read_found (readPolicy ▸ read))
      simp only [StatementReady, form] at original
      exact ⟨rfl, by simp [Tree.bindings], by simpa [Tree.children] using original⟩
  | returnUnit => simp [Tree.closed, Tree.bindings, Tree.children]
  | initialized read form statementType projected child generated childType remaining allocated ih =>
      have found := read_found (readPolicy ▸ read)
      have original := profile.at found
      simp only [StatementReady, form, Option.toList_some, List.mem_singleton] at original
      have next := ih ready (finish.elim Or.inl (fun h => Or.inr (h.tail found (by simp [form, returns]))))
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
      have original := profile.at found
      simp only [StatementReady, form] at original
      have next := ih ready (finish.elim Or.inl (fun h => Or.inr (h.tail found (by simp [form, returns]))))
      refine ⟨next.1, ?_, next.2.2⟩
      intro binding member
      rcases List.mem_cons.mp member with rfl | member
      · exact original.1
      · exact next.2.1 binding member
  | assigning read form statementType remaining assigned ih =>
      have original := profile.at (read_found (readPolicy ▸ read))
      simp only [StatementReady, form] at original
      exact False.elim (ready.1 original.1)
  | assigned read form statementType remaining receipt targetType ih =>
      have found := read_found (readPolicy ▸ read)
      have original := profile.at found
      simp only [StatementReady, form] at original
      have next := ih ready (finish.elim Or.inl (fun h => Or.inr (h.tail found (by simp [form, returns]))))
      refine ⟨next.1, next.2.1, ?_⟩
      intro actual member
      rcases List.mem_cons.mp member with rfl | member
      · exact original.2
      · exact next.2.2 actual member
  | whileLoop read form statementType child generated conditionType inner remaining innerIH tailIH =>
      have found := read_found (readPolicy ▸ read)
      have original := profile.at found
      simp only [StatementReady, form] at original
      have inside := innerIH ready.1 (Or.inl rfl)
      have next := tailIH ready.2 (finish.elim Or.inl (fun h => Or.inr (h.tail found (by simp [form, returns]))))
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
      have original := (profile.at (read_found (readPolicy ▸ read))).expanded
      rw [outside] at original
      cases original

end Solcore.SourceSemantics.CoreLowering.AcceptedCompilerBodyProfile
