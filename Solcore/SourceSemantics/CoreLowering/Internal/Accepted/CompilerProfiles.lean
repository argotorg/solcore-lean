import Solcore.SourceSemantics.CoreLowering.Internal.Accepted.NamedBodies
import Solcore.SourceSemantics.CoreLowering.Internal.Accepted.NamedExpressions

/-!
# Accepted compiler profiles

The finite body, subset and expression profiles over the compiler's acceptance.
-/

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.AcceptedCompilerBodyProfile
/-! Flat facts about original statement nodes close the refined compiler tree.
The tree supplies recursion, actual child actions and lexical scopes. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2400000
namespace Solcore.SourceSemantics.CoreLowering.AcceptedCompilerBodyProfile
open Core Frontend SourceInference AcceptedNamedBodyFlow AcceptedCompilerBodyCompletion

def returns : StatementForm → Bool
  | .returnStmt _ => true
  | _ => false

def HasReturn (source : TypedSource) (statements : List StatementId) : Prop :=
  ∃ id ∈ statements, ∃ node, source.lookupStatement? id = some node ∧ returns node.form = true

/-- Header facts describe one original item and its immediate expression. -/
def HeaderReady (source : TypedSource) (reached : ExpressionId → Prop) : ForItemForm → Prop
  | .letDecl binder initializer => binder.scheme.quantified = [] ∧ ∀ expression ∈ initializer.toList, reached expression
  | .expression expression => reached expression
  | .assignValue assignment operator expression => ValueAssignable source assignment operator ∧
      ∀ child ∈ expression :: DataPlaceKeyOrder.sourceKeys assignment.target.projections, reached child
  | .assignBitNot assignment => UnaryAssignable source assignment ∧
      ∀ child ∈ DataPlaceKeyOrder.sourceKeys assignment.target.projections, reached child

theorem header_forms {source reached items}
    (_ready : ∀ item ∈ items, HeaderReady source reached item) : HeaderForms items := True.intro

/-- These conditions inspect one original node and its immediate operands. -/
def StatementReady (source : TypedSource) (reached : ExpressionId → Prop)
    (node : StatementNode) : Prop :=
  match node.form with
  | .returnStmt none | .breakStmt | .continueStmt => True
  | .returnStmt (some expression) => reached expression
  | .letDecl binder initializer =>
      binder.scheme.quantified = [] ∧ ∀ expression ∈ initializer.toList, reached expression
  | .assignValue assignment operator expression => ValueAssignable source assignment operator ∧
      ∀ child ∈ expression :: DataPlaceKeyOrder.sourceKeys assignment.target.projections, reached child
  | .expression expression _ => reached expression
  | .block _ => True
  | .ifThen condition _ _ => reached condition
  | .matchWith resolution => reached resolution.scrutinee
  | .whileLoop condition _ => reached condition
  | .forLoop initializer condition post _ =>
      (∀ item ∈ initializer, HeaderReady source reached item) ∧ reached condition ∧
      (∀ item ∈ post, HeaderReady source reached item)
  | .assignBitNot assignment => UnaryAssignable source assignment ∧
      ∀ child ∈ DataPlaceKeyOrder.sourceKeys assignment.target.projections, reached child

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
  if profile : operator = .equal ∨ assignment.target.type = .word then
    if bare : assignment.target.projections = [] then
      match found : SourceCoreDataPlaces.rootBinder source assignment.target.root with
      | .error _ => none
      | .ok binder =>
        if typed : binder.scheme.body = assignment.target.type then
          some ⟨⟨profile, bare, by
            intro actual accepted
            cases Except.ok.inj (found.symm.trans accepted)
            exact typed⟩⟩
        else none
    else none
  else none

def projectedAssignment? (source : TypedSource) (assignment : AssignmentResolution)
    (operator : Solcore.Syntax.ValueAssignOp) : Option (PLift (ProjectedAssignable source assignment operator)) := do
  if profile : operator = .equal ∨ assignment.target.type = .word then
    if projected : assignment.target.projections ≠ [] then
      match found : SourceCoreDataPlaces.rootBinder source assignment.target.root with
      | .error _ => none
      | .ok binder => do
        let ⟨route⟩ ← AcceptedProjectedAssignmentRoute.check source binder.scheme.body assignment.target.projections assignment.target.type
        pure ⟨⟨profile, projected, by
          intro actual accepted
          cases Except.ok.inj (found.symm.trans accepted)
          exact route⟩⟩
    else none
  else none

def valueAssignment? (source : TypedSource) (assignment : AssignmentResolution)
    (operator : Solcore.Syntax.ValueAssignOp) : Option (PLift (ValueAssignable source assignment operator)) :=
  match assignment? source assignment operator with
  | some ⟨bare⟩ => some ⟨.inl bare⟩
  | none => do
      let ⟨projected⟩ ← projectedAssignment? source assignment operator
      pure ⟨.inr projected⟩

def bitNotAssignment? (source : TypedSource) (assignment : AssignmentResolution)
    : Option (PLift (BitNotAssignable source assignment)) := do
  if profile : assignment.target.type = .word then
    if bare : assignment.target.projections = [] then
      match found : SourceCoreDataPlaces.rootBinder source assignment.target.root with
      | .error _ => none
      | .ok binder =>
        if typed : binder.scheme.body = assignment.target.type then
          some ⟨⟨profile, bare, by
            intro actual accepted
            cases Except.ok.inj (found.symm.trans accepted)
            exact typed⟩⟩
        else none
    else none
  else none

def projectedBitNotAssignment? (source : TypedSource) (assignment : AssignmentResolution)
    : Option (PLift (ProjectedBitNotAssignable source assignment)) := do
  if profile : assignment.target.type = .word then
    if projected : assignment.target.projections ≠ [] then
      match found : SourceCoreDataPlaces.rootBinder source assignment.target.root with
      | .error _ => none
      | .ok binder => do
        let ⟨route⟩ ← AcceptedProjectedAssignmentRoute.check source binder.scheme.body assignment.target.projections assignment.target.type
        pure ⟨⟨profile, projected, by
          intro actual accepted
          cases Except.ok.inj (found.symm.trans accepted)
          exact route⟩⟩
    else none
  else none

def unaryAssignment? (source : TypedSource) (assignment : AssignmentResolution)
    : Option (PLift (UnaryAssignable source assignment)) :=
  match bitNotAssignment? source assignment with
  | some ⟨bare⟩ => some ⟨.inl bare⟩
  | none => do
      let ⟨projected⟩ ← projectedBitNotAssignment? source assignment
      pure ⟨.inr projected⟩

def header? (source : TypedSource) (reached : ExpressionId → Prop) [DecidablePred reached]
    (item : ForItemForm) : Option (PLift (HeaderReady source reached item)) := by
  cases item with
  | letDecl binder initializer =>
    exact if mono : binder.scheme.quantified = [] then do
      let ⟨children⟩ ← allProof? reached (fun expression =>
        if present : reached expression then some ⟨present⟩ else none) initializer.toList
      pure ⟨⟨mono, children⟩⟩
    else none
  | expression expression => exact if present : reached expression then some ⟨present⟩ else none
  | assignValue assignment operator expression =>
    exact do
      let ⟨target⟩ ← valueAssignment? source assignment operator
      let ⟨children⟩ ← allProof? reached (fun expression =>
        if present : reached expression then some ⟨present⟩ else none)
        (expression :: DataPlaceKeyOrder.sourceKeys assignment.target.projections)
      pure ⟨⟨target, children⟩⟩
  | assignBitNot assignment => exact do
      let ⟨target⟩ ← unaryAssignment? source assignment
      let ⟨children⟩ ← allProof? reached (fun expression =>
        if present : reached expression then some ⟨present⟩ else none)
        (DataPlaceKeyOrder.sourceKeys assignment.target.projections)
      pure ⟨⟨target, children⟩⟩

def statement? (source : TypedSource) (reached : ExpressionId → Prop) [DecidablePred reached]
    (node : StatementNode) : Option (PLift (StatementReady source reached node)) := by
  cases form : node.form
  case breakStmt => exact some ⟨by simp only [StatementReady, form]⟩
  case continueStmt => exact some ⟨by simp only [StatementReady, form]⟩
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
      let ⟨target⟩ ← valueAssignment? source assignment operator
      let ⟨children⟩ ← allProof? reached (fun expression =>
        if present : reached expression then some ⟨present⟩ else none)
        (expression :: DataPlaceKeyOrder.sourceKeys assignment.target.projections)
      pure ⟨by simpa only [StatementReady, form] using And.intro target children⟩
  case assignBitNot assignment =>
    exact do
      let ⟨target⟩ ← unaryAssignment? source assignment
      let ⟨children⟩ ← allProof? reached (fun expression =>
        if present : reached expression then some ⟨present⟩ else none)
        (DataPlaceKeyOrder.sourceKeys assignment.target.projections)
      pure ⟨by simpa only [StatementReady, form] using And.intro target children⟩
  case expression expression semicolon =>
    exact if present : reached expression then some ⟨by simpa only [StatementReady, form] using present⟩ else none
  case block body => exact some ⟨by simp only [StatementReady, form]⟩
  case ifThen condition left right =>
    exact if present : reached condition then
      some ⟨by simpa only [StatementReady, form] using present⟩ else none
  case matchWith resolution =>
    exact if present : reached resolution.scrutinee then
      some ⟨by simpa only [StatementReady, form] using present⟩ else none
  case whileLoop condition body =>
    exact if present : reached condition then some ⟨by simpa only [StatementReady, form] using present⟩ else none
  case forLoop initializer condition post body =>
    exact do
      let ⟨initial⟩ ← allProof? (HeaderReady source reached) (header? source reached) initializer
      if present : reached condition then
        let ⟨after⟩ ← allProof? (HeaderReady source reached) (header? source reached) post
        pure ⟨by simpa only [StatementReady, form] using And.intro initial (And.intro present after)⟩
      else none

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
    {node : StatementNode} (_ready : StatementReady source reached node) : expanded node.form = true := by
  cases form : node.form <;> simp_all [StatementReady, AcceptedNamedBodyFlow.expanded]

theorem header_facts {policy : SourceCoreLoops.Policy} {source : TypedSource}
    {site : SourceCoreElaboration.ErrorSite} {result : Ty} {reasonAt : ExpressionId → Word}
    {next : SourceCoreLocalCell.Scope → Except SourceCoreBasic.Error Expr} {finalScope : SourceCoreLocalCell.Scope}
    {finish : Expr} {fuel scope items code} {reached : ExpressionId → Prop}
    (tree : Items policy source site result reasonAt next finalScope finish fuel scope items code)
    (profile : ∀ item ∈ items, HeaderReady source reached item) (ready : tree.Ready) :
    tree.closed = true ∧ (∀ binding ∈ tree.bindings, binding.binder.scheme.quantified = []) ∧
      (∀ child ∈ tree.children, reached child.expression) := by
  induction tree with
  | nil => simp [Items.closed, Items.bindings, Items.children]
  | absent projected remaining allocated ih =>
    have head := profile _ List.mem_cons_self
    have tail := ih (fun item member => profile item (List.mem_cons_of_mem _ member)) ready
    refine ⟨tail.1, ?_, tail.2.2⟩
    intro binding member
    rcases List.mem_cons.mp member with rfl | member
    · exact head.1
    · exact tail.2.1 binding member
  | initialized projected child generated childType remaining allocated ih =>
    have head := profile _ List.mem_cons_self
    have tail := ih (fun item member => profile item (List.mem_cons_of_mem _ member)) ready
    refine ⟨tail.1, ?_, ?_⟩
    · intro binding member
      rcases List.mem_cons.mp member with rfl | member
      · exact head.1
      · exact tail.2.1 binding member
    · intro actual member
      rcases List.mem_cons.mp member with rfl | member
      · exact head.2 _ (by simp)
      · exact tail.2.2 actual member
  | discard child generated remaining ih =>
    have head := profile _ List.mem_cons_self
    have tail := ih (fun item member => profile item (List.mem_cons_of_mem _ member)) ready
    refine ⟨tail.1, tail.2.1, ?_⟩
    intro actual member
    rcases List.mem_cons.mp member with rfl | member
    · exact head
    · exact tail.2.2 actual member
  | assigning remaining accepted ih =>
    exact False.elim (ready.1 (profile _ List.mem_cons_self).1)
  | assigned remaining receipt targetType ih =>
    have head := profile _ List.mem_cons_self
    have tail := ih (fun item member => profile item (List.mem_cons_of_mem _ member)) ready
    refine ⟨tail.1, tail.2.1, ?_⟩
    intro actual member
    rcases List.mem_cons.mp member with rfl | member
    · exact head.2 _ List.mem_cons_self
    · exact tail.2.2 actual member

  | projectedAssigned remaining receipt route ih =>
    have head := profile _ List.mem_cons_self
    have tail := ih (fun item member => profile item (List.mem_cons_of_mem _ member)) ready
    refine ⟨tail.1, tail.2.1, ?_⟩
    intro actual member
    rcases List.mem_append.mp member with key | member
    · apply head.2 actual.expression
      apply List.mem_cons_of_mem
      rw [← receipt.keyIds, ← keyChildren_ids receipt.keysGenerated]
      exact List.mem_map.mpr ⟨actual, key, rfl⟩
    · rcases List.mem_cons.mp member with rfl | member
      · exact head.2 _ List.mem_cons_self
      · exact tail.2.2 actual member

  | projectedBitNotted remaining receipt route ih =>
    have head := profile _ List.mem_cons_self
    have tail := ih (fun item member => profile item (List.mem_cons_of_mem _ member)) ready
    refine ⟨tail.1, tail.2.1, ?_⟩
    intro actual member
    rcases List.mem_append.mp member with key | member
    · apply head.2 actual.expression
      rw [← receipt.keyIds, ← keyChildren_ids receipt.keysGenerated]
      exact List.mem_map.mpr ⟨actual, key, rfl⟩
    · exact tail.2.2 actual member

  | bitNotting remaining accepted ih =>
    exact False.elim (ready.1 (profile _ List.mem_cons_self).1)
  | bitNotted remaining receipt targetType ih =>
    exact ih (fun item member => profile item (List.mem_cons_of_mem _ member)) ready

/-- The actual compiler tree and finite original forms retain every visited
operand and binder, including the emitted suffix of a stopped branch. -/
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
      obtain ⟨projected, _, same⟩ := CompatibleEncoding.bind_ok accepted
      cases same
      rfl

theorem facts_forms {policy : SourceCoreLoops.Policy} {checked : SourceCoreCompatibleCatalog.Checked}
    {source : TypedSource} {result : Ty} {reasonAt : ExpressionId → Word}
    {mode : Bool} {escaped : Word} {fuel : Nat} {scope : SourceCoreLocalCell.Scope}
    {statements : List StatementId} {code : Expr} {reached : ExpressionId → Prop}
    (tree : Tree policy source result reasonAt mode escaped fuel scope statements code)
    (readPolicy : policy.readStatement = SourceCoreCompatibleDataExpressions.readStatement checked)
    (profile : Profile source reached) (ready : tree.Ready)
    (finish : TailForms source mode statements) :
    tree.formed = true ∧
      (∀ binding ∈ tree.bindings, binding.binder.scheme.quantified = []) ∧
      (∀ child ∈ tree.children, reached child.expression) := by
  induction tree with
  | nil => simp [Tree.formed, Tree.bindings, Tree.children]
  | returning read form statementType child generated childType =>
      have original := profile.at (read_found (readPolicy ▸ read))
      simp only [StatementReady, form] at original
      exact ⟨rfl, by simp [Tree.bindings], by simpa [Tree.children] using original⟩
  | returnUnit | breaking | continuing => simp [Tree.formed, Tree.bindings, Tree.children]
  | initialized read form statementType projected child generated childType remaining allocated ih =>
      have found := read_found (readPolicy ▸ read)
      have original := profile.at found
      simp only [StatementReady, form, Option.toList_some, List.mem_singleton] at original
      have next := ih ready (finish.tail found (by simp [form, stopsHere]))
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
      have next := ih ready (finish.tail found (by simp [form, stopsHere]))
      refine ⟨next.1, ?_, next.2.2⟩
      intro binding member
      rcases List.mem_cons.mp member with rfl | member
      · exact original.1
      · exact next.2.1 binding member
  | assigning read form statementType remaining assigned ih =>
      have original := profile.at (read_found (readPolicy ▸ read))
      simp only [StatementReady, form] at original
      exact False.elim (ready.1 original.1)
  | bitNotting read form statementType remaining assigned ih =>
      have original := profile.at (read_found (readPolicy ▸ read))
      simp only [StatementReady, form] at original
      exact False.elim (ready.1 original.1)
  | assigned read form statementType remaining receipt targetType ih =>
      have found := read_found (readPolicy ▸ read)
      have original := profile.at found
      simp only [StatementReady, form] at original
      have next := ih ready (finish.tail found (by simp [form, stopsHere]))
      refine ⟨next.1, next.2.1, ?_⟩
      intro actual member
      rcases List.mem_cons.mp member with rfl | member
      · exact original.2 _ List.mem_cons_self
      · exact next.2.2 actual member
  | projectedAssigned read form statementType remaining receipt route ih =>
      have found := read_found (readPolicy ▸ read)
      have original := profile.at found
      simp only [StatementReady, form] at original
      have next := ih ready (finish.tail found (by simp [form, stopsHere]))
      refine ⟨next.1, next.2.1, ?_⟩
      intro actual member
      rcases List.mem_append.mp member with key | member
      · apply original.2 actual.expression
        apply List.mem_cons_of_mem
        rw [← receipt.keyIds, ← keyChildren_ids receipt.keysGenerated]
        exact List.mem_map.mpr ⟨actual, key, rfl⟩
      · rcases List.mem_cons.mp member with rfl | member
        · exact original.2 _ List.mem_cons_self
        · exact next.2.2 actual member
  | projectedBitNotted read form statementType remaining receipt route ih =>
      have found := read_found (readPolicy ▸ read)
      have original := profile.at found
      simp only [StatementReady, form] at original
      have next := ih ready (finish.tail found (by simp [form, stopsHere]))
      refine ⟨next.1, next.2.1, ?_⟩
      intro actual member
      rcases List.mem_append.mp member with key | member
      · apply original.2 actual.expression
        rw [← receipt.keyIds, ← keyChildren_ids receipt.keysGenerated]
        exact List.mem_map.mpr ⟨actual, key, rfl⟩
      · exact next.2.2 actual member
  | bitNotted read form statementType remaining receipt targetType ih =>
      have found := read_found (readPolicy ▸ read)
      exact ih ready (finish.tail found (by simp [form, stopsHere]))
  | discard read form child generated statementType remaining tailIH =>
      have found := read_found (readPolicy ▸ read)
      have original := profile.at found
      simp only [StatementReady, form] at original
      have next := tailIH ready (finish.tail found (by simp [form, stopsHere]))
      refine ⟨next.1, next.2.1, ?_⟩
      intro actual member
      rcases List.mem_cons.mp member with rfl | member
      · exact original
      · exact next.2.2 actual member
  | tailValue read form child generated statementType childType =>
      have original := profile.at (read_found (readPolicy ▸ read))
      simp only [StatementReady, form] at original
      exact ⟨rfl, by simp [Tree.bindings], by simpa [Tree.children] using original⟩
  | valueDiscard read form notFinal child generated statementType remaining ih =>
      have found := read_found (readPolicy ▸ read)
      have original := profile.at found
      simp only [StatementReady, form] at original
      have modeFalse := finish.discard_mode found form notFinal
      have next := ih ready (finish.tail found (by simp [form, stopsHere]))
      refine ⟨by simp only [Tree.formed, modeFalse, Bool.not_false, Bool.true_and]; exact next.1, next.2.1, ?_⟩
      intro actual member
      rcases List.mem_cons.mp member with rfl | member
      · exact original
      · exact next.2.2 actual member
  | block read form inner remaining innerIH tailIH =>
      have found := read_found (readPolicy ▸ read)
      have inside := innerIH ready.1 (by simp [TailForms, tailForms?])
      have next := tailIH ready.2 (finish.tail found (by simp [form, stopsHere]))
      refine ⟨by simp only [Tree.formed, inside.1, next.1, Bool.and_true], ?_, ?_⟩
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
      have original := profile.at found
      simp only [StatementReady, form] at original
      have first := leftIH ready.1 (by simp [TailForms, tailForms?])
      have second := rightIH ready.2.1 (by simp [TailForms, tailForms?])
      have next := tailIH ready.2.2 (finish.tail found (by simp [form, stopsHere]))
      refine ⟨by simp [Tree.formed, first.1, second.1, next.1], ?_, ?_⟩
      · intro binding member
        simp only [Tree.bindings, List.mem_append] at member
        rcases member with (member | member) | member
        · exact first.2.1 binding member
        · exact second.2.1 binding member
        · exact next.2.1 binding member
      · intro actual member
        rcases List.mem_cons.mp member with rfl | member
        · exact original
        · simp only [List.mem_append] at member
          rcases member with (member | member) | member
          · exact first.2.2 actual member
          · exact second.2.2 actual member
          · exact next.2.2 actual member
  | matching => exact False.elim ready
  | matched read form receipt branches remaining branchIH tailIH =>
      have found := read_found (readPolicy ▸ read)
      have original := profile.at found
      simp only [StatementReady, form] at original
      have allBranches : ∀ request member,
          (branches request member).formed = true ∧
          (∀ binding ∈ (branches request member).bindings, binding.binder.scheme.quantified = []) ∧
          (∀ child ∈ (branches request member).children, reached child.expression) := by
        intro request member
        exact branchIH request member (ready.1 request member) (by simp [TailForms, tailForms?])
      have next := tailIH ready.2 (finish.tail found (by simp [form, stopsHere]))
      refine ⟨?_, ?_, ?_⟩
      · simp only [Tree.formed, Bool.and_eq_true]
        exact ⟨List.all_eq_true.mpr (fun request _ => (allBranches request.val request.property).1), next.1⟩
      · intro binding member
        rcases List.mem_append.mp member with member | member
        · obtain ⟨request, _, member⟩ := List.mem_flatMap.mp member
          exact (allBranches request.val request.property).2.1 binding member
        · exact next.2.1 binding member
      · intro actual member
        rcases List.mem_cons.mp member with rfl | member
        · exact original
        · rcases List.mem_append.mp member with member | member
          · obtain ⟨request, _, member⟩ := List.mem_flatMap.mp member
            exact (allBranches request.val request.property).2.2 actual member
          · exact next.2.2 actual member
  | whileLoop read form statementType child generated conditionType inner remaining innerIH tailIH =>
      have found := read_found (readPolicy ▸ read)
      have original := profile.at found
      simp only [StatementReady, form] at original
      have inside := innerIH ready.1 (by simp [TailForms, tailForms?])
      have next := tailIH ready.2 (finish.tail found (by simp [form, stopsHere]))
      refine ⟨by simp only [Tree.formed, inside.1, next.1, Bool.and_true], ?_, ?_⟩
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
  | forLoop read form statementType child generated conditionType initial inner after remaining innerIH tailIH =>
      have found := read_found (readPolicy ▸ read)
      have original := profile.at found
      simp only [StatementReady, form] at original
      have before := header_facts initial original.1 ready.1
      have inside := innerIH ready.2.1 (by simp [TailForms, tailForms?])
      have post := header_facts after original.2.2 ready.2.2.1
      have next := tailIH ready.2.2.2 (finish.tail found (by simp [form, stopsHere]))
      refine ⟨by simp only [Tree.formed, before.1, inside.1, post.1, next.1, Bool.and_true], ?_, ?_⟩
      · intro binding member
        simp only [Tree.bindings, List.mem_append] at member
        rcases member with ((member | member) | member) | member
        · exact before.2.1 binding member
        · exact inside.2.1 binding member
        · exact post.2.1 binding member
        · exact next.2.1 binding member
      · intro actual member
        simp only [Tree.children, List.mem_append, List.mem_cons] at member
        rcases member with member | rfl | ((member | member) | member)
        · exact before.2.2 actual member
        · exact original.2.1
        · exact inside.2.2 actual member
        · exact post.2.2 actual member
        · exact next.2.2 actual member
  | forBoundary read form outside accepted =>
      have original := profile.at (read_found (readPolicy ▸ read))
      simp only [StatementReady, form] at original
      exact False.elim (outside ⟨header_forms original.1, header_forms original.2.2⟩)
  | boundary read outside accepted =>
      have original := (profile.at (read_found (readPolicy ▸ read))).expanded
      rw [outside] at original
      cases original

/-- Original completion and the actual compiler action give the full body
certificate while retaining every original operand and binding receipt. -/
theorem facts {policy : SourceCoreLoops.Policy} {checked : SourceCoreCompatibleCatalog.Checked}
    {source : TypedSource} {result : Ty} {reasonAt : ExpressionId → Word}
    {mode : Bool} {escaped : Word} {fuel : Nat} {scope : SourceCoreLocalCell.Scope}
    {statements : List StatementId} {code : Expr} {reached : ExpressionId → Prop}
    {expected : TypeSystem.Ty}
    (tree : Tree policy source result reasonAt mode escaped fuel scope statements code)
    (readPolicy : policy.readStatement = SourceCoreCompatibleDataExpressions.readStatement checked)
    (profile : Profile source reached) (ready : tree.Ready)
    (finish : Finish source expected mode statements) :
    tree.complete expected = true ∧
      (∀ binding ∈ tree.bindings, binding.binder.scheme.quantified = []) ∧
      (∀ child ∈ tree.children, reached child.expression) := by
  obtain ⟨formed, bindings, children⟩ := facts_forms tree readPolicy profile ready finish.forms
  exact ⟨tree.complete_of_formed readPolicy formed finish, bindings, children⟩

end Solcore.SourceSemantics.CoreLowering.AcceptedCompilerBodyProfile
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.AcceptedCompilerBodySubsetProfile
/-! Flat statement membership closes an actual inner compiler tree. The checked
set excludes unrelated outer statements and retains every loop child and root. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2400000
namespace Solcore.SourceSemantics.CoreLowering.AcceptedCompilerBodySubsetProfile
open Core Frontend SourceInference AcceptedNamedBodyFlow AcceptedCompilerBodyCompletion
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
  | .block body | .whileLoop _ body | .forLoop _ _ _ body => ∀ id ∈ body, id ∈ ids source expressions
  | .ifThen _ left right =>
      (∀ id ∈ left, id ∈ ids source expressions) ∧
      (∀ id ∈ right.getD [], id ∈ ids source expressions)
  | .matchWith resolution =>
      (∀ arm ∈ resolution.cases, ∀ id ∈ arm.body, id ∈ ids source expressions) ∧
      (∀ id ∈ resolution.defaultBody.getD [], id ∈ ids source expressions)
  | _ => True

def NodeReady (source : TypedSource) (expressions : List ExpressionId) (id : StatementId) : Prop :=
  ∃ node, source.lookupStatement? id = some node ∧
    StatementReady source (fun expression => expression ∈ expressions) node ∧ LoopEdges source expressions node

structure Profile (source : TypedSource) (expressions : List ExpressionId) (roots : List StatementId) (expected : TypeSystem.Ty) : Prop where
  nodes : ∀ id ∈ ids source expressions, NodeReady source expressions id
  rootMembers : ∀ id ∈ roots, id ∈ ids source expressions
  finish : Finish source expected true roots

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
  case matchWith resolution =>
    exact if arms : resolution.cases.all (fun arm => arm.body.all (fun id => decide (id ∈ ids source expressions))) = true then
      if fallback : (resolution.defaultBody.getD []).all (fun id => decide (id ∈ ids source expressions)) = true then
        some ⟨by
          simp only [LoopEdges, form]
          exact ⟨fun arm member id present => of_decide_eq_true
            (List.all_eq_true.mp (List.all_eq_true.mp arms arm member) id present),
            fun id member => of_decide_eq_true (List.all_eq_true.mp fallback id member)⟩⟩
      else none
    else none
  case whileLoop condition body =>
    exact if closed : body.all (fun id => decide (id ∈ ids source expressions)) = true then
      some ⟨by
        simp only [LoopEdges, form]
        exact fun id member => of_decide_eq_true (List.all_eq_true.mp closed id member)⟩ else none
  case forLoop initializer condition post body =>
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
def validate (source : TypedSource) (expressions : List ExpressionId) (roots : List StatementId) (expected : TypeSystem.Ty) :
    Option (PLift (Profile source expressions roots expected)) := do
  let ⟨nodes⟩ ← allProof? (NodeReady source expressions) (node? source expressions) (ids source expressions)
  if present : roots.all (fun id => decide (id ∈ ids source expressions)) = true then
    let ⟨finish⟩ ← finish? source expected true roots
    pure ⟨⟨nodes, fun id member => of_decide_eq_true (List.all_eq_true.mp present id member), finish⟩⟩
  else none

theorem Profile.at {source : TypedSource} {expressions : List ExpressionId} {roots : List StatementId} {expected : TypeSystem.Ty}
    (profile : Profile source expressions roots expected) {id : StatementId} {node : StatementNode}
    (present : id ∈ ids source expressions) (found : source.lookupStatement? id = some node) :
    StatementReady source (fun expression => expression ∈ expressions) node ∧ LoopEdges source expressions node := by
  obtain ⟨actual, lookup, ready⟩ := profile.nodes id present
  cases Option.some.inj (lookup.symm.trans found)
  exact ready

private theorem expanded_of_ready {source : TypedSource} {expressions : List ExpressionId}
    {node : StatementNode} (_ready : StatementReady source (fun id => id ∈ expressions) node) :
    expanded node.form = true := by
  cases form : node.form <;> simp_all [StatementReady, AcceptedNamedBodyFlow.expanded]

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
      obtain ⟨projected, _, same⟩ := CompatibleEncoding.bind_ok accepted
      cases same
      rfl

private theorem facts_general {policy : SourceCoreLoops.Policy} {checked : SourceCoreCompatibleCatalog.Checked}
    {source : TypedSource} {result : Ty} {reasonAt : ExpressionId → Word}
    {mode : Bool} {escaped : Word} {fuel : Nat} {scope : SourceCoreLocalCell.Scope}
    {statements originalRoots : List StatementId} {code : Expr} {expressionIds : List ExpressionId} {expected : TypeSystem.Ty}
    (tree : Tree policy source result reasonAt mode escaped fuel scope statements code)
    (readPolicy : policy.readStatement = SourceCoreCompatibleDataExpressions.readStatement checked)
    (profile : Profile source expressionIds originalRoots expected) (ready : tree.Ready)
    (present : ∀ id ∈ statements, id ∈ ids source expressionIds)
    (finish : TailForms source mode statements) :
    tree.formed = true ∧
      (∀ binding ∈ tree.bindings, binding.binder.scheme.quantified = []) ∧
      (∀ child ∈ tree.children, child.expression ∈ expressionIds) := by
  induction tree with
  | nil => simp [Tree.formed, Tree.bindings, Tree.children]
  | returning read form statementType child generated childType =>
      have original := (profile.at (present _ List.mem_cons_self) (read_found (readPolicy ▸ read))).1
      simp only [StatementReady, form] at original
      exact ⟨rfl, by simp [Tree.bindings], by simpa [Tree.children] using original⟩
  | returnUnit | breaking | continuing => simp [Tree.formed, Tree.bindings, Tree.children]
  | initialized read form statementType projected child generated childType remaining allocated ih =>
      have found := read_found (readPolicy ▸ read)
      have original := (profile.at (present _ List.mem_cons_self) found).1
      simp only [StatementReady, form, Option.toList_some, List.mem_singleton] at original
      have next := ih ready (fun id member => present id (List.mem_cons_of_mem _ member)) (finish.tail found (by simp [form, stopsHere]))
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
      have next := ih ready (fun id member => present id (List.mem_cons_of_mem _ member)) (finish.tail found (by simp [form, stopsHere]))
      refine ⟨next.1, ?_, next.2.2⟩
      intro binding member
      rcases List.mem_cons.mp member with rfl | member
      · exact original.1
      · exact next.2.1 binding member
  | assigning read form statementType remaining assigned ih =>
      have original := (profile.at (present _ List.mem_cons_self) (read_found (readPolicy ▸ read))).1
      simp only [StatementReady, form] at original
      exact False.elim (ready.1 original.1)
  | bitNotting read form statementType remaining assigned ih =>
      have original := (profile.at (present _ List.mem_cons_self) (read_found (readPolicy ▸ read))).1
      simp only [StatementReady, form] at original
      exact False.elim (ready.1 original.1)
  | assigned read form statementType remaining receipt targetType ih =>
      have found := read_found (readPolicy ▸ read)
      have original := (profile.at (present _ List.mem_cons_self) found).1
      simp only [StatementReady, form] at original
      have next := ih ready (fun id member => present id (List.mem_cons_of_mem _ member)) (finish.tail found (by simp [form, stopsHere]))
      refine ⟨next.1, next.2.1, ?_⟩
      intro actual member
      rcases List.mem_cons.mp member with rfl | member
      · exact original.2 _ List.mem_cons_self
      · exact next.2.2 actual member
  | projectedAssigned read form statementType remaining receipt route ih =>
      have found := read_found (readPolicy ▸ read)
      have original := (profile.at (present _ List.mem_cons_self) found).1
      simp only [StatementReady, form] at original
      have next := ih ready (fun id member => present id (List.mem_cons_of_mem _ member)) (finish.tail found (by simp [form, stopsHere]))
      refine ⟨next.1, next.2.1, ?_⟩
      intro actual member
      rcases List.mem_append.mp member with key | member
      · apply original.2 actual.expression
        apply List.mem_cons_of_mem
        rw [← receipt.keyIds, ← keyChildren_ids receipt.keysGenerated]
        exact List.mem_map.mpr ⟨actual, key, rfl⟩
      · rcases List.mem_cons.mp member with rfl | member
        · exact original.2 _ List.mem_cons_self
        · exact next.2.2 actual member
  | projectedBitNotted read form statementType remaining receipt route ih =>
      have found := read_found (readPolicy ▸ read)
      have original := (profile.at (present _ List.mem_cons_self) found).1
      simp only [StatementReady, form] at original
      have next := ih ready (fun id member => present id (List.mem_cons_of_mem _ member)) (finish.tail found (by simp [form, stopsHere]))
      refine ⟨next.1, next.2.1, ?_⟩
      intro actual member
      rcases List.mem_append.mp member with key | member
      · apply original.2 actual.expression
        rw [← receipt.keyIds, ← keyChildren_ids receipt.keysGenerated]
        exact List.mem_map.mpr ⟨actual, key, rfl⟩
      · exact next.2.2 actual member
  | bitNotted read form statementType remaining receipt targetType ih =>
      have found := read_found (readPolicy ▸ read)
      exact ih ready (fun id member => present id (List.mem_cons_of_mem _ member))
        (finish.tail found (by simp [form, stopsHere]))
  | discard read form child generated statementType remaining tailIH =>
      have found := read_found (readPolicy ▸ read)
      have original := (profile.at (present _ List.mem_cons_self) found).1
      simp only [StatementReady, form] at original
      have next := tailIH ready (fun id member => present id (List.mem_cons_of_mem _ member)) (finish.tail found (by simp [form, stopsHere]))
      refine ⟨next.1, next.2.1, ?_⟩
      intro actual member
      rcases List.mem_cons.mp member with rfl | member
      · exact original
      · exact next.2.2 actual member
  | tailValue read form child generated statementType childType =>
      have original := (profile.at (present _ List.mem_cons_self) (read_found (readPolicy ▸ read))).1
      simp only [StatementReady, form] at original
      exact ⟨rfl, by simp [Tree.bindings], by simpa [Tree.children] using original⟩
  | valueDiscard read form notFinal child generated statementType remaining ih =>
      have found := read_found (readPolicy ▸ read)
      have original := (profile.at (present _ List.mem_cons_self) found).1
      simp only [StatementReady, form] at original
      have modeFalse := finish.discard_mode found form notFinal
      have next := ih ready (fun id member => present id (List.mem_cons_of_mem _ member)) (finish.tail found (by simp [form, stopsHere]))
      refine ⟨by simp only [Tree.formed, modeFalse, Bool.not_false, Bool.true_and]; exact next.1, next.2.1, ?_⟩
      intro actual member
      rcases List.mem_cons.mp member with rfl | member
      · exact original
      · exact next.2.2 actual member
  | block read form inner remaining innerIH tailIH =>
      have found := read_found (readPolicy ▸ read)
      have edges := (profile.at (present _ List.mem_cons_self) found).2
      simp only [LoopEdges, form] at edges
      have inside := innerIH ready.1 edges (by simp [TailForms, tailForms?])
      have next := tailIH ready.2 (fun id member => present id (List.mem_cons_of_mem _ member)) (finish.tail found (by simp [form, stopsHere]))
      refine ⟨by simp only [Tree.formed, inside.1, next.1, Bool.and_true], ?_, ?_⟩
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
      have first := leftIH ready.1 edges.1 (by simp [TailForms, tailForms?])
      have second := rightIH ready.2.1 edges.2 (by simp [TailForms, tailForms?])
      have next := tailIH ready.2.2 (fun id member => present id (List.mem_cons_of_mem _ member)) (finish.tail found (by simp [form, stopsHere]))
      refine ⟨by simp [Tree.formed, first.1, second.1, next.1], ?_, ?_⟩
      · intro binding member
        simp only [Tree.bindings, List.mem_append] at member
        rcases member with (member | member) | member
        · exact first.2.1 binding member
        · exact second.2.1 binding member
        · exact next.2.1 binding member
      · intro actual member
        rcases List.mem_cons.mp member with rfl | member
        · exact original
        · simp only [List.mem_append] at member
          rcases member with (member | member) | member
          · exact first.2.2 actual member
          · exact second.2.2 actual member
          · exact next.2.2 actual member
  | matching => exact False.elim ready
  | matched read form receipt branches remaining branchIH tailIH =>
      have found := read_found (readPolicy ▸ read)
      have original := (profile.at (present _ List.mem_cons_self) found).1
      simp only [StatementReady, form] at original
      have allBranches : ∀ request member,
          (branches request member).formed = true ∧
          (∀ binding ∈ (branches request member).bindings, binding.binder.scheme.quantified = []) ∧
          (∀ child ∈ (branches request member).children, child.expression ∈ expressionIds) := by
        intro request member
        have edges := (profile.at (present _ List.mem_cons_self) found).2
        simp only [LoopEdges, form] at edges
        have requestPresent : ∀ id ∈ request.statements, id ∈ ids source expressionIds := by
          rcases receipt.original request member with ⟨arm, armMember, same⟩ | same
          · rw [same]; exact edges.1 arm armMember
          · intro id member
            exact edges.2 id (by simpa only [same, Option.getD_some] using member)
        exact branchIH request member (ready.1 request member) requestPresent (by simp [TailForms, tailForms?])
      have next := tailIH ready.2 (fun id member => present id (List.mem_cons_of_mem _ member)) (finish.tail found (by simp [form, stopsHere]))
      refine ⟨?_, ?_, ?_⟩
      · simp only [Tree.formed, Bool.and_eq_true]
        exact ⟨List.all_eq_true.mpr (fun request _ => (allBranches request.val request.property).1), next.1⟩
      · intro binding member
        rcases List.mem_append.mp member with member | member
        · obtain ⟨request, _, member⟩ := List.mem_flatMap.mp member
          exact (allBranches request.val request.property).2.1 binding member
        · exact next.2.1 binding member
      · intro actual member
        rcases List.mem_cons.mp member with rfl | member
        · exact original
        · rcases List.mem_append.mp member with member | member
          · obtain ⟨request, _, member⟩ := List.mem_flatMap.mp member
            exact (allBranches request.val request.property).2.2 actual member
          · exact next.2.2 actual member
  | whileLoop read form statementType child generated conditionType inner remaining innerIH tailIH =>
      have found := read_found (readPolicy ▸ read)
      have original := (profile.at (present _ List.mem_cons_self) found).1
      simp only [StatementReady, form] at original
      have edges := (profile.at (present _ List.mem_cons_self) found).2
      simp only [LoopEdges, form] at edges
      have inside := innerIH ready.1 edges (by simp [TailForms, tailForms?])
      have next := tailIH ready.2 (fun id member => present id (List.mem_cons_of_mem _ member)) (finish.tail found (by simp [form, stopsHere]))
      refine ⟨by simp only [Tree.formed, inside.1, next.1, Bool.and_true], ?_, ?_⟩
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
  | forLoop read form statementType child generated conditionType initial inner after remaining innerIH tailIH =>
      have found := read_found (readPolicy ▸ read)
      have original := (profile.at (present _ List.mem_cons_self) found).1
      have edges := (profile.at (present _ List.mem_cons_self) found).2
      simp only [LoopEdges, form] at edges
      simp only [StatementReady, form] at original
      have before := AcceptedCompilerBodyProfile.header_facts initial original.1 ready.1
      have inside := innerIH ready.2.1 edges (by simp [TailForms, tailForms?])
      have post := AcceptedCompilerBodyProfile.header_facts after original.2.2 ready.2.2.1
      have next := tailIH ready.2.2.2 (fun id member => present id (List.mem_cons_of_mem _ member)) (finish.tail found (by simp [form, stopsHere]))
      refine ⟨by simp only [Tree.formed, before.1, inside.1, post.1, next.1, Bool.and_true], ?_, ?_⟩
      · intro binding member
        simp only [Tree.bindings, List.mem_append] at member
        rcases member with ((member | member) | member) | member
        · exact before.2.1 binding member
        · exact inside.2.1 binding member
        · exact post.2.1 binding member
        · exact next.2.1 binding member
      · intro actual member
        simp only [Tree.children, List.mem_append, List.mem_cons] at member
        rcases member with member | rfl | ((member | member) | member)
        · exact before.2.2 actual member
        · exact original.2.1
        · exact inside.2.2 actual member
        · exact post.2.2 actual member
        · exact next.2.2 actual member
  | forBoundary read form outside accepted =>
      have original := (profile.at (present _ List.mem_cons_self) (read_found (readPolicy ▸ read))).1
      simp only [StatementReady, form] at original
      exact False.elim (outside ⟨AcceptedCompilerBodyProfile.header_forms original.1, AcceptedCompilerBodyProfile.header_forms original.2.2⟩)
  | boundary read outside accepted =>
      have checked := (profile.at (present _ List.mem_cons_self) (read_found (readPolicy ▸ read))).1
      have original := expanded_of_ready checked
      rw [outside] at original
      cases original

/-- Original branch membership and raw completion are discharged by the finite
profile; the authentic compiler tree supplies all recursive body receipts. -/
theorem Profile.facts {source : TypedSource} {expressions : List ExpressionId}
    {statements : List StatementId} {expected : TypeSystem.Ty}
    (profile : Profile source expressions statements expected)
    {policy : SourceCoreLoops.Policy} {checked : SourceCoreCompatibleCatalog.Checked}
    {result : Ty} {reasonAt : ExpressionId → Word} {escaped : Word} {fuel : Nat}
    {scope : SourceCoreLocalCell.Scope} {code : Expr}
    (tree : Tree policy source result reasonAt true escaped fuel scope statements code)
    (readPolicy : policy.readStatement = SourceCoreCompatibleDataExpressions.readStatement checked)
    (ready : tree.Ready) :
    tree.complete expected = true ∧
      (∀ binding ∈ tree.bindings, binding.binder.scheme.quantified = []) ∧
      (∀ child ∈ tree.children, child.expression ∈ expressions) := by
  obtain ⟨formed, bindings, children⟩ :=
    facts_general tree readPolicy profile ready profile.rootMembers profile.finish.forms
  exact ⟨tree.complete_of_formed readPolicy formed profile.finish, bindings, children⟩

end Solcore.SourceSemantics.CoreLowering.AcceptedCompilerBodySubsetProfile
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.AcceptedCompilerExpressionProfile
/-! Flat checks of actual source nodes and operand edges supply the finite
facts used to close accepted compiler traces. Static declaration references
are excluded from the reached set; declaration calls retain only arguments.
This profile constructs no recursive expression grammar. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2400000
namespace Solcore.SourceSemantics.CoreLowering.AcceptedCompilerExpressionProfile
open Core Frontend SourceInference
open CallableIndexedNamedGeneration
open AcceptedNamedExpressionFlow
open CallableIndexedOwnedPreparedNamedSyntaxAdmission (DirectSite MetadataTest metadata? directSite?)
open CallableIndexedOwnedPreparedStagedGeneralCallerMethodProfiles (MetadataFor)

/-- The restricted lane is used by existing direct/read method and closure
producers. The general lane additionally accepts indirect and method calls,
composite data, and proxy values with their original metadata. -/
private def legacySupportedForm (directOnly : Bool) (allowIndices : Bool := false) (allowConstructors : Bool := false) : ExpressionForm → Bool
  | .reference _ (.local _) | .reference _ (.builtinBoolean _)
    | .literal _ | .integerLiteral _ _ | .tuple []
    | .call _ _ (.declaration _) => true
  | .call _ _ (.indirect _) | .unary _ _ | .binary _ _ _ => !directOnly
  | .index _ _ => allowIndices && !directOnly
  | .constructor _ _ => allowConstructors && !directOnly
  | _ => false

def compositeForm : ExpressionForm → Bool
  | .group _ | .tuple (_ :: _) | .conditional _ _ _ => true
  | _ => false

def proxyForm : ExpressionForm → Bool
  | .proxy _ => true
  | _ => false

private def compositeSupportedForm (directOnly : Bool) (allowIndices : Bool := false) (allowConstructors : Bool := false)
    (form : ExpressionForm) : Bool :=
  legacySupportedForm directOnly allowIndices allowConstructors form || (!directOnly && compositeForm form)

def builtinForm : ExpressionForm → Bool
  | .call _ _ (.builtinFunction _) => true
  | _ => false

def supportedForm (directOnly : Bool) (allowIndices : Bool := false) (allowConstructors : Bool := false)
    (form : ExpressionForm) : Bool :=
  compositeSupportedForm directOnly allowIndices allowConstructors form || (!directOnly && (builtinForm form || proxyForm form))

/-- Every child is listed in actual compiler order, including both compiled branches. -/
def operands : ExpressionForm → List ExpressionId
  | .call _ arguments (.declaration _) | .call _ arguments (.builtinFunction _) => arguments
  | .call callee arguments (.indirect _) => callee :: arguments
  | .unary _ operand => [operand]
  | .binary left _ right => [left, right]
  | .index base key => [base, key]
  | .constructor _ ids => ids
  | .group inner => [inner]
  | .tuple ids => ids
  | .conditional test yes no => [test, yes, no]
  | _ => []

def supportedIds (source : TypedSource) (directOnly : Bool) (allowIndices : Bool := false) (allowConstructors : Bool := false) : List ExpressionId :=
  source.nodes.filterMap fun node => match node with
    | .expression expression => if supportedForm directOnly allowIndices allowConstructors expression.form then some expression.id else none
    | .statement _ => none

private theorem supported_mem {source : TypedSource} {directOnly allowIndices allowConstructors : Bool}
    {id : ExpressionId} {node : ExpressionNode}
    (found : source.lookupExpression? id = some node)
    (supported : supportedForm directOnly allowIndices allowConstructors node.form = true) : id ∈ supportedIds source directOnly allowIndices allowConstructors := by
  obtain ⟨member, same⟩ := lookupExpression?_sound found
  apply List.mem_filterMap.mpr
  refine ⟨.expression node, member, ?_⟩
  simp only [supported, ↓reduceIte]
  exact congrArg some same

private theorem old_form_of_supported {directOnly : Bool} {form : ExpressionForm}
    (supported : legacySupportedForm directOnly false false form = true) :
    LeafForm form ∨ DirectForm form ∨
      (directOnly = false ∧ (IndirectForm form ∨ MethodForm form)) := by
  match form with
  | .reference name (.local binder) => exact .inl (.read name binder)
  | .reference name (.builtinBoolean value) => exact .inl (.literal (.bool name value))
  | .literal literal => exact .inl (.literal (.word literal))
  | .integerLiteral literal resolution => exact .inl (.literal (.integer literal resolution))
  | .tuple [] => exact .inl (.literal .unit)
  | .call callee arguments (.declaration instantiation) => exact .inr (.inl ⟨callee, arguments, instantiation, rfl⟩)
  | .call callee arguments (.indirect metadata) =>
      exact .inr (.inr ⟨(by cases directOnly <;> simp_all [legacySupportedForm]), .inl ⟨callee, arguments, metadata, rfl⟩⟩)
  | .unary operator operand =>
      exact .inr (.inr ⟨(by cases directOnly <;> simp_all [legacySupportedForm]), .inr (.inl ⟨operator, operand, rfl⟩)⟩)
  | .binary left operator right =>
      exact .inr (.inr ⟨(by cases directOnly <;> simp_all [legacySupportedForm]), .inr (.inr ⟨operator, left, right, rfl⟩)⟩)
  | .reference name resolution =>
      cases resolution with
      | «local» binder => exact .inl (.read name binder)
      | builtinBoolean value => exact .inl (.literal (.bool name value))
      | _ => cases supported
  | .tuple (_ :: _) | .group _ | .index _ _ | .conditional _ _ _
    | .constructor _ _ | .call _ _ (.builtinFunction _) | .lambda _ _ _ => cases supported

private theorem index_form_of_supported {directOnly allowIndices : Bool} {form : ExpressionForm}
    (supported : legacySupportedForm directOnly allowIndices false form = true) :
    (LeafForm form ∨ DirectForm form ∨
      (directOnly = false ∧ (IndirectForm form ∨ MethodForm form))) ∨
      (allowIndices = true ∧ directOnly = false ∧ IndexForm form) := by
  by_cases old : legacySupportedForm directOnly false false form = true
  · exact .inl (old_form_of_supported old)
  · cases form <;> try simp_all [legacySupportedForm]
    case reference name resolution => cases resolution <;> simp_all
    case tuple elements => cases elements <;> simp_all
    case call callee arguments resolution => cases resolution <;> simp_all
    case index base key =>
      cases directOnly <;> cases allowIndices <;> simp_all [IndexForm]

private theorem form_of_legacySupported {directOnly allowIndices allowConstructors : Bool} {form : ExpressionForm}
    (supported : legacySupportedForm directOnly allowIndices allowConstructors form = true) :
    ((LeafForm form ∨ DirectForm form ∨
      (directOnly = false ∧ (IndirectForm form ∨ MethodForm form))) ∨
      (allowIndices = true ∧ directOnly = false ∧ IndexForm form)) ∨
      (allowConstructors = true ∧ directOnly = false ∧ ConstructorForm form) := by
  by_cases old : legacySupportedForm directOnly allowIndices false form = true
  · exact .inl (index_form_of_supported old)
  · cases form <;> try simp_all [legacySupportedForm]
    case reference name resolution => cases resolution <;> simp_all
    case tuple elements => cases elements <;> simp_all
    case call callee arguments resolution => cases resolution <;> simp_all
    case constructor instantiation ids =>
      cases directOnly <;> cases allowConstructors <;> simp_all [ConstructorForm]

private theorem composite_of_true {form : ExpressionForm} (yes : compositeForm form = true) :
    CompositeForm form := by
  cases form <;> try cases yes
  case group inner => exact .group inner
  case conditional test yes no => exact .conditional test yes no
  case tuple ids =>
    cases ids with
    | nil => cases yes
    | cons first rest => exact .tuple first rest

private theorem form_of_compositeSupported {directOnly allowIndices allowConstructors : Bool} {form : ExpressionForm}
    (supported : compositeSupportedForm directOnly allowIndices allowConstructors form = true) :
    (((LeafForm form ∨ DirectForm form ∨ (directOnly = false ∧ (IndirectForm form ∨ MethodForm form))) ∨
      (allowIndices = true ∧ directOnly = false ∧ IndexForm form)) ∨
      (allowConstructors = true ∧ directOnly = false ∧ ConstructorForm form)) ∨
      (directOnly = false ∧ CompositeForm form) := by
  rcases Bool.or_eq_true_iff.mp supported with old | composite
  · exact .inl (form_of_legacySupported old)
  · obtain ⟨general, form⟩ := Bool.and_eq_true_iff.mp composite
    exact .inr ⟨by cases directOnly <;> simp_all, composite_of_true form⟩

private theorem builtin_of_true {form : ExpressionForm} (yes : builtinForm form = true) :
    BuiltinForm form := by
  cases form <;> simp_all [builtinForm, BuiltinForm, AcceptedOrdinaryExpressionReceipt.BuiltinForm]
  case call callee ids resolution =>
    cases resolution <;> simp_all

private theorem proxy_of_true {form : ExpressionForm} (yes : proxyForm form = true) :
    ProxyForm form := by
  cases form <;> simp_all [proxyForm, ProxyForm]

private theorem form_of_supported {directOnly allowIndices allowConstructors : Bool} {form : ExpressionForm}
    (supported : supportedForm directOnly allowIndices allowConstructors form = true) :
    ((((LeafForm form ∨ DirectForm form ∨ (directOnly = false ∧ (IndirectForm form ∨ MethodForm form))) ∨
      (allowIndices = true ∧ directOnly = false ∧ IndexForm form)) ∨
      (allowConstructors = true ∧ directOnly = false ∧ ConstructorForm form)) ∨
      (directOnly = false ∧ CompositeForm form)) ∨ (directOnly = false ∧ (BuiltinForm form ∨ ProxyForm form)) := by
  rcases Bool.or_eq_true_iff.mp supported with composite | builtin
  · exact .inl (form_of_compositeSupported composite)
  · obtain ⟨general, isBuiltin⟩ := Bool.and_eq_true_iff.mp builtin
    refine .inr ⟨by cases directOnly <;> simp_all, ?_⟩
    rcases Bool.or_eq_true_iff.mp isBuiltin with isBuiltin | isProxy
    · exact .inl (builtin_of_true isBuiltin)
    · exact .inr (proxy_of_true isProxy)

private theorem policy_supported {directOnly allowIndices allowConstructors : Bool} {form : ExpressionForm}
    (supported : supportedForm directOnly allowIndices allowConstructors form = true) :
    CallableIndexedOwnedPreparedStagedGeneralCallerPolicyProfiles.SupportedForm form := by
  rcases form_of_supported supported with ((((leaf | ⟨callee, args, instantiation, rfl⟩ | ⟨_, rest⟩) | ⟨_, _, base, key, rfl⟩) | ⟨_, _, instantiation, ids, rfl⟩) | ⟨_, composite⟩) | ⟨_, (⟨callee, ids, function, rfl⟩ | ⟨inner, rfl⟩)⟩
  · rcases leaf.view with atomic | ⟨name, binder, rfl⟩
    · exact .literal atomic
    · exact .read name binder
  · exact .direct callee args instantiation
  · rcases rest with ⟨callee, args, metadata, rfl⟩ | method
    · exact .call callee args metadata
    · rcases method with ⟨operator, operand, rfl⟩ | ⟨operator, left, right, rfl⟩
      · exact .unary operator operand
      · exact .binary left operator right

  · exact .index base key

  · exact .constructor instantiation ids

  · cases composite
    · exact .group _
    · exact .tuple _
    · exact .conditional _ _ _

  · exact .builtin callee ids function

  · exact .proxy inner

def SiteReady (rows : List SourceSpecialization.SpecializedFunction) (node : ExpressionNode) : Prop :=
  match node.form with
  | .call _ _ (.declaration instantiation) => DirectSite rows instantiation
  | _ => True

private def site? (rows : List SourceSpecialization.SpecializedFunction) (node : ExpressionNode) :
    Option (PLift (SiteReady rows node)) := by
  cases form : node.form with
  | call callee arguments resolution =>
      cases resolution with
      | declaration instantiation =>
          exact (directSite? rows instantiation).map fun site => ⟨by simpa only [SiteReady, form] using site.down⟩
      | _ => exact some ⟨by simp [SiteReady, form]⟩
  | _ => exact some ⟨by simp [SiteReady, form]⟩

def IndexReady (source : TypedSource) (node : ExpressionNode) : Prop :=
  match node.form with
  | .index base key => AcceptedIndexExpressionReceipt.Operands source base key
  | _ => True

private def index? (source : TypedSource) (node : ExpressionNode) : Option (PLift (IndexReady source node)) := by
  cases form : node.form
  case index base key =>
    exact do
      match baseFound : source.lookupExpression? base with
      | none => none
      | some baseNode =>
        match keyFound : source.lookupExpression? key with
        | none => none
        | some keyNode =>
          pure ⟨by
            simp only [IndexReady, form]
            exact ⟨baseNode, keyNode, baseFound, keyFound⟩⟩
  all_goals exact some ⟨by simp only [IndexReady, form]⟩

def ConstructorReady (node : ExpressionNode) : Prop :=
  match node.form with
  | .constructor instantiation _ => CompatibleSourceInstantiationClosure.ClosedParameterRange instantiation.parameterSubstitution
  | _ => True

private def constructor? (node : ExpressionNode) : Option (PLift (ConstructorReady node)) := by
  cases form : node.form
  case constructor instantiation ids =>
    exact if closed : instantiation.parameterSubstitution.all (fun item => SourceCoreDataCatalog.closed item.2) = true then
      some ⟨by
        simp only [ConstructorReady, form]
        intro parameter replacement member
        exact List.all_eq_true.mp closed _ member⟩
    else none
  all_goals exact some ⟨by simp only [ConstructorReady, form]⟩

/-- All facts refer to the node selected by the actual source lookup. -/
def NodeReady (source : TypedSource) (rows : List SourceSpecialization.SpecializedFunction)
    (directOnly allowIndices allowConstructors : Bool) (id : ExpressionId) : Prop :=
  ∃ node, source.lookupExpression? id = some node ∧ supportedForm directOnly allowIndices allowConstructors node.form = true ∧
    (∀ child ∈ operands node.form, child ∈ supportedIds source directOnly allowIndices allowConstructors) ∧
    SiteReady rows node ∧ IndexReady source node ∧ ConstructorReady node

private def node? (source : TypedSource) (rows : List SourceSpecialization.SpecializedFunction)
    (directOnly allowIndices allowConstructors : Bool) (id : ExpressionId) : Option (PLift (NodeReady source rows directOnly allowIndices allowConstructors id)) := do
  match found : source.lookupExpression? id with
  | none => none
  | some node =>
    if supported : supportedForm directOnly allowIndices allowConstructors node.form = true then do
      if edges : (operands node.form).all (fun child => decide (child ∈ supportedIds source directOnly allowIndices allowConstructors)) = true then do
        let ⟨site⟩ ← site? rows node
        let ⟨index⟩ ← index? source node
        let ⟨constructor⟩ ← constructor? node
        pure ⟨⟨node, found, supported, by
          intro child member
          exact of_decide_eq_true (List.all_eq_true.mp edges child member), site, index, constructor⟩⟩
      else none
    else none

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

structure Profile {checked : SourceCoreCompatibleCatalog.Checked}
    (prepared : CallableIndexedNamedGeneration.Prepared checked) (named : Named)
    (source : TypedSource) (rows : List SourceSpecialization.SpecializedFunction)
    (directOnly : Bool := false) (allowIndices : Bool := false) (allowConstructors : Bool := false) : Type where
  nodes : ∀ id ∈ supportedIds source directOnly allowIndices allowConstructors, NodeReady source rows directOnly allowIndices allowConstructors id
  metadataAccepted : ∃ receipt : PLift (MetadataFor prepared named source (DirectSite rows)),
    metadata? prepared named source (DirectSite rows) = some receipt

namespace Profile
variable {checked : SourceCoreCompatibleCatalog.Checked}
  {prepared : CallableIndexedNamedGeneration.Prepared checked} {named : Named}
  {source : TypedSource} {rows : List SourceSpecialization.SpecializedFunction} {directOnly allowIndices allowConstructors : Bool}

abbrev ids (_profile : Profile prepared named source rows directOnly allowIndices allowConstructors) : List ExpressionId := supportedIds source directOnly allowIndices allowConstructors
abbrev Reached (profile : Profile prepared named source rows directOnly allowIndices allowConstructors) (id : ExpressionId) : Prop := id ∈ profile.ids

private theorem at_node (profile : Profile prepared named source rows directOnly allowIndices allowConstructors) {id : ExpressionId} {node : ExpressionNode}
    (reached : profile.Reached id) (found : source.lookupExpression? id = some node) :
    supportedForm directOnly allowIndices allowConstructors node.form = true ∧
    (∀ child ∈ operands node.form, profile.Reached child) ∧ SiteReady rows node ∧ IndexReady source node ∧ ConstructorReady node := by
  obtain ⟨actual, selected, rest⟩ := profile.nodes id reached
  cases Option.some.inj (selected.symm.trans found)
  exact rest

theorem metadata (profile : Profile prepared named source rows directOnly allowIndices allowConstructors) : MetadataFor prepared named source (DirectSite rows) := by
  obtain ⟨receipt, _accepted⟩ := profile.metadataAccepted
  exact receipt.down

theorem covered (profile : Profile prepared named source rows directOnly allowIndices allowConstructors) (id : ExpressionId) (node : ExpressionNode)
    (found : source.lookupExpression? id = some node)
    (callee : ExpressionId) (arguments : List ExpressionId) (instantiation : DeclarationInstantiation)
    (form : node.form = .call callee arguments (.declaration instantiation)) : DirectSite rows instantiation := by
  have member := supported_mem found (show supportedForm directOnly allowIndices allowConstructors node.form = true by simp [form, supportedForm, compositeSupportedForm, legacySupportedForm])
  have facts := profile.at_node member found
  simpa only [SiteReady, form] using facts.2.2.1

theorem compositeForms (profile : Profile prepared named source rows directOnly allowIndices allowConstructors) : ReachedOrdinaryForms source profile.Reached := by
  intro id node reached found
  rcases form_of_supported (profile.at_node reached found).1 with ((((leaf | direct | ⟨_, rest⟩) | ⟨_, _, index⟩) | ⟨_, _, constructor⟩) | ⟨_, composite⟩) | ⟨_, builtin⟩
  · exact .inl (.inl (.inl (.inl (.inl leaf))))
  · exact .inl (.inl (.inl (.inl (.inr (.inl direct)))))
  · exact .inl (.inl (.inl (.inl (.inr (.inr rest)))))
  · exact .inl (.inl (.inl (.inr index)))
  · exact .inl (.inl (.inr constructor))
  · exact .inl (.inr composite)
  · exact .inr builtin

theorem forms (profile : Profile prepared named source rows directOnly false false) : ReachedOrdinaryForms source profile.Reached := profile.compositeForms

theorem indexForms (profile : Profile prepared named source rows directOnly allowIndices false) : ReachedOrdinaryForms source profile.Reached := profile.compositeForms

theorem constructorForms (profile : Profile prepared named source rows directOnly allowIndices allowConstructors) : ReachedOrdinaryForms source profile.Reached := profile.compositeForms

theorem arguments (profile : Profile prepared named source rows directOnly allowIndices allowConstructors) : ReachedMethodArguments source profile.Reached := by
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · intro id node reached found callee arguments instantiation form child member
    exact (profile.at_node reached found).2.1 child (by simpa only [operands, form] using member)
  · intro id node reached found callee arguments metadata form
    have edges := (profile.at_node reached found).2.1
    refine ⟨edges callee ?_, ?_⟩
    · simp only [form, operands, List.mem_cons_self]
    · intro child member
      exact edges child (by simp only [form, operands, List.mem_cons]; exact .inr member)
  · intro id node reached found operator operand form
    exact (profile.at_node reached found).2.1 operand (by simp only [form, operands, List.mem_singleton])
  · intro id node reached found operator left right form
    have edges := (profile.at_node reached found).2.1
    exact ⟨edges left (by simp [form, operands]), edges right (by simp [form, operands])⟩

theorem rawMetadata (profile : Profile prepared named source rows directOnly allowIndices allowConstructors) : ReachedMethodMetadata prepared named source profile.Reached := by
  obtain ⟨receipt, accepted⟩ := profile.metadataAccepted
  exact ReachedMethodMetadata.of_accepted accepted

theorem noInitializer (profile : Profile prepared named source rows directOnly allowIndices allowConstructors) (id : ExpressionId) (reached : profile.Reached id) :
    ¬ Nonempty (AcceptedContextualDirectReceipt.InitializerAt prepared (context prepared named) id) := by
  obtain ⟨node, found, supported, _rest⟩ := profile.nodes id reached
  obtain ⟨receipt, accepted⟩ := profile.metadataAccepted
  have raw := AcceptedNamedExpressionMetadata.at_of_accepted accepted found (policy_supported supported)
  have empty := raw.2.1
  rw [(lookupExpression?_sound found).2] at empty
  rintro ⟨initializer⟩
  have impossible := initializer.found
  rw [empty] at impossible
  cases impossible

theorem directForms (profile : Profile prepared named source rows true allowIndices allowConstructors) : ReachedForms source profile.Reached := by
  intro id node reached found
  rcases form_of_supported (profile.at_node reached found).1 with ((((leaf | direct | ⟨impossible, _⟩) | ⟨_, impossible, _⟩) | ⟨_, impossible, _⟩) | ⟨impossible, _⟩) | ⟨impossible, _⟩
  · exact .inl leaf
  · exact .inr direct
  · cases impossible

  · cases impossible

  · cases impossible

  · cases impossible

  · cases impossible

theorem directArguments (profile : Profile prepared named source rows true allowIndices allowConstructors) : ReachedArguments source profile.Reached :=
  profile.arguments.1.1

theorem indexArguments (profile : Profile prepared named source rows directOnly allowIndices allowConstructors) : ReachedIndexArguments source profile.Reached := by
  refine ⟨profile.arguments, ?_⟩
  intro id node reached found base key form
  have edges := (profile.at_node reached found).2.1
  exact ⟨edges base (by simp [form, operands]), edges key (by simp [form, operands])⟩

theorem indexOperands (profile : Profile prepared named source rows directOnly allowIndices allowConstructors) : ReachedIndexOperands source profile.Reached := by
  intro id node reached found base key form
  simpa only [IndexReady, form] using (profile.at_node reached found).2.2.2.1

theorem indexMetadata (profile : Profile prepared named source rows directOnly allowIndices allowConstructors) : ReachedIndexMetadata prepared named source profile.Reached := by
  obtain ⟨receipt, accepted⟩ := profile.metadataAccepted
  exact ReachedIndexMetadata.of_accepted accepted

theorem constructorArguments (profile : Profile prepared named source rows directOnly allowIndices allowConstructors) : ReachedConstructorArguments source profile.Reached := by
  refine ⟨profile.indexArguments, ?_⟩
  intro id node reached found instantiation ids form child member
  exact (profile.at_node reached found).2.1 child (by simpa only [form, operands] using member)

theorem constructorRanges (profile : Profile prepared named source rows directOnly allowIndices allowConstructors) : ReachedConstructorRanges source profile.Reached := by
  intro id node reached found instantiation ids form
  simpa only [ConstructorReady, form] using (profile.at_node reached found).2.2.2.2

theorem constructorMetadata (profile : Profile prepared named source rows directOnly allowIndices allowConstructors) : ReachedConstructorMetadata prepared named source profile.Reached := by
  obtain ⟨receipt, accepted⟩ := profile.metadataAccepted
  exact ReachedConstructorMetadata.of_accepted accepted

theorem compositeArguments (profile : Profile prepared named source rows directOnly allowIndices allowConstructors) : ReachedCompositeArguments source profile.Reached := by
  refine ⟨profile.constructorArguments, ?_⟩
  intro id node reached found form child member
  apply (profile.at_node reached found).2.1 child
  generalize eq : node.form = shape at form
  cases form <;> simpa only [eq, operands, AcceptedCompositeExpressionReceipt.operands] using member

theorem compositeMetadata (profile : Profile prepared named source rows directOnly allowIndices allowConstructors) : ReachedCompositeMetadata prepared named source profile.Reached := by
  obtain ⟨receipt, accepted⟩ := profile.metadataAccepted
  exact ReachedCompositeMetadata.of_accepted accepted

theorem ordinaryArguments (profile : Profile prepared named source rows directOnly allowIndices allowConstructors) : ReachedOrdinaryArguments source profile.Reached := by
  refine ⟨profile.compositeArguments, ?_⟩
  intro id node reached found callee ids function form child member
  exact (profile.at_node reached found).2.1 child (by simpa only [form, operands] using member)

theorem ordinaryMetadata (profile : Profile prepared named source rows directOnly allowIndices allowConstructors) : ReachedOrdinaryMetadata prepared named source profile.Reached := by
  obtain ⟨receipt, accepted⟩ := profile.metadataAccepted
  exact ReachedOrdinaryMetadata.of_accepted accepted

end Profile

/-- Only finite tables are traversed. Child closure is checked against the
flat set, and all original metadata checks run on the unchanged source. -/
def certify {checked : SourceCoreCompatibleCatalog.Checked}
    (prepared : CallableIndexedNamedGeneration.Prepared checked) (named : Named)
    (source : TypedSource) (rows : List SourceSpecialization.SpecializedFunction)
    (directOnly : Bool := false) (allowIndices : Bool := false) (allowConstructors : Bool := false) : Option (Profile prepared named source rows directOnly allowIndices allowConstructors) := do
  let ⟨nodes⟩ ← allProof? (NodeReady source rows directOnly allowIndices allowConstructors) (node? source rows directOnly allowIndices allowConstructors)
    (supportedIds source directOnly allowIndices allowConstructors)
  match accepted : metadata? prepared named source (DirectSite rows) with
  | none => none
  | some receipt => pure ⟨nodes, ⟨receipt, accepted⟩⟩

def certifyDirect {checked : SourceCoreCompatibleCatalog.Checked}
    (prepared : CallableIndexedNamedGeneration.Prepared checked) (named : Named)
    (source : TypedSource) (rows : List SourceSpecialization.SpecializedFunction) :
    Option (Profile prepared named source rows true) := certify prepared named source rows true

end Solcore.SourceSemantics.CoreLowering.AcceptedCompilerExpressionProfile
end
