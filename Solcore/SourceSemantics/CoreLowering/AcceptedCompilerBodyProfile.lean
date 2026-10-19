import Solcore.SourceSemantics.CoreLowering.AcceptedNamedBodyFinish

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
