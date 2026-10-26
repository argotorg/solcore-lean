import Solcore.SourceSemantics.CoreLowering.CellAwareInvocationAcceptedFlow
import Solcore.SourceSemantics.CoreLowering.CellAwareInvocationAcceptedSubsetCheck

/-! Source statement lists that the accepted-body route closes at named rows:
value and unit returns, monomorphic declarations, bare assignments the
compiler refines, expression statements, blocks and conditionals, each with
its expressions in a given predicate. `Shape` recognizes these lists on the
Source; `covered` shows that every refined accepted tree of such a list is
covered by the statement closure, and `shape?` recognizes them on an actually
compiled row with subset-site expressions. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Solcore.SourceSemantics.CoreLowering.CellAwareInvocationAcceptedBodyShape
open Core Frontend SourceInference
open AcceptedNamedBodyFlow (Tree Assignable)
open CellAwareInvocationAcceptedFlow (Covered)

/-- Statement lists of the supported forms. A list may end without returning
only as a branch or block body, or in a Unit function; every expression of the
list satisfies `child`. -/
inductive Shape (source : TypedSource) (expected : TypeSystem.Ty) (child : ExpressionId → Prop) :
    Bool → List StatementId → Prop where
  | nil {mode : Bool} (allowed : mode = false ∨ expected = .unit) : Shape source expected child mode []
  | returned {mode : Bool} {id : StatementId} {rest : List StatementId} {node : StatementNode}
      {expression : ExpressionId} (found : source.lookupStatement? id = some node)
      (form : node.form = .returnStmt (some expression)) (value : child expression) :
      Shape source expected child mode (id :: rest)
  | returnUnit {mode : Bool} {id : StatementId} {rest : List StatementId} {node : StatementNode}
      (found : source.lookupStatement? id = some node) (form : node.form = .returnStmt none) :
      Shape source expected child mode (id :: rest)
  | declared {mode : Bool} {id : StatementId} {rest : List StatementId} {node : StatementNode}
      {binder : TypedBinder} {expression : ExpressionId} (found : source.lookupStatement? id = some node)
      (form : node.form = .letDecl binder (some expression)) (monomorphic : binder.scheme.quantified = [])
      (value : child expression) (tail : Shape source expected child mode rest) :
      Shape source expected child mode (id :: rest)
  | uninitialized {mode : Bool} {id : StatementId} {rest : List StatementId} {node : StatementNode}
      {binder : TypedBinder} (found : source.lookupStatement? id = some node)
      (form : node.form = .letDecl binder none) (monomorphic : binder.scheme.quantified = [])
      (tail : Shape source expected child mode rest) : Shape source expected child mode (id :: rest)
  | assigned {mode : Bool} {id : StatementId} {rest : List StatementId} {node : StatementNode}
      {assignment : AssignmentResolution} {operator : Syntax.ValueAssignOp} {expression : ExpressionId}
      (found : source.lookupStatement? id = some node) (form : node.form = .assignValue assignment operator expression)
      (assignable : Assignable source assignment operator) (value : child expression)
      (tail : Shape source expected child mode rest) : Shape source expected child mode (id :: rest)
  | discarded {mode : Bool} {id : StatementId} {rest : List StatementId} {node : StatementNode}
      {expression : ExpressionId} (found : source.lookupStatement? id = some node)
      (form : node.form = .expression expression true) (value : child expression)
      (tail : Shape source expected child mode rest) : Shape source expected child mode (id :: rest)
  | block {mode : Bool} {id : StatementId} {rest : List StatementId} {node : StatementNode}
      {statements : List StatementId} (found : source.lookupStatement? id = some node)
      (form : node.form = .block statements) (inner : Shape source expected child false statements)
      (tail : Shape source expected child mode rest) : Shape source expected child mode (id :: rest)
  | conditional {mode : Bool} {id : StatementId} {rest : List StatementId} {node : StatementNode}
      {condition : ExpressionId} {thenBody : List StatementId} {elseBody : Option (List StatementId)}
      (found : source.lookupStatement? id = some node) (form : node.form = .ifThen condition thenBody elseBody)
      (test : child condition) (left : Shape source expected child false thenBody)
      (right : Shape source expected child false (elseBody.getD []))
      (tail : Shape source expected child mode rest) : Shape source expected child mode (id :: rest)

/-- Proof-producing recognition of a bare assignment the compiler refines. -/
def assignable? (source : TypedSource) (assignment : AssignmentResolution) (operator : Syntax.ValueAssignOp) :
    Option (PLift (Assignable source assignment operator)) :=
  if operatorOk : operator = .equal ∨ assignment.target.type = .word then
    match bare : assignment.target.projections with
    | [] =>
      match root : SourceCoreDataPlaces.rootBinder source assignment.target.root with
      | .ok binder =>
        if typed : binder.scheme.body = assignment.target.type then
          some ⟨⟨operatorOk, bare, fun other found => by rw [root] at found; cases found; exact typed⟩⟩
        else none
      | .error _ => some ⟨⟨operatorOk, bare, fun other found => by rw [root] at found; cases found⟩⟩
    | _ :: _ => none
  else none

/-- Proof-producing recognition of a supported statement list whose expressions
are subset sites of the row. The fuel bounds the nesting of statement lists. -/
def shape? {checked : SourceCoreCompatibleCatalog.Checked} (prepared : CallableIndexedNamedGeneration.Prepared checked)
    (named : SourceCoreGeneralFunctions.Function) (source : TypedSource) (expected : TypeSystem.Ty) :
    (fuel : Nat) → (mode : Bool) → (statements : List StatementId) →
      Option (PLift (Shape source expected
        (CellAwareInvocationAcceptedExpressionTrees.Subset prepared named source) mode statements))
  | _, mode, [] => if allowed : mode = false ∨ expected = .unit then some ⟨.nil allowed⟩ else none
  | 0, _, _ :: _ => none
  | fuel + 1, mode, id :: rest =>
    match found : source.lookupStatement? id with
    | none => none
    | some node =>
      match form : node.form with
      | .returnStmt (some expression) => do
        let ⟨value⟩ ← CellAwareInvocationAcceptedSubsetCheck.subset? prepared named source
          (source.nodes.length + 1) expression
        pure ⟨.returned found form value⟩
      | .returnStmt none => pure ⟨.returnUnit found form⟩
      | .letDecl binder (some expression) =>
        match monomorphic : binder.scheme.quantified with
        | [] => do
          let ⟨value⟩ ← CellAwareInvocationAcceptedSubsetCheck.subset? prepared named source
            (source.nodes.length + 1) expression
          let ⟨tail⟩ ← shape? prepared named source expected fuel mode rest
          pure ⟨.declared found form monomorphic value tail⟩
        | _ :: _ => none
      | .letDecl binder none =>
        match monomorphic : binder.scheme.quantified with
        | [] => do
          let ⟨tail⟩ ← shape? prepared named source expected fuel mode rest
          pure ⟨.uninitialized found form monomorphic tail⟩
        | _ :: _ => none
      | .assignValue assignment operator expression => do
        let ⟨assignable⟩ ← assignable? source assignment operator
        let ⟨value⟩ ← CellAwareInvocationAcceptedSubsetCheck.subset? prepared named source
          (source.nodes.length + 1) expression
        let ⟨tail⟩ ← shape? prepared named source expected fuel mode rest
        pure ⟨.assigned found form assignable value tail⟩
      | .expression expression true => do
        let ⟨value⟩ ← CellAwareInvocationAcceptedSubsetCheck.subset? prepared named source
          (source.nodes.length + 1) expression
        let ⟨tail⟩ ← shape? prepared named source expected fuel mode rest
        pure ⟨.discarded found form value tail⟩
      | .block statements => do
        let ⟨inner⟩ ← shape? prepared named source expected fuel false statements
        let ⟨tail⟩ ← shape? prepared named source expected fuel mode rest
        pure ⟨.block found form inner tail⟩
      | .ifThen condition thenBody elseBody => do
        let ⟨test⟩ ← CellAwareInvocationAcceptedSubsetCheck.subset? prepared named source
          (source.nodes.length + 1) condition
        let ⟨left⟩ ← shape? prepared named source expected fuel false thenBody
        let ⟨right⟩ ← shape? prepared named source expected fuel false (elseBody.getD [])
        let ⟨tail⟩ ← shape? prepared named source expected fuel mode rest
        pure ⟨.conditional found form test left right tail⟩
      | _ => none

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
      obtain ⟨_, _, same⟩ := CompatibleEncoding.bind_ok accepted
      cases same
      rfl

/-- The first statement of a supported nonempty list is a form the compiler
expands. -/
private theorem head_expanded {source : TypedSource} {expected : TypeSystem.Ty} {child : ExpressionId → Prop}
    {mode : Bool} {id : StatementId} {rest : List StatementId}
    (shape : Shape source expected child mode (id :: rest)) :
    ∃ node, source.lookupStatement? id = some node ∧ AcceptedNamedBodyFlow.expanded node.form = true := by
  cases shape with
  | returned found form => exact ⟨_, found, by rw [form]; rfl⟩
  | returnUnit found form => exact ⟨_, found, by rw [form]; rfl⟩
  | declared found form => exact ⟨_, found, by rw [form]; rfl⟩
  | uninitialized found form => exact ⟨_, found, by rw [form]; rfl⟩
  | assigned found form => exact ⟨_, found, by rw [form]; rfl⟩
  | discarded found form => exact ⟨_, found, by rw [form]; rfl⟩
  | block found form => exact ⟨_, found, by rw [form]; rfl⟩
  | conditional found form => exact ⟨_, found, by rw [form]; rfl⟩

variable {whole : SourceCoreUnifiedCompilation.Compiled} {bodyRelation : ActualBodyInvocation.BodyRelation}

private theorem node_of_read (index : ActualBodyInvocation.Index whole bodyRelation) {id : StatementId}
    {node : StatementNode} {stored : Ty}
    (read : index.policy.readStatement index.compilerSource id = .ok (node, stored)) :
    index.compilerSource.lookupStatement? id = some node := by
  rw [index.statement_reader] at read
  exact read_found read

/-- Every refined accepted tree of a supported statement list is covered, for
every match and generalized input. -/
theorem covered (index : ActualBodyInvocation.Index whole bodyRelation) {semantic : TypedSource}
    {expected : TypeSystem.Ty} {admitted : SourceCoreCompatibleDataMatches.Context → Prop} {generalized : Prop}
    {child : ExpressionId → Prop} (sameSource : index.compilerSource = semantic) :
    ∀ {mode : Bool} {escaped : Word} {fuel : Nat} {scope : SourceCoreLocalCell.Scope}
      {statements : List StatementId} {code : Expr}
      (tree : Tree index.policy index.compilerSource index.result index.reasonAt mode escaped fuel scope
        statements code),
      tree.Ready → Shape index.compilerSource expected child mode statements →
      Covered semantic expected admitted generalized tree := by
  intro mode escaped fuel scope statements code tree
  induction tree with
  | nil =>
    intro _ shape
    cases shape with
    | nil allowed => exact allowed
  | returning => intro _ _; trivial
  | returnUnit => intro _ _; trivial
  | breaking => intro _ _; trivial
  | continuing => intro _ _; trivial
  | initialized read form _ _ _ _ _ _ _ ih =>
    intro ready shape
    cases shape with
    | declared found form' monomorphic _ tail =>
      obtain rfl := Option.some.inj ((node_of_read index read).symm.trans found)
      rw [form] at form'
      cases form'
      exact ⟨.inl monomorphic, ih ready tail⟩
    | _ =>
      exfalso
      obtain rfl := Option.some.inj ((node_of_read index read).symm.trans (by assumption))
      clear ih ready
      simp_all
  | absent read form _ _ _ _ ih =>
    intro ready shape
    cases shape with
    | uninitialized found form' _ tail =>
      obtain rfl := Option.some.inj ((node_of_read index read).symm.trans found)
      exact ih ready tail
    | _ =>
      exfalso
      obtain rfl := Option.some.inj ((node_of_read index read).symm.trans (by assumption))
      clear ih ready
      simp_all
  | assigning read form _ _ _ _ =>
    intro ready shape
    cases shape with
    | assigned found form' assignable _ _ =>
      obtain rfl := Option.some.inj ((node_of_read index read).symm.trans found)
      rw [form] at form'
      cases form'
      exact absurd (.inl assignable) ready.1
    | _ =>
      exfalso
      obtain rfl := Option.some.inj ((node_of_read index read).symm.trans (by assumption))
      clear ready
      simp_all
  | assigned read form _ _ _ _ ih =>
    intro ready shape
    cases shape with
    | assigned found _ _ _ tail =>
      obtain rfl := Option.some.inj ((node_of_read index read).symm.trans found)
      exact ⟨sameSource, ih ready tail⟩
    | _ =>
      exfalso
      obtain rfl := Option.some.inj ((node_of_read index read).symm.trans (by assumption))
      clear ih ready
      simp_all
  | projectedAssigned read form _ _ _ _ ih =>
    intro ready shape
    cases shape with
    | assigned found _ _ _ tail =>
      obtain rfl := Option.some.inj ((node_of_read index read).symm.trans found)
      exact ⟨sameSource, ih ready tail⟩
    | _ =>
      exfalso
      obtain rfl := Option.some.inj ((node_of_read index read).symm.trans (by assumption))
      clear ih ready
      simp_all
  | discard read form _ _ _ _ ih =>
    intro ready shape
    cases shape with
    | discarded found _ _ tail =>
      obtain rfl := Option.some.inj ((node_of_read index read).symm.trans found)
      exact ih ready tail
    | _ =>
      exfalso
      obtain rfl := Option.some.inj ((node_of_read index read).symm.trans (by assumption))
      clear ih ready
      simp_all
  | block read form _ _ innerIH tailIH =>
    intro ready shape
    cases shape with
    | block found form' inner tail =>
      obtain rfl := Option.some.inj ((node_of_read index read).symm.trans found)
      rw [form] at form'
      cases form'
      exact ⟨innerIH ready.1 inner, tailIH ready.2 tail⟩
    | _ =>
      exfalso
      obtain rfl := Option.some.inj ((node_of_read index read).symm.trans (by assumption))
      clear innerIH tailIH ready
      simp_all
  | conditional read form _ _ _ _ _ _ leftIH rightIH tailIH =>
    intro ready shape
    cases shape with
    | conditional found form' _ left right tail =>
      obtain rfl := Option.some.inj ((node_of_read index read).symm.trans found)
      rw [form] at form'
      cases form'
      exact ⟨leftIH ready.1 left, rightIH ready.2.1 right, tailIH ready.2.2 tail⟩
    | _ =>
      exfalso
      obtain rfl := Option.some.inj ((node_of_read index read).symm.trans (by assumption))
      clear leftIH rightIH tailIH ready
      simp_all
  | boundary read outside =>
    intro _ shape
    obtain ⟨_, found, expanded⟩ := head_expanded shape
    obtain rfl := Option.some.inj ((node_of_read index read).symm.trans found)
    rw [outside] at expanded
    cases expanded
  | _ =>
    intro _ shape
    exfalso
    cases shape <;>
    · obtain rfl := Option.some.inj ((node_of_read index (by assumption)).symm.trans (by assumption))
      simp_all

end Solcore.SourceSemantics.CoreLowering.CellAwareInvocationAcceptedBodyShape
