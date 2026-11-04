import Solcore.SourceSemantics.CoreLowering.AcceptedStatements
import Solcore.SourceSemantics.CoreLowering.AcceptedExpressions
import Solcore.SourceSemantics.CoreLowering.Internal.Compatible.ExpressionPrimitives
import Solcore.SourceSemantics.Staging.RecursiveAtomicLifting

/-!
# Accepted bodies: shapes and lifted traces

The premises of the accepted-body theorems, produced at an actual program: a shape that
can be checked on the Source, and a staged trace lifted from an independent execution.

Main declarations:
- `CellAwareInvocationAcceptedBodyShape.Shape` and
  `CellAwareInvocationAcceptedBodyShape.covered`, a Source shape that implies `Covered`;
- `CellAwareInvocationAcceptedSourceLifting.expression_value`, staging a value execution
  of a subset expression;
- `CellAwareInvocationAcceptedStatementLifting.statements` and
  `CellAwareInvocationAcceptedStatementLifting.body`, staging a shaped list and a function
  body.
-/

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CellAwareInvocationAcceptedBodyShape
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
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CellAwareInvocationAcceptedSourceLifting
/-! Original Source executions of closed-subset expressions are staged
executions. A subset expression contains no call, so every original value rule
at a subset site is the staged rule of the same form, and a generalized local
read keeps its descriptor and empty coercion path. Fault outcomes are not
lifted here; `CellAwareInvocationAcceptedStatementLifting` lifts statement
lists. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2000000
namespace Solcore.SourceSemantics.CoreLowering.CellAwareInvocationAcceptedSourceLifting
open Core Frontend SourceInference
open CallableIndexedNamedGeneration (Prepared)
open CellAwareNamedExpressionSyntax (Site)
open CellAwareInvocationAcceptedExpressionTrees (Subset)

variable {checked : SourceCoreCompatibleCatalog.Checked} {prepared : Prepared checked}
  {named : SourceCoreGeneralFunctions.Function} {program : Program} {registry : Staging.Recursive.Registry}
  {scope : Staging.Recursive.Scope} {context : SourceSemantics.Context}

private theorem node_unique (unique : NodeOccurrencesUnique scope.source) {id : ExpressionId}
    {left right : ExpressionNode} (first : ContainsExpression scope.source id left)
    (second : ContainsExpression scope.source id right) : left = right :=
  Option.some.inj ((lookupExpression?_complete unique first).symm.trans (lookupExpression?_complete unique second))

private theorem requirements_of {id : ExpressionId} (site : Site prepared named scope.source id)
    {form : ExpressionForm} (same : site.node.form = form)
    (notInteger : ∀ literal resolution, form ≠ .integerLiteral literal resolution) :
    site.node.requirements = [] := by
  have requirements := site.requirements
  split at requirements
  · rename_i literal resolution integer
    exact absurd (same.symm.trans integer) (notInteger literal resolution)
  · exact requirements

private theorem occurrence {id : ExpressionId} (site : Site prepared named scope.source id)
    {form : ExpressionForm} (same : site.node.form = form)
    (notInteger : ∀ literal resolution, form ≠ .integerLiteral literal resolution) :
    Staging.Recursive.Occurrence scope id form :=
  ⟨site.node, lookupExpression?_sound site.found, same, requirements_of site same notInteger, site.coercions⟩

private theorem atomic_form {form : ExpressionForm} (atomic : CompatibleExpressionLiterals.Atomic form) :
    Staging.Recursive.AtomicForm form := by
  cases atomic <;> constructor

private theorem atomic_not_local {form : ExpressionForm} (atomic : CompatibleExpressionLiterals.Atomic form)
    (name : String) (binder : Resolved.LocalId) : form ≠ .reference name (.local binder) := by
  cases atomic <;> intro same <;> cases same

/-- A value execution of a subset expression is a staged execution with the
same value and heap. -/
theorem expression_value (unique : NodeOccurrencesUnique scope.source) {id : ExpressionId}
    (subset : Subset prepared named scope.source id) :
    ∀ {environment : Dynamic.Environment} {before after : Dynamic.Heap} {value : Dynamic.Value},
      Dynamic.ExpressionEvaluates program context scope.evidence scope.source environment before id value after →
      Staging.Recursive.Expression program registry scope context environment before id (.value value) after := by
  induction subset with
  | literal site atomic =>
    intro environment before after value evaluation
    exact Staging.Recursive.Lifting.atomic unique (lookupExpression?_sound site.found) (atomic_form atomic)
      site.coercions (fun name binder _ _ same => absurd same (atomic_not_local atomic name binder))
      (.value evaluation)
  | read site form =>
    intro environment before after value evaluation
    have contains := lookupExpression?_sound site.found
    cases evaluation with
    | intro found raw coercions =>
      cases node_unique unique found contains
      rw [site.coercions] at coercions
      cases coercions
      rw [site.coercions] at raw
      exact .atomicValue contains (by rw [form]; exact .reference _ _) site.coercions raw
    | generalizedLocal found formEq layout lookup read descriptor contextFields instantiation coercions =>
      cases node_unique unique found contains
      rw [site.coercions] at coercions
      cases coercions
      exact .generalizedLocal contains formEq layout lookup read descriptor contextFields instantiation
        (by rw [site.coercions]; exact .coercionsNil)
  | unary site form _ child =>
    intro environment before after value evaluation
    have contains := lookupExpression?_sound site.found
    have raw := CompatibleExpressionPrimitives.evaluation_raw unique contains
      (fun name binder same => by rw [form] at same; cases same) site.coercions evaluation
    rw [form, requirements_of site form (fun _ _ same => by cases same), site.coercions] at raw
    cases raw with
    | unary layout operand applies =>
      have empty := CompatibleExpressionPrimitives.no_owned layout
      subst empty
      cases applies with
      | primitive applied =>
        exact .unary (occurrence site form (fun _ _ same => by cases same)) (child operand) applied
      | method _ selected _ => cases selected
  | binary site form _ _ left right =>
    intro environment before after value evaluation
    have contains := lookupExpression?_sound site.found
    have raw := CompatibleExpressionPrimitives.evaluation_raw unique contains
      (fun name binder same => by rw [form] at same; cases same) site.coercions evaluation
    rw [form, requirements_of site form (fun _ _ same => by cases same), site.coercions] at raw
    cases raw with
    | binaryShortCircuit _ first circuit _ =>
      exact .binaryShortCircuit (occurrence site form (fun _ _ same => by cases same)) (left first) circuit
    | binaryEvaluateRight layout first continues second applies =>
      have empty := CompatibleExpressionPrimitives.no_owned layout
      subst empty
      cases applies with
      | primitive applied =>
        exact .binary (occurrence site form (fun _ _ same => by cases same)) (left first) continues
          (right second) applied
      | method _ selected _ => cases selected
  | conditional site form _ _ _ test yes no =>
    intro environment before after value evaluation
    have contains := lookupExpression?_sound site.found
    have raw := CompatibleExpressionPrimitives.evaluation_raw unique contains
      (fun name binder same => by rw [form] at same; cases same) site.coercions evaluation
    rw [form, requirements_of site form (fun _ _ same => by cases same), site.coercions] at raw
    cases raw with
    | conditionalTrue _ first second =>
      exact .conditional (occurrence site form (fun _ _ same => by cases same)) (test first) (yes second)
    | conditionalFalse _ first second =>
      exact .conditional (occurrence site form (fun _ _ same => by cases same)) (test first) (no second)
  | group site form _ child =>
    intro environment before after value evaluation
    have contains := lookupExpression?_sound site.found
    have raw := CompatibleExpressionPrimitives.evaluation_raw unique contains
      (fun name binder same => by rw [form] at same; cases same) site.coercions evaluation
    rw [form, requirements_of site form (fun _ _ same => by cases same), site.coercions] at raw
    cases raw with
    | group _ inner => exact .group (occurrence site form (fun _ _ same => by cases same)) (child inner)
  | pair site form _ _ left right =>
    intro environment before after value evaluation
    have contains := lookupExpression?_sound site.found
    have raw := CompatibleExpressionPrimitives.evaluation_raw unique contains
      (fun name binder same => by rw [form] at same; cases same) site.coercions evaluation
    rw [form, requirements_of site form (fun _ _ same => by cases same), site.coercions] at raw
    cases raw with
    | tuple _ elements pack =>
      cases elements with
      | cons first rest =>
        cases rest with
        | cons second tail =>
          cases tail
          cases pack with
          | cons tail =>
            cases tail
            exact .pair (occurrence site form (fun _ _ same => by cases same)) (left first) (right second)

end Solcore.SourceSemantics.CoreLowering.CellAwareInvocationAcceptedSourceLifting
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CellAwareInvocationAcceptedStatementLifting
/-! Original Source executions of supported statement lists are staged
executions. Every statement of `CellAwareInvocationAcceptedBodyShape.Shape`
runs the same rule in both semantics once its subset expressions are staged:
declarations allocate the same cell, a bare assignment resolves its target
without changing the heap and writes it by the same rule, and blocks and
conditional arms restore their entry bindings while keeping their heap. Each
control outcome is carried unchanged, with the context, environment and heap
of the original execution. Fault executions are not lifted here. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Solcore.SourceSemantics.CoreLowering.CellAwareInvocationAcceptedStatementLifting
open Core Frontend SourceInference
open CallableIndexedNamedGeneration (Prepared)
open CellAwareInvocationAcceptedExpressionTrees (Subset)
open CellAwareInvocationAcceptedBodyShape (Shape)
open CellAwareInvocationAcceptedSourceLifting (expression_value)

/-- An ordinary control outcome as a staged body outcome. -/
def control : Dynamic.ControlOutcome → Staging.Recursive.BodyOutcome
  | .fallthrough environment => .fallthrough environment
  | .returned value => .returned value
  | .breaking environment => .breaking environment
  | .continuing environment => .continuing environment
  | .fault reason => .fault (.semantic reason)

/-- The ordinary statement-list judgment of each compiler mode: a function body
has the implicit final return, a branch or block body does not. -/
def Original (program : Program) : Bool → SourceSemantics.Context → Dynamic.EvidenceEnvironment → TypedSource →
    Dynamic.Environment → Dynamic.Heap → List StatementId → SourceSemantics.Context → Dynamic.ControlOutcome →
    Dynamic.Heap → Prop
  | true => Dynamic.FunctionStatementsExecute program
  | false => Dynamic.StatementsExecute program

section Inversion
variable {program : Program} {source : TypedSource} {context finalContext : SourceSemantics.Context}
  {evidence : Dynamic.EvidenceEnvironment} {environment : Dynamic.Environment} {before after : Dynamic.Heap}
  {id : StatementId} {node : StatementNode} {outcome : Dynamic.ControlOutcome}

private theorem same_node (unique : NodeOccurrencesUnique source) (found : source.lookupStatement? id = some node)
    {other : StatementNode} (contains : ContainsStatement source id other) : other = node :=
  Option.some.inj ((lookupStatement?_complete unique contains).symm.trans found)

private theorem returned_inv (unique : NodeOccurrencesUnique source) (found : source.lookupStatement? id = some node)
    {expression : ExpressionId} (form : node.form = .returnStmt (some expression))
    (head : Dynamic.StatementExecutes program context evidence source environment before id finalContext outcome after) :
    ∃ value, Dynamic.ExpressionEvaluates program context evidence source environment before expression value after ∧
      finalContext = context ∧ outcome = .returned value := by
  cases head with
  | returnValue contains formEq evaluate =>
    obtain rfl := same_node unique found contains
    rw [form] at formEq
    cases formEq
    exact ⟨_, evaluate, rfl, rfl⟩
  | _ =>
    exfalso
    obtain rfl := same_node unique found (by assumption)
    simp_all

private theorem return_unit_inv (unique : NodeOccurrencesUnique source) (found : source.lookupStatement? id = some node)
    (form : node.form = .returnStmt none)
    (head : Dynamic.StatementExecutes program context evidence source environment before id finalContext outcome after) :
    finalContext = context ∧ outcome = .returned .unit ∧ after = before := by
  cases head with
  | returnUnit => exact ⟨rfl, rfl, rfl⟩
  | _ =>
    exfalso
    obtain rfl := same_node unique found (by assumption)
    simp_all

private theorem declared_inv (unique : NodeOccurrencesUnique source) (found : source.lookupStatement? id = some node)
    {binder : TypedBinder} {expression : ExpressionId} (form : node.form = .letDecl binder (some expression))
    (monomorphic : binder.scheme.quantified = [])
    (head : Dynamic.StatementExecutes program context evidence source environment before id finalContext outcome after) :
    ∃ value middle location,
      Dynamic.ExpressionEvaluates program context evidence source environment before expression value middle ∧
      BinderExtends source.owner context binder finalContext ∧
      Dynamic.Heap.Allocates middle binder.scheme.body (some value) location after ∧
      outcome = .fallthrough ((binder.id, location) :: environment) := by
  cases head with
  | letInitialized contains formEq evaluate _ extension allocate =>
    obtain rfl := same_node unique found contains
    rw [form] at formEq
    cases formEq
    exact ⟨_, _, _, evaluate, extension, allocate, rfl⟩
  | letInitializedGeneralized contains formEq _ _ polymorphic _ _ =>
    obtain rfl := same_node unique found contains
    rw [form] at formEq
    cases formEq
    exact absurd monomorphic polymorphic
  | _ =>
    exfalso
    obtain rfl := same_node unique found (by assumption)
    simp_all

private theorem uninitialized_inv (unique : NodeOccurrencesUnique source)
    (found : source.lookupStatement? id = some node) {binder : TypedBinder} (form : node.form = .letDecl binder none)
    (head : Dynamic.StatementExecutes program context evidence source environment before id finalContext outcome after) :
    ∃ location, BinderExtends source.owner context binder finalContext ∧
      Dynamic.Heap.Allocates before binder.scheme.body none location after ∧
      outcome = .fallthrough ((binder.id, location) :: environment) := by
  cases head with
  | letUninitialized contains formEq _ extension allocate =>
    obtain rfl := same_node unique found contains
    rw [form] at formEq
    cases formEq
    exact ⟨_, extension, allocate, rfl⟩
  | _ =>
    exfalso
    obtain rfl := same_node unique found (by assumption)
    simp_all

private theorem assigned_inv (unique : NodeOccurrencesUnique source) (found : source.lookupStatement? id = some node)
    {assignment : AssignmentResolution} {operator : Syntax.ValueAssignOp} {expression : ExpressionId}
    (form : node.form = .assignValue assignment operator expression)
    (head : Dynamic.StatementExecutes program context evidence source environment before id finalContext outcome after) :
    ∃ updatedRoot, Dynamic.SourcePlaceAssignment program context evidence source
        (Dynamic.AssignmentValueApplies operator) environment before assignment.target expression updatedRoot after ∧
      finalContext = context ∧ outcome = .fallthrough environment := by
  cases head with
  | assignValue contains formEq executes =>
    obtain rfl := same_node unique found contains
    rw [form] at formEq
    cases formEq
    exact ⟨_, executes, rfl, rfl⟩
  | _ =>
    exfalso
    obtain rfl := same_node unique found (by assumption)
    simp_all

private theorem discarded_inv (unique : NodeOccurrencesUnique source) (found : source.lookupStatement? id = some node)
    {expression : ExpressionId} (form : node.form = .expression expression true)
    (head : Dynamic.StatementExecutes program context evidence source environment before id finalContext outcome after) :
    ∃ value, Dynamic.ExpressionEvaluates program context evidence source environment before expression value after ∧
      finalContext = context ∧ outcome = .fallthrough environment := by
  cases head with
  | expression contains formEq evaluate =>
    obtain rfl := same_node unique found contains
    rw [form] at formEq
    cases formEq
    exact ⟨_, evaluate, rfl, rfl⟩
  | _ =>
    exfalso
    obtain rfl := same_node unique found (by assumption)
    simp_all

private theorem block_inv (unique : NodeOccurrencesUnique source) (found : source.lookupStatement? id = some node)
    {statements : List StatementId} (form : node.form = .block statements)
    (head : Dynamic.StatementExecutes program context evidence source environment before id finalContext outcome after) :
    ∃ innerContext inner,
      Dynamic.StatementsExecute program context evidence source environment before statements innerContext inner after ∧
      finalContext = context ∧ outcome = Dynamic.restoreControl environment inner := by
  cases head with
  | block contains formEq executes =>
    obtain rfl := same_node unique found contains
    rw [form] at formEq
    cases formEq
    exact ⟨_, _, executes, rfl, rfl⟩
  | _ =>
    exfalso
    obtain rfl := same_node unique found (by assumption)
    simp_all

private theorem conditional_inv (unique : NodeOccurrencesUnique source)
    (found : source.lookupStatement? id = some node) {condition : ExpressionId} {thenBody : List StatementId}
    {elseBody : Option (List StatementId)} (form : node.form = .ifThen condition thenBody elseBody)
    (head : Dynamic.StatementExecutes program context evidence source environment before id finalContext outcome after) :
    finalContext = context ∧ ∃ truth middle innerContext inner,
      Dynamic.ExpressionEvaluates program context evidence source environment before condition (.bool truth) middle ∧
      Dynamic.StatementsExecute program context evidence source environment middle
        (if truth then thenBody else elseBody.getD []) innerContext inner after ∧
      outcome = Dynamic.restoreControl environment inner := by
  cases head with
  | ifTrue contains formEq test executes =>
    obtain rfl := same_node unique found contains
    rw [form] at formEq
    cases formEq
    exact ⟨rfl, true, _, _, _, test, executes, rfl⟩
  | ifFalseWithoutElse contains formEq test =>
    obtain rfl := same_node unique found contains
    rw [form] at formEq
    cases formEq
    exact ⟨rfl, false, _, _, _, test, .nil, rfl⟩
  | ifFalseWithElse contains formEq test executes =>
    obtain rfl := same_node unique found contains
    rw [form] at formEq
    cases formEq
    exact ⟨rfl, false, _, _, _, test, executes, rfl⟩
  | _ =>
    exfalso
    obtain rfl := same_node unique found (by assumption)
    simp_all
end Inversion

variable {checked : SourceCoreCompatibleCatalog.Checked} {prepared : Prepared checked}
  {named : SourceCoreGeneralFunctions.Function} {program : Program} {registry : Staging.Recursive.Registry}
  {scope : Staging.Recursive.Scope} {expected : TypeSystem.Ty}

/-- One statement followed by the rest of its list. A falling-through head runs
the rest; a terminal head ends the list. Both compiler modes share this
sequencing, except for the function body's implicit final value, which the
head form excludes. -/
private theorem sequence {mode : Bool} {id : StatementId} {rest : List StatementId} {node : StatementNode}
    (unique : NodeOccurrencesUnique scope.source) (found : scope.source.lookupStatement? id = some node)
    (notTail : ∀ expression, node.form ≠ .expression expression false)
    (step : ∀ {context environment before middleContext nextEnvironment middle finalContext outcome after},
      Dynamic.StatementExecutes program context scope.evidence scope.source environment before id middleContext
        (.fallthrough nextEnvironment) middle →
      Original program mode middleContext scope.evidence scope.source nextEnvironment middle rest finalContext
        outcome after →
      Staging.Recursive.StatementsIn program registry mode scope context environment before (id :: rest)
        finalContext (control outcome) after)
    (stop : ∀ {context environment before finalContext outcome after},
      Dynamic.StatementExecutes program context scope.evidence scope.source environment before id finalContext
        outcome after →
      Dynamic.TerminalControl outcome →
      Staging.Recursive.StatementsIn program registry mode scope context environment before (id :: rest)
        finalContext (control outcome) after) :
    ∀ {context environment before finalContext outcome after},
      Original program mode context scope.evidence scope.source environment before (id :: rest) finalContext
        outcome after →
      Staging.Recursive.StatementsIn program registry mode scope context environment before (id :: rest)
        finalContext (control outcome) after := by
  intro context environment before finalContext outcome after original
  cases mode with
  | false =>
    unfold Original at original
    cases original with
    | cons head next => exact step head next
    | terminal head terminal => exact stop head terminal
  | true =>
    unfold Original at original
    cases original with
    | tailExpression contains form _ =>
      obtain rfl := same_node unique found contains
      exact absurd form (notTail _)
    | singleton _ _ head =>
      cases outcome with
      | fallthrough nextEnvironment => exact step head .nil
      | returned value => exact stop head (.returned value)
      | breaking environment => exact stop head (.breaking environment)
      | continuing environment => exact stop head (.continuing environment)
      | fault reason => exact stop head (.fault reason)
    | cons head next => exact step head next
    | terminal head terminal => exact stop head terminal

/-- An ordinary execution of a supported statement list whose expressions are
subset sites is a staged execution with the same context, outcome and heap. -/
theorem statements (unique : NodeOccurrencesUnique scope.source) {mode : Bool} {statements : List StatementId}
    (shape : Shape scope.source expected (Subset prepared named scope.source) mode statements) :
    ∀ {context : SourceSemantics.Context} {environment : Dynamic.Environment} {before after : Dynamic.Heap}
      {finalContext : SourceSemantics.Context} {outcome : Dynamic.ControlOutcome},
      Original program mode context scope.evidence scope.source environment before statements finalContext
        outcome after →
      Staging.Recursive.StatementsIn program registry mode scope context environment before statements finalContext
        (control outcome) after := by
  induction shape with
  | @nil mode _ =>
    intro context environment before after finalContext outcome original
    cases mode <;> unfold Original at original <;> cases original <;> exact .nil
  | returned found form value =>
    intro context environment before after finalContext outcome
    apply sequence unique found (fun _ same => by rw [form] at same; cases same)
    · intro context environment before middleContext nextEnvironment middle finalContext outcome after head _
      obtain ⟨_, _, _, impossible⟩ := returned_inv unique found form head
      cases impossible
    · intro context environment before finalContext outcome after head _
      obtain ⟨_, evaluate, rfl, rfl⟩ := returned_inv unique found form head
      exact .returnValue (lookupStatement?_sound found) form (expression_value unique value evaluate)
  | returnUnit found form =>
    intro context environment before after finalContext outcome
    apply sequence unique found (fun _ same => by rw [form] at same; cases same)
    · intro context environment before middleContext nextEnvironment middle finalContext outcome after head _
      obtain ⟨_, impossible, _⟩ := return_unit_inv unique found form head
      cases impossible
    · intro context environment before finalContext outcome after head _
      obtain ⟨rfl, rfl, rfl⟩ := return_unit_inv unique found form head
      exact .returnUnit (lookupStatement?_sound found) form
  | declared found form monomorphic value _ tailIH =>
    intro context environment before after finalContext outcome
    apply sequence unique found (fun _ same => by rw [form] at same; cases same)
    · intro context environment before middleContext nextEnvironment middle finalContext outcome after head next
      obtain ⟨_, _, _, evaluate, extension, allocate, same⟩ := declared_inv unique found form monomorphic head
      cases same
      exact .letInitialized (lookupStatement?_sound found) form (expression_value unique value evaluate)
        monomorphic extension allocate (tailIH next)
    · intro context environment before finalContext outcome after head terminal
      obtain ⟨_, _, _, _, _, _, same⟩ := declared_inv unique found form monomorphic head
      subst same
      cases terminal
  | uninitialized found form monomorphic _ tailIH =>
    intro context environment before after finalContext outcome
    apply sequence unique found (fun _ same => by rw [form] at same; cases same)
    · intro context environment before middleContext nextEnvironment middle finalContext outcome after head next
      obtain ⟨_, extension, allocate, same⟩ := uninitialized_inv unique found form head
      cases same
      exact .letUninitialized (lookupStatement?_sound found) form monomorphic extension allocate (tailIH next)
    · intro context environment before finalContext outcome after head terminal
      obtain ⟨_, _, _, same⟩ := uninitialized_inv unique found form head
      subst same
      cases terminal
  | assigned found form assignable value _ tailIH =>
    intro context environment before after finalContext outcome
    apply sequence unique found (fun _ same => by rw [form] at same; cases same)
    · intro context environment before middleContext nextEnvironment middle finalContext outcome after head next
      obtain ⟨_, executes, rfl, same⟩ := assigned_inv unique found form head
      cases same
      cases executes with
      | intro resolve evaluate write =>
        obtain ⟨rfl, snapshot⟩ := Staging.Recursive.BareTarget.of_resolves assignable.2.1 resolve
        exact .assignBare (lookupStatement?_sound found) form snapshot (expression_value unique value evaluate)
          write (tailIH next)
    · intro context environment before finalContext outcome after head terminal
      obtain ⟨_, _, _, same⟩ := assigned_inv unique found form head
      subst same
      cases terminal
  | discarded found form value _ tailIH =>
    intro context environment before after finalContext outcome
    apply sequence unique found (fun _ same => by rw [form] at same; cases same)
    · intro context environment before middleContext nextEnvironment middle finalContext outcome after head next
      obtain ⟨_, evaluate, rfl, same⟩ := discarded_inv unique found form head
      cases same
      exact .discard (lookupStatement?_sound found) form (expression_value unique value evaluate) (tailIH next)
    · intro context environment before finalContext outcome after head terminal
      obtain ⟨_, _, _, same⟩ := discarded_inv unique found form head
      subst same
      cases terminal
  | block found form _ _ innerIH tailIH =>
    intro context environment before after finalContext outcome
    apply sequence unique found (fun _ same => by rw [form] at same; cases same)
    · intro context environment before middleContext nextEnvironment middle finalContext outcome after head next
      obtain ⟨_, inner, executes, rfl, same⟩ := block_inv unique found form head
      cases inner with
      | fallthrough innerEnvironment =>
        cases same
        exact .blockFallthrough (lookupStatement?_sound found) form (innerIH executes) (tailIH next)
      | _ => cases same
    · intro context environment before finalContext outcome after head terminal
      obtain ⟨_, inner, executes, rfl, rfl⟩ := block_inv unique found form head
      have staged := innerIH executes
      cases inner with
      | fallthrough => cases terminal
      | returned => exact .blockReturned (lookupStatement?_sound found) form staged
      | breaking => exact .blockBreaking (lookupStatement?_sound found) form staged
      | continuing => exact .blockContinuing (lookupStatement?_sound found) form staged
      | fault => exact .blockFault (lookupStatement?_sound found) form staged
  | @conditional mode id rest node condition thenBody elseBody found form test _ _ _ leftIH rightIH tailIH =>
    intro context environment before after finalContext outcome
    have branch : ∀ {truth : Bool} {context environment before innerContext inner after},
        Dynamic.StatementsExecute program context scope.evidence scope.source environment before
          (if truth then thenBody else elseBody.getD []) innerContext inner after →
        Staging.Recursive.StatementsIn program registry false scope context environment before
          (if truth then thenBody else elseBody.getD []) innerContext (control inner) after := by
      intro truth context environment before innerContext inner after executes
      cases truth
      · exact rightIH executes
      · exact leftIH executes
    apply sequence unique found (fun _ same => by rw [form] at same; cases same)
    · intro context environment before middleContext nextEnvironment middle finalContext outcome after head next
      obtain ⟨rfl, truth, _, _, inner, evaluate, executes, same⟩ := conditional_inv unique found form head
      cases inner with
      | fallthrough innerEnvironment =>
        cases same
        exact .ifFallthrough (lookupStatement?_sound found) form (expression_value unique test evaluate)
          (branch executes) (tailIH next)
      | _ => cases same
    · intro context environment before finalContext outcome after head terminal
      obtain ⟨rfl, truth, _, _, inner, evaluate, executes, rfl⟩ := conditional_inv unique found form head
      have staged := branch executes
      have tested := expression_value (registry := registry) unique test evaluate
      cases inner with
      | fallthrough => cases terminal
      | returned => exact .ifReturned (lookupStatement?_sound found) form tested staged
      | breaking => exact .ifBreaking (lookupStatement?_sound found) form tested staged
      | continuing => exact .ifContinuing (lookupStatement?_sound found) form tested staged
      | fault => exact .ifFault (lookupStatement?_sound found) form tested staged

/-- An ordinary function-body execution of a supported list whose expressions
are subset sites is a staged execution with the same context, outcome and heap,
at any scope with the execution's Source and evidence. -/
theorem body {source : TypedSource} {evidence : Dynamic.EvidenceEnvironment}
    (sourceEq : scope.source = source) (evidenceEq : scope.evidence = evidence)
    (unique : NodeOccurrencesUnique source) {statements : List StatementId}
    (shape : Shape source expected (Subset prepared named source) true statements)
    {context : SourceSemantics.Context} {environment : Dynamic.Environment} {before after : Dynamic.Heap}
    {finalContext : SourceSemantics.Context} {outcome : Dynamic.ControlOutcome}
    (trace : Dynamic.FunctionStatementsExecute program context evidence source environment before statements
      finalContext outcome after) :
    ∃ size, Staging.Recursive.Size.Statements program registry size scope context environment before statements
      finalContext (control outcome) after := by
  subst sourceEq evidenceEq
  exact Staging.Recursive.Size.Statements.of_trace (CellAwareInvocationAcceptedStatementLifting.statements
    (registry := registry) unique shape trace)

end Solcore.SourceSemantics.CoreLowering.CellAwareInvocationAcceptedStatementLifting
end
