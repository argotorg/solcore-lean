import Solcore.SourceSemantics.CoreLowering.AcceptedStatements
import Solcore.SourceSemantics.CoreLowering.AcceptedExpressions
import Solcore.SourceSemantics.CoreLowering.Internal.Compatible.ExpressionPrimitives
import Solcore.SourceSemantics.Staging.Erasure
import Solcore.SourceSemantics.CoreLowering.Internal.CellAware.ElementTargetLifting

/-!
# Accepted bodies: shapes and lifted traces

The premises of the accepted-body theorems, produced at an actual program: a shape that
can be checked on the Source, and a staged trace lifted from an independent execution. The
shape includes a function body's final value.

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
value and unit returns, monomorphic declarations, bare assignments, assignments
through mapping indices and in-place `~`, bare or through mapping indices, that
the compiler refines, expression statements, blocks, conditionals, matches, `while` and
`for` loops with headers of these forms, `break` and `continue`, and a function body's final value of its
declared type, each with its expressions in a given predicate. `Shape` recognizes these lists on the
Source; `covered` shows that every refined accepted tree of such a list whose
match receipts are at admitted contexts is covered by the statement closure,
and `shapeWith?` recognizes them on an actually compiled row with the
expressions a given check admits; `shape?` is its instance at subset sites. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Solcore.SourceSemantics.CoreLowering.CellAwareInvocationAcceptedBodyShape
open Core Frontend SourceInference
open AcceptedNamedBodyFlow (Tree Assignable ProjectedAssignable BitNotAssignable ProjectedBitNotAssignable)
open AcceptedNamedBodyFlow (ElementAssignable ElementBitNotAssignable)
open CellAwareInvocationAcceptedFlow (Covered)

/-- For-header vectors of the supported forms: monomorphic declarations,
expression items, and bare assignments, assignments through mapping indices
and in-place `~`, bare or through mapping indices, that the compiler refines,
each with its expressions in `child`. -/
inductive ItemsShape (source : TypedSource) (child : ExpressionId → Prop) : List ForItemForm → Prop where
  | nil : ItemsShape source child []
  | absent {binder : TypedBinder} {rest : List ForItemForm} (monomorphic : binder.scheme.quantified = [])
      (tail : ItemsShape source child rest) : ItemsShape source child (.letDecl binder none :: rest)
  | initialized {binder : TypedBinder} {expression : ExpressionId} {rest : List ForItemForm}
      (monomorphic : binder.scheme.quantified = []) (value : child expression)
      (tail : ItemsShape source child rest) : ItemsShape source child (.letDecl binder (some expression) :: rest)
  | discarded {expression : ExpressionId} {rest : List ForItemForm} (value : child expression)
      (tail : ItemsShape source child rest) : ItemsShape source child (.expression expression :: rest)
  | assigned {assignment : AssignmentResolution} {operator : Syntax.ValueAssignOp} {expression : ExpressionId}
      {rest : List ForItemForm} (assignable : Assignable source assignment operator) (value : child expression)
      (tail : ItemsShape source child rest) :
      ItemsShape source child (.assignValue assignment operator expression :: rest)
  | projectedAssigned {assignment : AssignmentResolution} {operator : Syntax.ValueAssignOp}
      {expression : ExpressionId} {rest : List ForItemForm}
      (assignable : ProjectedAssignable source assignment operator)
      (keys : ∀ projection ∈ assignment.target.projections, ∃ key, projection = .index key ∧ child key)
      (value : child expression) (tail : ItemsShape source child rest) :
      ItemsShape source child (.assignValue assignment operator expression :: rest)
  | bitNotted {assignment : AssignmentResolution} {rest : List ForItemForm}
      (assignable : BitNotAssignable source assignment) (tail : ItemsShape source child rest) :
      ItemsShape source child (.assignBitNot assignment :: rest)
  | projectedBitNotted {assignment : AssignmentResolution} {rest : List ForItemForm}
      (assignable : ProjectedBitNotAssignable source assignment)
      (keys : ∀ projection ∈ assignment.target.projections, ∃ key, projection = .index key ∧ child key)
      (tail : ItemsShape source child rest) : ItemsShape source child (.assignBitNot assignment :: rest)

/-- Statement lists of the supported forms. A list may end without returning
only as a branch or block body, or in a Unit function, and a function body may
end in a value whose node has the expected type; every expression of the list
satisfies `child`. The arms of a match and its default, when it has one, are
branch bodies. -/
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
  | projectedAssigned {mode : Bool} {id : StatementId} {rest : List StatementId} {node : StatementNode}
      {assignment : AssignmentResolution} {operator : Syntax.ValueAssignOp} {expression : ExpressionId}
      (found : source.lookupStatement? id = some node) (form : node.form = .assignValue assignment operator expression)
      (assignable : ProjectedAssignable source assignment operator)
      (keys : ∀ projection ∈ assignment.target.projections, ∃ key, projection = .index key ∧ child key)
      (value : child expression)
      (tail : Shape source expected child mode rest) : Shape source expected child mode (id :: rest)
  | bitNotted {mode : Bool} {id : StatementId} {rest : List StatementId} {node : StatementNode}
      {assignment : AssignmentResolution} (found : source.lookupStatement? id = some node)
      (form : node.form = .assignBitNot assignment) (assignable : BitNotAssignable source assignment)
      (tail : Shape source expected child mode rest) : Shape source expected child mode (id :: rest)
  | projectedBitNotted {mode : Bool} {id : StatementId} {rest : List StatementId} {node : StatementNode}
      {assignment : AssignmentResolution} (found : source.lookupStatement? id = some node)
      (form : node.form = .assignBitNot assignment) (assignable : ProjectedBitNotAssignable source assignment)
      (keys : ∀ projection ∈ assignment.target.projections, ∃ key, projection = .index key ∧ child key)
      (tail : Shape source expected child mode rest) : Shape source expected child mode (id :: rest)
  | elementAssigned {mode : Bool} {id : StatementId} {rest : List StatementId} {node : StatementNode}
      {assignment : AssignmentResolution} {operator : Syntax.ValueAssignOp} {expression key : ExpressionId}
      (found : source.lookupStatement? id = some node) (form : node.form = .assignValue assignment operator expression)
      (assignable : ElementAssignable assignment operator) (single : assignment.target.projections = [.element key])
      (index : child key) (value : child expression)
      (tail : Shape source expected child mode rest) : Shape source expected child mode (id :: rest)
  | elementBitNotted {mode : Bool} {id : StatementId} {rest : List StatementId} {node : StatementNode}
      {assignment : AssignmentResolution} {key : ExpressionId} (found : source.lookupStatement? id = some node)
      (form : node.form = .assignBitNot assignment) (assignable : ElementBitNotAssignable assignment)
      (single : assignment.target.projections = [.element key]) (index : child key)
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
  | matched {mode : Bool} {id : StatementId} {rest : List StatementId} {node : StatementNode}
      {resolution : MatchResolution} (found : source.lookupStatement? id = some node)
      (form : node.form = .matchWith resolution) (scrutinee : child resolution.scrutinee)
      (arms : ∀ arm ∈ resolution.cases, Shape source expected child false arm.body)
      (fallback : Shape source expected child false (resolution.defaultBody.getD []))
      (tail : Shape source expected child mode rest) : Shape source expected child mode (id :: rest)
  | breaking {mode : Bool} {id : StatementId} {rest : List StatementId} {node : StatementNode}
      (found : source.lookupStatement? id = some node) (form : node.form = .breakStmt) :
      Shape source expected child mode (id :: rest)
  | continuing {mode : Bool} {id : StatementId} {rest : List StatementId} {node : StatementNode}
      (found : source.lookupStatement? id = some node) (form : node.form = .continueStmt) :
      Shape source expected child mode (id :: rest)
  | whileLooped {mode : Bool} {id : StatementId} {rest : List StatementId} {node : StatementNode}
      {condition : ExpressionId} {body : List StatementId}
      (found : source.lookupStatement? id = some node) (form : node.form = .whileLoop condition body)
      (test : child condition) (inner : Shape source expected child false body)
      (tail : Shape source expected child mode rest) : Shape source expected child mode (id :: rest)
  | forLooped {mode : Bool} {id : StatementId} {rest : List StatementId} {node : StatementNode}
      {initializer : List ForItemForm} {condition : ExpressionId} {post : List ForItemForm}
      {body : List StatementId} (found : source.lookupStatement? id = some node)
      (form : node.form = .forLoop initializer condition post body) (initial : ItemsShape source child initializer)
      (test : child condition) (inner : Shape source expected child false body)
      (after : ItemsShape source child post) (tail : Shape source expected child mode rest) :
      Shape source expected child mode (id :: rest)
  | tail {id : StatementId} {node : StatementNode} {expression : ExpressionId}
      (found : source.lookupStatement? id = some node) (form : node.form = .expression expression false)
      (typed : ∀ expressionNode, source.lookupExpression? expression = some expressionNode →
        expressionNode.type = expected)
      (value : child expression) : Shape source expected child true [id]

/-- Proof-producing recognition of a final value's node of the expected type,
as `Covered` asks. -/
def tailTyped? (source : TypedSource) (expected : TypeSystem.Ty) (expression : ExpressionId) :
    Option (PLift (∀ expressionNode, source.lookupExpression? expression = some expressionNode →
      expressionNode.type = expected)) :=
  match found : source.lookupExpression? expression with
  | some node =>
    if typed : node.type = expected then
      some ⟨fun other same => by cases same; exact typed⟩
    else none
  | none => none

/-- Proof-producing recognition of a bare assignment the compiler refines. -/
def assignable? (source : TypedSource) (assignment : AssignmentResolution) (operator : Syntax.ValueAssignOp) :
    Option (PLift (Assignable source assignment operator)) :=
  if operatorOk : (operator = .equal ∨ assignment.target.type = .word) ∨ FixedCompoundAssignment operator assignment.target.type then
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

/-- Proof-producing recognition of a mapping route. -/
def route? (source : TypedSource) : (root : TypeSystem.Ty) → (projections : List PlaceProjection) →
    (leaf : TypeSystem.Ty) → Option (PLift (AcceptedProjectedAssignmentRoute.Route source root projections leaf))
  | root, [], leaf => if same : root = leaf then some ⟨by subst same; exact .nil⟩ else none
  | .mapping keyType valueType, .index key :: rest, leaf =>
    match found : source.lookupExpression? key with
    | some node =>
      if same : node.type = keyType then do
        let ⟨tail⟩ ← route? source valueType rest leaf
        pure ⟨.index found same tail⟩
      else none
    | none => none
  | _, _, _ => none

/-- Proof-producing recognition of an assignment through mapping indices the
compiler refines. -/
def projectedAssignable? (source : TypedSource) (assignment : AssignmentResolution)
    (operator : Syntax.ValueAssignOp) : Option (PLift (ProjectedAssignable source assignment operator)) :=
  if operatorOk : (operator = .equal ∨ assignment.target.type = .word) ∨ FixedCompoundAssignment operator assignment.target.type then
    if projected : assignment.target.projections ≠ [] then
      match root : SourceCoreDataPlaces.rootBinder source assignment.target.root with
      | .ok binder => do
        let ⟨route⟩ ← route? source binder.scheme.body assignment.target.projections assignment.target.type
        pure ⟨⟨operatorOk, projected, fun other found => by rw [root] at found; cases found; exact route⟩⟩
      | .error _ => some ⟨⟨operatorOk, projected, fun other found => by rw [root] at found; cases found⟩⟩
    else none
  else none

/-- Proof-producing recognition of a path of mapping indices whose keys `child?`
admits. -/
def indexKeys? {child : ExpressionId → Prop} (child? : (id : ExpressionId) → Option (PLift (child id))) :
    (projections : List PlaceProjection) →
      Option (PLift (∀ projection ∈ projections, ∃ key, projection = .index key ∧ child key))
  | [] => some ⟨fun _ member => by cases member⟩
  | .index key :: rest => do
    let ⟨head⟩ ← child? key
    let ⟨tail⟩ ← indexKeys? child? rest
    pure ⟨fun projection member => by
      rcases List.mem_cons.mp member with same | member
      · exact ⟨key, same, head⟩
      · exact tail projection member⟩
  | _ :: _ => none

/-- A path of mapping indices has no element projection. -/
theorem indices_no_element {child : ExpressionId → Prop} {projections leading : List PlaceProjection}
    {index : ExpressionId} (keys : ∀ projection ∈ projections, ∃ key, projection = .index key ∧ child key) :
    projections ≠ leading ++ [.element index] := by
  intro same
  obtain ⟨key, wrong, _⟩ := keys (.element index) (by rw [same]; simp)
  cases wrong

/-- Proof-producing recognition of a bare in-place `~` the compiler refines. -/
def bitNotAssignable? (source : TypedSource) (assignment : AssignmentResolution) :
    Option (PLift (BitNotAssignable source assignment)) :=
  if profile : assignment.target.type = .word ∨ ∃ type, assignment.target.type = .fixed type then
    match bare : assignment.target.projections with
    | [] =>
      match root : SourceCoreDataPlaces.rootBinder source assignment.target.root with
      | .ok binder =>
        if typed : binder.scheme.body = assignment.target.type then
          some ⟨⟨profile, bare, fun other found => by rw [root] at found; cases found; exact typed⟩⟩
        else none
      | .error _ => some ⟨⟨profile, bare, fun other found => by rw [root] at found; cases found⟩⟩
    | _ :: _ => none
  else none

/-- Proof-producing recognition of an in-place `~` through mapping indices the
compiler refines. -/
def projectedBitNotAssignable? (source : TypedSource) (assignment : AssignmentResolution) :
    Option (PLift (ProjectedBitNotAssignable source assignment)) :=
  if profile : assignment.target.type = .word ∨ ∃ type, assignment.target.type = .fixed type then
    if projected : assignment.target.projections ≠ [] then
      match root : SourceCoreDataPlaces.rootBinder source assignment.target.root with
      | .ok binder => do
        let ⟨route⟩ ← route? source binder.scheme.body assignment.target.projections assignment.target.type
        pure ⟨⟨profile, projected, fun other found => by rw [root] at found; cases found; exact route⟩⟩
      | .error _ => some ⟨⟨profile, projected, fun other found => by rw [root] at found; cases found⟩⟩
    else none
  else none

/-- Proof-producing recognition of a supported header vector whose
expressions satisfy `child`, which `child?` checks. -/
def itemsWith? (source : TypedSource) (child : ExpressionId → Prop)
    (child? : (id : ExpressionId) → Option (PLift (child id))) :
    (items : List ForItemForm) → Option (PLift (ItemsShape source child items))
  | [] => some ⟨.nil⟩
  | .letDecl binder none :: rest =>
    match monomorphic : binder.scheme.quantified with
    | [] => do
      let ⟨tail⟩ ← itemsWith? source child child? rest
      pure ⟨.absent monomorphic tail⟩
    | _ :: _ => none
  | .letDecl binder (some expression) :: rest =>
    match monomorphic : binder.scheme.quantified with
    | [] => do
      let ⟨value⟩ ← child? expression
      let ⟨tail⟩ ← itemsWith? source child child? rest
      pure ⟨.initialized monomorphic value tail⟩
    | _ :: _ => none
  | .expression expression :: rest => do
    let ⟨value⟩ ← child? expression
    let ⟨tail⟩ ← itemsWith? source child child? rest
    pure ⟨.discarded value tail⟩
  | .assignValue assignment operator expression :: rest =>
    match assignable? source assignment operator with
    | some ⟨assignable⟩ => do
      let ⟨value⟩ ← child? expression
      let ⟨tail⟩ ← itemsWith? source child child? rest
      pure ⟨.assigned assignable value tail⟩
    | none => do
      let ⟨assignable⟩ ← projectedAssignable? source assignment operator
      let ⟨keys⟩ ← indexKeys? child? assignment.target.projections
      let ⟨value⟩ ← child? expression
      let ⟨tail⟩ ← itemsWith? source child child? rest
      pure ⟨.projectedAssigned assignable keys value tail⟩
  | .assignBitNot assignment :: rest =>
    match bitNotAssignable? source assignment with
    | some ⟨assignable⟩ => do
      let ⟨tail⟩ ← itemsWith? source child child? rest
      pure ⟨.bitNotted assignable tail⟩
    | none => do
      let ⟨assignable⟩ ← projectedBitNotAssignable? source assignment
      let ⟨keys⟩ ← indexKeys? child? assignment.target.projections
      let ⟨tail⟩ ← itemsWith? source child child? rest
      pure ⟨.projectedBitNotted assignable keys tail⟩

/-- Proof-producing recognition of match arms whose bodies `body?` recognizes. -/
def armsWith? {body : List StatementId → Prop}
    (body? : (statements : List StatementId) → Option (PLift (body statements))) :
    (cases : List TypedMatchCase) → Option (PLift (∀ arm ∈ cases, body arm.body))
  | [] => some ⟨fun _ member => by cases member⟩
  | arm :: rest => do
    let ⟨head⟩ ← body? arm.body
    let ⟨tail⟩ ← armsWith? body? rest
    pure ⟨fun other member => by
      rcases List.mem_cons.mp member with same | member
      · subst same
        exact head
      · exact tail other member⟩

/-- Proof-producing recognition of a supported statement list whose
expressions satisfy `child`, which `child?` checks. The fuel bounds the nesting
of statement lists. -/
def shapeWith? (source : TypedSource) (expected : TypeSystem.Ty) (child : ExpressionId → Prop)
    (child? : (id : ExpressionId) → Option (PLift (child id))) :
    (fuel : Nat) → (mode : Bool) → (statements : List StatementId) →
      Option (PLift (Shape source expected child mode statements))
  | _, mode, [] => if allowed : mode = false ∨ expected = .unit then some ⟨.nil allowed⟩ else none
  | 0, _, _ :: _ => none
  | fuel + 1, mode, id :: rest =>
    match found : source.lookupStatement? id with
    | none => none
    | some node =>
      match form : node.form with
      | .returnStmt (some expression) => do
        let ⟨value⟩ ← child? expression
        pure ⟨.returned found form value⟩
      | .returnStmt none => pure ⟨.returnUnit found form⟩
      | .letDecl binder (some expression) =>
        match monomorphic : binder.scheme.quantified with
        | [] => do
          let ⟨value⟩ ← child? expression
          let ⟨tail⟩ ← shapeWith? source expected child child? fuel mode rest
          pure ⟨.declared found form monomorphic value tail⟩
        | _ :: _ => none
      | .letDecl binder none =>
        match monomorphic : binder.scheme.quantified with
        | [] => do
          let ⟨tail⟩ ← shapeWith? source expected child child? fuel mode rest
          pure ⟨.uninitialized found form monomorphic tail⟩
        | _ :: _ => none
      | .assignValue assignment operator expression =>
        match assignable? source assignment operator with
        | some ⟨assignable⟩ => do
          let ⟨value⟩ ← child? expression
          let ⟨tail⟩ ← shapeWith? source expected child child? fuel mode rest
          pure ⟨.assigned found form assignable value tail⟩
        | none =>
          match single : assignment.target.projections with
          | [.element key] =>
            if operatorOk : (operator = .equal ∨ assignment.target.type = .word) ∨
                FixedCompoundAssignment operator assignment.target.type then do
              let ⟨index⟩ ← child? key
              let ⟨value⟩ ← child? expression
              let ⟨tail⟩ ← shapeWith? source expected child child? fuel mode rest
              pure ⟨.elementAssigned found form ⟨operatorOk, key, single⟩ single index value tail⟩
            else none
          | _ => do
            let ⟨assignable⟩ ← projectedAssignable? source assignment operator
            let ⟨keys⟩ ← indexKeys? child? assignment.target.projections
            let ⟨value⟩ ← child? expression
            let ⟨tail⟩ ← shapeWith? source expected child child? fuel mode rest
            pure ⟨.projectedAssigned found form assignable keys value tail⟩
      | .assignBitNot assignment =>
        match bitNotAssignable? source assignment with
        | some ⟨assignable⟩ => do
          let ⟨tail⟩ ← shapeWith? source expected child child? fuel mode rest
          pure ⟨.bitNotted found form assignable tail⟩
        | none =>
          match single : assignment.target.projections with
          | [.element key] =>
            if profile : assignment.target.type = .word ∨ ∃ type, assignment.target.type = .fixed type then do
              let ⟨index⟩ ← child? key
              let ⟨tail⟩ ← shapeWith? source expected child child? fuel mode rest
              pure ⟨.elementBitNotted found form ⟨profile, key, single⟩ single index tail⟩
            else none
          | _ => do
            let ⟨assignable⟩ ← projectedBitNotAssignable? source assignment
            let ⟨keys⟩ ← indexKeys? child? assignment.target.projections
            let ⟨tail⟩ ← shapeWith? source expected child child? fuel mode rest
            pure ⟨.projectedBitNotted found form assignable keys tail⟩
      | .expression expression true => do
        let ⟨value⟩ ← child? expression
        let ⟨tail⟩ ← shapeWith? source expected child child? fuel mode rest
        pure ⟨.discarded found form value tail⟩
      | .expression expression false =>
        match mode, rest with
        | true, [] => do
          let ⟨value⟩ ← child? expression
          let ⟨typed⟩ ← tailTyped? source expected expression
          pure ⟨.tail found form typed value⟩
        | _, _ => none
      | .block statements => do
        let ⟨inner⟩ ← shapeWith? source expected child child? fuel false statements
        let ⟨tail⟩ ← shapeWith? source expected child child? fuel mode rest
        pure ⟨.block found form inner tail⟩
      | .ifThen condition thenBody elseBody => do
        let ⟨test⟩ ← child? condition
        let ⟨left⟩ ← shapeWith? source expected child child? fuel false thenBody
        let ⟨right⟩ ← shapeWith? source expected child child? fuel false (elseBody.getD [])
        let ⟨tail⟩ ← shapeWith? source expected child child? fuel mode rest
        pure ⟨.conditional found form test left right tail⟩
      | .breakStmt => pure ⟨.breaking found form⟩
      | .continueStmt => pure ⟨.continuing found form⟩
      | .whileLoop condition body => do
        let ⟨test⟩ ← child? condition
        let ⟨inner⟩ ← shapeWith? source expected child child? fuel false body
        let ⟨tail⟩ ← shapeWith? source expected child child? fuel mode rest
        pure ⟨.whileLooped found form test inner tail⟩
      | .forLoop initializer condition post body => do
        let ⟨initial⟩ ← itemsWith? source child child? initializer
        let ⟨test⟩ ← child? condition
        let ⟨inner⟩ ← shapeWith? source expected child child? fuel false body
        let ⟨after⟩ ← itemsWith? source child child? post
        let ⟨tail⟩ ← shapeWith? source expected child child? fuel mode rest
        pure ⟨.forLooped found form initial test inner after tail⟩
      | .matchWith resolution => do
        let ⟨scrutinee⟩ ← child? resolution.scrutinee
        let ⟨arms⟩ ← armsWith? (fun statements => shapeWith? source expected child child? fuel false statements)
          resolution.cases
        let ⟨fallback⟩ ← shapeWith? source expected child child? fuel false (resolution.defaultBody.getD [])
        let ⟨tail⟩ ← shapeWith? source expected child child? fuel mode rest
        pure ⟨.matched found form scrutinee arms fallback tail⟩

/-- Proof-producing recognition of a supported statement list whose expressions
are subset sites of the row. The fuel bounds the nesting of statement lists. -/
def shape? {checked : SourceCoreCompatibleCatalog.Checked} (prepared : CallableIndexedNamedGeneration.Prepared checked)
    (named : SourceCoreGeneralFunctions.Function) (source : TypedSource) (expected : TypeSystem.Ty) :
    (fuel : Nat) → (mode : Bool) → (statements : List StatementId) →
      Option (PLift (Shape source expected
        (CellAwareInvocationAcceptedExpressionTrees.Subset prepared named source) mode statements)) :=
  shapeWith? source expected _
    (CellAwareInvocationAcceptedSubsetCheck.subset? prepared named source (source.nodes.length + 1))

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
  | projectedAssigned found form => exact ⟨_, found, by rw [form]; rfl⟩
  | bitNotted found form => exact ⟨_, found, by rw [form]; rfl⟩
  | projectedBitNotted found form => exact ⟨_, found, by rw [form]; rfl⟩
  | elementAssigned found form => exact ⟨_, found, by rw [form]; rfl⟩
  | elementBitNotted found form => exact ⟨_, found, by rw [form]; rfl⟩
  | discarded found form => exact ⟨_, found, by rw [form]; rfl⟩
  | block found form => exact ⟨_, found, by rw [form]; rfl⟩
  | conditional found form => exact ⟨_, found, by rw [form]; rfl⟩
  | matched found form => exact ⟨_, found, by rw [form]; rfl⟩
  | breaking found form => exact ⟨_, found, by rw [form]; rfl⟩
  | continuing found form => exact ⟨_, found, by rw [form]; rfl⟩
  | whileLooped found form => exact ⟨_, found, by rw [form]; rfl⟩
  | forLooped found form => exact ⟨_, found, by rw [form]; rfl⟩
  | tail found form => exact ⟨_, found, by rw [form]; rfl⟩

variable {whole : SourceCoreUnifiedCompilation.Compiled} {bodyRelation : ActualBodyInvocation.BodyRelation}

private theorem node_of_read (index : ActualBodyInvocation.Index whole bodyRelation) {id : StatementId}
    {node : StatementNode} {stored : Ty}
    (read : index.policy.readStatement index.compilerSource id = .ok (node, stored)) :
    index.compilerSource.lookupStatement? id = some node := by
  rw [index.statement_reader] at read
  exact read_found read

/-- Every refined accepted header tree of a supported header vector is covered
when the compiler's view is the original Source. -/
private theorem items_covered {policy : SourceCoreLoops.Policy} {source semantic : TypedSource}
    {site : SourceCoreElaboration.ErrorSite} {result : Ty} {reasonAt : ExpressionId → Word}
    {next : SourceCoreLocalCell.Scope → Except SourceCoreBasic.Error Expr} {finalScope : SourceCoreLocalCell.Scope}
    {finish : Expr} {child : ExpressionId → Prop} (sameSource : source = semantic) :
    ∀ {fuel : Nat} {scope : SourceCoreLocalCell.Scope} {items : List ForItemForm} {code : Expr}
      (tree : AcceptedNamedBodyFlow.Items policy source site result reasonAt next finalScope finish fuel scope items
        code),
      tree.Ready → ItemsShape source child items → CellAwareInvocationAcceptedForItems.ItemsCovered semantic tree := by
  have view : LambdaMetadataViews.MetadataView semantic source := by subst sameSource; exact .refl _
  intro fuel scope items code tree
  induction tree with
  | nil => intro _ _; trivial
  | absent _ _ _ ih =>
    intro ready shape
    cases shape with
    | absent _ tail => exact ih ready tail
  | initialized _ _ _ _ _ _ ih =>
    intro ready shape
    cases shape with
    | initialized monomorphic _ tail => exact ⟨monomorphic, ih ready tail⟩
  | discard _ _ _ ih =>
    intro ready shape
    cases shape with
    | discarded _ tail => exact ih ready tail
  | assigning =>
    intro ready shape
    cases shape with
    | assigned assignable _ _ => exact absurd (.inl assignable) ready.1
    | projectedAssigned assignable _ _ _ => exact absurd (.inr assignable) ready.1
  | assigned _ _ _ ih =>
    intro ready shape
    cases shape with
    | assigned _ _ tail => exact ⟨view, ih ready tail⟩
    | projectedAssigned _ _ _ tail => exact ⟨view, ih ready tail⟩
  | projectedAssigned _ _ route ih =>
    intro ready shape
    cases shape with
    | assigned _ _ tail => exact ⟨view, by subst sameSource; exact route, ih ready tail⟩
    | projectedAssigned _ _ _ tail => exact ⟨view, by subst sameSource; exact route, ih ready tail⟩
  | bitNotting =>
    intro ready shape
    cases shape with
    | bitNotted assignable _ => exact absurd (.inl assignable) ready.1
    | projectedBitNotted assignable _ _ => exact absurd (.inr assignable) ready.1
  | bitNotted _ _ _ ih =>
    intro ready shape
    cases shape with
    | bitNotted _ tail => exact ⟨view, ih ready tail⟩
    | projectedBitNotted _ _ tail => exact ⟨view, ih ready tail⟩
  | projectedBitNotted _ _ route ih =>
    intro ready shape
    cases shape with
    | bitNotted _ tail => exact ⟨view, by subst sameSource; exact route, ih ready tail⟩
    | projectedBitNotted _ _ tail => exact ⟨view, by subst sameSource; exact route, ih ready tail⟩

/-- Every refined accepted tree of a supported statement list whose match
receipts are at contexts that `admitted` admits is covered, for every
generalized input. -/
theorem covered (index : ActualBodyInvocation.Index whole bodyRelation) {semantic : TypedSource}
    {expected : TypeSystem.Ty} {admitted : SourceCoreCompatibleDataMatches.Context → Prop} {generalized : Prop}
    {child : ExpressionId → Prop} (sameSource : index.compilerSource = semantic) :
    ∀ {mode : Bool} {escaped : Word} {fuel : Nat} {scope : SourceCoreLocalCell.Scope}
      {statements : List StatementId} {code : Expr}
      (tree : Tree index.policy index.compilerSource index.result index.reasonAt mode escaped fuel scope
        statements code),
      tree.Ready → tree.MatchContexts admitted → Shape index.compilerSource expected child mode statements →
      Covered semantic expected admitted generalized tree := by
  have view : LambdaMetadataViews.MetadataView semantic index.compilerSource := by subst sameSource; exact .refl _
  intro mode escaped fuel scope statements code tree
  induction tree with
  | nil =>
    intro _ _ shape
    cases shape with
    | nil allowed => exact allowed
  | returning => intro _ _ _; trivial
  | returnUnit => intro _ _ _; trivial
  | breaking => intro _ _ _; trivial
  | continuing => intro _ _ _; trivial
  | initialized read form _ _ _ _ _ _ _ ih =>
    intro ready contexts shape
    cases shape with
    | declared found form' monomorphic _ tail =>
      obtain rfl := Option.some.inj ((node_of_read index read).symm.trans found)
      rw [form] at form'
      cases form'
      exact ⟨.inl monomorphic, ih ready contexts tail⟩
    | _ =>
      exfalso
      obtain rfl := Option.some.inj ((node_of_read index read).symm.trans (by assumption))
      clear ih ready contexts
      simp_all
  | absent read form _ _ _ _ ih =>
    intro ready contexts shape
    cases shape with
    | uninitialized found form' _ tail =>
      obtain rfl := Option.some.inj ((node_of_read index read).symm.trans found)
      exact ih ready contexts tail
    | _ =>
      exfalso
      obtain rfl := Option.some.inj ((node_of_read index read).symm.trans (by assumption))
      clear ih ready contexts
      simp_all
  | assigning read form _ _ _ _ =>
    intro ready contexts shape
    cases shape with
    | assigned found form' assignable _ _ =>
      obtain rfl := Option.some.inj ((node_of_read index read).symm.trans found)
      rw [form] at form'
      cases form'
      exact absurd (.inl assignable) ready.1
    | projectedAssigned found form' assignable _ _ _ =>
      obtain rfl := Option.some.inj ((node_of_read index read).symm.trans found)
      rw [form] at form'
      cases form'
      exact absurd (.inr assignable) ready.1
    | elementAssigned found form' assignable _ _ _ _ =>
      obtain rfl := Option.some.inj ((node_of_read index read).symm.trans found)
      rw [form] at form'
      cases form'
      exact absurd assignable ready.2.1
    | _ =>
      exfalso
      obtain rfl := Option.some.inj ((node_of_read index read).symm.trans (by assumption))
      clear ready contexts
      simp_all
  | assigned read form _ _ _ _ ih =>
    intro ready contexts shape
    cases shape with
    | assigned found _ _ _ tail =>
      obtain rfl := Option.some.inj ((node_of_read index read).symm.trans found)
      exact ⟨view, ih ready contexts tail⟩
    | projectedAssigned found _ _ _ _ tail =>
      obtain rfl := Option.some.inj ((node_of_read index read).symm.trans found)
      exact ⟨view, ih ready contexts tail⟩
    | elementAssigned found _ _ _ _ _ tail =>
      obtain rfl := Option.some.inj ((node_of_read index read).symm.trans found)
      exact ⟨view, ih ready contexts tail⟩
    | _ =>
      exfalso
      obtain rfl := Option.some.inj ((node_of_read index read).symm.trans (by assumption))
      clear ih ready contexts
      simp_all
  | projectedAssigned read form _ _ _ route ih =>
    intro ready contexts shape
    cases shape with
    | assigned found _ _ _ tail =>
      obtain rfl := Option.some.inj ((node_of_read index read).symm.trans found)
      exact ⟨view, by subst sameSource; exact route, ih ready contexts tail⟩
    | projectedAssigned found _ _ _ _ tail =>
      obtain rfl := Option.some.inj ((node_of_read index read).symm.trans found)
      exact ⟨view, by subst sameSource; exact route, ih ready contexts tail⟩
    | elementAssigned found _ _ _ _ _ tail =>
      obtain rfl := Option.some.inj ((node_of_read index read).symm.trans found)
      exact ⟨view, by subst sameSource; exact route, ih ready contexts tail⟩
    | _ =>
      exfalso
      obtain rfl := Option.some.inj ((node_of_read index read).symm.trans (by assumption))
      clear ih ready contexts
      simp_all
  | bitNotting read form _ _ _ _ =>
    intro ready contexts shape
    cases shape with
    | bitNotted found form' assignable _ =>
      obtain rfl := Option.some.inj ((node_of_read index read).symm.trans found)
      rw [form] at form'
      cases form'
      exact absurd (.inl assignable) ready.1
    | projectedBitNotted found form' assignable _ _ =>
      obtain rfl := Option.some.inj ((node_of_read index read).symm.trans found)
      rw [form] at form'
      cases form'
      exact absurd (.inr assignable) ready.1
    | elementBitNotted found form' assignable _ _ _ =>
      obtain rfl := Option.some.inj ((node_of_read index read).symm.trans found)
      rw [form] at form'
      cases form'
      exact absurd assignable ready.2.1
    | _ =>
      exfalso
      obtain rfl := Option.some.inj ((node_of_read index read).symm.trans (by assumption))
      clear ready contexts
      simp_all
  | bitNotted read form _ _ _ _ ih =>
    intro ready contexts shape
    cases shape with
    | bitNotted found _ _ tail =>
      obtain rfl := Option.some.inj ((node_of_read index read).symm.trans found)
      exact ⟨view, ih ready contexts tail⟩
    | projectedBitNotted found _ _ _ tail =>
      obtain rfl := Option.some.inj ((node_of_read index read).symm.trans found)
      exact ⟨view, ih ready contexts tail⟩
    | elementBitNotted found _ _ _ _ tail =>
      obtain rfl := Option.some.inj ((node_of_read index read).symm.trans found)
      exact ⟨view, ih ready contexts tail⟩
    | _ =>
      exfalso
      obtain rfl := Option.some.inj ((node_of_read index read).symm.trans (by assumption))
      clear ih ready contexts
      simp_all
  | projectedBitNotted read form _ _ _ route ih =>
    intro ready contexts shape
    cases shape with
    | bitNotted found _ _ tail =>
      obtain rfl := Option.some.inj ((node_of_read index read).symm.trans found)
      exact ⟨view, by subst sameSource; exact route, ih ready contexts tail⟩
    | projectedBitNotted found _ _ _ tail =>
      obtain rfl := Option.some.inj ((node_of_read index read).symm.trans found)
      exact ⟨view, by subst sameSource; exact route, ih ready contexts tail⟩
    | elementBitNotted found _ _ _ _ tail =>
      obtain rfl := Option.some.inj ((node_of_read index read).symm.trans found)
      exact ⟨view, by subst sameSource; exact route, ih ready contexts tail⟩
    | _ =>
      exfalso
      obtain rfl := Option.some.inj ((node_of_read index read).symm.trans (by assumption))
      clear ih ready contexts
      simp_all
  | elementAssigned read form _ _ _ ih =>
    intro ready contexts shape
    cases shape with
    | assigned found _ _ _ tail =>
      obtain rfl := Option.some.inj ((node_of_read index read).symm.trans found)
      exact ⟨view, ih ready contexts tail⟩
    | projectedAssigned found _ _ _ _ tail =>
      obtain rfl := Option.some.inj ((node_of_read index read).symm.trans found)
      exact ⟨view, ih ready contexts tail⟩
    | elementAssigned found _ _ _ _ _ tail =>
      obtain rfl := Option.some.inj ((node_of_read index read).symm.trans found)
      exact ⟨view, ih ready contexts tail⟩
    | _ =>
      exfalso
      obtain rfl := Option.some.inj ((node_of_read index read).symm.trans (by assumption))
      clear ih ready contexts
      simp_all
  | elementBitNotted read form _ _ _ ih =>
    intro ready contexts shape
    cases shape with
    | bitNotted found _ _ tail =>
      obtain rfl := Option.some.inj ((node_of_read index read).symm.trans found)
      exact ⟨view, ih ready contexts tail⟩
    | projectedBitNotted found _ _ _ tail =>
      obtain rfl := Option.some.inj ((node_of_read index read).symm.trans found)
      exact ⟨view, ih ready contexts tail⟩
    | elementBitNotted found _ _ _ _ tail =>
      obtain rfl := Option.some.inj ((node_of_read index read).symm.trans found)
      exact ⟨view, ih ready contexts tail⟩
    | _ =>
      exfalso
      obtain rfl := Option.some.inj ((node_of_read index read).symm.trans (by assumption))
      clear ih ready contexts
      simp_all
  | discard read form _ _ _ _ ih =>
    intro ready contexts shape
    cases shape with
    | discarded found _ _ tail =>
      obtain rfl := Option.some.inj ((node_of_read index read).symm.trans found)
      exact ih ready contexts tail
    | _ =>
      exfalso
      obtain rfl := Option.some.inj ((node_of_read index read).symm.trans (by assumption))
      clear ih ready contexts
      simp_all
  | block read form _ _ innerIH tailIH =>
    intro ready contexts shape
    cases shape with
    | block found form' inner tail =>
      obtain rfl := Option.some.inj ((node_of_read index read).symm.trans found)
      rw [form] at form'
      cases form'
      exact ⟨innerIH ready.1 contexts.1 inner, tailIH ready.2 contexts.2 tail⟩
    | _ =>
      exfalso
      obtain rfl := Option.some.inj ((node_of_read index read).symm.trans (by assumption))
      clear innerIH tailIH ready contexts
      simp_all
  | conditional read form _ _ _ _ _ _ leftIH rightIH tailIH =>
    intro ready contexts shape
    cases shape with
    | conditional found form' _ left right tail =>
      obtain rfl := Option.some.inj ((node_of_read index read).symm.trans found)
      rw [form] at form'
      cases form'
      exact ⟨leftIH ready.1 contexts.1 left, rightIH ready.2.1 contexts.2.1 right,
        tailIH ready.2.2 contexts.2.2 tail⟩
    | _ =>
      exfalso
      obtain rfl := Option.some.inj ((node_of_read index read).symm.trans (by assumption))
      clear leftIH rightIH tailIH ready contexts
      simp_all
  | whileLoop read form _ _ _ _ _ _ innerIH tailIH =>
    intro ready contexts shape
    cases shape with
    | whileLooped found form' _ inner tail =>
      obtain rfl := Option.some.inj ((node_of_read index read).symm.trans found)
      rw [form] at form'
      cases form'
      exact ⟨innerIH ready.1 contexts.1 inner, tailIH ready.2 contexts.2 tail⟩
    | _ =>
      exfalso
      obtain rfl := Option.some.inj ((node_of_read index read).symm.trans (by assumption))
      clear innerIH tailIH ready contexts
      simp_all
  | forLoop read form _ _ _ _ initial _ after _ innerIH tailIH =>
    intro ready contexts shape
    cases shape with
    | forLooped found form' initialShape _ inner afterShape tail =>
      obtain rfl := Option.some.inj ((node_of_read index read).symm.trans found)
      rw [form] at form'
      cases form'
      exact ⟨items_covered sameSource initial ready.1 initialShape, innerIH ready.2.1 contexts.1 inner,
        items_covered sameSource after ready.2.2.1 afterShape, tailIH ready.2.2.2 contexts.2 tail⟩
    | _ =>
      exfalso
      obtain rfl := Option.some.inj ((node_of_read index read).symm.trans (by assumption))
      clear innerIH tailIH ready contexts
      simp_all
  | forBoundary _ _ outside _ =>
    intro _ _ _
    exact absurd ⟨True.intro, True.intro⟩ outside
  | tailValue read form _ _ _ _ =>
    intro _ _ shape
    cases shape with
    | tail found form' typed _ =>
      obtain rfl := Option.some.inj ((node_of_read index read).symm.trans found)
      rw [form] at form'
      cases form'
      rw [← sameSource]
      exact typed
    | _ =>
      exfalso
      obtain rfl := Option.some.inj ((node_of_read index read).symm.trans (by assumption))
      simp_all
  | valueDiscard read form notTail _ _ _ _ _ =>
    intro _ _ shape
    cases shape with
    | tail => exact absurd notTail (by decide)
    | _ =>
      exfalso
      obtain rfl := Option.some.inj ((node_of_read index read).symm.trans (by assumption))
      simp_all
  | boundary read outside =>
    intro _ _ shape
    obtain ⟨_, found, expanded⟩ := head_expanded shape
    obtain rfl := Option.some.inj ((node_of_read index read).symm.trans found)
    rw [outside] at expanded
    cases expanded
  | matching => intro ready _ _; exact False.elim ready
  | matched read form receipt branches _ branchIH tailIH =>
    intro ready contexts shape
    cases shape with
    | matched found form' _ arms fallback tail =>
      obtain rfl := Option.some.inj ((node_of_read index read).symm.trans found)
      rw [form] at form'
      cases form'
      refine ⟨contexts.1, view, by subst sameSource; rfl, fun request member => ?_, tailIH ready.2 contexts.2.2 tail⟩
      refine branchIH request member (ready.1 request member) (contexts.2.1 request member) ?_
      rcases receipt.original request member with ⟨arm, armMember, same⟩ | same
      · rw [same]
        exact arms arm armMember
      · rw [same] at fallback
        exact fallback
    | _ =>
      exfalso
      obtain rfl := Option.some.inj ((node_of_read index read).symm.trans (by assumption))
      clear branchIH tailIH ready contexts
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
without changing the heap and writes it by the same rule, an assignment or an
in-place `~` through mapping indices evaluates its keys in order before the
same snapshot and write, blocks and conditional arms restore their entry bindings while
keeping their heap, a match allocates the same hidden cell and runs the arm or default it selects,
restoring its entry bindings after it, and a `while` or `for` loop runs the same header items and
iterations, falling through at its own bindings. Each control outcome is carried unchanged, with the
context, environment and heap of the original execution. Fault executions are
not lifted here. -/
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

/-- A selected arm's body is the body of one of the match's arms, and a selected default is the match's
default. -/
theorem selected_body {context : SourceSemantics.Context} {value : Dynamic.Value} {cases : List TypedMatchCase}
    {fallback : Option (List StatementId)} {selection : Dynamic.MatchCaseSelection}
    (selected : Dynamic.MatchCasesSelect context value cases fallback selection) :
    (∀ statements bindings, selection = .arm statements bindings → ∃ arm ∈ cases, arm.body = statements) ∧
      ∀ statements, selection = .default statements → fallback = some statements := by
  induction selected with
  | head =>
    exact ⟨(fun _ _ same => by cases same; exact ⟨_, List.mem_cons_self, rfl⟩), fun _ same => by cases same⟩
  | tail _ _ ih =>
    refine ⟨fun statements bindings same => ?_, ih.2⟩
    obtain ⟨arm, member, body⟩ := ih.1 statements bindings same
    exact ⟨arm, List.mem_cons_of_mem _ member, body⟩
  | default => exact ⟨(fun _ _ same => by cases same), fun _ same => by cases same; rfl⟩
  | noBranch => exact ⟨(fun _ _ same => by cases same), fun _ same => by cases same⟩

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
        (Dynamic.CompoundAssignmentApplies assignment.target.type operator) environment before assignment.target expression
        updatedRoot after ∧
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

private theorem bitNotted_inv (unique : NodeOccurrencesUnique source) (found : source.lookupStatement? id = some node)
    {assignment : AssignmentResolution} (form : node.form = .assignBitNot assignment)
    (head : Dynamic.StatementExecutes program context evidence source environment before id finalContext outcome after) :
    ∃ updatedRoot, Dynamic.SourcePlaceSnapshotUpdate program context evidence source
        (Dynamic.BitNotAssignmentApplies assignment.target.type) environment before assignment.target updatedRoot after ∧
      finalContext = context ∧ outcome = .fallthrough environment := by
  cases head with
  | assignBitNot contains formEq executes =>
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

private theorem break_inv (unique : NodeOccurrencesUnique source) (found : source.lookupStatement? id = some node)
    (form : node.form = .breakStmt)
    (head : Dynamic.StatementExecutes program context evidence source environment before id finalContext outcome after) :
    finalContext = context ∧ outcome = .breaking environment ∧ after = before := by
  cases head with
  | breakStmt => exact ⟨rfl, rfl, rfl⟩
  | _ =>
    exfalso
    obtain rfl := same_node unique found (by assumption)
    simp_all

private theorem continue_inv (unique : NodeOccurrencesUnique source) (found : source.lookupStatement? id = some node)
    (form : node.form = .continueStmt)
    (head : Dynamic.StatementExecutes program context evidence source environment before id finalContext outcome after) :
    finalContext = context ∧ outcome = .continuing environment ∧ after = before := by
  cases head with
  | continueStmt => exact ⟨rfl, rfl, rfl⟩
  | _ =>
    exfalso
    obtain rfl := same_node unique found (by assumption)
    simp_all

private theorem while_inv (unique : NodeOccurrencesUnique source) (found : source.lookupStatement? id = some node)
    {condition : ExpressionId} {body : List StatementId} (form : node.form = .whileLoop condition body)
    (head : Dynamic.StatementExecutes program context evidence source environment before id finalContext outcome after) :
    ∃ loopContext inner,
      Dynamic.WhileExecutes program context evidence source environment before condition body loopContext inner after ∧
      finalContext = context ∧ outcome = Dynamic.restoreControl environment inner := by
  cases head with
  | whileLoop contains formEq iterate =>
    obtain rfl := same_node unique found contains
    rw [form] at formEq
    cases formEq
    exact ⟨_, _, iterate, rfl, rfl⟩
  | _ =>
    exfalso
    obtain rfl := same_node unique found (by assumption)
    simp_all

private theorem for_inv (unique : NodeOccurrencesUnique source) (found : source.lookupStatement? id = some node)
    {initializer : List ForItemForm} {condition : ExpressionId} {post : List ForItemForm} {body : List StatementId}
    (form : node.form = .forLoop initializer condition post body)
    (head : Dynamic.StatementExecutes program context evidence source environment before id finalContext outcome after) :
    ∃ loopContext loopEnvironment initialized loopFinalContext inner,
      Dynamic.ForItemsExecute program context evidence source environment before initializer loopContext
        loopEnvironment initialized ∧
      Dynamic.ForLoopExecutes program loopContext evidence source loopEnvironment initialized condition post body
        loopFinalContext inner after ∧
      finalContext = context ∧ outcome = Dynamic.restoreControl environment inner := by
  cases head with
  | forLoop contains formEq initial iterate =>
    obtain rfl := same_node unique found contains
    rw [form] at formEq
    cases formEq
    exact ⟨_, _, _, _, _, initial, iterate, rfl, rfl⟩
  | _ =>
    exfalso
    obtain rfl := same_node unique found (by assumption)
    simp_all
end Inversion

variable {checked : SourceCoreCompatibleCatalog.Checked} {prepared : Prepared checked}
  {named : SourceCoreGeneralFunctions.Function} {program : Program} {registry : Staging.Recursive.Registry}
  {scope : Staging.Recursive.Scope} {expected : TypeSystem.Ty}

/-- The Source's evaluation of a path of mapping indices whose keys are subset
sites is the staged evaluation of its keys, in order. -/
private theorem projections_values (unique : NodeOccurrencesUnique scope.source) {context : SourceSemantics.Context}
    {environment : Dynamic.Environment} :
    ∀ {projections : List PlaceProjection},
    (∀ projection ∈ projections, ∃ key, projection = .index key ∧ Subset prepared named scope.source key) →
    ∀ {before after : Dynamic.Heap} {evaluated : List Dynamic.EvaluatedProjection},
      Dynamic.SourceProjectionsEvaluate program context scope.evidence scope.source environment before projections
        evaluated after →
      ∃ values, Staging.Recursive.Expressions program registry scope context environment before
          (Staging.Recursive.ProjectedTarget.keys projections) (.values values) after ∧
        Staging.Recursive.ProjectedTarget.Values projections values evaluated := by
  intro projections
  induction projections with
  | nil =>
    intro _ before after evaluated evaluate
    cases evaluate
    exact ⟨[], .nil, .nil⟩
  | cons projection rest ih =>
    intro keys before after evaluated evaluate
    obtain ⟨key, rfl, site⟩ := keys projection List.mem_cons_self
    cases evaluate with
    | index head tail =>
      obtain ⟨values, staged, ordered⟩ := ih (fun other member => keys other (List.mem_cons_of_mem _ member)) tail
      exact ⟨_ :: values, .cons (expression_value unique site head) staged, .index ordered⟩

/-- The Source's resolution of a place through mapping indices whose keys are
subset sites is the staged evaluation of its keys followed by its staged
snapshot. -/
private theorem projected_target (unique : NodeOccurrencesUnique scope.source) {context : SourceSemantics.Context}
    {environment : Dynamic.Environment} {place : PlaceResolution}
    (keys : ∀ projection ∈ place.projections, ∃ key, projection = .index key ∧ Subset prepared named scope.source key)
    {before after : Dynamic.Heap} {target : Dynamic.ResolvedPlace}
    (resolve : Dynamic.SourcePlaceResolves program context scope.evidence scope.source environment before place target
      after) :
    ∃ values, Staging.Recursive.Expressions program registry scope context environment before
        (Staging.Recursive.ProjectedTarget.keys place.projections) (.values values) after ∧
      Staging.Recursive.ProjectedTarget.Snapshot environment before after place values target := by
  cases resolve with
  | intro lookup initialRead evaluate currentRead initialValue selection =>
    obtain ⟨values, staged, ordered⟩ := projections_values unique keys evaluate
    exact ⟨values, staged, .intro lookup initialRead ordered currentRead initialValue selection⟩
  | element projectionsEq => exact absurd projectionsEq (CellAwareInvocationAcceptedBodyShape.indices_no_element keys)

/-- The Source's iterations of a `while` loop whose condition and body lift are
the staged iterations, with the same outcome and heap. The loop falls through
at its own bindings or returns. -/
private theorem while_lift {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource}
    {condition : ExpressionId} {body : List StatementId}
    (test : ∀ {context environment before value after},
      Dynamic.ExpressionEvaluates program context evidence source environment before condition value after →
      Staging.Recursive.Expression program registry scope context environment before condition (.value value) after)
    (inner : ∀ {context environment before innerContext outcome after},
      Dynamic.StatementsExecute program context evidence source environment before body innerContext outcome after →
      Staging.Recursive.StatementsIn program registry false scope context environment before body innerContext
        (control outcome) after)
    {context : SourceSemantics.Context} {environment : Dynamic.Environment} {before after : Dynamic.Heap}
    {loopContext : SourceSemantics.Context} {outcome : Dynamic.ControlOutcome}
    (loop : Dynamic.WhileExecutes program context evidence source environment before condition body loopContext
      outcome after) :
    Staging.Recursive.While program registry scope context environment before condition body (control outcome)
        after ∧
      (outcome = .fallthrough environment ∨ ∃ value, outcome = .returned value) := by
  obtain ⟨size, sized⟩ := SourceExecutionSize.WhileExecutes.has_size loop
  clear loop
  induction size using Nat.strongRecOn generalizing before loopContext outcome after with
  | ind size ih =>
    cases sized with
    | done evaluate => exact ⟨.done (test evaluate.sound), .inl rfl⟩
    | nextFallthrough evaluate executes next =>
      obtain ⟨staged, ended⟩ := ih _ (SourceExecutionSize.child_lt_stepSize (by simp)) next
      exact ⟨.next (test evaluate.sound) (inner executes.sound) staged, ended⟩
    | nextContinue evaluate executes next =>
      obtain ⟨staged, ended⟩ := ih _ (SourceExecutionSize.child_lt_stepSize (by simp)) next
      exact ⟨.continueNext (test evaluate.sound) (inner executes.sound) staged, ended⟩
    | breaks evaluate executes => exact ⟨.breakFromBody (test evaluate.sound) (inner executes.sound), .inl rfl⟩
    | returns evaluate executes => exact ⟨.returned (test evaluate.sound) (inner executes.sound), .inr ⟨_, rfl⟩⟩

/-- The Source's execution of a supported header vector whose expressions are
subset sites is the staged execution of the vector, with the same context,
bindings and heap. -/
private theorem items_lift (unique : NodeOccurrencesUnique scope.source) {items : List ForItemForm}
    (shape : CellAwareInvocationAcceptedBodyShape.ItemsShape scope.source (Subset prepared named scope.source)
      items) :
    ∀ {context : SourceSemantics.Context} {environment : Dynamic.Environment} {before after : Dynamic.Heap}
      {finalContext : SourceSemantics.Context} {finalEnvironment : Dynamic.Environment},
      Dynamic.ForItemsExecute program context scope.evidence scope.source environment before items finalContext
        finalEnvironment after →
      Staging.Recursive.ForItems program registry scope context environment before items finalContext
        (.done finalEnvironment) after := by
  induction shape with
  | nil =>
    intro context environment before after finalContext finalEnvironment executes
    cases executes
    exact .empty
  | absent monomorphic _ tailIH =>
    intro context environment before after finalContext finalEnvironment executes
    cases executes with
    | cons head tail =>
      cases head with
      | letUninitialized _ extension allocate => exact .absent monomorphic extension allocate (tailIH tail)
  | initialized monomorphic value _ tailIH =>
    intro context environment before after finalContext finalEnvironment executes
    cases executes with
    | cons head tail =>
      cases head with
      | letInitialized evaluate _ extension allocate =>
        exact .initialized monomorphic extension (expression_value unique value evaluate) allocate (tailIH tail)
      | letInitializedGeneralized _ _ polymorphic => exact absurd monomorphic polymorphic
  | discarded value _ tailIH =>
    intro context environment before after finalContext finalEnvironment executes
    cases executes with
    | cons head tail =>
      cases head with
      | expression evaluate => exact .expression (expression_value unique value evaluate) (tailIH tail)
  | assigned assignable value _ tailIH =>
    intro context environment before after finalContext finalEnvironment executes
    cases executes with
    | cons head tail =>
      cases head with
      | assignValue executes =>
        cases executes with
        | intro resolve evaluate write =>
          obtain ⟨rfl, snapshot⟩ := Staging.Recursive.BareTarget.of_resolves assignable.2.1 resolve
          exact .assignment snapshot (expression_value unique value evaluate) write (tailIH tail)
  | projectedAssigned assignable keys value _ tailIH =>
    intro context environment before after finalContext finalEnvironment executes
    cases executes with
    | cons head tail =>
      cases head with
      | assignValue executes =>
        cases executes with
        | intro resolve evaluate write =>
          obtain ⟨values, staged, snapshot⟩ := projected_target unique keys resolve
          exact .projectedAssignment assignable.2.1 staged snapshot (expression_value unique value evaluate) write
            (tailIH tail)
  | bitNotted assignable _ tailIH =>
    intro context environment before after finalContext finalEnvironment executes
    cases executes with
    | cons head tail =>
      cases head with
      | assignBitNot executes =>
        cases executes with
        | intro resolve write =>
          obtain ⟨rfl, snapshot⟩ := Staging.Recursive.BareTarget.of_resolves assignable.2.1 resolve
          exact .bitNot snapshot write (tailIH tail)
  | projectedBitNotted assignable keys _ tailIH =>
    intro context environment before after finalContext finalEnvironment executes
    cases executes with
    | cons head tail =>
      cases head with
      | assignBitNot executes =>
        cases executes with
        | intro resolve write =>
          obtain ⟨values, staged, snapshot⟩ := projected_target unique keys resolve
          exact .projectedBitNot assignable.2.1 staged snapshot write (tailIH tail)

/-- The Source's iterations of a `for` loop whose condition, body and post
header lift are the staged iterations, with the same outcome and heap. The
loop falls through at its own bindings or returns. -/
private theorem for_lift {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource}
    {condition : ExpressionId} {post : List ForItemForm} {body : List StatementId}
    (test : ∀ {context environment before value after},
      Dynamic.ExpressionEvaluates program context evidence source environment before condition value after →
      Staging.Recursive.Expression program registry scope context environment before condition (.value value) after)
    (inner : ∀ {context environment before innerContext outcome after},
      Dynamic.StatementsExecute program context evidence source environment before body innerContext outcome after →
      Staging.Recursive.StatementsIn program registry false scope context environment before body innerContext
        (control outcome) after)
    (postLift : ∀ {context environment before finalContext finalEnvironment after},
      Dynamic.ForItemsExecute program context evidence source environment before post finalContext finalEnvironment
        after →
      Staging.Recursive.ForItems program registry scope context environment before post finalContext
        (.done finalEnvironment) after)
    {context : SourceSemantics.Context} {environment : Dynamic.Environment} {before after : Dynamic.Heap}
    {loopContext : SourceSemantics.Context} {outcome : Dynamic.ControlOutcome}
    (loop : Dynamic.ForLoopExecutes program context evidence source environment before condition post body
      loopContext outcome after) :
    Staging.Recursive.ForLoop program registry scope context environment before condition post body
        (control outcome) after ∧
      (outcome = .fallthrough environment ∨ ∃ value, outcome = .returned value) := by
  obtain ⟨size, sized⟩ := SourceExecutionSize.ForLoopExecutes.has_size loop
  clear loop
  induction size using Nat.strongRecOn generalizing before loopContext outcome after with
  | ind size ih =>
    cases sized with
    | done evaluate => exact ⟨.finished (test evaluate.sound), .inl rfl⟩
    | nextFallthrough evaluate executes postExecutes next =>
      obtain ⟨staged, ended⟩ := ih _ (SourceExecutionSize.child_lt_stepSize (by simp)) next
      exact ⟨.iterate (test evaluate.sound) (inner executes.sound) (postLift postExecutes.sound) staged, ended⟩
    | nextContinue evaluate executes postExecutes next =>
      obtain ⟨staged, ended⟩ := ih _ (SourceExecutionSize.child_lt_stepSize (by simp)) next
      exact ⟨.continueIterate (test evaluate.sound) (inner executes.sound) (postLift postExecutes.sound) staged,
        ended⟩
    | breaks evaluate executes =>
      exact ⟨.forBreakFromBody (test evaluate.sound) (inner executes.sound), .inl rfl⟩
    | returns evaluate executes =>
      exact ⟨.returnedFromBody (test evaluate.sound) (inner executes.sound), .inr ⟨_, rfl⟩⟩

/-- A Source match whose scrutinee and selected body lift is the staged match at its entry context. The
outcome is the selected body's, restored to the entry bindings; without a selected body it falls through. -/
private theorem match_lift (unique : NodeOccurrencesUnique scope.source) {id : StatementId} {node : StatementNode}
    (found : scope.source.lookupStatement? id = some node) {resolution : MatchResolution}
    (form : node.form = .matchWith resolution)
    (scrutinee : ∀ {context environment before value after},
      Dynamic.ExpressionEvaluates program context scope.evidence scope.source environment before
        resolution.scrutinee value after →
      Staging.Recursive.Expression program registry scope context environment before resolution.scrutinee
        (.value value) after)
    (body : ∀ {statements : List StatementId}, ((∃ arm ∈ resolution.cases, arm.body = statements) ∨
        resolution.defaultBody = some statements) →
      ∀ {context environment before innerContext inner after},
      Dynamic.StatementsExecute program context scope.evidence scope.source environment before statements
        innerContext inner after →
      Staging.Recursive.StatementsIn program registry false scope context environment before statements
        innerContext (control inner) after)
    {context finalContext : SourceSemantics.Context} {environment : Dynamic.Environment}
    {before after : Dynamic.Heap} {outcome : Dynamic.ControlOutcome}
    (head : Dynamic.StatementExecutes program context scope.evidence scope.source environment before id
      finalContext outcome after) :
    finalContext = context ∧ ∃ inner, outcome = Dynamic.restoreControl environment inner ∧
      Staging.Recursive.Match program registry scope context environment before resolution
        ((control inner).restore environment) after := by
  cases head with
  | matchArm contains formEq scrutineeContains evaluate allocate select bindersEq valuesEq extended allocated
      executes =>
    obtain rfl := same_node unique found contains
    rw [form] at formEq
    cases formEq
    subst bindersEq valuesEq
    obtain ⟨arm, member, same⟩ := (selected_body select).1 _ _ rfl
    exact ⟨rfl, _, rfl, .arm scrutineeContains (scrutinee evaluate) allocate select extended allocated
      (body (.inl ⟨arm, member, same⟩) executes)⟩
  | matchDefault contains formEq scrutineeContains evaluate allocate select executes =>
    obtain rfl := same_node unique found contains
    rw [form] at formEq
    cases formEq
    exact ⟨rfl, _, rfl, .default scrutineeContains (scrutinee evaluate) allocate select
      (body (.inr ((selected_body select).2 _ rfl)) executes)⟩
  | matchNoBranch contains formEq scrutineeContains evaluate allocate select =>
    obtain rfl := same_node unique found contains
    rw [form] at formEq
    cases formEq
    exact ⟨rfl, .fallthrough environment, rfl, .noBranch scrutineeContains (scrutinee evaluate) allocate select⟩
  | _ =>
    exfalso
    clear scrutinee body
    obtain rfl := same_node unique found (by assumption)
    simp_all

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
subset sites is a staged execution with the same context, outcome and heap. A
function body's final value is the staged final value. -/
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
  | projectedAssigned found form assignable keys value _ tailIH =>
    intro context environment before after finalContext outcome
    apply sequence unique found (fun _ same => by rw [form] at same; cases same)
    · intro context environment before middleContext nextEnvironment middle finalContext outcome after head next
      obtain ⟨_, executes, rfl, same⟩ := assigned_inv unique found form head
      cases same
      cases executes with
      | intro resolve evaluate write =>
        obtain ⟨values, staged, snapshot⟩ := projected_target unique keys resolve
        exact .assignProjected (lookupStatement?_sound found) form assignable.2.1 staged snapshot
          (expression_value unique value evaluate) write (tailIH next)
    · intro context environment before finalContext outcome after head terminal
      obtain ⟨_, _, _, same⟩ := assigned_inv unique found form head
      subst same
      cases terminal
  | bitNotted found form assignable _ tailIH =>
    intro context environment before after finalContext outcome
    apply sequence unique found (fun _ same => by rw [form] at same; cases same)
    · intro context environment before middleContext nextEnvironment middle finalContext outcome after head next
      obtain ⟨_, executes, rfl, same⟩ := bitNotted_inv unique found form head
      cases same
      cases executes with
      | intro resolve write =>
        obtain ⟨rfl, snapshot⟩ := Staging.Recursive.BareTarget.of_resolves assignable.2.1 resolve
        exact .bitNotBare (lookupStatement?_sound found) form snapshot write (tailIH next)
    · intro context environment before finalContext outcome after head terminal
      obtain ⟨_, _, _, same⟩ := bitNotted_inv unique found form head
      subst same
      cases terminal
  | projectedBitNotted found form assignable keys _ tailIH =>
    intro context environment before after finalContext outcome
    apply sequence unique found (fun _ same => by rw [form] at same; cases same)
    · intro context environment before middleContext nextEnvironment middle finalContext outcome after head next
      obtain ⟨_, executes, rfl, same⟩ := bitNotted_inv unique found form head
      cases same
      cases executes with
      | intro resolve write =>
        obtain ⟨values, staged, snapshot⟩ := projected_target unique keys resolve
        exact .bitNotProjected (lookupStatement?_sound found) form assignable.2.1 staged snapshot write (tailIH next)
    · intro context environment before finalContext outcome after head terminal
      obtain ⟨_, _, _, same⟩ := bitNotted_inv unique found form head
      subst same
      cases terminal
  | elementAssigned found form _ single index value _ tailIH =>
    intro context environment before after finalContext outcome
    apply sequence unique found (fun _ same => by rw [form] at same; cases same)
    · intro context environment before middleContext nextEnvironment middle finalContext outcome after head next
      obtain ⟨_, executes, rfl, same⟩ := assigned_inv unique found form head
      cases same
      cases executes with
      | intro resolve evaluate write =>
        exact .assignElement (lookupStatement?_sound found) form (CellAwareElementTargetLifting.element_place single)
          (CellAwareElementTargetLifting.resolved single (expression_value unique index) resolve)
          (expression_value unique value evaluate) write (tailIH next)
    · intro context environment before finalContext outcome after head terminal
      obtain ⟨_, _, _, same⟩ := assigned_inv unique found form head
      subst same
      cases terminal
  | elementBitNotted found form _ single index _ tailIH =>
    intro context environment before after finalContext outcome
    apply sequence unique found (fun _ same => by rw [form] at same; cases same)
    · intro context environment before middleContext nextEnvironment middle finalContext outcome after head next
      obtain ⟨_, executes, rfl, same⟩ := bitNotted_inv unique found form head
      cases same
      cases executes with
      | intro resolve write =>
        exact .bitNotElement (lookupStatement?_sound found) form (CellAwareElementTargetLifting.element_place single)
          (CellAwareElementTargetLifting.resolved single (expression_value unique index) resolve) write (tailIH next)
    · intro context environment before finalContext outcome after head terminal
      obtain ⟨_, _, _, same⟩ := bitNotted_inv unique found form head
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
  | @matched mode id rest node resolution found form scrutinee _ _ _ armsIH fallbackIH tailIH =>
    intro context environment before after finalContext outcome
    have body : ∀ {statements : List StatementId}, ((∃ arm ∈ resolution.cases, arm.body = statements) ∨
        resolution.defaultBody = some statements) →
        ∀ {context environment before innerContext inner after},
        Dynamic.StatementsExecute program context scope.evidence scope.source environment before statements
          innerContext inner after →
        Staging.Recursive.StatementsIn program registry false scope context environment before statements
          innerContext (control inner) after := by
      intro statements selected context environment before innerContext inner after executes
      rcases selected with ⟨arm, member, rfl⟩ | same
      · exact armsIH arm member executes
      · rw [same] at fallbackIH
        exact fallbackIH executes
    apply sequence unique found (fun _ same => by rw [form] at same; cases same)
    · intro context environment before middleContext nextEnvironment middle finalContext outcome after head next
      obtain ⟨rfl, inner, same, staged⟩ := match_lift unique found form
        (fun evaluate => expression_value unique scrutinee evaluate) body head
      cases inner with
      | fallthrough innerEnvironment =>
        cases same
        exact .matchFallthrough (lookupStatement?_sound found) form staged (tailIH next)
      | _ => cases same
    · intro context environment before finalContext outcome after head terminal
      obtain ⟨rfl, inner, rfl, staged⟩ := match_lift unique found form
        (fun evaluate => expression_value unique scrutinee evaluate) body head
      cases inner with
      | fallthrough => cases terminal
      | returned => exact .matchReturned (lookupStatement?_sound found) form staged
      | breaking => exact .matchBreaking (lookupStatement?_sound found) form staged
      | continuing => exact .matchContinuing (lookupStatement?_sound found) form staged
      | fault => exact .matchFault (lookupStatement?_sound found) form staged
  | breaking found form =>
    intro context environment before after finalContext outcome
    apply sequence unique found (fun _ same => by rw [form] at same; cases same)
    · intro context environment before middleContext nextEnvironment middle finalContext outcome after head _
      obtain ⟨_, impossible, _⟩ := break_inv unique found form head
      cases impossible
    · intro context environment before finalContext outcome after head _
      obtain ⟨rfl, rfl, rfl⟩ := break_inv unique found form head
      exact .breaking (lookupStatement?_sound found) form
  | continuing found form =>
    intro context environment before after finalContext outcome
    apply sequence unique found (fun _ same => by rw [form] at same; cases same)
    · intro context environment before middleContext nextEnvironment middle finalContext outcome after head _
      obtain ⟨_, impossible, _⟩ := continue_inv unique found form head
      cases impossible
    · intro context environment before finalContext outcome after head _
      obtain ⟨rfl, rfl, rfl⟩ := continue_inv unique found form head
      exact .continuing (lookupStatement?_sound found) form
  | whileLooped found form test _ _ innerIH tailIH =>
    intro context environment before after finalContext outcome
    apply sequence unique found (fun _ same => by rw [form] at same; cases same)
    · intro context environment before middleContext nextEnvironment middle finalContext outcome after head next
      obtain ⟨_, loopOutcome, iterate, rfl, same⟩ := while_inv unique found form head
      obtain ⟨loop, ended⟩ := while_lift (registry := registry) (scope := scope) (evidence := scope.evidence)
        (source := scope.source) (fun evaluate => expression_value unique test evaluate)
        (fun executes => innerIH executes) iterate
      rcases ended with rfl | ⟨_, rfl⟩
      · cases same
        exact .whileFallthrough (lookupStatement?_sound found) form loop (tailIH next)
      · cases same
    · intro context environment before finalContext outcome after head terminal
      obtain ⟨_, loopOutcome, iterate, rfl, rfl⟩ := while_inv unique found form head
      obtain ⟨loop, ended⟩ := while_lift (registry := registry) (scope := scope) (evidence := scope.evidence)
        (source := scope.source) (fun evaluate => expression_value unique test evaluate)
        (fun executes => innerIH executes) iterate
      rcases ended with rfl | ⟨_, rfl⟩
      · cases terminal
      · exact .whileReturned (lookupStatement?_sound found) form loop
  | forLooped found form initialItems test _ postItems _ innerIH tailIH =>
    intro context environment before after finalContext outcome
    apply sequence unique found (fun _ same => by rw [form] at same; cases same)
    · intro context environment before middleContext nextEnvironment middle finalContext outcome after head next
      obtain ⟨_, _, _, _, loopOutcome, initialized, iterate, rfl, same⟩ := for_inv unique found form head
      obtain ⟨loop, ended⟩ := for_lift (registry := registry) (scope := scope) (evidence := scope.evidence)
        (source := scope.source) (fun evaluate => expression_value unique test evaluate)
        (fun executes => innerIH executes) (fun executes => items_lift unique postItems executes) iterate
      rcases ended with rfl | ⟨_, rfl⟩
      · cases same
        exact .forFallthrough (lookupStatement?_sound found) form (items_lift unique initialItems initialized) loop
          (tailIH next)
      · cases same
    · intro context environment before finalContext outcome after head terminal
      obtain ⟨_, _, _, _, loopOutcome, initialized, iterate, rfl, rfl⟩ := for_inv unique found form head
      obtain ⟨loop, ended⟩ := for_lift (registry := registry) (scope := scope) (evidence := scope.evidence)
        (source := scope.source) (fun evaluate => expression_value unique test evaluate)
        (fun executes => innerIH executes) (fun executes => items_lift unique postItems executes) iterate
      rcases ended with rfl | ⟨_, rfl⟩
      · cases terminal
      · exact .forReturned (lookupStatement?_sound found) form (items_lift unique initialItems initialized) loop
  | tail found form _ value =>
    intro context environment before after finalContext outcome original
    unfold Original at original
    cases original with
    | tailExpression contains formEq evaluate =>
      obtain rfl := same_node unique found contains
      rw [form] at formEq
      cases formEq
      exact .tail (lookupStatement?_sound found) form (expression_value unique value evaluate)
    | singleton contains notTail _ =>
      obtain rfl := same_node unique found contains
      exact absurd form (notTail _)

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
