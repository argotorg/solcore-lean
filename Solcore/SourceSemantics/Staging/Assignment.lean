import Solcore.SourceSemantics.WellFormed

/-!
Flow-insensitive assignment classification for source staging.

The executable analysis conservatively marks a binder deferred when any
assignment node in the declaration targets that binder.  `for` header items
are stored inside their enclosing statement rather than as table nodes, so
their assignment roots are exposed explicitly below.
-/

set_option autoImplicit false

namespace Solcore.SourceSemantics.Staging

open Frontend.SourceInference

/-- One `for` initializer or post item assigns this exact place root. -/
inductive ForItemAssigns : ForItemForm → Resolved.LocalId → Prop where
  | value
      (assignment : AssignmentResolution) (operator : Syntax.ValueAssignOp)
      (value : ExpressionId) :
      ForItemAssigns (.assignValue assignment operator value)
        assignment.target.root
  | bitNot (assignment : AssignmentResolution) :
      ForItemAssigns (.assignBitNot assignment) assignment.target.root

/-- One statement form contributes this exact flow-insensitive assignment
root.  Nested statement bodies are represented by their own table nodes. -/
inductive StatementAssigns : StatementForm → Resolved.LocalId → Prop where
  | value
      (assignment : AssignmentResolution) (operator : Syntax.ValueAssignOp)
      (value : ExpressionId) :
      StatementAssigns (.assignValue assignment operator value)
        assignment.target.root
  | bitNot (assignment : AssignmentResolution) :
      StatementAssigns (.assignBitNot assignment) assignment.target.root
  | forInitializer
      {initializer post : List ForItemForm} {condition : ExpressionId}
      {body : List StatementId} {item : ForItemForm}
      {binder : Resolved.LocalId}
      (member : item ∈ initializer)
      (assigns : ForItemAssigns item binder) :
      StatementAssigns (.forLoop initializer condition post body) binder
  | forPost
      {initializer post : List ForItemForm} {condition : ExpressionId}
      {body : List StatementId} {item : ForItemForm}
      {binder : Resolved.LocalId}
      (member : item ∈ post)
      (assigns : ForItemAssigns item binder) :
      StatementAssigns (.forLoop initializer condition post body) binder

/-- A declaration assigns a local exactly when a retained statement node, or
one of its retained `for` header items, targets that local as its place root. -/
def AssignedIn (source : TypedSource) (binder : Resolved.LocalId) : Prop :=
  ∃ id node,
    SourceSemantics.ContainsStatement source id node ∧
      StatementAssigns node.form binder

end Solcore.SourceSemantics.Staging
