import Solcore.SourceSemantics.CoreLowering.GenericAssignmentDiagnosticCertificates
import Solcore.SourceSemantics.CoreLowering.AssignmentDiagnosticPolicy
import Solcore.SourceSemantics.CoreLowering.TypedImperativeForCertificates

/-! Static provenance of operand diagnostics. Header items retain the owning
for statement and their suffix position. Raw scalar eligibility is obtained
from independent source assignment typing, never from a runtime type view. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.AssignmentDiagnosticOrigins
open Core Frontend SourceInference
abbrev Site := SourceCoreElaboration.ErrorSite

/-- The RHS is retained as well as the diagnostic key. -/
inductive Occurs (source : TypedSource) : Site → AssignmentResolution → Syntax.ValueAssignOp → ExpressionId → Prop where
  | statement {id node assignment operator rhs}
      (found : source.lookupStatement? id = some node)
      (form : node.form = .assignValue assignment operator rhs) :
      Occurs source (.occurrence id.occurrence) assignment operator rhs
  | header {id node initializer condition post body assignment operator rhs}
      (found : source.lookupStatement? id = some node)
      (form : node.form = .forLoop initializer condition post body)
      (member : .assignValue assignment operator rhs ∈ initializer ++ post) :
      Occurs source (.occurrence id.occurrence) assignment operator rhs

/-- Current header items are an actual suffix of one vector of the parent. -/
def HeaderOrigin (source : TypedSource) (site : Site) (items : List ForItemForm) : Prop :=
  (∃ id node initializer condition post body,
    source.lookupStatement? id = some node ∧ node.form = .forLoop initializer condition post body ∧
    site = .occurrence id.occurrence ∧
    (∃ beforeItems, beforeItems ++ items = initializer)) ∨
  (∃ id node initializer condition post body,
    source.lookupStatement? id = some node ∧ node.form = .forLoop initializer condition post body ∧
    site = .occurrence id.occurrence ∧ (∃ beforeItems, beforeItems ++ items = post))

/-- An initializer suffix retains the same condition, post and body. -/
def ForOrigin (source : TypedSource) (site : Site) (items : List ForItemForm)
    (condition : ExpressionId) (post : List ForItemForm) (body : List StatementId) : Prop :=
  ∃ id node initializer, source.lookupStatement? id = some node ∧
    node.form = .forLoop initializer condition post body ∧ site = .occurrence id.occurrence ∧
    ∃ beforeItems, beforeItems ++ items = initializer

abbrev OccursFor (tracked : Bool) (source : TypedSource) (site : Site)
    (assignment : AssignmentResolution) (operator : Syntax.ValueAssignOp) (rhs : ExpressionId) : Prop :=
  if tracked then Occurs source site assignment operator rhs else True
abbrev HeaderOriginFor (tracked : Bool) (source : TypedSource) (site : Site) (items : List ForItemForm) : Prop :=
  if tracked then HeaderOrigin source site items else True
abbrev ForOriginFor (tracked : Bool) (source : TypedSource) (site : Site) (items : List ForItemForm)
    (condition : ExpressionId) (post : List ForItemForm) (body : List StatementId) : Prop :=
  if tracked then ForOrigin source site items condition post body else True

variable {source : TypedSource} {site : Site} {items : List ForItemForm}
  {condition : ExpressionId} {post : List ForItemForm} {body : List StatementId} {tracked : Bool}

private theorem suffix_tail {α : Type} {item : α} {rest original : List α}
    (suffix : ∃ beforeItems, beforeItems ++ item :: rest = original) : ∃ beforeItems, beforeItems ++ rest = original := by
  obtain ⟨beforeItems, rfl⟩ := suffix
  exact ⟨beforeItems ++ [item], by simp only [List.append_assoc, List.singleton_append]⟩

private theorem suffix_mem {α : Type} {item : α} {rest original : List α}
    (suffix : ∃ beforeItems, beforeItems ++ item :: rest = original) : item ∈ original := by
  obtain ⟨beforeItems, rfl⟩ := suffix
  exact List.mem_append_right _ (List.mem_cons_self)

theorem HeaderOriginFor.tail {item : ForItemForm}
    (origin : HeaderOriginFor tracked source site (item :: items)) : HeaderOriginFor tracked source site items := by
  cases tracked with
  | false => trivial
  | true =>
    rcases origin with ⟨id, node, initializer, condition, post, body, found, form, same, suffix⟩ |
      ⟨id, node, initializer, condition, post, body, found, form, same, suffix⟩
    · exact .inl ⟨id, node, initializer, condition, post, body, found, form, same, suffix_tail suffix⟩
    · exact .inr ⟨id, node, initializer, condition, post, body, found, form, same, suffix_tail suffix⟩

theorem ForOriginFor.tail {item : ForItemForm}
    (origin : ForOriginFor tracked source site (item :: items) condition post body) :
    ForOriginFor tracked source site items condition post body := by
  cases tracked with
  | false => trivial
  | true =>
    obtain ⟨id, node, initializer, found, form, same, suffix⟩ := origin
    exact ⟨id, node, initializer, found, form, same, suffix_tail suffix⟩

theorem ForOriginFor.start {id : StatementId} {node : StatementNode}
    (found : source.lookupStatement? id = some node) (form : node.form = .forLoop items condition post body) :
    ForOriginFor tracked source (.occurrence id.occurrence) items condition post body := by
  cases tracked with
  | false => trivial
  | true => exact ⟨id, node, items, found, form, rfl, [], rfl⟩

theorem ForOriginFor.header (origin : ForOriginFor tracked source site items condition post body) :
    HeaderOriginFor tracked source site items := by
  cases tracked with
  | false => trivial
  | true =>
    obtain ⟨id, node, initializer, found, form, same, suffix⟩ := origin
    exact .inl ⟨id, node, initializer, condition, post, body, found, form, same, suffix⟩

theorem ForOriginFor.post_origin (origin : ForOriginFor tracked source site items condition post body) :
    HeaderOriginFor tracked source site post := by
  cases tracked with
  | false => trivial
  | true =>
    obtain ⟨id, node, initializer, found, form, same, _⟩ := origin
    exact .inr ⟨id, node, initializer, condition, post, body, found, form, same, [], rfl⟩

theorem OccursFor.statement {id : StatementId} {node : StatementNode}
    {assignment : AssignmentResolution} {operator : Syntax.ValueAssignOp} {rhs : ExpressionId}
    (found : source.lookupStatement? id = some node) (form : node.form = .assignValue assignment operator rhs) :
    OccursFor tracked source (.occurrence id.occurrence) assignment operator rhs := by
  cases tracked with
  | false => trivial
  | true => exact .statement found form

theorem HeaderOriginFor.operand {assignment : AssignmentResolution} {operator : Syntax.ValueAssignOp} {rhs : ExpressionId}
    (origin : HeaderOriginFor tracked source site (.assignValue assignment operator rhs :: items)) :
    OccursFor tracked source site assignment operator rhs := by
  cases tracked with
  | false => trivial
  | true =>
    rcases origin with ⟨id, node, initializer, condition, post, body, found, form, rfl, suffix⟩ |
      ⟨id, node, initializer, condition, post, body, found, form, rfl, suffix⟩
    · exact .header found form (List.mem_append_left _ (suffix_mem suffix))
    · exact .header found form (List.mem_append_right _ (suffix_mem suffix))

/-- Independent source typing is an explicit static profile. -/
def OperandsTyped (source : TypedSource) : Prop :=
  ∀ {site assignment operator rhs}, Occurs source site assignment operator rhs →
    ∃ context, SourceAssignmentHasType source context assignment operator rhs

theorem raw_profile {context : SourceSemantics.Context} {assignment : AssignmentResolution}
    {operator : Syntax.ValueAssignOp} {rhs : ExpressionId}
    (typed : SourceAssignmentHasType source context assignment operator rhs) :
    operator = .equal ∨ assignment.target.type = .word ∨ assignment.target.type = .integer := by
  cases typed with
  | equal => exact .inl rfl
  | wordCompound _ place _ _ =>
    cases place with
    | intro _ _ same => exact .inr (.inl same)

theorem Occurs.prepared {assignment : AssignmentResolution} {operator : Syntax.ValueAssignOp} {rhs : ExpressionId}
    {first : Nat} {table : SourceCoreAssignmentFaultSites.Table} {faults : FunctionCalls.FaultRep}
    (origin : Occurs source site assignment operator rhs) (typed : OperandsTyped source)
    (prepared : SourceCoreAssignmentFaultSites.prepare source first = .ok table)
    (included : ∀ reason word, GenericAssignmentDiagnostics.OperandRep table reason word → faults reason word) :
    AssignmentOperandDiagnostics.OperandsLaw faults operator
      (GenericAssignmentDiagnostics.token table site assignment.target.root operator) := by
  obtain ⟨context, sourceTyped⟩ := typed origin
  cases origin with
  | statement found form =>
    have present := lookupStatement?_sound found
    rw [← present.2]
    exact GenericAssignmentDiagnostics.prepared_operands_included included prepared present.1 (.statement form) (raw_profile sourceTyped)
  | header found form member =>
    have present := lookupStatement?_sound found
    rw [← present.2]
    exact GenericAssignmentDiagnostics.prepared_operands_included included prepared present.1 (.header form member) (raw_profile sourceTyped)

/-- A static local diagnostic factory. Its result retains all remaining laws. -/
structure Factory (tracked : Bool) (diagnosticPolicy : AssignmentDiagnosticPolicy)
    (source : TypedSource) (invalidOperand : Site → Resolved.LocalId → Syntax.ValueAssignOp → Word) where
  residual : ∀ {values context certificate scope administrative definitions assignment operator rhs},
    GenericAssignmentStatements.Head values source context certificate scope administrative definitions assignment operator rhs →
    SourceCoreRawMetadata.Registry → FunctionCalls.FaultRep → Prop
  materialize : ∀ {values context certificate scope administrative definitions assignment operator rhs}
    (head : GenericAssignmentStatements.Head values source context certificate scope administrative definitions assignment operator rhs)
    (site : Site), OccursFor tracked source site assignment operator rhs →
    head.invalid = invalidOperand site assignment.target.root operator →
    ∀ registry faults, residual head registry faults → head.ErrorsFor diagnosticPolicy registry faults

def Factory.unchanged (diagnosticPolicy : AssignmentDiagnosticPolicy) (source : TypedSource)
    (invalidOperand : Site → Resolved.LocalId → Syntax.ValueAssignOp → Word) :
    Factory false diagnosticPolicy source invalidOperand :=
  ⟨fun head registry faults => head.ErrorsFor diagnosticPolicy registry faults,
   fun _ _ _ _ _ _ given => given⟩

/-- Missing/default and uninitialized laws, together with the explicit inclusion
of real operand diagnostics in the caller's whole fault interpretation. -/
structure Residual {values : SourceCoreCompatibleValues.Context} {source : TypedSource}
    {context : SourceSemantics.Context} {certificate : GenericExpressionMeaning.Certificate}
    {scope : SourceCoreLocalCell.Scope} {administrative : Core.Context} {definitions : DataEnvironment}
    {assignment : AssignmentResolution} {operator : Syntax.ValueAssignOp} {rhs : ExpressionId}
    (head : GenericAssignmentStatements.Head values source context certificate scope administrative definitions assignment operator rhs)
    (table : SourceCoreAssignmentFaultSites.Table) (registry : SourceCoreRawMetadata.Registry) (faults : FunctionCalls.FaultRep) : Prop where
  missing : ∀ {root resolved reason word count},
    CompatibleMixedRoute.FaultToken values.checked registry root head.prepared.steps resolved reason word count → faults reason word
  uninitialized : ∀ location, faults (.uninitializedLocation location) head.prepared.invalidProjection
  included : ∀ reason word, GenericAssignmentDiagnostics.OperandRep table reason word → faults reason word

def Factory.prepared {first : Nat} {table : SourceCoreAssignmentFaultSites.Table}
    (typed : OperandsTyped source) (prepared : SourceCoreAssignmentFaultSites.prepare source first = .ok table) :
    Factory true .reachable source (GenericAssignmentDiagnostics.token table) where
  residual := fun head registry faults => Residual head table registry faults
  materialize := by
    intro values context certificate scope administrative definitions assignment operator rhs head site origin same registry faults given
    exact ⟨given.missing, given.uninitialized, same.symm ▸ origin.prepared typed prepared given.included⟩

/-- The initializer compiler graph retains the authentic parent site. In the
untracked compatibility mode this is exactly the old existential graph. -/
def InitialAcceptedFor (tracked : Bool) (policy : SourceCoreLoops.Policy) (fuel : Nat)
    (source : TypedSource) (scope : SourceCoreLocalCell.Scope) (items : List ForItemForm)
    (condition : ExpressionId) (post : List ForItemForm) (statements : List StatementId)
    (type : Ty) (reasonAt : ExpressionId → Word) (selfReason : Word) (code : Expr) : Prop :=
  ∃ headerFuel parentSite, ∃ next : SourceCoreLocalCell.Scope → Except SourceCoreBasic.Error Expr,
    ForOriginFor tracked source parentSite items condition post statements ∧
    SourceCoreLoops.lowerForItems policy parentSite headerFuel source scope items type reasonAt next = .ok code ∧
    ∀ loopScope nextCode, next loopScope = .ok nextCode →
      ∃ conditionCode : SourceCoreBasic.LoweredExpr, ∃ loopCode postCode,
        policy.lowerExpression fuel source loopScope condition reasonAt = .ok conditionCode ∧ conditionCode.type = .bool ∧
        SourceCoreLoops.lowerFlowStatementsWithPolicy policy fuel source loopScope statements type reasonAt false selfReason = .ok loopCode ∧
        SourceCoreLoops.lowerForItems policy parentSite fuel source loopScope post type reasonAt
          (fun _ => pure (LocalLoop.fallthrough type)) = .ok postCode ∧
        nextCode = LocalLoop.iterate type conditionCode.expression loopCode postCode selfReason

def AcceptedFor (tracked : Bool) (policy : SourceCoreLoops.Policy) (fuel : Nat)
    (source : TypedSource) (scope : SourceCoreLocalCell.Scope) (position : TypedImperativeFor.Position)
    (type : Ty) (reasonAt : ExpressionId → Word) (selfReason : Word) (code : Expr) : Prop :=
  match position with
  | .statements mode statements => SourceCoreLoops.lowerFlowStatementsWithPolicy policy fuel source scope statements type reasonAt mode selfReason = .ok code
  | .initializers items condition post statements => InitialAcceptedFor tracked policy fuel source scope items condition post statements type reasonAt selfReason code

theorem AcceptedFor.untracked {policy : SourceCoreLoops.Policy} {fuel : Nat} {scope : SourceCoreLocalCell.Scope}
    {position : TypedImperativeFor.Position} {type : Ty} {reasonAt : ExpressionId → Word} {selfReason : Word} {code : Expr}
    (accepted : TypedImperativeFor.Accepted policy fuel source scope position type reasonAt selfReason code) :
    AcceptedFor false policy fuel source scope position type reasonAt selfReason code := by
  cases position with
  | statements => exact accepted
  | initializers =>
    obtain ⟨fuel, site, next, accepted, continuation⟩ := accepted
    exact ⟨fuel, site, next, True.intro, accepted, continuation⟩

end Solcore.SourceSemantics.CoreLowering.AssignmentDiagnosticOrigins
