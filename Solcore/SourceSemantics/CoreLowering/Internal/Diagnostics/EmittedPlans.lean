import Solcore.SourceSemantics.CoreLowering.Internal.Statements.GenericAssignments
import Solcore.SourceSemantics.CoreLowering.Internal.Statements.TypedImperativeForTrees
import Solcore.SourceSemantics.CoreLowering.Internal.Compatible.BitNotStatements

/-!
# Emitted diagnostic plans

Plans of emitted diagnostics, in plain, token and prepared form, and the policy and origins of assignment diagnostics.
-/

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.AssignmentDiagnosticPolicy
/-! One static policy selects the original unconditional operand receipt or its
reachable form. Both preserve missing/default and uninitialized laws. The policy
contains no execution and its interpretation never enlarges the fault relation. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering
open Core Frontend SourceInference

inductive AssignmentDiagnosticPolicy where
  | unconditional
  | reachable

namespace GenericAssignmentStatements.Head
variable {values : ValuesContext} {source : TypedSource}
  {context : SourceSemantics.Context} {certificate : GenericExpressionMeaning.Certificate}
  {scope : Scope} {administrative : Core.Context} {definitions : DataEnvironment}
  {assignment : AssignmentResolution} {operator : Syntax.ValueAssignOp} {rhs : ExpressionId}

/-- The selected assignment diagnostic receipt at one actual Head. -/
def ErrorsFor
    (head : Head values source context certificate scope administrative definitions assignment operator rhs)
    (policy : AssignmentDiagnosticPolicy) (registry : SourceCoreRawMetadata.Registry)
    (faults : FunctionCalls.FaultRep) : Prop :=
  match policy with
  | .unconditional => head.Errors registry faults
  | .reachable => head.ReachableErrors registry faults

theorem ErrorsFor.reachable
    {head : Head values source context certificate scope administrative definitions assignment operator rhs}
    {policy : AssignmentDiagnosticPolicy} {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
    (errors : head.ErrorsFor policy registry faults) : head.ReachableErrors registry faults := by
  cases policy with
  | unconditional => exact Errors.reachable errors
  | reachable => exact errors

end GenericAssignmentStatements.Head
end Solcore.SourceSemantics.CoreLowering
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.AssignmentDiagnosticOrigins
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
    operator = .equal ∨ assignment.target.type = .word ∨ assignment.target.type = .integer ∧ operator.wordOnly = false := by
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
  uninitialized : head.prepared.steps ≠ [] → ∀ location, faults (.uninitializedLocation location) head.prepared.invalidProjection
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
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.EmittedDiagnosticPlan
/-! Diagnostic plans retain the genuine local heads and scoped child indices
selected by the original static compiler traversals. Their requirements contain
only pure leaves, concrete local residuals and actual child combinations. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.EmittedDiagnosticPlan
open Core Frontend SourceInference

variable {source : TypedSource} {tracked : Bool} {diagnosticPolicy : AssignmentDiagnosticPolicy}
  {invalidOperand : SourceCoreElaboration.ErrorSite → Resolved.LocalId → Syntax.ValueAssignOp → Word}
  (factory : AssignmentDiagnosticOrigins.Factory tracked diagnosticPolicy source invalidOperand)

inductive Plan (factory : AssignmentDiagnosticOrigins.Factory tracked diagnosticPolicy source invalidOperand) : Type where
  | pure : Plan factory
  | pair (left right : Plan factory) : Plan factory
  | assignment {values : SourceCoreCompatibleValues.Context} {context : SourceSemantics.Context}
      {certificate : GenericExpressionMeaning.Certificate} {scope : SourceCoreLocalCell.Scope}
      {administrative : Core.Context} {definitions : DataEnvironment}
      {assignment : AssignmentResolution} {operator : Syntax.ValueAssignOp} {rhs : ExpressionId}
      (head : GenericAssignmentStatements.Head values source context certificate scope administrative definitions assignment operator rhs)
      (site : SourceCoreElaboration.ErrorSite)
      (origin : AssignmentDiagnosticOrigins.OccursFor tracked source site assignment operator rhs)
      (same : head.invalid = invalidOperand site assignment.target.root operator)
      (sourceTyped : ∀ binder, SourceCoreDataPlaces.rootBinder source assignment.target.root = .ok binder →
        SourceProjectionsHaveType source context binder.scheme.body assignment.target.projections assignment.target.type)
      (rightTyped : ExpressionHasType source context rhs assignment.target.type)
      (profile : operator = .equal ∨ SourceCoreRawMetadata.runtimeType assignment.target.type = .word ∨
        SourceCoreRawMetadata.runtimeType assignment.target.type = .integer ∧ operator.wordOnly = false) : Plan factory
  | unary {context : SourceSemantics.Context} {scope : SourceCoreLocalCell.Scope} {assignment : AssignmentResolution}
      (head : CompatibleBitNotStatements.Head context scope assignment)
      (writable : ∀ binder, SourceCoreDataPlaces.rootBinder source assignment.target.root = .ok binder →
        WritableLocal context assignment.target.root binder.scheme.body)
      (bare : assignment.target.projections = [])
      (profile : SourceCoreRawMetadata.runtimeType assignment.target.type = .word ∨
        SourceCoreRawMetadata.runtimeType assignment.target.type = .integer) : Plan factory
  | selected (requests : List GenericMatchChildren.Request) (parent : SourceSemantics.Context)
      (hiddenIds : List Resolved.LocalId) (scrutineeType : TypeSystem.Ty)
      (cases : List TypedMatchCase) (fallback : Option (List StatementId))
      (children : ∀ request, request ∈ requests → ∀ childContext,
        GenericMatchChildren.ScopedContextFor source parent hiddenIds scrutineeType cases fallback request childContext → Plan factory) : Plan factory

namespace Plan
variable {factory}
/-- The exact emitted predicate is visible through the concrete diagnostic plan. -/
def requirements : Plan factory → SourceCoreRawMetadata.Registry → FunctionCalls.FaultRep → Prop
  | .pure, _, _ => True
  | .pair left right, registry, faults => requirements left registry faults ∧ requirements right registry faults
  | .assignment head _ _ _ _ _ _, registry, faults => factory.residual head registry faults
  | .unary head _ _ _, _, faults => head.Errors faults
  | .selected _ _ _ _ _ _ children, registry, faults =>
    ∀ request member childContext related, requirements (children request member childContext related) registry faults

/-- Local diagnostic receipts concern the exact generated heads and their
original Source typing. They contain no expression or body execution law. -/
structure LocalReceipts (registry : SourceCoreRawMetadata.Registry) (faults : FunctionCalls.FaultRep) : Prop where
  assignment : ∀ {values context certificate scope administrative definitions assignment operator rhs}
    (head : GenericAssignmentStatements.Head values source context certificate scope administrative definitions assignment operator rhs)
    (site : SourceCoreElaboration.ErrorSite)
    (_origin : AssignmentDiagnosticOrigins.OccursFor tracked source site assignment operator rhs)
    (_same : head.invalid = invalidOperand site assignment.target.root operator)
    (_sourceTyped : ∀ binder, SourceCoreDataPlaces.rootBinder source assignment.target.root = .ok binder →
      SourceProjectionsHaveType source context binder.scheme.body assignment.target.projections assignment.target.type)
    (_rightTyped : ExpressionHasType source context rhs assignment.target.type)
    (_profile : operator = .equal ∨ SourceCoreRawMetadata.runtimeType assignment.target.type = .word ∨
      SourceCoreRawMetadata.runtimeType assignment.target.type = .integer ∧ operator.wordOnly = false), factory.residual head registry faults
  unary : ∀ {context scope assignment} (head : CompatibleBitNotStatements.Head context scope assignment)
    (_writable : ∀ binder, SourceCoreDataPlaces.rootBinder source assignment.target.root = .ok binder →
      WritableLocal context assignment.target.root binder.scheme.body)
    (_bare : assignment.target.projections = [])
    (_profile : SourceCoreRawMetadata.runtimeType assignment.target.type = .word ∨
      SourceCoreRawMetadata.runtimeType assignment.target.type = .integer), head.Errors faults

/-- This finite static interpreter follows only the retained diagnostic plan. -/
theorem interpret {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
    (receipts : LocalReceipts (factory := factory) registry faults) : (plan : Plan factory) → requirements plan registry faults
  | .pure => True.intro
  | .pair left right => ⟨interpret receipts left, interpret receipts right⟩
  | .assignment head site origin same sourceTyped rightTyped profile =>
      receipts.assignment head site origin same sourceTyped rightTyped profile
  | .unary head writable bare profile => receipts.unary head writable bare profile
  | .selected _ _ _ _ _ _ children => fun request member childContext related =>
      interpret receipts (children request member childContext related)
end Plan

/-- The original extraction and its exact emitted diagnostic equation travel
as one witness. The code, Tree and materialization remain original. -/
structure Produced (α : Type) (diagnostics : α → SourceCoreRawMetadata.Registry → FunctionCalls.FaultRep → Prop) where
  original : α
  plan : Plan factory
  equation : ∀ registry faults, diagnostics original registry faults = plan.requirements registry faults

namespace Produced
variable {factory} {α : Type} {diagnostics : α → SourceCoreRawMetadata.Registry → FunctionCalls.FaultRep → Prop}
theorem interpreted (produced : Produced factory α diagnostics) {registry : SourceCoreRawMetadata.Registry}
    {faults : FunctionCalls.FaultRep} (receipts : Plan.LocalReceipts (factory := factory) registry faults) :
    diagnostics produced.original registry faults :=
  (produced.equation registry faults).symm ▸ produced.plan.interpret receipts
end Produced
end Solcore.SourceSemantics.CoreLowering.EmittedDiagnosticPlan
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.EmittedDiagnosticTokenPlan
/-! The companion token witness retains actual unary sites beside the original
emitted plan. Prepared tables supply only their genuine unary and operand
categories. Missing defaults and uninitialized places keep their explicit laws
at the actual assignment atoms; no broader fault interpretation is inferred. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.EmittedDiagnosticTokenPlan
open Core Frontend SourceInference
open EmittedDiagnosticPlan

/-- Both ordinary statements and header items retain their real owning site. -/
inductive UnaryOccurs (source : TypedSource) : SourceCoreElaboration.ErrorSite → AssignmentResolution → Prop where
  | statement {id node assignment}
      (found : source.lookupStatement? id = some node) (form : node.form = .assignBitNot assignment) :
      UnaryOccurs source (.occurrence id.occurrence) assignment
  | header {id node initial condition post body assignment}
      (found : source.lookupStatement? id = some node) (form : node.form = .forLoop initial condition post body)
      (member : .assignBitNot assignment ∈ initial ++ post) :
      UnaryOccurs source (.occurrence id.occurrence) assignment

abbrev UnaryOccursFor (tracked : Bool) (source : TypedSource) (site : SourceCoreElaboration.ErrorSite)
    (assignment : AssignmentResolution) : Prop := if tracked then UnaryOccurs source site assignment else True

variable {source : TypedSource} {site : SourceCoreElaboration.ErrorSite} {tracked : Bool}
  {assignment : AssignmentResolution} {items : List ForItemForm}

theorem UnaryOccursFor.statement {id : StatementId} {node : StatementNode}
    (found : source.lookupStatement? id = some node) (form : node.form = .assignBitNot assignment) :
    UnaryOccursFor tracked source (.occurrence id.occurrence) assignment := by
  cases tracked with
  | false => trivial
  | true => exact .statement found form

/-- The genuine header suffix identifies the current unary occurrence. -/
theorem UnaryOccursFor.of_header
    (origin : AssignmentDiagnosticOrigins.HeaderOriginFor tracked source site (.assignBitNot assignment :: items)) :
    UnaryOccursFor tracked source site assignment := by
  cases tracked with
  | false => trivial
  | true =>
    rcases origin with ⟨id,node,initial,condition,post,body,found,form,rfl,beforeItems,suffix⟩ |
      ⟨id,node,initial,condition,post,body,found,form,rfl,beforeItems,suffix⟩
    · exact .header found form (List.mem_append_left _ (suffix ▸ List.mem_append_right _ (List.mem_cons_self)))
    · exact .header found form (List.mem_append_right _ (suffix ▸ List.mem_append_right _ (List.mem_cons_self)))

/-- Raw scalar eligibility is established by original Source unary typing. -/
def UnaryTyped (source : TypedSource) : Prop :=
  ∀ {site assignment}, UnaryOccurs source site assignment →
    ∃ context, SourceBitNotAssignmentValid source context assignment

theorem unary_raw_type {context : SourceSemantics.Context}
    (typed : SourceBitNotAssignmentValid source context assignment) : assignment.target.type = .word := by
  cases typed with
  | intro place => cases place with
    | intro _ _ same => exact same

/-- Only authentic unary table entries belong to this concrete relation. -/
def UnaryRep (table : SourceCoreAssignmentFaultSites.Table) : FunctionCalls.FaultRep
  | .invalidUnaryOperand .bitNot, token => ∃ diagnostic,
      table.diagnostic? token = some diagnostic ∧ diagnostic.error = .invalidUnaryOperand .bitNot none
  | _, _ => False

/-- A real Source occurrence and the original table producer recover its token. -/
theorem UnaryOccurs.prepared {first : Nat} {table : SourceCoreAssignmentFaultSites.Table}
    (origin : UnaryOccurs source site assignment) (typed : UnaryTyped source)
    (issued : SourceCoreAssignmentFaultSites.prepare source first = .ok table) :
    UnaryRep table (.invalidUnaryOperand .bitNot) (table.reasonAt site assignment.target.root .bitNot) := by
  obtain ⟨context, sourceTyped⟩ := typed origin
  have scalar : assignment.target.type = .word ∨ assignment.target.type = .integer := .inl (unary_raw_type sourceTyped)
  cases origin with
  | statement found form =>
    have present := lookupStatement?_sound found
    obtain ⟨entry,_,_,_,kind,reason,diagnostic⟩ :=
      SourceCoreAssignmentFaultSites.Certificates.prepare_unary issued present.1 (.statement form) scalar
    rw [← present.2, reason]
    exact ⟨entry.diagnostic, diagnostic, by simp only [SourceCoreAssignmentFaultSites.Site.diagnostic,kind]⟩
  | header found form member =>
    have present := lookupStatement?_sound found
    obtain ⟨entry,_,_,_,kind,reason,diagnostic⟩ :=
      SourceCoreAssignmentFaultSites.Certificates.prepare_unary issued present.1 (.header form member) scalar
    rw [← present.2, reason]
    exact ⟨entry.diagnostic, diagnostic, by simp only [SourceCoreAssignmentFaultSites.Site.diagnostic,kind]⟩

variable {diagnosticPolicy : AssignmentDiagnosticPolicy}
  {invalidOperand : SourceCoreElaboration.ErrorSite → Resolved.LocalId → Syntax.ValueAssignOp → Word}
  (factory : AssignmentDiagnosticOrigins.Factory tracked diagnosticPolicy source invalidOperand)
  (invalidUnary : SourceCoreElaboration.ErrorSite → Resolved.LocalId → Word)

/-- Token witnesses follow the exact retained plan and selected scoped requests. -/
inductive TokensFor : Plan factory → Prop where
  | pure : TokensFor .pure
  | pair {left right} (first : TokensFor left) (second : TokensFor right) : TokensFor (.pair left right)
  | assignment {values context certificate scope administrative definitions assignment operator rhs}
      (head : GenericAssignmentStatements.Head values source context certificate scope administrative definitions assignment operator rhs)
      (site : SourceCoreElaboration.ErrorSite)
      (origin : AssignmentDiagnosticOrigins.OccursFor tracked source site assignment operator rhs)
      (same : head.invalid = invalidOperand site assignment.target.root operator)
      (sourceTyped : ∀ binder, SourceCoreDataPlaces.rootBinder source assignment.target.root = .ok binder →
        SourceProjectionsHaveType source context binder.scheme.body assignment.target.projections assignment.target.type)
      (rightTyped : ExpressionHasType source context rhs assignment.target.type)
      (profile : operator = .equal ∨ SourceCoreRawMetadata.runtimeType assignment.target.type = .word ∨
        SourceCoreRawMetadata.runtimeType assignment.target.type = .integer ∧ operator.wordOnly = false) :
      TokensFor (.assignment head site origin same sourceTyped rightTyped profile)
  | unary {context scope assignment}
      (head : CompatibleBitNotStatements.Head context scope assignment)
      (writable : ∀ binder, SourceCoreDataPlaces.rootBinder source assignment.target.root = .ok binder →
        WritableLocal context assignment.target.root binder.scheme.body)
      (bare : assignment.target.projections = [])
      (profile : SourceCoreRawMetadata.runtimeType assignment.target.type = .word ∨
        SourceCoreRawMetadata.runtimeType assignment.target.type = .integer)
      (site : SourceCoreElaboration.ErrorSite) (origin : UnaryOccursFor tracked source site assignment)
      (same : head.invalid = invalidUnary site assignment.target.root) :
      TokensFor (.unary head writable bare profile)
  | selected {requests parent hiddenIds scrutineeType cases fallback children}
      (tokens : ∀ request member childContext related,
        TokensFor (children request member childContext related)) :
      TokensFor (.selected requests parent hiddenIds scrutineeType cases fallback children)

/-- The original extraction, plan and own diagnostic equation remain intact. -/
structure Produced (α : Type) (diagnostics : α → SourceCoreRawMetadata.Registry → FunctionCalls.FaultRep → Prop)
    extends EmittedDiagnosticPlan.Produced factory α diagnostics where
  tokens : TokensFor factory invalidUnary plan

/-- The unresolved place categories retain their original scope explicitly. -/
structure PlaceErrors {values : SourceCoreCompatibleValues.Context} {context : SourceSemantics.Context}
    {certificate : GenericExpressionMeaning.Certificate} {scope : SourceCoreLocalCell.Scope}
    {administrative : Core.Context} {definitions : DataEnvironment}
    {assignment : AssignmentResolution} {operator : Syntax.ValueAssignOp} {rhs : ExpressionId}
    (head : GenericAssignmentStatements.Head values source context certificate scope administrative definitions assignment operator rhs)
    (registry : SourceCoreRawMetadata.Registry) (faults : FunctionCalls.FaultRep) : Prop where
  missing : ∀ {root resolved reason token count},
    CompatibleMixedRoute.FaultToken values.checked registry root head.prepared.steps resolved reason token count → faults reason token
  uninitialized : ∀ location, faults (.uninitializedLocation location) head.prepared.invalidProjection

namespace Plan
variable {factory}
/-- These two remaining laws concern only actual assignment atoms. Pure and
unary plans require no local place receipt. The scope remains explicit. -/
def PlaceFaults (registry : SourceCoreRawMetadata.Registry) (faults : FunctionCalls.FaultRep) : Plan factory → Prop
  | .pure => True
  | .pair left right => PlaceFaults registry faults left ∧ PlaceFaults registry faults right
  | .assignment head _ _ _ _ _ _ =>
      PlaceErrors head registry faults
  | .unary _ _ _ _ => True
  | .selected _ _ _ _ _ _ children =>
      ∀ request member childContext related, PlaceFaults registry faults (children request member childContext related)
end Plan

/-- Only genuine assignment atoms request the unresolved place categories.
All Source occurrence, RHS and path typing receipts remain attached. -/
def PlaceReceipts (registry : SourceCoreRawMetadata.Registry) (faults : FunctionCalls.FaultRep) : Prop :=
  ∀ {values context certificate scope administrative definitions assignment operator rhs}
    (head : GenericAssignmentStatements.Head values source context certificate scope administrative definitions assignment operator rhs)
    (site : SourceCoreElaboration.ErrorSite),
    AssignmentDiagnosticOrigins.OccursFor tracked source site assignment operator rhs →
    head.invalid = invalidOperand site assignment.target.root operator →
    (∀ binder, SourceCoreDataPlaces.rootBinder source assignment.target.root = .ok binder →
      SourceProjectionsHaveType source context binder.scheme.body assignment.target.projections assignment.target.type) →
    ExpressionHasType source context rhs assignment.target.type →
    (operator = .equal ∨ SourceCoreRawMetadata.runtimeType assignment.target.type = .word ∨
      SourceCoreRawMetadata.runtimeType assignment.target.type = .integer ∧ operator.wordOnly = false) →
    PlaceErrors head registry faults

namespace TokensFor
/-- The actual token witness projects local place receipts only at its
assignment atoms. Pure and unary atoms require no such receipt. -/
theorem place_faults {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
    {plan : Plan factory} (tokens : TokensFor factory invalidUnary plan)
    (places : PlaceReceipts (source := source) (tracked := tracked) (invalidOperand := invalidOperand) registry faults) :
    Plan.PlaceFaults registry faults plan := by
  induction tokens with
  | pure => trivial
  | pair _ _ firstIH secondIH => exact ⟨firstIH, secondIH⟩
  | assignment head site origin same sourceTyped rightTyped profile =>
    exact places head site origin same sourceTyped rightTyped profile
  | unary => trivial
  | selected _ ih => exact fun request member childContext related => ih request member childContext related
/-- Prepared table interpretation supplies actual unary and operand categories;
the remaining two place laws are passed only at the retained assignment atoms. -/
theorem interpret_prepared {first : Nat} {table : SourceCoreAssignmentFaultSites.Table}
    {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
    (operandTyped : AssignmentDiagnosticOrigins.OperandsTyped source)
    (unaryTyped : UnaryTyped source) (issued : SourceCoreAssignmentFaultSites.prepare source first = .ok table)
    (operandIncluded : ∀ reason token, GenericAssignmentDiagnostics.OperandRep table reason token → faults reason token)
    (unaryIncluded : ∀ reason token, UnaryRep table reason token → faults reason token)
    {plan : Plan (AssignmentDiagnosticOrigins.Factory.prepared operandTyped issued)}
    (tokens : TokensFor (AssignmentDiagnosticOrigins.Factory.prepared operandTyped issued)
      (fun site root => table.reasonAt site root .bitNot) plan)
    (remaining : Plan.PlaceFaults registry faults plan) : plan.requirements registry faults := by
  revert remaining
  induction tokens with
  | pure => intro _; trivial
  | pair first second firstIH secondIH =>
    intro remaining
    exact ⟨firstIH remaining.1, secondIH remaining.2⟩
  | assignment head _ _ _ _ _ _ =>
    intro remaining
    exact ⟨remaining.missing, (fun _ => remaining.uninitialized), operandIncluded⟩
  | unary head _ _ _ site origin same =>
    intro _
    change faults (.invalidUnaryOperand .bitNot) head.invalid
    exact same.symm ▸ unaryIncluded _ _ (origin.prepared unaryTyped issued)
  | selected children ih =>
    intro remaining request member childContext related
    exact ih request member childContext related (remaining request member childContext related)
end TokensFor
end Solcore.SourceSemantics.CoreLowering.EmittedDiagnosticTokenPlan
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.EmittedDiagnosticPreparedPlan
/-! Static preparation facets belong to the same retained emitted plan. Each
assignment atom keeps its chosen head and actual owning site and preparation
parameters. No runtime state or fault interpretation is stored here. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.EmittedDiagnosticPreparedPlan
open Core Frontend SourceInference
open EmittedDiagnosticPlan
variable {tracked : Bool} {diagnosticPolicy : AssignmentDiagnosticPolicy} {source : TypedSource}
  {invalidOperand : SourceCoreElaboration.ErrorSite → Resolved.LocalId → Syntax.ValueAssignOp → Word}
  {factory : AssignmentDiagnosticOrigins.Factory tracked diagnosticPolicy source invalidOperand}

/-- Every assignment retains its real selected preparation at its owning site. -/
def PreparedFor
    (invalidProjection : SourceCoreElaboration.ErrorSite → Resolved.LocalId → Word)
    (missingDefault : SourceCoreElaboration.ErrorSite → Resolved.LocalId → TypeSystem.Ty → Word) : Plan factory → Prop
  | .pure => True
  | .pair left right => PreparedFor invalidProjection missingDefault left ∧ PreparedFor invalidProjection missingDefault right
  | .assignment (assignment := assignment) head site _ _ _ _ _ =>
      ∃ fuel, head.PreparedAt site fuel (invalidProjection site assignment.target.root)
        (missingDefault site assignment.target.root)
  | .unary _ _ _ _ => True
  | .selected _ _ _ _ _ _ children =>
      ∀ request member childContext related, PreparedFor invalidProjection missingDefault (children request member childContext related)

/-- The original complete token extraction and plan stay together with their
static preparation facets. -/
structure Produced
    (factory : AssignmentDiagnosticOrigins.Factory tracked diagnosticPolicy source invalidOperand)
    (invalidUnary : SourceCoreElaboration.ErrorSite → Resolved.LocalId → Word)
    (invalidProjection : SourceCoreElaboration.ErrorSite → Resolved.LocalId → Word)
    (missingDefault : SourceCoreElaboration.ErrorSite → Resolved.LocalId → TypeSystem.Ty → Word)
    (α : Type) (diagnostics : α → SourceCoreRawMetadata.Registry → FunctionCalls.FaultRep → Prop) where
  original : EmittedDiagnosticTokenPlan.Produced factory invalidUnary α diagnostics
  prepared : PreparedFor invalidProjection missingDefault original.plan

end Solcore.SourceSemantics.CoreLowering.EmittedDiagnosticPreparedPlan
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.EmittedPreparedDiagnostics
/-! The actual operand table interprets the prepared assignment residual.
Missing/default and uninitialized receipts still concern each real generated
Head. Only genuine table diagnostics are included in the supplied fault model. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.EmittedDiagnosticPlan.Plan.LocalReceipts
open Core Frontend SourceInference

variable {source : TypedSource} {first : Nat} {table : SourceCoreAssignmentFaultSites.Table}
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}

/-- The emitted prepared residual follows from real local Errors and the
original table inclusion, preserving the independent Source origin typing. -/
theorem prepared
    (typed : AssignmentDiagnosticOrigins.OperandsTyped source)
    (issued : SourceCoreAssignmentFaultSites.prepare source first = .ok table)
    (errors : Plan.LocalReceipts (factory := AssignmentDiagnosticOrigins.Factory.unchanged .reachable source
      (GenericAssignmentDiagnostics.token table)) registry faults)
    (included : ∀ reason token, GenericAssignmentDiagnostics.OperandRep table reason token → faults reason token) :
    Plan.LocalReceipts (factory := AssignmentDiagnosticOrigins.Factory.prepared typed issued) registry faults := by
  refine ⟨?_, errors.unary⟩
  intro values context certificate scope administrative definitions assignment operator rhs head site _origin same
    sourceTyped rightTyped profile
  have actual := errors.assignment head site True.intro same sourceTyped rightTyped profile
  exact ⟨actual.missing, actual.uninitialized, included⟩

end Solcore.SourceSemantics.CoreLowering.EmittedDiagnosticPlan.Plan.LocalReceipts
end
