import Solcore.SourceSemantics.CoreLowering.EmittedDiagnosticPlan

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
        SourceCoreRawMetadata.runtimeType assignment.target.type = .integer) :
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
      SourceCoreRawMetadata.runtimeType assignment.target.type = .integer) →
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
    exact ⟨remaining.missing, remaining.uninitialized, operandIncluded⟩
  | unary head _ _ _ site origin same =>
    intro _
    change faults (.invalidUnaryOperand .bitNot) head.invalid
    exact same.symm ▸ unaryIncluded _ _ (origin.prepared unaryTyped issued)
  | selected children ih =>
    intro remaining request member childContext related
    exact ih request member childContext related (remaining request member childContext related)
end TokensFor
end Solcore.SourceSemantics.CoreLowering.EmittedDiagnosticTokenPlan
