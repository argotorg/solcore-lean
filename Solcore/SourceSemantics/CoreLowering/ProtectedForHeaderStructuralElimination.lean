import Solcore.SourceSemantics.CoreLowering.EmittedForHeaderCoupling
import Solcore.SourceSemantics.CoreLowering.EmittedDiagnosticTokenPlan

/-! Structural eliminators use the existing static recursors. Assignment and
unary payloads describe the actual selected head. The motive depends only on
the header indices; semantic branches are supplied once by each consumer. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.GenericForHeader.Structural
open Core Frontend SourceInference
open TypedLexicalWhile (absentRequest initializedRequest sequence)
variable {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
  {active : TypeSystem.Substitution} {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error}
  {values : ValuesContext} {source : TypedSource}
  {certificates : SourceSemantics.Context → GenericExpressionMeaning.Certificate}
  {definitions : DataEnvironment} {administrative : Core.Context} {type : Ty}
  {continuation : SourceSemantics.Context → Scope → Expr → Prop}

abbrev AssignmentPayload (values : ValuesContext) (source : TypedSource)
    (certificates : SourceSemantics.Context → GenericExpressionMeaning.Certificate)
    (administrative : Core.Context) (definitions : DataEnvironment) :=
  ∀ {context scope assignment operator rhs},
    GenericAssignmentStatements.Head values source context (certificates context) scope
      administrative definitions assignment operator rhs → Prop

abbrev UnaryPayload := ∀ {context scope assignment}, CompatibleBitNotStatements.Head context scope assignment → Prop

structure BranchAlgebra
    (AP : AssignmentPayload values source certificates administrative definitions) (UP : UnaryPayload)
    (M : SourceSemantics.Context → Scope → List ForItemForm → Expr → Prop) : Prop where
  nil : ∀ {context scope code}, continuation context scope code → M context scope [] code
  uninitialized : ∀ {context nextContext scope binder rest body payload},
    binder.scheme.quantified = [] → BinderExtends source.owner context binder nextContext →
    source.inputs.any (fun input => decide (input.id = binder.id)) = false →
    values.checked.catalog.project binder.scheme.body = .ok payload →
    ∀ (allocation : SourceCoreAllocationLayouts.Allocation layouts owner active (absentRequest source scope binder payload))
      (annotation : SourceCoreCallableIndexedAllocationFrames.Annotated frame globals
        (layouts.allocatorAt owner active onError) (absentRequest source scope binder payload)),
    annotation.original = allocation.expression → M nextContext ((binder.id, payload) :: scope) rest body →
    M context scope (.letDecl binder none :: rest) (.letE annotation.expression body)
  initialized : ∀ {context nextContext scope binder initializer initializerNode lowered body rest},
    binder.scheme.quantified = [] → BinderExtends source.owner context binder nextContext →
    source.inputs.any (fun input => decide (input.id = binder.id)) = false →
    source.lookupExpression? initializer = some initializerNode → initializerNode.type = binder.scheme.body →
    certificates context scope initializer lowered →
    ∀ (allocation : SourceCoreAllocationLayouts.Allocation layouts owner active (initializedRequest source scope binder lowered.type))
      (annotation : SourceCoreCallableIndexedAllocationFrames.Annotated frame globals
        (layouts.allocatorAt owner active onError) (initializedRequest source scope binder lowered.type)),
    annotation.original = allocation.expression → M nextContext ((binder.id, lowered.type) :: scope) rest body →
    M context scope (.letDecl binder (some initializer) :: rest) (sequence type lowered.expression annotation.expression body)
  discard : ∀ {context scope expression expressionNode rest lowered body},
    source.lookupExpression? expression = some expressionNode → certificates context scope expression lowered →
    M context scope rest body →
    M context scope (.expression expression :: rest) (LocalSequence.discard (LocalLoop.controlType type) lowered.expression body)
  assign : ∀ {context scope assignment operator rhs rest body}
    (head : GenericAssignmentStatements.Head values source context (certificates context) scope administrative definitions assignment operator rhs),
    AP head → M context scope rest body →
    M context scope (.assignValue assignment operator rhs :: rest) (head.emit body (LocalLoop.controlType type))
  bitNot : ∀ {context scope assignment rest body} (head : CompatibleBitNotStatements.Head context scope assignment),
    UP head → M context scope rest body →
    M context scope (.assignBitNot assignment :: rest) (head.emit body (LocalLoop.controlType type))

def Eliminates (AP : AssignmentPayload values source certificates administrative definitions) (UP : UnaryPayload)
    (context : SourceSemantics.Context) (scope : Scope) (items : List ForItemForm) (code : Expr) : Prop :=
  ∀ M : SourceSemantics.Context → Scope → List ForItemForm → Expr → Prop,
    BranchAlgebra (layouts := layouts) (owner := owner) (active := active) (frame := frame)
      (globals := globals) (onError := onError) (type := type) (continuation := continuation) AP UP M →
    M context scope items code

/-- Legacy payloads retain their exact original diagnostic receipts. -/
theorem of_reachable_errors {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
    {context scope items code}
    {tree : Tree layouts owner active frame globals onError values source certificates definitions administrative type continuation context scope items code}
    (errors : Tree.ReachableErrors registry faults tree) :
    Eliminates (layouts := layouts) (owner := owner) (active := active) (frame := frame)
      (globals := globals) (onError := onError) (type := type) (continuation := continuation)
      (values := values) (source := source) (certificates := certificates)
      (definitions := definitions) (administrative := administrative)
      (fun head => head.ReachableErrors registry faults) (fun head => head.Errors faults) context scope items code := by
  intro M algebra
  refine Tree.ErrorsFor.rec
    (motive := fun {context scope items code} _ _ => M context scope items code)
    ?_ ?_ ?_ ?_ ?_ ?_ errors
  · intro context scope code next
    exact algebra.nil next
  · intro context nextContext scope binder rest body payload mono extended ordinary projected allocation annotation same remaining remainingErrors ih
    exact algebra.uninitialized mono extended ordinary projected allocation annotation same ih
  · intro context nextContext scope binder initializer initializerNode lowered body rest mono extended ordinary found sourceType initial allocation annotation same remaining remainingErrors ih
    exact algebra.initialized mono extended ordinary found sourceType initial allocation annotation same ih
  · intro context scope expression expressionNode rest lowered body found value remaining remainingErrors ih
    exact algebra.discard found value ih
  · intro context scope assignment operator rhs rest body head remaining remainingErrors receipt ih
    exact algebra.assign head receipt ih
  · intro context scope assignment rest body head remaining remainingErrors receipt ih
    exact algebra.bitNot head receipt ih

variable {tracked : Bool} {diagnosticPolicy : AssignmentDiagnosticPolicy}
  {invalidOperand : SourceCoreElaboration.ErrorSite → Resolved.LocalId → Syntax.ValueAssignOp → Word}
  {factory : AssignmentDiagnosticOrigins.Factory tracked diagnosticPolicy source invalidOperand}
  {invalidUnary : SourceCoreElaboration.ErrorSite → Resolved.LocalId → Word}
  {invalidProjection : SourceCoreElaboration.ErrorSite → Resolved.LocalId → Word}
  {missingDefault : SourceCoreElaboration.ErrorSite → Resolved.LocalId → TypeSystem.Ty → Word}

inductive PreparedAssignment
    (factory : AssignmentDiagnosticOrigins.Factory tracked diagnosticPolicy source invalidOperand)
    (invalidProjection : SourceCoreElaboration.ErrorSite → Resolved.LocalId → Word)
    (missingDefault : SourceCoreElaboration.ErrorSite → Resolved.LocalId → TypeSystem.Ty → Word)
    {context scope assignment operator rhs}
    (head : GenericAssignmentStatements.Head values source context (certificates context) scope administrative definitions assignment operator rhs) : Prop where
  | intro (site : SourceCoreElaboration.ErrorSite)
      (origin : AssignmentDiagnosticOrigins.OccursFor tracked source site assignment operator rhs)
      (same : head.invalid = invalidOperand site assignment.target.root operator)
      (sourceTyped : ∀ binder, SourceCoreDataPlaces.rootBinder source assignment.target.root = .ok binder →
        SourceProjectionsHaveType source context binder.scheme.body assignment.target.projections assignment.target.type)
      (rightTyped : ExpressionHasType source context rhs assignment.target.type)
      (profile : operator = .equal ∨ SourceCoreRawMetadata.runtimeType assignment.target.type = .word ∨
        SourceCoreRawMetadata.runtimeType assignment.target.type = .integer)
      (fuel : Nat)
      (prepared : head.PreparedAt site fuel (invalidProjection site assignment.target.root) (missingDefault site assignment.target.root)) :
      PreparedAssignment factory invalidProjection missingDefault head

inductive PreparedUnary (tracked : Bool) (source : TypedSource)
    (invalidUnary : SourceCoreElaboration.ErrorSite → Resolved.LocalId → Word)
    {context scope assignment} (head : CompatibleBitNotStatements.Head context scope assignment) : Prop where
  | intro
      (writable : ∀ binder, SourceCoreDataPlaces.rootBinder source assignment.target.root = .ok binder →
        WritableLocal context assignment.target.root binder.scheme.body)
      (bare : assignment.target.projections = [])
      (profile : SourceCoreRawMetadata.runtimeType assignment.target.type = .word ∨
        SourceCoreRawMetadata.runtimeType assignment.target.type = .integer)
      (site : SourceCoreElaboration.ErrorSite)
      (origin : EmittedDiagnosticTokenPlan.UnaryOccursFor tracked source site assignment)
      (same : head.invalid = invalidUnary site assignment.target.root) : PreparedUnary tracked source invalidUnary head

/-- The joint recursor obtains tokens only from the same retained Plan. -/
theorem of_coupled {context scope items code}
    {tree : Tree layouts owner active frame globals onError values source certificates definitions administrative type continuation context scope items code}
    {plan : EmittedDiagnosticPlan.Plan factory}
    (coupled : Coupled factory invalidProjection missingDefault tree plan)
    (tokens : EmittedDiagnosticTokenPlan.TokensFor factory invalidUnary plan) :
    Eliminates (layouts := layouts) (owner := owner) (active := active) (frame := frame)
      (globals := globals) (onError := onError) (type := type) (continuation := continuation)
      (values := values) (source := source) (certificates := certificates)
      (definitions := definitions) (administrative := administrative)
      (fun head => PreparedAssignment factory invalidProjection missingDefault head)
      (fun head => PreparedUnary tracked source invalidUnary head) context scope items code := by
  intro M algebra
  have result : EmittedDiagnosticTokenPlan.TokensFor factory invalidUnary plan → M context scope items code := by
    refine Coupled.rec (motive := fun {context scope items code} _ plan _ =>
      EmittedDiagnosticTokenPlan.TokensFor factory invalidUnary plan → M context scope items code)
      ?_ ?_ ?_ ?_ ?_ ?_ coupled
    · intro context scope code next tokens
      exact algebra.nil next
    · intro context nextContext scope binder rest body payload mono extended ordinary projected allocation annotation same remaining remainingPlan remainingCoupled ih tokens
      exact algebra.uninitialized mono extended ordinary projected allocation annotation same (ih tokens)
    · intro context nextContext scope binder initializer initializerNode lowered body rest mono extended ordinary found sourceType initial allocation annotation same remaining remainingPlan remainingCoupled ih tokens
      exact algebra.initialized mono extended ordinary found sourceType initial allocation annotation same (ih tokens)
    · intro context scope expression expressionNode rest lowered body found value remaining remainingPlan remainingCoupled ih tokens
      exact algebra.discard found value (ih tokens)
    · intro context scope assignment operator rhs rest body head remaining remainingPlan remainingCoupled site origin same sourceTyped rightTyped profile fuel prepared ih tokens
      cases tokens with
      | pair child _ =>
        exact algebra.assign head (.intro site origin same sourceTyped rightTyped profile fuel prepared) (ih child)
    · intro context scope assignment rest body head remaining remainingPlan remainingCoupled writable bare profile ih tokens
      cases tokens with
      | pair child unary => cases unary with
        | unary _ _ _ _ site origin same =>
          exact algebra.bitNot head (.intro writable bare profile site origin same) (ih child)
  exact result tokens

/-- This interpretation consumes the genuine unary row of an actual table. -/
theorem PreparedUnary.errors {context scope assignment} {head : CompatibleBitNotStatements.Head context scope assignment}
    {first : Nat} {table : SourceCoreAssignmentFaultSites.Table} {faults : FunctionCalls.FaultRep}
    (receipt : PreparedUnary true source (fun site root => table.reasonAt site root .bitNot) head)
    (typed : EmittedDiagnosticTokenPlan.UnaryTyped source)
    (issued : SourceCoreAssignmentFaultSites.prepare source first = .ok table)
    (included : ∀ reason token, EmittedDiagnosticTokenPlan.UnaryRep table reason token → faults reason token) : head.Errors faults := by
  cases receipt with
  | intro _ _ _ site origin same =>
    change faults (.invalidUnaryOperand .bitNot) head.invalid
    exact same.symm ▸ included _ _ (origin.prepared typed issued)
end Solcore.SourceSemantics.CoreLowering.GenericForHeader.Structural
