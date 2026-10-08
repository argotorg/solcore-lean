import Solcore.SourceSemantics.CoreLowering.EmittedForHeaderTokenExtraction
import Solcore.SourceSemantics.CoreLowering.EmittedDiagnosticPreparedPlan

/-! Finite Header adapters retain the exact existing token extraction and its
chosen assignment preparation. The static compiler fold builds these sidecars
beside the original plan without selecting another head. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.GenericForHeader
open Core Frontend SourceInference
open EmittedDiagnosticPlan EmittedDiagnosticTokenPlan
open TypedLexicalWhile (absentRequest initializedRequest sequence)
variable {tracked : Bool} {diagnosticPolicy : AssignmentDiagnosticPolicy}
  {invalidOperand : SourceCoreElaboration.ErrorSite → Resolved.LocalId → Syntax.ValueAssignOp → Word}
abbrev PreparedTokenDiagnosticExtraction (diagnosticPolicy : AssignmentDiagnosticPolicy) (layouts : SourceCoreAllocationLayouts.Prepared)
    (owner : SourceSpecialization.SpecializationKey) (active : TypeSystem.Substitution)
    (frame : SourceCoreCallableIndexedFrames.Layout) (globals : Nat)
    (onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error)
    (values : ValuesContext) (source : TypedSource)
    (factory : AssignmentDiagnosticOrigins.Factory tracked diagnosticPolicy source invalidOperand)
    (invalidUnary : SourceCoreElaboration.ErrorSite → Resolved.LocalId → Word)
    (invalidProjection : SourceCoreElaboration.ErrorSite → Resolved.LocalId → Word)
    (missingDefault : SourceCoreElaboration.ErrorSite → Resolved.LocalId → TypeSystem.Ty → Word)
    (certificates : SourceSemantics.Context → GenericExpressionMeaning.Certificate)
    (definitions : DataEnvironment) (administrative : Core.Context) (type : Ty)
    (continuation : SourceSemantics.Context → Scope → Expr → Prop)
    (context : SourceSemantics.Context) (scope : Scope) (items : List ForItemForm) (code : Expr) :=
  EmittedDiagnosticPreparedPlan.Produced factory invalidUnary invalidProjection missingDefault (DiagnosticExtraction diagnosticPolicy layouts owner active frame globals onError values source certificates definitions administrative type continuation context scope items code) (fun receipt => receipt.diagnostics)
namespace PreparedTokenDiagnosticExtraction
variable {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
  {active : TypeSystem.Substitution} {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error}
  {values : ValuesContext} {source : TypedSource}
  {certificates : SourceSemantics.Context → GenericExpressionMeaning.Certificate} {definitions : DataEnvironment} {administrative : Core.Context}
  {type : Ty} {continuation : SourceSemantics.Context → Scope → Expr → Prop}



variable {tracked : Bool} {invalidUnary : SourceCoreElaboration.ErrorSite → Resolved.LocalId → Word}
  {invalidProjection : SourceCoreElaboration.ErrorSite → Resolved.LocalId → Word}
  {missingDefault : SourceCoreElaboration.ErrorSite → Resolved.LocalId → TypeSystem.Ty → Word}
  {factory : AssignmentDiagnosticOrigins.Factory tracked diagnosticPolicy source invalidOperand}
def nil {context scope code} (next : continuation context scope code) :
    PreparedTokenDiagnosticExtraction diagnosticPolicy layouts owner active frame globals onError values source factory invalidUnary invalidProjection missingDefault certificates definitions administrative type continuation
        context scope [] code := by
  exact ⟨TokenDiagnosticExtraction.nil (factory := factory) next, True.intro⟩

def uninitialized {context nextContext scope binder rest body payload}
      (monomorphic : binder.scheme.quantified = [])
      (extended : BinderExtends source.owner context binder nextContext)
      (ordinary : source.inputs.any (fun input => decide (input.id = binder.id)) = false)
      (projected : values.checked.catalog.project binder.scheme.body = .ok payload)
      (allocation : SourceCoreAllocationLayouts.Allocation layouts owner active (absentRequest source scope binder payload))
      (annotation : SourceCoreCallableIndexedAllocationFrames.Annotated frame globals
        (layouts.allocatorAt owner active onError) (absentRequest source scope binder payload))
      (same : annotation.original = allocation.expression)
      (remaining : PreparedTokenDiagnosticExtraction diagnosticPolicy layouts owner active frame globals onError values source factory invalidUnary invalidProjection missingDefault certificates definitions administrative type continuation
        nextContext ((binder.id, payload) :: scope) rest body) :
    PreparedTokenDiagnosticExtraction diagnosticPolicy layouts owner active frame globals onError values source factory invalidUnary invalidProjection missingDefault certificates definitions administrative type continuation
        context scope (.letDecl binder none :: rest) (.letE annotation.expression body) := by
  exact ⟨TokenDiagnosticExtraction.uninitialized (factory := factory) monomorphic extended ordinary projected allocation annotation same remaining.original, remaining.prepared⟩

def initialized {context nextContext scope binder initializer initializerNode lowered body rest}
      (monomorphic : binder.scheme.quantified = [])
      (extended : BinderExtends source.owner context binder nextContext)
      (ordinary : source.inputs.any (fun input => decide (input.id = binder.id)) = false)
      (initializerFound : source.lookupExpression? initializer = some initializerNode)
      (sourceType : initializerNode.type = binder.scheme.body)
      (initial : certificates context scope initializer lowered)
      (allocation : SourceCoreAllocationLayouts.Allocation layouts owner active (initializedRequest source scope binder lowered.type))
      (annotation : SourceCoreCallableIndexedAllocationFrames.Annotated frame globals
        (layouts.allocatorAt owner active onError) (initializedRequest source scope binder lowered.type))
      (same : annotation.original = allocation.expression)
      (remaining : PreparedTokenDiagnosticExtraction diagnosticPolicy layouts owner active frame globals onError values source factory invalidUnary invalidProjection missingDefault certificates definitions administrative type continuation
        nextContext ((binder.id, lowered.type) :: scope) rest body) :
    PreparedTokenDiagnosticExtraction diagnosticPolicy layouts owner active frame globals onError values source factory invalidUnary invalidProjection missingDefault certificates definitions administrative type continuation
        context scope (.letDecl binder (some initializer) :: rest) (sequence type lowered.expression annotation.expression body) := by
  exact ⟨TokenDiagnosticExtraction.initialized (factory := factory) monomorphic extended ordinary initializerFound sourceType initial allocation annotation same remaining.original, remaining.prepared⟩

def discard {context scope expression expressionNode rest lowered body}
      (found : source.lookupExpression? expression = some expressionNode)
      (value : certificates context scope expression lowered)
      (remaining : PreparedTokenDiagnosticExtraction diagnosticPolicy layouts owner active frame globals onError values source factory invalidUnary invalidProjection missingDefault certificates definitions administrative type continuation
        context scope rest body) :
    PreparedTokenDiagnosticExtraction diagnosticPolicy layouts owner active frame globals onError values source factory invalidUnary invalidProjection missingDefault certificates definitions administrative type continuation
        context scope (.expression expression :: rest) (LocalSequence.discard (LocalLoop.controlType type) lowered.expression body) := by
  exact ⟨TokenDiagnosticExtraction.discard (factory := factory) found value remaining.original, remaining.prepared⟩

def assign {context scope assignment operator rhs rest body}
      (head : GenericAssignmentStatements.Head values source context (certificates context) scope administrative definitions assignment operator rhs)
      (site : SourceCoreElaboration.ErrorSite)
    (origin : AssignmentDiagnosticOrigins.OccursFor tracked source site assignment operator rhs)
    (same : head.invalid = invalidOperand site assignment.target.root operator)
    (sourceTyped : ∀ binder, SourceCoreDataPlaces.rootBinder source assignment.target.root = .ok binder →
      SourceProjectionsHaveType source context binder.scheme.body assignment.target.projections assignment.target.type)
    (rightTyped : ExpressionHasType source context rhs assignment.target.type)
    (profile : operator = .equal ∨ SourceCoreRawMetadata.runtimeType assignment.target.type = .word ∨
      SourceCoreRawMetadata.runtimeType assignment.target.type = .integer)
    (headFuel : Nat)
    (prepared : head.PreparedAt site headFuel (invalidProjection site assignment.target.root)
      (missingDefault site assignment.target.root))
    (remaining : PreparedTokenDiagnosticExtraction diagnosticPolicy layouts owner active frame globals onError values source factory invalidUnary invalidProjection missingDefault certificates definitions administrative type continuation
        context scope rest body) :
    PreparedTokenDiagnosticExtraction diagnosticPolicy layouts owner active frame globals onError values source factory invalidUnary invalidProjection missingDefault certificates definitions administrative type continuation
        context scope (.assignValue assignment operator rhs :: rest) (head.emit body (LocalLoop.controlType type)) := by
  exact ⟨TokenDiagnosticExtraction.assign (factory := factory) head site origin same sourceTyped rightTyped profile remaining.original, remaining.prepared, ⟨headFuel, prepared⟩⟩

def bitNot {context scope assignment rest body}
      (head : CompatibleBitNotStatements.Head context scope assignment)
      (writable : ∀ binder, SourceCoreDataPlaces.rootBinder source assignment.target.root = .ok binder →
      WritableLocal context assignment.target.root binder.scheme.body)
    (bare : assignment.target.projections = [])
    (profile : SourceCoreRawMetadata.runtimeType assignment.target.type = .word ∨
      SourceCoreRawMetadata.runtimeType assignment.target.type = .integer)
    (site : SourceCoreElaboration.ErrorSite)
    (origin : EmittedDiagnosticTokenPlan.UnaryOccursFor tracked source site assignment)
    (same : head.invalid = invalidUnary site assignment.target.root)
    (remaining : PreparedTokenDiagnosticExtraction diagnosticPolicy layouts owner active frame globals onError values source factory invalidUnary invalidProjection missingDefault certificates definitions administrative type continuation
        context scope rest body) :
    PreparedTokenDiagnosticExtraction diagnosticPolicy layouts owner active frame globals onError values source factory invalidUnary invalidProjection missingDefault certificates definitions administrative type continuation
        context scope (.assignBitNot assignment :: rest) (head.emit body (LocalLoop.controlType type)) := by
  exact ⟨TokenDiagnosticExtraction.bitNot (factory := factory) head writable bare profile site origin same remaining.original, remaining.prepared, True.intro⟩
end PreparedTokenDiagnosticExtraction
end Solcore.SourceSemantics.CoreLowering.GenericForHeader
