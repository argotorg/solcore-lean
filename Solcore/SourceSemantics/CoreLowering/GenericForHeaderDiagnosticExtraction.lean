import Solcore.SourceSemantics.CoreLowering.AssignmentDiagnosticOrigins
import Solcore.SourceSemantics.CoreLowering.GenericForHeaderTree

/-! A diagnostic factory for the existing header Tree. The residual predicate
retains missing/default, uninitialized and unary laws; operand laws are supplied
only by the chosen static origin factory. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.GenericForHeader
open Core Frontend SourceInference
open TypedLexicalWhile (absentRequest initializedRequest sequence)
structure DiagnosticExtraction (diagnosticPolicy : AssignmentDiagnosticPolicy) (layouts : SourceCoreAllocationLayouts.Prepared)
    (owner : SourceSpecialization.SpecializationKey) (active : TypeSystem.Substitution)
    (frame : SourceCoreCallableIndexedFrames.Layout) (globals : Nat)
    (onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error)
    (values : ValuesContext) (source : TypedSource)
    (certificates : SourceSemantics.Context → GenericExpressionMeaning.Certificate)
    (definitions : DataEnvironment) (administrative : Core.Context) (type : Ty)
    (continuation : SourceSemantics.Context → Scope → Expr → Prop)
    (context : SourceSemantics.Context) (scope : Scope) (items : List ForItemForm) (code : Expr) where
  tree : Tree layouts owner active frame globals onError values source certificates definitions administrative type continuation context scope items code
  diagnostics : SourceCoreRawMetadata.Registry → FunctionCalls.FaultRep → Prop
  materialize : ∀ registry faults, diagnostics registry faults → Tree.ErrorsFor diagnosticPolicy registry faults tree

namespace DiagnosticExtraction
variable {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
  {active : TypeSystem.Substitution} {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error}
  {values : ValuesContext} {source : TypedSource}
  {certificates : SourceSemantics.Context → GenericExpressionMeaning.Certificate} {definitions : DataEnvironment} {administrative : Core.Context}
  {type : Ty} {continuation : SourceSemantics.Context → Scope → Expr → Prop}

variable {diagnosticPolicy : AssignmentDiagnosticPolicy}

def nil {context scope code} (next : continuation context scope code) :
    DiagnosticExtraction diagnosticPolicy layouts owner active frame globals onError values source certificates definitions administrative type continuation
        context scope [] code := by
  refine ⟨.nil next, (fun registry faults => True), ?_⟩
  intro registry faults given
  exact @Tree.ErrorsFor.nil layouts owner active frame globals onError values source certificates definitions administrative type continuation diagnosticPolicy registry faults context scope code next

def uninitialized {context nextContext scope binder rest body payload}
      (monomorphic : binder.scheme.quantified = [])
      (extended : BinderExtends source.owner context binder nextContext)
      (ordinary : source.inputs.any (fun input => decide (input.id = binder.id)) = false)
      (projected : values.checked.catalog.project binder.scheme.body = .ok payload)
      (allocation : SourceCoreAllocationLayouts.Allocation layouts owner active (absentRequest source scope binder payload))
      (annotation : SourceCoreCallableIndexedAllocationFrames.Annotated frame globals
        (layouts.allocatorAt owner active onError) (absentRequest source scope binder payload))
      (same : annotation.original = allocation.expression)
      (remaining : DiagnosticExtraction diagnosticPolicy layouts owner active frame globals onError values source certificates definitions administrative type continuation
        nextContext ((binder.id, payload) :: scope) rest body) :
    DiagnosticExtraction diagnosticPolicy layouts owner active frame globals onError values source certificates definitions administrative type continuation
        context scope (.letDecl binder none :: rest) (.letE annotation.expression body) := by
  refine ⟨.uninitialized monomorphic extended ordinary projected allocation annotation same remaining.tree, (fun registry faults => remaining.diagnostics registry faults), ?_⟩
  intro registry faults given
  exact @Tree.ErrorsFor.uninitialized layouts owner active frame globals onError values source certificates definitions administrative type continuation diagnosticPolicy registry faults context nextContext scope binder rest body payload monomorphic extended ordinary projected allocation annotation same remaining.tree (remaining.materialize registry faults given)

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
      (remaining : DiagnosticExtraction diagnosticPolicy layouts owner active frame globals onError values source certificates definitions administrative type continuation
        nextContext ((binder.id, lowered.type) :: scope) rest body) :
    DiagnosticExtraction diagnosticPolicy layouts owner active frame globals onError values source certificates definitions administrative type continuation
        context scope (.letDecl binder (some initializer) :: rest) (sequence type lowered.expression annotation.expression body) := by
  refine ⟨.initialized monomorphic extended ordinary initializerFound sourceType initial allocation annotation same remaining.tree, (fun registry faults => remaining.diagnostics registry faults), ?_⟩
  intro registry faults given
  exact @Tree.ErrorsFor.initialized layouts owner active frame globals onError values source certificates definitions administrative type continuation diagnosticPolicy registry faults context nextContext scope binder initializer initializerNode lowered body rest monomorphic extended ordinary initializerFound sourceType initial allocation annotation same remaining.tree (remaining.materialize registry faults given)

def discard {context scope expression expressionNode rest lowered body}
      (found : source.lookupExpression? expression = some expressionNode)
      (value : certificates context scope expression lowered)
      (remaining : DiagnosticExtraction diagnosticPolicy layouts owner active frame globals onError values source certificates definitions administrative type continuation
        context scope rest body) :
    DiagnosticExtraction diagnosticPolicy layouts owner active frame globals onError values source certificates definitions administrative type continuation
        context scope (.expression expression :: rest) (LocalSequence.discard (LocalLoop.controlType type) lowered.expression body) := by
  refine ⟨.discard found value remaining.tree, (fun registry faults => remaining.diagnostics registry faults), ?_⟩
  intro registry faults given
  exact @Tree.ErrorsFor.discard layouts owner active frame globals onError values source certificates definitions administrative type continuation diagnosticPolicy registry faults context scope expression expressionNode rest lowered body found value remaining.tree (remaining.materialize registry faults given)

def assign {context scope assignment operator rhs rest body}
      (head : GenericAssignmentStatements.Head values source context (certificates context) scope administrative definitions assignment operator rhs)
      (headDiagnostics : SourceCoreRawMetadata.Registry → FunctionCalls.FaultRep → Prop)
    (headErrors : ∀ registry faults, headDiagnostics registry faults → head.ErrorsFor diagnosticPolicy registry faults)
    (remaining : DiagnosticExtraction diagnosticPolicy layouts owner active frame globals onError values source certificates definitions administrative type continuation
        context scope rest body) :
    DiagnosticExtraction diagnosticPolicy layouts owner active frame globals onError values source certificates definitions administrative type continuation
        context scope (.assignValue assignment operator rhs :: rest) (head.emit body (LocalLoop.controlType type)) := by
  refine ⟨.assign head remaining.tree, (fun registry faults => remaining.diagnostics registry faults ∧ headDiagnostics registry faults), ?_⟩
  intro registry faults given
  obtain ⟨remainingGiven, headGiven⟩ := given
  exact @Tree.ErrorsFor.assign layouts owner active frame globals onError values source certificates definitions administrative type continuation diagnosticPolicy registry faults context scope assignment operator rhs rest body head remaining.tree (remaining.materialize registry faults remainingGiven) (headErrors registry faults headGiven)

def bitNot {context scope assignment rest body}
      (head : CompatibleBitNotStatements.Head context scope assignment)
      (remaining : DiagnosticExtraction diagnosticPolicy layouts owner active frame globals onError values source certificates definitions administrative type continuation
        context scope rest body) :
    DiagnosticExtraction diagnosticPolicy layouts owner active frame globals onError values source certificates definitions administrative type continuation
        context scope (.assignBitNot assignment :: rest) (head.emit body (LocalLoop.controlType type)) := by
  refine ⟨.bitNot head remaining.tree, (fun registry faults => remaining.diagnostics registry faults ∧ head.Errors faults), ?_⟩
  intro registry faults given
  obtain ⟨remainingGiven, headGiven⟩ := given
  exact @Tree.ErrorsFor.bitNot layouts owner active frame globals onError values source certificates definitions administrative type continuation diagnosticPolicy registry faults context scope assignment rest body head remaining.tree (remaining.materialize registry faults remainingGiven) headGiven

end DiagnosticExtraction
end Solcore.SourceSemantics.CoreLowering.GenericForHeader
