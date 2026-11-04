import Solcore.SourceSemantics.CoreLowering.Internal.Statements.GenericForHeaderTrees
import Solcore.SourceSemantics.CoreLowering.Internal.Diagnostics.EmittedPlans

/-!
# Emitted diagnostics of for headers

Extraction of diagnostics from emitted `for` headers, with their tokens and coupling.
-/

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.EmittedForHeaderDiagnosticExtraction
/-! The original extraction constructors retain their actual diagnostic plans.
Only diagnostic equations are added; Trees and materialization are unchanged. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.GenericForHeader
open Core Frontend SourceInference
open EmittedDiagnosticPlan
open TypedLexicalWhile (absentRequest initializedRequest sequence)
variable {tracked : Bool} {diagnosticPolicy : AssignmentDiagnosticPolicy}
  {invalidOperand : SourceCoreElaboration.ErrorSite → Resolved.LocalId → Syntax.ValueAssignOp → Word}
abbrev ProducedDiagnosticExtraction (diagnosticPolicy : AssignmentDiagnosticPolicy) (layouts : SourceCoreAllocationLayouts.Prepared)
    (owner : SourceSpecialization.SpecializationKey) (active : TypeSystem.Substitution)
    (frame : SourceCoreCallableIndexedFrames.Layout) (globals : Nat)
    (onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error)
    (values : ValuesContext) (source : TypedSource)
    (factory : AssignmentDiagnosticOrigins.Factory tracked diagnosticPolicy source invalidOperand)
    (certificates : SourceSemantics.Context → GenericExpressionMeaning.Certificate)
    (definitions : DataEnvironment) (administrative : Core.Context) (type : Ty)
    (continuation : SourceSemantics.Context → Scope → Expr → Prop)
    (context : SourceSemantics.Context) (scope : Scope) (items : List ForItemForm) (code : Expr) :=
  EmittedDiagnosticPlan.Produced factory (DiagnosticExtraction diagnosticPolicy layouts owner active frame globals onError values source certificates definitions administrative type continuation context scope items code) (fun receipt => receipt.diagnostics)
namespace ProducedDiagnosticExtraction
variable {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
  {active : TypeSystem.Substitution} {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error}
  {values : ValuesContext} {source : TypedSource}
  {certificates : SourceSemantics.Context → GenericExpressionMeaning.Certificate} {definitions : DataEnvironment} {administrative : Core.Context}
  {type : Ty} {continuation : SourceSemantics.Context → Scope → Expr → Prop}



variable {tracked : Bool} {factory : AssignmentDiagnosticOrigins.Factory tracked diagnosticPolicy source invalidOperand}
def nil {context scope code} (next : continuation context scope code) :
    ProducedDiagnosticExtraction diagnosticPolicy layouts owner active frame globals onError values source factory certificates definitions administrative type continuation
        context scope [] code := by
  refine ⟨DiagnosticExtraction.nil (diagnosticPolicy := diagnosticPolicy) next, .pure, ?_⟩
  intro registry faults
  rfl

def uninitialized {context nextContext scope binder rest body payload}
      (monomorphic : binder.scheme.quantified = [])
      (extended : BinderExtends source.owner context binder nextContext)
      (ordinary : source.inputs.any (fun input => decide (input.id = binder.id)) = false)
      (projected : values.checked.catalog.project binder.scheme.body = .ok payload)
      (allocation : SourceCoreAllocationLayouts.Allocation layouts owner active (absentRequest source scope binder payload))
      (annotation : SourceCoreCallableIndexedAllocationFrames.Annotated frame globals
        (layouts.allocatorAt owner active onError) (absentRequest source scope binder payload))
      (same : annotation.original = allocation.expression)
      (remaining : ProducedDiagnosticExtraction diagnosticPolicy layouts owner active frame globals onError values source factory certificates definitions administrative type continuation
        nextContext ((binder.id, payload) :: scope) rest body) :
    ProducedDiagnosticExtraction diagnosticPolicy layouts owner active frame globals onError values source factory certificates definitions administrative type continuation
        context scope (.letDecl binder none :: rest) (.letE annotation.expression body) := by
  refine ⟨DiagnosticExtraction.uninitialized (diagnosticPolicy := diagnosticPolicy) monomorphic extended ordinary projected allocation annotation same remaining.original, remaining.plan, ?_⟩
  intro registry faults
  dsimp only [DiagnosticExtraction.uninitialized, EmittedDiagnosticPlan.Plan.requirements]
  rw [remaining.equation registry faults]

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
      (remaining : ProducedDiagnosticExtraction diagnosticPolicy layouts owner active frame globals onError values source factory certificates definitions administrative type continuation
        nextContext ((binder.id, lowered.type) :: scope) rest body) :
    ProducedDiagnosticExtraction diagnosticPolicy layouts owner active frame globals onError values source factory certificates definitions administrative type continuation
        context scope (.letDecl binder (some initializer) :: rest) (sequence type lowered.expression annotation.expression body) := by
  refine ⟨DiagnosticExtraction.initialized (diagnosticPolicy := diagnosticPolicy) monomorphic extended ordinary initializerFound sourceType initial allocation annotation same remaining.original, remaining.plan, ?_⟩
  intro registry faults
  dsimp only [DiagnosticExtraction.initialized, EmittedDiagnosticPlan.Plan.requirements]
  rw [remaining.equation registry faults]

def discard {context scope expression expressionNode rest lowered body}
      (found : source.lookupExpression? expression = some expressionNode)
      (value : certificates context scope expression lowered)
      (remaining : ProducedDiagnosticExtraction diagnosticPolicy layouts owner active frame globals onError values source factory certificates definitions administrative type continuation
        context scope rest body) :
    ProducedDiagnosticExtraction diagnosticPolicy layouts owner active frame globals onError values source factory certificates definitions administrative type continuation
        context scope (.expression expression :: rest) (LocalSequence.discard (LocalLoop.controlType type) lowered.expression body) := by
  refine ⟨DiagnosticExtraction.discard (diagnosticPolicy := diagnosticPolicy) found value remaining.original, remaining.plan, ?_⟩
  intro registry faults
  dsimp only [DiagnosticExtraction.discard, EmittedDiagnosticPlan.Plan.requirements]
  rw [remaining.equation registry faults]

def assign {context scope assignment operator rhs rest body}
      (head : GenericAssignmentStatements.Head values source context (certificates context) scope administrative definitions assignment operator rhs)
      (site : SourceCoreElaboration.ErrorSite)
    (origin : AssignmentDiagnosticOrigins.OccursFor tracked source site assignment operator rhs)
    (same : head.invalid = invalidOperand site assignment.target.root operator)
    (sourceTyped : ∀ binder, SourceCoreDataPlaces.rootBinder source assignment.target.root = .ok binder →
      SourceProjectionsHaveType source context binder.scheme.body assignment.target.projections assignment.target.type)
    (rightTyped : ExpressionHasType source context rhs assignment.target.type)
    (profile : operator = .equal ∨ SourceCoreRawMetadata.runtimeType assignment.target.type = .word ∨
      SourceCoreRawMetadata.runtimeType assignment.target.type = .integer ∧ operator.wordOnly = false)
    (remaining : ProducedDiagnosticExtraction diagnosticPolicy layouts owner active frame globals onError values source factory certificates definitions administrative type continuation
        context scope rest body) :
    ProducedDiagnosticExtraction diagnosticPolicy layouts owner active frame globals onError values source factory certificates definitions administrative type continuation
        context scope (.assignValue assignment operator rhs :: rest) (head.emit body (LocalLoop.controlType type)) := by
  refine ⟨DiagnosticExtraction.assign (diagnosticPolicy := diagnosticPolicy) head (factory.residual head) (factory.materialize head site origin same) remaining.original, .pair remaining.plan (.assignment head site origin same sourceTyped rightTyped profile), ?_⟩
  intro registry faults
  dsimp only [DiagnosticExtraction.assign, EmittedDiagnosticPlan.Plan.requirements]
  rw [remaining.equation registry faults]

def bitNot {context scope assignment rest body}
      (head : CompatibleBitNotStatements.Head context scope assignment)
      (writable : ∀ binder, SourceCoreDataPlaces.rootBinder source assignment.target.root = .ok binder →
      WritableLocal context assignment.target.root binder.scheme.body)
    (bare : assignment.target.projections = [])
    (profile : SourceCoreRawMetadata.runtimeType assignment.target.type = .word ∨
      SourceCoreRawMetadata.runtimeType assignment.target.type = .integer)
    (remaining : ProducedDiagnosticExtraction diagnosticPolicy layouts owner active frame globals onError values source factory certificates definitions administrative type continuation
        context scope rest body) :
    ProducedDiagnosticExtraction diagnosticPolicy layouts owner active frame globals onError values source factory certificates definitions administrative type continuation
        context scope (.assignBitNot assignment :: rest) (head.emit body (LocalLoop.controlType type)) := by
  refine ⟨DiagnosticExtraction.bitNot (diagnosticPolicy := diagnosticPolicy) head remaining.original, .pair remaining.plan (.unary head writable bare profile), ?_⟩
  intro registry faults
  dsimp only [DiagnosticExtraction.bitNot, EmittedDiagnosticPlan.Plan.requirements]
  rw [remaining.equation registry faults]
end ProducedDiagnosticExtraction
end Solcore.SourceSemantics.CoreLowering.GenericForHeader
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.EmittedForHeaderTokenExtraction
/-! Finite constructor adapters retain the original complete extraction and
its plan while carrying authentic unary token sites to that same witness. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.GenericForHeader
open Core Frontend SourceInference
open EmittedDiagnosticPlan EmittedDiagnosticTokenPlan
open TypedLexicalWhile (absentRequest initializedRequest sequence)
variable {tracked : Bool} {diagnosticPolicy : AssignmentDiagnosticPolicy}
  {invalidOperand : SourceCoreElaboration.ErrorSite → Resolved.LocalId → Syntax.ValueAssignOp → Word}
abbrev TokenDiagnosticExtraction (diagnosticPolicy : AssignmentDiagnosticPolicy) (layouts : SourceCoreAllocationLayouts.Prepared)
    (owner : SourceSpecialization.SpecializationKey) (active : TypeSystem.Substitution)
    (frame : SourceCoreCallableIndexedFrames.Layout) (globals : Nat)
    (onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error)
    (values : ValuesContext) (source : TypedSource)
    (factory : AssignmentDiagnosticOrigins.Factory tracked diagnosticPolicy source invalidOperand)
    (invalidUnary : SourceCoreElaboration.ErrorSite → Resolved.LocalId → Word)
    (certificates : SourceSemantics.Context → GenericExpressionMeaning.Certificate)
    (definitions : DataEnvironment) (administrative : Core.Context) (type : Ty)
    (continuation : SourceSemantics.Context → Scope → Expr → Prop)
    (context : SourceSemantics.Context) (scope : Scope) (items : List ForItemForm) (code : Expr) :=
  EmittedDiagnosticTokenPlan.Produced factory invalidUnary (DiagnosticExtraction diagnosticPolicy layouts owner active frame globals onError values source certificates definitions administrative type continuation context scope items code) (fun receipt => receipt.diagnostics)
namespace TokenDiagnosticExtraction
variable {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
  {active : TypeSystem.Substitution} {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error}
  {values : ValuesContext} {source : TypedSource}
  {certificates : SourceSemantics.Context → GenericExpressionMeaning.Certificate} {definitions : DataEnvironment} {administrative : Core.Context}
  {type : Ty} {continuation : SourceSemantics.Context → Scope → Expr → Prop}



variable {tracked : Bool} {invalidUnary : SourceCoreElaboration.ErrorSite → Resolved.LocalId → Word}
  {factory : AssignmentDiagnosticOrigins.Factory tracked diagnosticPolicy source invalidOperand}
def nil {context scope code} (next : continuation context scope code) :
    TokenDiagnosticExtraction diagnosticPolicy layouts owner active frame globals onError values source factory invalidUnary certificates definitions administrative type continuation
        context scope [] code := by
  exact ⟨ProducedDiagnosticExtraction.nil (factory := factory) next, .pure⟩

def uninitialized {context nextContext scope binder rest body payload}
      (monomorphic : binder.scheme.quantified = [])
      (extended : BinderExtends source.owner context binder nextContext)
      (ordinary : source.inputs.any (fun input => decide (input.id = binder.id)) = false)
      (projected : values.checked.catalog.project binder.scheme.body = .ok payload)
      (allocation : SourceCoreAllocationLayouts.Allocation layouts owner active (absentRequest source scope binder payload))
      (annotation : SourceCoreCallableIndexedAllocationFrames.Annotated frame globals
        (layouts.allocatorAt owner active onError) (absentRequest source scope binder payload))
      (same : annotation.original = allocation.expression)
      (remaining : TokenDiagnosticExtraction diagnosticPolicy layouts owner active frame globals onError values source factory invalidUnary certificates definitions administrative type continuation
        nextContext ((binder.id, payload) :: scope) rest body) :
    TokenDiagnosticExtraction diagnosticPolicy layouts owner active frame globals onError values source factory invalidUnary certificates definitions administrative type continuation
        context scope (.letDecl binder none :: rest) (.letE annotation.expression body) := by
  exact ⟨ProducedDiagnosticExtraction.uninitialized (factory := factory) monomorphic extended ordinary projected allocation annotation same remaining.toProduced, remaining.tokens⟩

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
      (remaining : TokenDiagnosticExtraction diagnosticPolicy layouts owner active frame globals onError values source factory invalidUnary certificates definitions administrative type continuation
        nextContext ((binder.id, lowered.type) :: scope) rest body) :
    TokenDiagnosticExtraction diagnosticPolicy layouts owner active frame globals onError values source factory invalidUnary certificates definitions administrative type continuation
        context scope (.letDecl binder (some initializer) :: rest) (sequence type lowered.expression annotation.expression body) := by
  exact ⟨ProducedDiagnosticExtraction.initialized (factory := factory) monomorphic extended ordinary initializerFound sourceType initial allocation annotation same remaining.toProduced, remaining.tokens⟩

def discard {context scope expression expressionNode rest lowered body}
      (found : source.lookupExpression? expression = some expressionNode)
      (value : certificates context scope expression lowered)
      (remaining : TokenDiagnosticExtraction diagnosticPolicy layouts owner active frame globals onError values source factory invalidUnary certificates definitions administrative type continuation
        context scope rest body) :
    TokenDiagnosticExtraction diagnosticPolicy layouts owner active frame globals onError values source factory invalidUnary certificates definitions administrative type continuation
        context scope (.expression expression :: rest) (LocalSequence.discard (LocalLoop.controlType type) lowered.expression body) := by
  exact ⟨ProducedDiagnosticExtraction.discard (factory := factory) found value remaining.toProduced, remaining.tokens⟩

def assign {context scope assignment operator rhs rest body}
      (head : GenericAssignmentStatements.Head values source context (certificates context) scope administrative definitions assignment operator rhs)
      (site : SourceCoreElaboration.ErrorSite)
    (origin : AssignmentDiagnosticOrigins.OccursFor tracked source site assignment operator rhs)
    (same : head.invalid = invalidOperand site assignment.target.root operator)
    (sourceTyped : ∀ binder, SourceCoreDataPlaces.rootBinder source assignment.target.root = .ok binder →
      SourceProjectionsHaveType source context binder.scheme.body assignment.target.projections assignment.target.type)
    (rightTyped : ExpressionHasType source context rhs assignment.target.type)
    (profile : operator = .equal ∨ SourceCoreRawMetadata.runtimeType assignment.target.type = .word ∨
      SourceCoreRawMetadata.runtimeType assignment.target.type = .integer ∧ operator.wordOnly = false)
    (remaining : TokenDiagnosticExtraction diagnosticPolicy layouts owner active frame globals onError values source factory invalidUnary certificates definitions administrative type continuation
        context scope rest body) :
    TokenDiagnosticExtraction diagnosticPolicy layouts owner active frame globals onError values source factory invalidUnary certificates definitions administrative type continuation
        context scope (.assignValue assignment operator rhs :: rest) (head.emit body (LocalLoop.controlType type)) := by
  exact ⟨ProducedDiagnosticExtraction.assign (factory := factory) head site origin same sourceTyped rightTyped profile remaining.toProduced, .pair remaining.tokens (.assignment head site origin same sourceTyped rightTyped profile)⟩

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
    (remaining : TokenDiagnosticExtraction diagnosticPolicy layouts owner active frame globals onError values source factory invalidUnary certificates definitions administrative type continuation
        context scope rest body) :
    TokenDiagnosticExtraction diagnosticPolicy layouts owner active frame globals onError values source factory invalidUnary certificates definitions administrative type continuation
        context scope (.assignBitNot assignment :: rest) (head.emit body (LocalLoop.controlType type)) := by
  exact ⟨ProducedDiagnosticExtraction.bitNot (factory := factory) head writable bare profile remaining.toProduced, .pair remaining.tokens (.unary head writable bare profile site origin same)⟩
end TokenDiagnosticExtraction
end Solcore.SourceSemantics.CoreLowering.GenericForHeader
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.EmittedForHeaderPreparedExtraction
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
      SourceCoreRawMetadata.runtimeType assignment.target.type = .integer ∧ operator.wordOnly = false)
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
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.EmittedForHeaderCoupling
/-! Joint static receipts bind the retained Tree and Plan to one selected head.
Consumers recurse this receipt, whose assignment constructor shares the full
head data and actual preparation with both indices. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.GenericForHeader
open Core Frontend SourceInference
open EmittedDiagnosticPlan
open TypedLexicalWhile (absentRequest initializedRequest sequence)
variable {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
  {active : TypeSystem.Substitution} {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error}
  {values : ValuesContext} {source : TypedSource}
  {certificates : SourceSemantics.Context → GenericExpressionMeaning.Certificate} {definitions : DataEnvironment} {administrative : Core.Context}
  {type : Ty} {continuation : SourceSemantics.Context → Scope → Expr → Prop}

variable {tracked : Bool} {diagnosticPolicy : AssignmentDiagnosticPolicy}
  {invalidOperand : SourceCoreElaboration.ErrorSite → Resolved.LocalId → Syntax.ValueAssignOp → Word}
inductive Coupled (factory : AssignmentDiagnosticOrigins.Factory tracked diagnosticPolicy source invalidOperand)
    (invalidProjection : SourceCoreElaboration.ErrorSite → Resolved.LocalId → Word)
    (missingDefault : SourceCoreElaboration.ErrorSite → Resolved.LocalId → TypeSystem.Ty → Word) :
    {context : SourceSemantics.Context} → {scope : Scope} → {items : List ForItemForm} → {code : Expr} →
    Tree layouts owner active frame globals onError values source certificates definitions administrative type continuation
      context scope items code → Plan factory → Prop where
  | nil {context scope code}
      {next : continuation context scope code}
      : Coupled factory invalidProjection missingDefault (.nil next) .pure
  | uninitialized {context nextContext scope binder rest body payload}
      {monomorphic : binder.scheme.quantified = []}
      {extended : BinderExtends source.owner context binder nextContext}
      {ordinary : source.inputs.any (fun input => decide (input.id = binder.id)) = false}
      {projected : values.checked.catalog.project binder.scheme.body = .ok payload}
      {allocation : SourceCoreAllocationLayouts.Allocation layouts owner active (absentRequest source scope binder payload)}
      {annotation : SourceCoreCallableIndexedAllocationFrames.Annotated frame globals
        (layouts.allocatorAt owner active onError) (absentRequest source scope binder payload)}
      {same : annotation.original = allocation.expression}
      {remaining : Tree layouts owner active frame globals onError values source certificates definitions administrative type continuation
        nextContext ((binder.id, payload) :: scope) rest body}
      {remainingPlan : Plan factory}
      (remainingCoupled : Coupled factory invalidProjection missingDefault remaining remainingPlan)
      : Coupled factory invalidProjection missingDefault (.uninitialized monomorphic extended ordinary projected allocation annotation same remaining) remainingPlan
  | initialized {context nextContext scope binder initializer initializerNode lowered body rest}
      {monomorphic : binder.scheme.quantified = []}
      {extended : BinderExtends source.owner context binder nextContext}
      {ordinary : source.inputs.any (fun input => decide (input.id = binder.id)) = false}
      {initializerFound : source.lookupExpression? initializer = some initializerNode}
      {sourceType : initializerNode.type = binder.scheme.body}
      {initial : certificates context scope initializer lowered}
      {allocation : SourceCoreAllocationLayouts.Allocation layouts owner active (initializedRequest source scope binder lowered.type)}
      {annotation : SourceCoreCallableIndexedAllocationFrames.Annotated frame globals
        (layouts.allocatorAt owner active onError) (initializedRequest source scope binder lowered.type)}
      {same : annotation.original = allocation.expression}
      {remaining : Tree layouts owner active frame globals onError values source certificates definitions administrative type continuation
        nextContext ((binder.id, lowered.type) :: scope) rest body}
      {remainingPlan : Plan factory}
      (remainingCoupled : Coupled factory invalidProjection missingDefault remaining remainingPlan)
      : Coupled factory invalidProjection missingDefault (.initialized monomorphic extended ordinary initializerFound sourceType initial allocation annotation same remaining) remainingPlan
  | discard {context scope expression expressionNode rest lowered body}
      {found : source.lookupExpression? expression = some expressionNode}
      {value : certificates context scope expression lowered}
      {remaining : Tree layouts owner active frame globals onError values source certificates definitions administrative type continuation
        context scope rest body}
      {remainingPlan : Plan factory}
      (remainingCoupled : Coupled factory invalidProjection missingDefault remaining remainingPlan)
      : Coupled factory invalidProjection missingDefault (.discard found value remaining) remainingPlan
  | assign {context scope assignment operator rhs rest body}
      {head : GenericAssignmentStatements.Head values source context (certificates context) scope administrative definitions assignment operator rhs}
      {remaining : Tree layouts owner active frame globals onError values source certificates definitions administrative type continuation
        context scope rest body}
      {remainingPlan : Plan factory}
      (remainingCoupled : Coupled factory invalidProjection missingDefault remaining remainingPlan)
      (site : SourceCoreElaboration.ErrorSite)
      (origin : AssignmentDiagnosticOrigins.OccursFor tracked source site assignment operator rhs)
      (sameToken : head.invalid = invalidOperand site assignment.target.root operator)
      (sourceTyped : ∀ binder, SourceCoreDataPlaces.rootBinder source assignment.target.root = .ok binder →
        SourceProjectionsHaveType source context binder.scheme.body assignment.target.projections assignment.target.type)
      (rightTyped : ExpressionHasType source context rhs assignment.target.type)
      (profile : operator = .equal ∨ SourceCoreRawMetadata.runtimeType assignment.target.type = .word ∨
        SourceCoreRawMetadata.runtimeType assignment.target.type = .integer ∧ operator.wordOnly = false)
      (fuel : Nat)
      (prepared : head.PreparedAt site fuel (invalidProjection site assignment.target.root) (missingDefault site assignment.target.root))
      : Coupled factory invalidProjection missingDefault (.assign head remaining) (.pair remainingPlan (.assignment head site origin sameToken sourceTyped rightTyped profile))
  | bitNot {context scope assignment rest body}
      {head : CompatibleBitNotStatements.Head context scope assignment}
      {remaining : Tree layouts owner active frame globals onError values source certificates definitions administrative type continuation
        context scope rest body}
      {remainingPlan : Plan factory}
      (remainingCoupled : Coupled factory invalidProjection missingDefault remaining remainingPlan)
      (writable : ∀ binder, SourceCoreDataPlaces.rootBinder source assignment.target.root = .ok binder →
        WritableLocal context assignment.target.root binder.scheme.body)
      (bare : assignment.target.projections = [])
      (profile : SourceCoreRawMetadata.runtimeType assignment.target.type = .word ∨
        SourceCoreRawMetadata.runtimeType assignment.target.type = .integer)
      : Coupled factory invalidProjection missingDefault (.bitNot head remaining) (.pair remainingPlan (.unary head writable bare profile))

end Solcore.SourceSemantics.CoreLowering.GenericForHeader
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.EmittedForHeaderCoupledExtraction
/-! Finite adapters retain the original extraction and actual preparation.
The joint receipt shares each chosen head with both Tree and Plan, and keeps
the corresponding receipt for every actual child. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.GenericForHeader
open Core Frontend SourceInference
open EmittedDiagnosticPlan EmittedDiagnosticTokenPlan
open TypedLexicalWhile (absentRequest initializedRequest sequence)
variable {tracked : Bool} {diagnosticPolicy : AssignmentDiagnosticPolicy}
  {invalidOperand : SourceCoreElaboration.ErrorSite → Resolved.LocalId → Syntax.ValueAssignOp → Word}
structure CoupledTokenDiagnosticExtraction (diagnosticPolicy : AssignmentDiagnosticPolicy) (layouts : SourceCoreAllocationLayouts.Prepared)
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
    (context : SourceSemantics.Context) (scope : Scope) (items : List ForItemForm) (code : Expr) where
  original : EmittedDiagnosticPreparedPlan.Produced factory invalidUnary invalidProjection missingDefault (DiagnosticExtraction diagnosticPolicy layouts owner active frame globals onError values source certificates definitions administrative type continuation context scope items code) (fun receipt => receipt.diagnostics)
  coupled : Coupled factory invalidProjection missingDefault original.original.original.tree original.original.plan
namespace CoupledTokenDiagnosticExtraction
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
    CoupledTokenDiagnosticExtraction diagnosticPolicy layouts owner active frame globals onError values source factory invalidUnary invalidProjection missingDefault certificates definitions administrative type continuation
        context scope [] code := by
  exact ⟨PreparedTokenDiagnosticExtraction.nil (factory := factory) next, .nil (next := next)⟩

def uninitialized {context nextContext scope binder rest body payload}
      (monomorphic : binder.scheme.quantified = [])
      (extended : BinderExtends source.owner context binder nextContext)
      (ordinary : source.inputs.any (fun input => decide (input.id = binder.id)) = false)
      (projected : values.checked.catalog.project binder.scheme.body = .ok payload)
      (allocation : SourceCoreAllocationLayouts.Allocation layouts owner active (absentRequest source scope binder payload))
      (annotation : SourceCoreCallableIndexedAllocationFrames.Annotated frame globals
        (layouts.allocatorAt owner active onError) (absentRequest source scope binder payload))
      (same : annotation.original = allocation.expression)
      (remaining : CoupledTokenDiagnosticExtraction diagnosticPolicy layouts owner active frame globals onError values source factory invalidUnary invalidProjection missingDefault certificates definitions administrative type continuation
        nextContext ((binder.id, payload) :: scope) rest body) :
    CoupledTokenDiagnosticExtraction diagnosticPolicy layouts owner active frame globals onError values source factory invalidUnary invalidProjection missingDefault certificates definitions administrative type continuation
        context scope (.letDecl binder none :: rest) (.letE annotation.expression body) := by
  exact ⟨PreparedTokenDiagnosticExtraction.uninitialized (factory := factory) monomorphic extended ordinary projected allocation annotation same remaining.original, .uninitialized (monomorphic := monomorphic) (extended := extended) (ordinary := ordinary) (projected := projected) (allocation := allocation) (annotation := annotation) (same := same) remaining.coupled⟩

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
      (remaining : CoupledTokenDiagnosticExtraction diagnosticPolicy layouts owner active frame globals onError values source factory invalidUnary invalidProjection missingDefault certificates definitions administrative type continuation
        nextContext ((binder.id, lowered.type) :: scope) rest body) :
    CoupledTokenDiagnosticExtraction diagnosticPolicy layouts owner active frame globals onError values source factory invalidUnary invalidProjection missingDefault certificates definitions administrative type continuation
        context scope (.letDecl binder (some initializer) :: rest) (sequence type lowered.expression annotation.expression body) := by
  exact ⟨PreparedTokenDiagnosticExtraction.initialized (factory := factory) monomorphic extended ordinary initializerFound sourceType initial allocation annotation same remaining.original, .initialized (monomorphic := monomorphic) (extended := extended) (ordinary := ordinary) (initializerFound := initializerFound) (sourceType := sourceType) (initial := initial) (allocation := allocation) (annotation := annotation) (same := same) remaining.coupled⟩

def discard {context scope expression expressionNode rest lowered body}
      (found : source.lookupExpression? expression = some expressionNode)
      (value : certificates context scope expression lowered)
      (remaining : CoupledTokenDiagnosticExtraction diagnosticPolicy layouts owner active frame globals onError values source factory invalidUnary invalidProjection missingDefault certificates definitions administrative type continuation
        context scope rest body) :
    CoupledTokenDiagnosticExtraction diagnosticPolicy layouts owner active frame globals onError values source factory invalidUnary invalidProjection missingDefault certificates definitions administrative type continuation
        context scope (.expression expression :: rest) (LocalSequence.discard (LocalLoop.controlType type) lowered.expression body) := by
  exact ⟨PreparedTokenDiagnosticExtraction.discard (factory := factory) found value remaining.original, .discard (found := found) (value := value) remaining.coupled⟩

def assign {context scope assignment operator rhs rest body}
      (head : GenericAssignmentStatements.Head values source context (certificates context) scope administrative definitions assignment operator rhs)
      (site : SourceCoreElaboration.ErrorSite)
    (origin : AssignmentDiagnosticOrigins.OccursFor tracked source site assignment operator rhs)
    (same : head.invalid = invalidOperand site assignment.target.root operator)
    (sourceTyped : ∀ binder, SourceCoreDataPlaces.rootBinder source assignment.target.root = .ok binder →
      SourceProjectionsHaveType source context binder.scheme.body assignment.target.projections assignment.target.type)
    (rightTyped : ExpressionHasType source context rhs assignment.target.type)
    (profile : operator = .equal ∨ SourceCoreRawMetadata.runtimeType assignment.target.type = .word ∨
      SourceCoreRawMetadata.runtimeType assignment.target.type = .integer ∧ operator.wordOnly = false)
    (headFuel : Nat)
    (prepared : head.PreparedAt site headFuel (invalidProjection site assignment.target.root)
      (missingDefault site assignment.target.root))
    (remaining : CoupledTokenDiagnosticExtraction diagnosticPolicy layouts owner active frame globals onError values source factory invalidUnary invalidProjection missingDefault certificates definitions administrative type continuation
        context scope rest body) :
    CoupledTokenDiagnosticExtraction diagnosticPolicy layouts owner active frame globals onError values source factory invalidUnary invalidProjection missingDefault certificates definitions administrative type continuation
        context scope (.assignValue assignment operator rhs :: rest) (head.emit body (LocalLoop.controlType type)) := by
  exact ⟨PreparedTokenDiagnosticExtraction.assign (factory := factory) head site origin same sourceTyped rightTyped profile headFuel prepared remaining.original, .assign remaining.coupled site origin same sourceTyped rightTyped profile headFuel prepared⟩

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
    (remaining : CoupledTokenDiagnosticExtraction diagnosticPolicy layouts owner active frame globals onError values source factory invalidUnary invalidProjection missingDefault certificates definitions administrative type continuation
        context scope rest body) :
    CoupledTokenDiagnosticExtraction diagnosticPolicy layouts owner active frame globals onError values source factory invalidUnary invalidProjection missingDefault certificates definitions administrative type continuation
        context scope (.assignBitNot assignment :: rest) (head.emit body (LocalLoop.controlType type)) := by
  exact ⟨PreparedTokenDiagnosticExtraction.bitNot (factory := factory) head writable bare profile site origin same remaining.original, .bitNot remaining.coupled writable bare profile⟩

end CoupledTokenDiagnosticExtraction
end Solcore.SourceSemantics.CoreLowering.GenericForHeader
end
