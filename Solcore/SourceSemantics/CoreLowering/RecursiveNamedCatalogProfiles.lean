import Solcore.SourceSemantics.CoreLowering.RecursiveNamedCatalog
import Solcore.SourceSemantics.CoreLowering.NamedCallExpressionMeaning
import Solcore.SourceSemantics.CoreLowering.CompatibleExpressionCallTree
import Solcore.SourceSemantics.CoreLowering.GenericImperativeForTree
import Solcore.SourceSemantics.CoreLowering.GenericImperativeForControlShape

/-! Static expression heads can refer to the finite header inventory, including
self and mutual targets. The same existing imperative grammar supplies body
profiles. These records contain neither body execution nor runtime meaning. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.RecursiveNamedCatalog
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableAncestryPairedLookup
abbrev Scope := SourceCoreLocalCell.Scope
variable {checked : Checked} {base : Base checked}
  {prepared : SourceCoreCallableIndexedAncestry.Prepared base} {values : ValuesContext}
  {ambient : AmbientDefinitions values.checked.catalog.definitions} {program : Program}

inductive Head (bodies : Inventory prepared values ambient.definitions program)
    (compilation : SourceCoreFunctions.Context) (source : TypedSource)
    (context : SourceSemantics.Context) (children : GenericExpressionMeaning.Certificate) (scope : Scope) :
    ExpressionId → SourceCoreBasic.LoweredExpr → Prop where
  | named {id callee arguments body node calleeNode name codes expression}
      (member : body ∈ bodies)
      (metadata : CompatibleExpressionPrimitives.Metadata values.checked source id node body.output)
      (sourceType : node.type = body.function.resultType)
      (form : node.form = .call callee arguments (.declaration body.instantiation))
      (calleeFound : source.lookupExpression? callee = some calleeNode)
      (calleeForm : calleeNode.form = .reference name (.declaration body.instantiation))
      (calleeRequirements : calleeNode.requirements = []) (calleeCoercions : calleeNode.coercions = [])
      (valid : SourceSemantics.DeclarationInstantiation.Valid context body.instantiation)
      (predicates : body.instantiation.predicates = []) (evidence : body.function.evidence = [])
      (arity : body.function.parameters.length = arguments.length)
      (emission : NamedCalls.Arguments.Emission compilation source scope id callee arguments
        body.instantiation body.named.signature codes ⟨body.output, expression⟩)
      (selectedSlot : emission.index = body.slot)
      (sequence : DataExpressionSequence.Tree source children scope arguments
        (body.bindings.map (fun binding => binding.1.scheme.body)) codes)
      (nativeTypes : codes.map (·.type) = body.bindings.map Prod.snd) :
      Head bodies compilation source context children scope id ⟨body.output, expression⟩

abbrev Expressions (headers : Inventory prepared values ambient.definitions program)
    (compilation : SourceCoreFunctions.Context) (fuel : Nat) (source : TypedSource)
    (context : SourceSemantics.Context) (solved : List SolvedRequirement) (reasonAt : ExpressionId → Word) :=
  CompatibleExpressionCalls.Tree (Head headers compilation source context) fuel values source context solved reasonAt

/-- The actual body pass and its independent static tree are separate from the
header inventory. Call children therefore refer to headers, rather than to
recursive body-profile records. -/
structure Profile (headers : Inventory prepared values ambient.definitions program)
    (header : Header prepared values ambient.definitions program)
    (compilation : SourceCoreFunctions.Context) (expressionFuel : Nat)
    (expressionSyntax : ExpressionId → Prop) (administrative : Core.Context)
    (registry : SourceCoreRawMetadata.Registry) (faults : FunctionCalls.FaultRep) where private mk ::
  accepted : SourceCoreLoops.lowerStatementsWithPolicy header.policy header.fuel header.function.source
    (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2))) header.function.body
    header.output header.reasonAt header.fellThrough header.escaped = .ok header.body
  projection : values.checked.catalog.project header.function.resultType = .ok header.output
  flow : Expr
  generated : SourceCoreLoops.lowerFlowStatementsWithPolicy header.policy header.fuel header.function.source
    (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2))) header.function.body
    header.output header.reasonAt true header.escaped = .ok flow
  emitted : header.body = CompatibleStatements.finish header.output flow header.fellThrough header.escaped
  tree : GenericImperativeFor.Tree header.layouts header.owner header.active prepared.layout.frame header.globals
    header.onError values header.function.source expressionSyntax
    (fun context => Expressions headers compilation expressionFuel header.function.source context header.solved header.reasonAt)
    ambient.definitions administrative header.context
    (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)))
    (.statements true header.function.body) header.function.resultType header.output flow
  errors : GenericImperativeFor.Tree.Errors registry faults tree

/-- Static profiles select operand laws without storing runtime body meaning. -/
structure ProfileFor (diagnosticPolicy : AssignmentDiagnosticPolicy) (headers : Inventory prepared values ambient.definitions program)
    (header : Header prepared values ambient.definitions program)
    (compilation : SourceCoreFunctions.Context) (expressionFuel : Nat)
    (expressionSyntax : ExpressionId → Prop) (administrative : Core.Context)
    (registry : SourceCoreRawMetadata.Registry) (faults : FunctionCalls.FaultRep) where private mk ::
  accepted : SourceCoreLoops.lowerStatementsWithPolicy header.policy header.fuel header.function.source
    (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2))) header.function.body
    header.output header.reasonAt header.fellThrough header.escaped = .ok header.body
  projection : values.checked.catalog.project header.function.resultType = .ok header.output
  flow : Expr
  generated : SourceCoreLoops.lowerFlowStatementsWithPolicy header.policy header.fuel header.function.source
    (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2))) header.function.body
    header.output header.reasonAt true header.escaped = .ok flow
  emitted : header.body = CompatibleStatements.finish header.output flow header.fellThrough header.escaped
  tree : GenericImperativeFor.Tree header.layouts header.owner header.active prepared.layout.frame header.globals
    header.onError values header.function.source expressionSyntax
    (fun context => Expressions headers compilation expressionFuel header.function.source context header.solved header.reasonAt)
    ambient.definitions administrative header.context
    (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)))
    (.statements true header.function.body) header.function.resultType header.output flow
  errors : GenericImperativeFor.Tree.ErrorsFor diagnosticPolicy registry faults tree

/-- Keep the original static record as the unconditional interface. -/
def Profile.to_for
    {headers : Inventory prepared values ambient.definitions program}
    {header : Header prepared values ambient.definitions program}
    {compilation : SourceCoreFunctions.Context} {expressionFuel : Nat}
    {expressionSyntax : ExpressionId → Prop} {administrative : Core.Context}
    {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
    (certificate : Profile headers header compilation expressionFuel expressionSyntax administrative registry faults) :
    ProfileFor .unconditional headers header compilation expressionFuel expressionSyntax administrative registry faults :=
  ⟨certificate.accepted, certificate.projection, certificate.flow, certificate.generated, certificate.emitted, certificate.tree, certificate.errors⟩

/-- Restore only the original unconditional record, field by field. -/
def ProfileFor.to_strict
    {headers : Inventory prepared values ambient.definitions program}
    {header : Header prepared values ambient.definitions program}
    {compilation : SourceCoreFunctions.Context} {expressionFuel : Nat}
    {expressionSyntax : ExpressionId → Prop} {administrative : Core.Context}
    {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
    (certificate : ProfileFor .unconditional headers header compilation expressionFuel expressionSyntax administrative registry faults) :
    Profile headers header compilation expressionFuel expressionSyntax administrative registry faults :=
  ⟨certificate.accepted, certificate.projection, certificate.flow, certificate.generated, certificate.emitted, certificate.tree, certificate.errors⟩

def ProfileFor.of_extracted {diagnosticPolicy : AssignmentDiagnosticPolicy}
    {headers : Inventory prepared values ambient.definitions program}
    {header : Header prepared values ambient.definitions program}
    {compilation : SourceCoreFunctions.Context} {expressionFuel : Nat}
    {expressionSyntax : ExpressionId → Prop} {administrative : Core.Context}
    {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep} {flow : Expr}
    (accepted : SourceCoreLoops.lowerStatementsWithPolicy header.policy header.fuel header.function.source
      (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2))) header.function.body
      header.output header.reasonAt header.fellThrough header.escaped = .ok header.body)
    (projection : values.checked.catalog.project header.function.resultType = .ok header.output)
    (generated : SourceCoreLoops.lowerFlowStatementsWithPolicy header.policy header.fuel header.function.source
      (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2))) header.function.body
      header.output header.reasonAt true header.escaped = .ok flow)
    (tree : GenericImperativeFor.Tree header.layouts header.owner header.active prepared.layout.frame header.globals
      header.onError values header.function.source expressionSyntax
      (fun context => Expressions headers compilation expressionFuel header.function.source context header.solved header.reasonAt)
      ambient.definitions administrative header.context
      (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)))
      (.statements true header.function.body) header.function.resultType header.output flow)
    (errors : GenericImperativeFor.Tree.ErrorsFor diagnosticPolicy registry faults tree) :
    ProfileFor diagnosticPolicy headers header compilation expressionFuel expressionSyntax administrative registry faults := by
  have emitted : header.body = CompatibleStatements.finish header.output flow header.fellThrough header.escaped := by
    unfold SourceCoreLoops.lowerStatementsWithPolicy at accepted
    rw [generated] at accepted
    exact Except.ok.inj accepted.symm
  exact ⟨accepted, projection, flow, generated, emitted, tree, errors⟩

/-- Backward-compatible unconditional extraction. -/
def Profile.of_extracted
    {headers : Inventory prepared values ambient.definitions program}
    {header : Header prepared values ambient.definitions program}
    {compilation : SourceCoreFunctions.Context} {expressionFuel : Nat}
    {expressionSyntax : ExpressionId → Prop} {administrative : Core.Context}
    {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep} {flow : Expr}
    (accepted : SourceCoreLoops.lowerStatementsWithPolicy header.policy header.fuel header.function.source
      (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2))) header.function.body
      header.output header.reasonAt header.fellThrough header.escaped = .ok header.body)
    (projection : values.checked.catalog.project header.function.resultType = .ok header.output)
    (generated : SourceCoreLoops.lowerFlowStatementsWithPolicy header.policy header.fuel header.function.source
      (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2))) header.function.body
      header.output header.reasonAt true header.escaped = .ok flow)
    (tree : GenericImperativeFor.Tree header.layouts header.owner header.active prepared.layout.frame header.globals
      header.onError values header.function.source expressionSyntax
      (fun context => Expressions headers compilation expressionFuel header.function.source context header.solved header.reasonAt)
      ambient.definitions administrative header.context
      (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)))
      (.statements true header.function.body) header.function.resultType header.output flow)
    (errors : GenericImperativeFor.Tree.Errors registry faults tree) :
    Profile headers header compilation expressionFuel expressionSyntax administrative registry faults :=
  (ProfileFor.of_extracted accepted projection generated tree errors).to_strict

/-- Runtime correspondence is deliberately absent from this family. -/
def Profiles (headers : Inventory prepared values ambient.definitions program)
    (compilation : SourceCoreFunctions.Context) (expressionFuel : Nat)
    (expressionSyntax : Header prepared values ambient.definitions program → ExpressionId → Prop)
    (administrative : Header prepared values ambient.definitions program → Core.Context)
    (registry : SourceCoreRawMetadata.Registry) (faults : FunctionCalls.FaultRep) : Prop :=
  ∀ header, header ∈ headers → Nonempty
    (Profile headers header compilation expressionFuel (expressionSyntax header) (administrative header) registry faults)

/-- Every header uses the same diagnostic policy; execution remains absent. -/
def ProfilesFor (diagnosticPolicy : AssignmentDiagnosticPolicy) (headers : Inventory prepared values ambient.definitions program)
    (compilation : SourceCoreFunctions.Context) (expressionFuel : Nat)
    (expressionSyntax : Header prepared values ambient.definitions program → ExpressionId → Prop)
    (administrative : Header prepared values ambient.definitions program → Core.Context)
    (registry : SourceCoreRawMetadata.Registry) (faults : FunctionCalls.FaultRep) : Prop :=
  ∀ header, header ∈ headers → Nonempty
    (ProfileFor diagnosticPolicy headers header compilation expressionFuel (expressionSyntax header) (administrative header) registry faults)

theorem Profiles.to_for (headers : Inventory prepared values ambient.definitions program)
    (compilation : SourceCoreFunctions.Context) (expressionFuel : Nat)
    (expressionSyntax : Header prepared values ambient.definitions program → ExpressionId → Prop)
    (administrative : Header prepared values ambient.definitions program → Core.Context)
    (registry : SourceCoreRawMetadata.Registry) (faults : FunctionCalls.FaultRep)
    (profiles : Profiles headers compilation expressionFuel expressionSyntax administrative registry faults) :
    ProfilesFor .unconditional headers compilation expressionFuel expressionSyntax administrative registry faults := by
  intro header member
  obtain ⟨certificate⟩ := profiles header member
  exact ⟨certificate.to_for⟩


theorem ProfilesFor.to_strict (headers : Inventory prepared values ambient.definitions program)
    (compilation : SourceCoreFunctions.Context) (expressionFuel : Nat)
    (expressionSyntax : Header prepared values ambient.definitions program → ExpressionId → Prop)
    (administrative : Header prepared values ambient.definitions program → Core.Context)
    (registry : SourceCoreRawMetadata.Registry) (faults : FunctionCalls.FaultRep)
    (profiles : ProfilesFor .unconditional headers compilation expressionFuel expressionSyntax administrative registry faults) :
    Profiles headers compilation expressionFuel expressionSyntax administrative registry faults := by
  intro header member
  obtain ⟨certificate⟩ := profiles header member
  exact ⟨certificate.to_strict⟩

/-- Existing static heads can forget their builtin-only body certificate.
The resulting call receipt refers only to the finite header inventory. -/
theorem Head.of_existing
    {bodies : NamedCallExpressions.Bodies prepared values ambient.definitions program}
    {compilation : SourceCoreFunctions.Context} {source : TypedSource} {context : SourceSemantics.Context}
    {children : GenericExpressionMeaning.Certificate} {scope : Scope} {id : ExpressionId} {code : SourceCoreBasic.LoweredExpr}
    (head : NamedCallExpressions.Head bodies compilation source context children scope id code) :
    Head (bodies.map Header.of_body) compilation source context children scope id code := by
  cases head with
  | named member metadata sourceType form calleeFound calleeForm calleeRequirements calleeCoercions
      valid predicates evidence arity emission selectedSlot sequence nativeTypes =>
    exact .named (List.mem_map.mpr ⟨_, member, rfl⟩) metadata sourceType form calleeFound calleeForm
      calleeRequirements calleeCoercions valid predicates evidence arity emission selectedSlot sequence nativeTypes

end Solcore.SourceSemantics.CoreLowering.RecursiveNamedCatalog
