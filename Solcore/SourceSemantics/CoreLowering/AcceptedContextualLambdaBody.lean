import Solcore.SourceSemantics.CoreLowering.AcceptedContextualLambdaReceipt
import Solcore.SourceSemantics.CoreLowering.AcceptedNamedBodyFlow

/-! A reached ordinary lambda retains its complete accepted body. Its source
position, enclosing body shape and the number of other lambdas are unrestricted.
The root budget and captured scope come from the same original compiler action. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 3200000
namespace Solcore.SourceSemantics.CoreLowering.AcceptedContextualLambdaBody
open Core Frontend SourceInference
open CallableIndexedNamedGeneration
open CallableIndexedOwnedContextualCompilerPolicyProfiles (RootPolicyReceipt)
open AcceptedNamedExpressionFlow (Head)
open AcceptedContextualLambdaReceipt (bodyPolicy)
open AcceptedNamedBodyFlow (Body)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
    {named : Named} {diagnostics : SourceCoreDataPlaceFaultSites.Program} {namedCode : Expr}
    {compilation : Compilation compiled.indexed named diagnostics namedCode}
    {rootFuel : Nat} {rootSource : TypedSource} {rootScope : SourceCoreLocalCell.Scope}
    {rootId : ExpressionId} {rootReasonAt : ExpressionId → Word}
    {rootLowered : SourceCoreBasic.LoweredExpr}
    (root : RootPolicyReceipt (compiled := compiled) named diagnostics namedCode compilation
      rootFuel rootSource rootScope rootId rootReasonAt rootLowered)
    {source : TypedSource} {scope : SourceCoreLocalCell.Scope} {reasonAt : ExpressionId → Word}
    {fuel : Nat} {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}

/-- This is the actual match context, with the final compiled data table. -/
def ambientMatch : SourceCoreCompatibleDataMatches.Context :=
  CompatibleMatchAmbientLowering.withDefinitions
    ⟨.initial compiled.compatible.checked, named.specialized.function.solvedRequirements,
      some (allocator compiled.indexed named), none⟩ compiled.indexed.layouts.definitions

private theorem assignments :
    CompatibleAssignmentStatements.AssignmentPolicy (bodyPolicy root fuel)
      (.initial compiled.compatible.checked)
      (fun site binderId => diagnostics.placeReason named.signature.key site binderId none)
      (fun site binderId operator => if operator = .equal then Word.zero
        else compilation.own.assignments.reasonAt site binderId (.value operator))
      (fun site binderId type => diagnostics.placeReason named.signature.key site binderId (some type)) := by
  refine ⟨rfl, rfl, ?_⟩
  change some _ = some _
  apply congrArg some
  funext expression fuel source scope site assignment operator rhs output next reasonAt
  cases operator <;> rfl

private theorem unary :
    CompatibleBitNotStatements.Policy (bodyPolicy root fuel)
      (.initial compiled.compatible.checked)
      (fun site binderId => diagnostics.placeReason named.signature.key site binderId none)
      (fun site binderId => compilation.own.assignments.reasonAt site binderId .bitNot)
      (fun site binderId type => diagnostics.placeReason named.signature.key site binderId (some type)) := rfl

private theorem matched :
    CompatibleMatchAmbientLowering.PolicySuccess (bodyPolicy root fuel)
      (ambientMatch (compiled := compiled) (named := named)) := by
  apply CompatibleMatchAmbientLowering.PolicySuccess.extend (by rfl)
  exact ⟨_, CallableIndexedAmbient.definitions_exact compiled.indexed⟩

/-- The compiler certificate and its refined body have the identical capture
scope, parameter allocation, fuel, result type and emitted code. -/
structure Receipt
    (head : Head root.selected.policy root.selected.lowerBody fuel
      (context compiled.indexed named) source scope id reasonAt lowered)
    (parameters : List TypedBinder) (result : TypeSystem.Ty) (statements : List StatementId) where
  form : head.node.form = .lambda parameters result statements
  reported : Core.Ty
  read : SourceCoreCompatibleDataExpressions.readExpression compiled.compatible.checked source id =
    .ok (head.node, reported)
  requirements : head.node.requirements = []
  coercions : head.node.coercions = []
  notInitializer : compiled.indexed.base.locals.bindings.find? (fun binding =>
    decide (binding.caller = named.signature.key ∧ binding.initializer = id)) = none
  compiler : CallableIndexedLambdaCertificates.Certificate root.selected.policy root.selected.lowerBody
    fuel (context compiled.indexed named) source scope id head.node parameters result statements
    reported reasonAt lowered
  body : Body (bodyPolicy root fuel) fuel source compiler.bodyScope statements compiler.resultCore
    reasonAt (context compiled.indexed named).internalReason
    (context compiled.indexed named).internalReason compiler.body
  ready : body.tree.Ready

/-- Every ordinary lambda action supplies the complete body receipt directly
from its accepted compiler call, including nested lambdas and nonterminal bodies. -/
theorem of_head
    (head : Head root.selected.policy root.selected.lowerBody fuel
      (context compiled.indexed named) source scope id reasonAt lowered)
    {parameters : List TypedBinder} {result : TypeSystem.Ty} {statements : List StatementId}
    (plain : head.special = none) (form : head.node.form = .lambda parameters result statements) :
    Nonempty (Receipt root head parameters result statements) := by
  obtain ⟨reported, read, requirements, coercions, ordinary, ⟨compiler⟩⟩ :=
    AcceptedContextualLambdaReceipt.of_head root head plain form
  have accepted := compiler.bodyCompiled
  rw [AcceptedContextualLambdaReceipt.body_callback root fuel] at accepted
  obtain ⟨body⟩ := AcceptedNamedBodyFlow.body_of_accepted accepted
  obtain ⟨tree, ready⟩ := body.tree.refine (assignments root) (unary root) (matched root)
  exact ⟨⟨form, reported, read, requirements, coercions, ordinary, compiler,
    ⟨body.flow, tree, body.emitted⟩, ready⟩⟩

end Solcore.SourceSemantics.CoreLowering.AcceptedContextualLambdaBody
