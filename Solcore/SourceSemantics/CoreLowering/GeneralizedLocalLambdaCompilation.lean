import Solcore.SourceSemantics.CoreLowering.GeneralizedLocalLambdaEmissionFacts
import Solcore.SourceSemantics.CoreLowering.CallableIndexedLambdaCertificates

/-! The literal contextual child of a generalized initializer retains its
actual lambda certificate. No source closure or read-site dictionary is
chosen while the native bundle is created. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 4096
namespace Solcore.SourceSemantics.CoreLowering.GeneralizedLocalLambdaCompilation
open Core Frontend SourceInference SourceCoreLocalPolymorphism
open GeneralizedLocalInstanceCompilation (Inputs Receipt)

def context (inputs : Inputs) (prepared : SourceCoreLocalEvidence.Prepared) : SourceCoreFunctions.Context :=
  { inputs.current with solvedRequirements := prepared.caller.function.solvedRequirements }

def representation (inputs : Inputs) (prepared : SourceCoreLocalEvidence.Prepared) :
    SourceCoreGeneralFunctions.Representation :=
  inputs.representation.atContext inputs.current.owner prepared.substitution

def binder (inputs : Inputs) (prepared : SourceCoreLocalEvidence.Prepared) :=
  SourceCoreGeneralFunctions.contextualBinder (representation inputs prepared)
    inputs.locals inputs.current.owner prepared.substitution

def lowerBody (inputs : Inputs) (prepared : SourceCoreLocalEvidence.Prepared) :=
  SourceCoreGeneralFunctions.bodyLowererWithRepresentation (representation inputs prepared)
    prepared.caller.function.solvedRequirements inputs.assignments inputs.diagnostics inputs.current.owner
    (binder inputs prepared)

private def localError (id : ExpressionId) (node : ExpressionNode) : SourceCoreLocalPolymorphism.Error → SourceCoreBasic.Error
  | .metadata error => error
  | _ => .unsupportedExpression id node.form

def special (inputs : Inputs) (prepared : SourceCoreLocalEvidence.Prepared) (fuel : Nat) :
    SourceCoreFunctions.Context → SourceCoreFunctions.ExpressionLowerer → Nat →
      TypedSource → SourceCoreBasic.Scope → ExpressionId → (ExpressionId → Word) →
      Except SourceCoreBasic.Error (Option SourceCoreBasic.LoweredExpr) :=
  fun current child budget source scope id reasonAt => do
    let source ← SourceCoreGeneralFunctions.contextualSource inputs.program current.plan inputs.locals
      current.owner (some prepared) source id
    let node ← match source.lookupExpression? id with
      | some node => pure node
      | none => throw (.missingExpression id)
    let initialized := inputs.locals.bindings.find? fun binding =>
      decide (binding.caller = current.owner ∧ binding.initializer = id)
    if let some initialized := initialized.filter (fun _ => some inputs.initializer ≠ some id) then
      let binding ← (inputs.locals.binding current.owner initialized.binder.id).mapError (localError id node)
      let lowered ← (SourceCoreLocalPolymorphism.lowerInitializer binding prepared.substitution
        (GeneralizedLocalInstanceCompilation.compile {
          inputs with representation := representation inputs prepared
                      current := current
                      parent := some prepared
                      budget := budget
                      fuel := fuel
                      initializer := id
                      scope := scope
                      reasonAt := reasonAt })).mapError (localError id node)
      return some lowered
    let evidence ← SourceCoreEvidence.lowerWithProjector inputs.program
      (representation inputs prepared).expressions.projectType prepared.caller current child budget
      source scope id reasonAt (SourceCoreGeneralFunctions.callablePolicy inputs.native prepared.substitution)
    if let some lowered := evidence then return some lowered
    match node.form with
    | .reference _ (.local identifier) =>
      if inputs.locals.bindings.any (fun binding =>
          decide (binding.caller = current.owner ∧ binding.binder.id = identifier)) then
        let lowered ← (SourceCoreLocalPolymorphism.lowerRead inputs.locals current.owner
          prepared.substitution source scope id (reasonAt id)).mapError (localError id node)
        let viewed ← (representation inputs prepared).localReadView current.owner prepared.substitution
          source scope id lowered
        SourceCoreBasic.ensureType (.occurrence id.occurrence) lowered.type viewed.type
        return some viewed
      else return none
    | _ => return none

def policy (inputs : Inputs) (prepared : SourceCoreLocalEvidence.Prepared) (fuel : Nat) : SourceCoreFunctions.Policy :=
  { (representation inputs prepared).expressions with
    callables := SourceCoreGeneralFunctions.callablePolicy inputs.native prepared.substitution
    lowerBinder := binder inputs prepared
    readExpression := fun source id => do
      let source ← SourceCoreGeneralFunctions.contextualSource inputs.program inputs.current.plan
        inputs.locals inputs.current.owner (some prepared) source id
      (representation inputs prepared).expressions.readExpression source id
    lowerSpecial? := some (special inputs prepared fuel) }

/-- This equation unfolds the actual recursive contextual call, including its
original fuel cap and the exact initializer skipped by this one child. -/
theorem child_at_succ (inputs : Inputs) (prepared : SourceCoreLocalEvidence.Prepared) {fuel : Nat}
    (budget : min inputs.budget inputs.fuel = fuel + 1) :
    inputs.child prepared = SourceCoreFunctions.lowerExpressionWithPolicy
      (policy inputs prepared fuel) (lowerBody inputs prepared) (fuel + 1) (context inputs prepared)
      prepared.source inputs.scope inputs.initializer inputs.reasonAt := by
  unfold Inputs.child
  rw [budget, SourceCoreGeneralFunctions.lowerContextualExpression.eq_def]
  rfl

private theorem evidence_lambda (program : CheckedProgram) (projector : SourceCoreEvidence.Projector)
    (caller : SourceSpecialization.SpecializedFunction) (compilation : SourceCoreFunctions.Context)
    (child : SourceCoreFunctions.ExpressionLowerer) (fuel : Nat) (scope : SourceCoreBasic.Scope)
    (reasonAt : ExpressionId → Word) (callables : SourceCoreFunctions.CallablePolicy)
    {source : TypedSource} {id : ExpressionId} {node : ExpressionNode}
    {parameters : List TypedBinder} {result : TypeSystem.Ty} {statements : List StatementId}
    (found : source.lookupExpression? id = some node) (form : node.form = .lambda parameters result statements)
    (requirements : node.requirements = []) (coercions : node.coercions = []) :
    SourceCoreEvidence.lowerWithProjector program projector caller compilation child fuel source scope id reasonAt callables = .ok none := by
  have owned : SourceCompilationPlan.ordinaryOwnedRequirements? node = some [] := by
    unfold SourceCompilationPlan.ordinaryOwnedRequirements?
    rw [requirements, coercions]
    rfl
  simp [SourceCoreEvidence.lowerWithProjector, found, form, owned, requirements, coercions,
    bind, Except.bind, pure, Except.pure]

structure Packet (inputs : Inputs) (candidate : Instance) (raw : Expr) where
  original : Receipt inputs candidate raw
  node : ExpressionNode
  parameters : List TypedBinder
  result : TypeSystem.Ty
  statements : List StatementId
  reported : Ty
  found : original.emission.prepared.source.lookupExpression? inputs.initializer = some node
  form : node.form = .lambda parameters result statements
  owner : inputs.initializer.occurrence.owner = original.emission.prepared.source.owner
  requirements : node.requirements = []
  coercions : node.coercions = []
  fuel : Nat
  budget : min inputs.budget inputs.fuel = fuel + 1
  accepted : SourceCoreFunctions.lowerExpressionWithPolicy
    (policy inputs original.emission.prepared fuel) (lowerBody inputs original.emission.prepared)
    (fuel + 1) (context inputs original.emission.prepared) original.emission.prepared.source
    inputs.scope inputs.initializer inputs.reasonAt = .ok original.lowered
  certificate : CallableIndexedLambdaCertificates.Certificate
    (policy inputs original.emission.prepared fuel) (lowerBody inputs original.emission.prepared)
    fuel (context inputs original.emission.prepared) original.emission.prepared.source inputs.scope
    inputs.initializer node parameters result statements reported inputs.reasonAt original.lowered

/-- The factory result and its child certificate are retained together before
any particular source materialization supplies an evidence environment. -/
theorem of_receipt {inputs : Inputs} {candidate : Instance} {raw : Expr}
    (original : Receipt inputs candidate raw)
    {node : ExpressionNode} {parameters : List TypedBinder} {result : TypeSystem.Ty}
    {statements : List StatementId} {reported : Ty}
    (found : original.emission.prepared.source.lookupExpression? inputs.initializer = some node)
    (form : node.form = .lambda parameters result statements)
    (owner : inputs.initializer.occurrence.owner = original.emission.prepared.source.owner)
    (requirements : node.requirements = []) (coercions : node.coercions = [])
    (read : inputs.representation.expressions.readExpression original.emission.prepared.source
      inputs.initializer = .ok (node, reported)) : Nonempty (Packet inputs candidate raw) := by
  have accepted := original.compiled
  cases budget : min inputs.budget inputs.fuel with
  | zero => simp [Inputs.child, budget, SourceCoreGeneralFunctions.lowerContextualExpression.eq_def] at accepted
  | succ fuel =>
    rw [child_at_succ inputs original.emission.prepared budget] at accepted
    have unchanged : SourceCoreGeneralFunctions.contextualSource inputs.program inputs.current.plan inputs.locals
        inputs.current.owner (some original.emission.prepared) original.emission.prepared.source
        inputs.initializer = .ok original.emission.prepared.source := by
      simp [SourceCoreGeneralFunctions.contextualSource, found, form]
    obtain ⟨certificate⟩ := CallableIndexedLambdaCertificates.of_accepted
      (owner := owner) (found := found) (form := form) (accepted := accepted)
      (ordinary := by
        change special inputs original.emission.prepared fuel _ _ _ _ _ _ _ = .ok none
        unfold special
        change (do
          let source ← SourceCoreGeneralFunctions.contextualSource inputs.program inputs.current.plan inputs.locals
            inputs.current.owner (some original.emission.prepared) original.emission.prepared.source inputs.initializer
          _) = .ok none
        rw [unchanged]
        simp only [bind, Except.bind, pure, Except.pure, found]
        rw [evidence_lambda _ _ _ _ _ _ _ _ _ found form requirements coercions]
        simp [form])
      (read := by
        change (do
          let source ← SourceCoreGeneralFunctions.contextualSource inputs.program inputs.current.plan inputs.locals
            inputs.current.owner (some original.emission.prepared) original.emission.prepared.source inputs.initializer
          inputs.representation.expressions.readExpression source inputs.initializer) = .ok (node, reported)
        simpa only [unchanged, bind, Except.bind] using read)
    exact ⟨⟨original, node, parameters, result, statements, reported, found, form, owner,
      requirements, coercions, fuel, budget, accepted, certificate⟩⟩

end Solcore.SourceSemantics.CoreLowering.GeneralizedLocalLambdaCompilation
