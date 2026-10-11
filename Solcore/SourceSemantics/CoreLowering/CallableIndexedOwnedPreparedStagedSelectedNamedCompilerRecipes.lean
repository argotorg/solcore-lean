import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPreparedHeaders
import Solcore.SourceSemantics.CoreLowering.CallableIndexedActualNamedSourceReceipts
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedTerminalNamedGlobalDispatch

/-! The actual prepared Header retains the concrete contextual expression
callback. Its cached specialization fixes the root policy and body recipe at
the terminal receipt's own child fuel. The packet remains the same throughout
callback projection and compiler-recipe extraction. Original typing, read
profiles, declarations and reachable-call authority remain separate inputs. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedSelectedNamedCompilerRecipes
open Core Frontend SourceInference
open CallableIndexedNamedGeneration
open CallableIndexedOwnedFunctionValues (Header)
open CallableIndexedOwnedPreparedStagedTerminalNamedGlobalDispatch (Terminal)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}

/-- This is the literal contextual lowerer retained by the prepared policy. -/
def contextual {row : SourceSpecialization.SpecializedFunction}
    (prepared : RecursiveNamedPublicSpecializationMeaning.Prepared compiled row) :
    SourceCoreFunctions.ExpressionLowerer :=
  SourceCoreGeneralFunctions.lowerContextualExpression compiled.indexed.base.sourceProgram
    ((representation compiled.indexed).atContext prepared.named.signature.key [])
    compiled.indexed.base.sourceProgram.signatures compiled.indexed.base.locals
    prepared.compilation.parents prepared.compilation.own.assignments prepared.diagnostics
    (context compiled.indexed prepared.named) compiled.indexed.base.callableContext none none

/-- The Header's actual policy supplies this full callback by construction. -/
theorem expression_callback
    {header : Header compiled (Program.ofChecked compiled.sourceProgram)}
    (packet : Terminal header) :
    header.policy.lowerExpression = contextual packet.prepared := by
  have selected := congrArg (fun policy : SourceCoreLoops.Policy => policy.lowerExpression)
    packet.aligned.policy
  exact selected.trans (by rfl)

/-- Named agreement identifies the original Source, independently of metadata. -/
theorem original_source
    {header : Header compiled (Program.ofChecked compiled.sourceProgram)}
    (packet : Terminal header) :
    header.function.source = source packet.prepared.named := by
  calc
    header.function.source = source header.named := header.agreement.source
    _ = source packet.prepared.named := congrArg source packet.aligned.named

private theorem recipe_of_record {row : SourceSpecialization.SpecializedFunction}
    (prepared : RecursiveNamedPublicSpecializationMeaning.Prepared compiled row)
    (record : SourceCompilationPlan.exactSpecialization compiled.indexed.base.plan
      prepared.named.signature.key = .ok prepared.named.specialized)
    (fuel : Nat) :
    ∃ (policy : SourceCoreFunctions.Policy) (body : SourceCoreFunctions.BodyLowerer),
      contextual prepared (fuel + 1) =
        SourceCoreFunctions.lowerExpressionWithPolicy policy body (fuel + 1)
          (context compiled.indexed prepared.named) ∧
      policy.callables = SourceCoreGeneralFunctions.callablePolicy
        compiled.indexed.base.callableContext [] ∧
      body = SourceCoreGeneralFunctions.bodyLowererWithRepresentation
        ((representation compiled.indexed).atContext prepared.named.signature.key [])
        (context compiled.indexed prepared.named).solvedRequirements
        prepared.compilation.own.assignments prepared.diagnostics
        (context compiled.indexed prepared.named).owner
        (SourceCoreGeneralFunctions.contextualBinder
          ((representation compiled.indexed).atContext prepared.named.signature.key [])
          compiled.indexed.base.locals prepared.named.signature.key []) := by
  refine ⟨?policy, ?body, ?callback, ?callables, ?recipe⟩
  case callback =>
    funext actualSource scope id reasonAt
    unfold contextual
    rw [SourceCoreGeneralFunctions.lowerContextualExpression.eq_def]
    dsimp only
    change (SourceCompilationPlan.exactSpecialization compiled.indexed.base.plan
      prepared.named.signature.key |>.mapError SourceCoreBasic.Error.callPreparation) >>= _ = _
    rw [record]
    simp only [Except.mapError, bind, Except.bind]
    rfl
  case callables => rfl
  case recipe => rfl

/-- Unwrap the actual specialization bind once and retain its full callback,
rather than only incomplete read or callable-policy projections. -/
theorem contextual_recipe
    {header : Header compiled (Program.ofChecked compiled.sourceProgram)}
    (packet : Terminal header) (fuel : Nat) :
    ∃ (policy : SourceCoreFunctions.Policy) (body : SourceCoreFunctions.BodyLowerer),
      header.policy.lowerExpression (fuel + 1) =
        SourceCoreFunctions.lowerExpressionWithPolicy policy body (fuel + 1)
          (context compiled.indexed packet.prepared.named) ∧
      policy.callables = SourceCoreGeneralFunctions.callablePolicy
        compiled.indexed.base.callableContext [] ∧
      body = SourceCoreGeneralFunctions.bodyLowererWithRepresentation
        ((representation compiled.indexed).atContext packet.prepared.named.signature.key [])
        (context compiled.indexed packet.prepared.named).solvedRequirements
        packet.prepared.compilation.own.assignments packet.prepared.diagnostics
        (context compiled.indexed packet.prepared.named).owner
        (SourceCoreGeneralFunctions.contextualBinder
          ((representation compiled.indexed).atContext packet.prepared.named.signature.key [])
          compiled.indexed.base.locals packet.prepared.named.signature.key []) := by
  have record := CallableIndexedActualNamedSourceReceipts.header_record compiled header
  have actualRecord : SourceCompilationPlan.exactSpecialization compiled.indexed.base.plan
      packet.prepared.named.signature.key = .ok packet.prepared.named.specialized := by
    simpa only [packet.aligned.named] using record
  obtain ⟨policy, body, callback, callables, bodyRecipe⟩ :=
    recipe_of_record packet.prepared actualRecord fuel
  have selected := congrArg (fun lower : SourceCoreFunctions.ExpressionLowerer => lower (fuel + 1))
    (expression_callback packet)
  exact ⟨policy, body, selected.trans callback, callables, bodyRecipe⟩

/-- Genuine generated acceptance excludes zero traversal fuel at this packet. -/
theorem child_fuel_positive
    {header : Header compiled (Program.ofChecked compiled.sourceProgram)}
    (packet : Terminal header) : packet.receipt.childFuel ≠ 0 := by
  intro zero
  have selected := congrArg
    (fun lower : SourceCoreFunctions.ExpressionLowerer =>
      lower packet.receipt.childFuel header.function.source
        (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)))
        packet.expression header.reasonAt) (expression_callback packet)
  have accepted := selected.symm.trans packet.receipt.generated
  have atZero := congrArg
    (fun fuel : Nat => contextual packet.prepared fuel header.function.source
      (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)))
      packet.expression header.reasonAt) zero
  have impossible := atZero.symm.trans accepted
  unfold contextual at impossible
  rw [SourceCoreGeneralFunctions.lowerContextualExpression.eq_def] at impossible
  cases impossible

private theorem predecessor_of_positive (fuel : Nat) (positive : fuel ≠ 0) :
    ∃ predecessor, fuel = predecessor + 1 := by
  cases fuel with
  | zero => exact False.elim (positive rfl)
  | succ predecessor => exact ⟨predecessor, rfl⟩

/-- The actual child fuel stays distinct from independent read and compiled
fuel. The contextual special hook retains its real predecessor budget. -/
structure Recipe (header : Header compiled (Program.ofChecked compiled.sourceProgram))
    (packet : Terminal header) where
  policy : SourceCoreFunctions.Policy
  body : SourceCoreFunctions.BodyLowerer
  predecessor : Nat
  fuel : packet.receipt.childFuel = predecessor + 1
  source : header.function.source = CallableIndexedNamedGeneration.source packet.prepared.named
  callables : policy.callables = SourceCoreGeneralFunctions.callablePolicy
    compiled.indexed.base.callableContext []
  callback : header.policy.lowerExpression packet.receipt.childFuel header.function.source =
    SourceCoreFunctions.lowerExpressionWithPolicy policy body packet.receipt.childFuel
      (context compiled.indexed packet.prepared.named) header.function.source
  bodyRecipe : body = SourceCoreGeneralFunctions.bodyLowererWithRepresentation
    ((representation compiled.indexed).atContext packet.prepared.named.signature.key [])
    (context compiled.indexed packet.prepared.named).solvedRequirements
    packet.prepared.compilation.own.assignments packet.prepared.diagnostics
    (context compiled.indexed packet.prepared.named).owner
    (SourceCoreGeneralFunctions.contextualBinder
      ((representation compiled.indexed).atContext packet.prepared.named.signature.key [])
      compiled.indexed.base.locals packet.prepared.named.signature.key [])

/-- Actual Header and terminal receipts construct the exact expression recipe.
No callback equality, original acceptance or execution law is an input. -/
theorem of_terminal
    {header : Header compiled (Program.ofChecked compiled.sourceProgram)}
    (packet : Terminal header) : Nonempty (Recipe header packet) := by
  obtain ⟨predecessor, fuel⟩ :=
    predecessor_of_positive packet.receipt.childFuel (child_fuel_positive packet)
  obtain ⟨policy, body, callback, callables, bodyRecipe⟩ := contextual_recipe packet predecessor
  have callbackAt := congrArg
    (fun lower : TypedSource → SourceCoreLocalCell.Scope → ExpressionId →
        (ExpressionId → Word) → Except SourceCoreBasic.Error SourceCoreBasic.LoweredExpr =>
      lower header.function.source) callback
  have selectedFuel := congrArg
    (fun actualFuel : Nat => header.policy.lowerExpression actualFuel header.function.source) fuel
  have recipeFuel := congrArg
    (fun actualFuel : Nat => SourceCoreFunctions.lowerExpressionWithPolicy policy body actualFuel
      (context compiled.indexed packet.prepared.named) header.function.source) fuel
  exact ⟨{
    policy := policy
    body := body
    predecessor := predecessor
    fuel := fuel
    source := original_source packet
    callables := callables
    callback := selectedFuel.trans (callbackAt.trans recipeFuel.symm)
    bodyRecipe := bodyRecipe }⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedSelectedNamedCompilerRecipes
