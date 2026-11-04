import Solcore.Frontend.Fragments.Internal.ClosedSource
import Solcore.Frontend.Fragments.Internal.LocalExpressions

/-!
# Lambda depth

Bounds on lambda depth in closed source, and self-application.
-/

section
-- leanmerge: from Solcore.Frontend.BoundedCalleeLambdaDepth
/- A supplied successful finite callee run makes outer-call bounds compositional.
It is an explicit premise, not a search for a callee budget. The actual selected
saved fields, caller argument and intermediate/full stores are kept literally. -/
set_option autoImplicit false
namespace Solcore.Frontend

/-- Compose a known successful callee budget with admitted argument and saved-body depths. -/
def boundedCalleeLambdaDepthBound (calleeBudget : Nat) (argument : Syntax.Expr) (body : Syntax.Block) : Nat :=
  max calleeBudget (max (closedSourceDataDepthBound argument) (closedSourceDataBodyDepthBound body)) + 1

/-- A supplied finite callee run fixes its actual closure and store; argument and
body success are needed only inside the original successful whole endpoint. -/
theorem boundedCalleeLambda_evaluates_at_depthBound
    {source callee argument : Syntax.Expr} {name : Syntax.Identifier} {body : Syntax.Block}
    (shape : SourceUnaryLambdaShape source name body)
    (argumentFragment : ClosedSourceDataExpression argument)
    (bodyFragment : ClosedSourceDataBody body)
    {callerOwner savedOwner : Resolved.DeclarationId} {callerNames savedNames : LocalNameTable}
    {callerCaptured savedCaptured : Resolved.LocalScope RuntimeValue}
    {initialStore calleeStore finalStore : List RuntimeValue} {calleeBudget : Nat}
    (selected : evaluateClosedSourceExpression? calleeBudget callerOwner callerNames callerCaptured initialStore
      callee = some (.sourceClosure source savedOwner savedNames savedCaptured,calleeStore))
    {callSpan argumentsSpan : Syntax.SourceSpan} {actual : RuntimeValue}
    (original : ClosedSourceExpressionEvaluates callerOwner callerNames callerCaptured initialStore
      ⟨callSpan, .call callee ⟨argumentsSpan,[argument]⟩⟩ actual finalStore)
    {budget : Nat} (enough : boundedCalleeLambdaDepthBound calleeBudget argument body ≤ budget) :
    evaluateClosedSourceExpression? budget callerOwner callerNames callerCaptured initialStore
      ⟨callSpan, .call callee ⟨argumentsSpan,[argument]⟩⟩ = some (actual,finalStore) := by
  have independent := evaluateClosedSourceExpression?_sound selected
  unfold boundedCalleeLambdaDepthBound at enough
  cases budget with
  | zero => omega
  | succ budget =>
    cases original with
    | creation impossible => cases impossible
    | call actualShape calleeEvaluation argumentEvaluation bodyEvaluation =>
      obtain ⟨sameCallee,sameStore⟩ := calleeEvaluation.deterministic independent
      cases sameCallee; cases sameStore
      obtain ⟨sameName,sameBody⟩ := Prod.mk.inj (Option.some.inj
        ((sourceUnaryLambdaShape?_iff.mpr actualShape).symm.trans
          (sourceUnaryLambdaShape?_iff.mpr shape)))
      cases sameName; cases sameBody
      have calleeRun := evaluateClosedSourceExpression?_monotone (by omega : calleeBudget ≤ budget) selected
      have argumentRun := argumentFragment.evaluates_at_depthBound argumentEvaluation
        (by omega : closedSourceDataDepthBound argument ≤ budget)
      have bodyRun := bodyFragment.evaluates_at_depthBound bodyEvaluation
        (by omega : closedSourceDataBodyDepthBound body ≤ budget)
      simpa only [evaluateClosedSourceExpression?,calleeRun,argumentRun,
        sourceUnaryLambdaShape?_iff.mpr shape,bind,Option.bind_some] using bodyRun

end Solcore.Frontend

/-!
## Consolidated module: `Solcore.Frontend.BoundedCalleeLambdaDepthDecisionProperties`
-/

/- Exact outer-call decisions under a supplied successful finite callee run.
No successful argument or body premise is required for these decision laws. -/
set_option autoImplicit false
namespace Solcore.Frontend

section
variable {source callee argument : Syntax.Expr} {name : Syntax.Identifier} {body : Syntax.Block}
variable (shape : SourceUnaryLambdaShape source name body)
variable (argumentFragment : ClosedSourceDataExpression argument)
variable (bodyFragment : ClosedSourceDataBody body)
variable {callerOwner savedOwner : Resolved.DeclarationId} {callerNames savedNames : LocalNameTable}
variable {callerCaptured savedCaptured : Resolved.LocalScope RuntimeValue}
variable {initialStore calleeStore : List RuntimeValue} {calleeBudget : Nat}
variable (selected : evaluateClosedSourceExpression? calleeBudget callerOwner callerNames callerCaptured initialStore
  callee = some (.sourceClosure source savedOwner savedNames savedCaptured,calleeStore))
variable {callSpan argumentsSpan : Syntax.SourceSpan}
include shape argumentFragment bodyFragment selected

/-- A sufficiently deep bounded-selected-callee call returns exactly each original full endpoint. -/
theorem boundedCalleeLambda_evaluate_at_depthBound_iff
    {actual : RuntimeValue} {finalStore : List RuntimeValue} {budget : Nat}
    (enough : boundedCalleeLambdaDepthBound calleeBudget argument body ≤ budget) :
    evaluateClosedSourceExpression? budget callerOwner callerNames callerCaptured initialStore
      ⟨callSpan, .call callee ⟨argumentsSpan, [argument]⟩⟩ = some (actual, finalStore) ↔
    ClosedSourceExpressionEvaluates callerOwner callerNames callerCaptured initialStore
      ⟨callSpan, .call callee ⟨argumentsSpan, [argument]⟩⟩ actual finalStore :=
  ⟨evaluateClosedSourceExpression?_sound,
    fun original => boundedCalleeLambda_evaluates_at_depthBound shape argumentFragment bodyFragment selected original enough⟩

/-- Whole Option stability includes argument and selected-body failure. -/
theorem boundedCalleeLambda_evaluate_depth_stable
    {budget : Nat} (enough : boundedCalleeLambdaDepthBound calleeBudget argument body ≤ budget) :
    evaluateClosedSourceExpression? budget callerOwner callerNames callerCaptured initialStore
      ⟨callSpan, .call callee ⟨argumentsSpan, [argument]⟩⟩ =
    evaluateClosedSourceExpression? (boundedCalleeLambdaDepthBound calleeBudget argument body)
      callerOwner callerNames callerCaptured initialStore ⟨callSpan, .call callee ⟨argumentsSpan, [argument]⟩⟩ := by
  cases low : evaluateClosedSourceExpression? (boundedCalleeLambdaDepthBound calleeBudget argument body)
      callerOwner callerNames callerCaptured initialStore ⟨callSpan, .call callee ⟨argumentsSpan, [argument]⟩⟩ with
  | none =>
    cases high : evaluateClosedSourceExpression? budget callerOwner callerNames callerCaptured initialStore
        ⟨callSpan, .call callee ⟨argumentsSpan, [argument]⟩⟩ with
    | none => rfl
    | some endpoint =>
      obtain ⟨actual, finalStore⟩ := endpoint
      have atBound := boundedCalleeLambda_evaluates_at_depthBound shape argumentFragment bodyFragment selected
        (evaluateClosedSourceExpression?_sound high) (Nat.le_refl _)
      rw [low] at atBound
      cases atBound
  | some endpoint =>
    obtain ⟨actual, finalStore⟩ := endpoint
    exact evaluateClosedSourceExpression?_monotone enough low

/-- Sufficient-depth None excludes every original successful call endpoint,
without classifying its cause or assuming empty lexical inputs. -/
theorem boundedCalleeLambda_evaluate_depth_none_iff
    {budget : Nat} (enough : boundedCalleeLambdaDepthBound calleeBudget argument body ≤ budget) :
    evaluateClosedSourceExpression? budget callerOwner callerNames callerCaptured initialStore
      ⟨callSpan, .call callee ⟨argumentsSpan, [argument]⟩⟩ = none ↔
    ∀ actual finalStore, ¬ ClosedSourceExpressionEvaluates callerOwner callerNames callerCaptured initialStore
      ⟨callSpan, .call callee ⟨argumentsSpan, [argument]⟩⟩ actual finalStore := by
  constructor
  · intro absent actual finalStore original
    have accepted := boundedCalleeLambda_evaluates_at_depthBound shape argumentFragment bodyFragment selected original enough
    rw [absent] at accepted
    cases accepted
  · intro impossible
    cases ran : evaluateClosedSourceExpression? budget callerOwner callerNames callerCaptured initialStore
        ⟨callSpan, .call callee ⟨argumentsSpan, [argument]⟩⟩ with
    | none => rfl
    | some endpoint =>
      obtain ⟨actual, finalStore⟩ := endpoint
      exact False.elim (impossible actual finalStore (evaluateClosedSourceExpression?_sound ran))

/-- A supplied callee run and actual saved syntax bound one outer-call search.
This does not find a successful callee budget or decide arbitrary callee evaluation. -/
theorem boundedCalleeLambda_evaluate_depth_none_iff_all_budgets :
    evaluateClosedSourceExpression? (boundedCalleeLambdaDepthBound calleeBudget argument body)
      callerOwner callerNames callerCaptured initialStore ⟨callSpan, .call callee ⟨argumentsSpan, [argument]⟩⟩ = none ↔
    ∀ budget, evaluateClosedSourceExpression? budget callerOwner callerNames callerCaptured initialStore
      ⟨callSpan, .call callee ⟨argumentsSpan, [argument]⟩⟩ = none := by
  constructor
  · intro absent budget
    have impossible := (boundedCalleeLambda_evaluate_depth_none_iff shape argumentFragment bodyFragment selected
      (Nat.le_refl _)).mp absent
    cases ran : evaluateClosedSourceExpression? budget callerOwner callerNames callerCaptured initialStore
        ⟨callSpan, .call callee ⟨argumentsSpan, [argument]⟩⟩ with
    | none => rfl
    | some endpoint =>
      obtain ⟨actual, finalStore⟩ := endpoint
      exact False.elim (impossible actual finalStore (evaluateClosedSourceExpression?_sound ran))
  · intro absent
    exact absent _

end
end Solcore.Frontend
end

section
-- leanmerge: from Solcore.Frontend.BoundedInputsLambdaDepth
/- Both finite successful input runs are supplied, not discovered. The argument
starts from the actual callee store; only the selected saved body is data-gated.
No saved-body success is required outside an original successful endpoint. -/
set_option autoImplicit false
namespace Solcore.Frontend

/-- Compose supplied successful input budgets with the actual saved data-body depth. -/
def boundedInputsLambdaDepthBound (calleeBudget argumentBudget : Nat) (body : Syntax.Block) : Nat :=
  max calleeBudget (max argumentBudget (closedSourceDataBodyDepthBound body)) + 1

/-- Actual finite input endpoints fix the selected closure and its fresh body inputs. -/
theorem boundedInputsLambda_evaluates_at_depthBound
    {source callee argument : Syntax.Expr} {name : Syntax.Identifier} {body : Syntax.Block}
    (shape : SourceUnaryLambdaShape source name body)
    (bodyFragment : ClosedSourceDataBody body)
    {callerOwner savedOwner : Resolved.DeclarationId} {callerNames savedNames : LocalNameTable}
    {callerCaptured savedCaptured : Resolved.LocalScope RuntimeValue}
    {initialStore calleeStore argumentStore finalStore : List RuntimeValue}
    {calleeBudget argumentBudget : Nat} {argumentValue : RuntimeValue}
    (selected : evaluateClosedSourceExpression? calleeBudget callerOwner callerNames callerCaptured initialStore
      callee = some (.sourceClosure source savedOwner savedNames savedCaptured,calleeStore))
    (supplied : evaluateClosedSourceExpression? argumentBudget callerOwner callerNames callerCaptured calleeStore
      argument = some (argumentValue,argumentStore))
    {callSpan argumentsSpan : Syntax.SourceSpan} {actual : RuntimeValue}
    (original : ClosedSourceExpressionEvaluates callerOwner callerNames callerCaptured initialStore
      ⟨callSpan, .call callee ⟨argumentsSpan,[argument]⟩⟩ actual finalStore)
    {budget : Nat} (enough : boundedInputsLambdaDepthBound calleeBudget argumentBudget body ≤ budget) :
    evaluateClosedSourceExpression? budget callerOwner callerNames callerCaptured initialStore
      ⟨callSpan, .call callee ⟨argumentsSpan,[argument]⟩⟩ = some (actual,finalStore) := by
  have independentCallee := evaluateClosedSourceExpression?_sound selected
  have independentArgument := evaluateClosedSourceExpression?_sound supplied
  unfold boundedInputsLambdaDepthBound at enough
  cases budget with
  | zero => omega
  | succ budget =>
    cases original with
    | creation impossible => cases impossible
    | call actualShape calleeEvaluation argumentEvaluation bodyEvaluation =>
      obtain ⟨sameCallee,sameCalleeStore⟩ := calleeEvaluation.deterministic independentCallee
      cases sameCallee; cases sameCalleeStore
      obtain ⟨sameName,sameBody⟩ := Prod.mk.inj (Option.some.inj
        ((sourceUnaryLambdaShape?_iff.mpr actualShape).symm.trans
          (sourceUnaryLambdaShape?_iff.mpr shape)))
      cases sameName; cases sameBody
      obtain ⟨sameArgument,sameArgumentStore⟩ := argumentEvaluation.deterministic independentArgument
      cases sameArgument; cases sameArgumentStore
      have calleeRun := evaluateClosedSourceExpression?_monotone (by omega : calleeBudget ≤ budget) selected
      have argumentRun := evaluateClosedSourceExpression?_monotone (by omega : argumentBudget ≤ budget) supplied
      have bodyRun := bodyFragment.evaluates_at_depthBound bodyEvaluation
        (by omega : closedSourceDataBodyDepthBound body ≤ budget)
      simpa only [evaluateClosedSourceExpression?,calleeRun,argumentRun,
        sourceUnaryLambdaShape?_iff.mpr shape,bind,Option.bind_some] using bodyRun

end Solcore.Frontend

/-!
## Consolidated module: `Solcore.Frontend.BoundedInputsLambdaDepthDecisionProperties`
-/

/- Exact outer-call decisions under two supplied successful finite input runs.
The actual saved body is data-gated; its success is not an admission premise. -/
set_option autoImplicit false
namespace Solcore.Frontend

section
variable {source callee argument : Syntax.Expr} {name : Syntax.Identifier} {body : Syntax.Block}
variable (shape : SourceUnaryLambdaShape source name body)
variable (bodyFragment : ClosedSourceDataBody body)
variable {callerOwner savedOwner : Resolved.DeclarationId} {callerNames savedNames : LocalNameTable}
variable {callerCaptured savedCaptured : Resolved.LocalScope RuntimeValue}
variable {initialStore calleeStore argumentStore : List RuntimeValue}
variable {calleeBudget argumentBudget : Nat} {argumentValue : RuntimeValue}
variable (selected : evaluateClosedSourceExpression? calleeBudget callerOwner callerNames callerCaptured initialStore
  callee = some (.sourceClosure source savedOwner savedNames savedCaptured,calleeStore))
variable (supplied : evaluateClosedSourceExpression? argumentBudget callerOwner callerNames callerCaptured calleeStore
  argument = some (argumentValue,argumentStore))
variable {callSpan argumentsSpan : Syntax.SourceSpan}
include shape bodyFragment selected supplied

/-- A sufficiently deep call with supplied finite inputs returns each original full endpoint. -/
theorem boundedInputsLambda_evaluate_at_depthBound_iff
    {actual : RuntimeValue} {finalStore : List RuntimeValue} {budget : Nat}
    (enough : boundedInputsLambdaDepthBound calleeBudget argumentBudget body ≤ budget) :
    evaluateClosedSourceExpression? budget callerOwner callerNames callerCaptured initialStore
      ⟨callSpan, .call callee ⟨argumentsSpan, [argument]⟩⟩ = some (actual, finalStore) ↔
    ClosedSourceExpressionEvaluates callerOwner callerNames callerCaptured initialStore
      ⟨callSpan, .call callee ⟨argumentsSpan, [argument]⟩⟩ actual finalStore :=
  ⟨evaluateClosedSourceExpression?_sound,
    fun original => boundedInputsLambda_evaluates_at_depthBound shape bodyFragment selected supplied original enough⟩

/-- Whole Option stability includes actual selected-body failure under successful inputs. -/
theorem boundedInputsLambda_evaluate_depth_stable
    {budget : Nat} (enough : boundedInputsLambdaDepthBound calleeBudget argumentBudget body ≤ budget) :
    evaluateClosedSourceExpression? budget callerOwner callerNames callerCaptured initialStore
      ⟨callSpan, .call callee ⟨argumentsSpan, [argument]⟩⟩ =
    evaluateClosedSourceExpression? (boundedInputsLambdaDepthBound calleeBudget argumentBudget body)
      callerOwner callerNames callerCaptured initialStore ⟨callSpan, .call callee ⟨argumentsSpan, [argument]⟩⟩ := by
  cases low : evaluateClosedSourceExpression? (boundedInputsLambdaDepthBound calleeBudget argumentBudget body)
      callerOwner callerNames callerCaptured initialStore ⟨callSpan, .call callee ⟨argumentsSpan, [argument]⟩⟩ with
  | none =>
    cases high : evaluateClosedSourceExpression? budget callerOwner callerNames callerCaptured initialStore
        ⟨callSpan, .call callee ⟨argumentsSpan, [argument]⟩⟩ with
    | none => rfl
    | some endpoint =>
      obtain ⟨actual, finalStore⟩ := endpoint
      have atBound := boundedInputsLambda_evaluates_at_depthBound shape bodyFragment selected supplied
        (evaluateClosedSourceExpression?_sound high) (Nat.le_refl _)
      rw [low] at atBound
      cases atBound
  | some endpoint =>
    obtain ⟨actual, finalStore⟩ := endpoint
    exact evaluateClosedSourceExpression?_monotone enough low

/-- Sufficient-depth None excludes every original successful call endpoint,
without classifying its cause or assuming empty lexical inputs. -/
theorem boundedInputsLambda_evaluate_depth_none_iff
    {budget : Nat} (enough : boundedInputsLambdaDepthBound calleeBudget argumentBudget body ≤ budget) :
    evaluateClosedSourceExpression? budget callerOwner callerNames callerCaptured initialStore
      ⟨callSpan, .call callee ⟨argumentsSpan, [argument]⟩⟩ = none ↔
    ∀ actual finalStore, ¬ ClosedSourceExpressionEvaluates callerOwner callerNames callerCaptured initialStore
      ⟨callSpan, .call callee ⟨argumentsSpan, [argument]⟩⟩ actual finalStore := by
  constructor
  · intro absent actual finalStore original
    have accepted := boundedInputsLambda_evaluates_at_depthBound shape bodyFragment selected supplied original enough
    rw [absent] at accepted
    cases accepted
  · intro impossible
    cases ran : evaluateClosedSourceExpression? budget callerOwner callerNames callerCaptured initialStore
        ⟨callSpan, .call callee ⟨argumentsSpan, [argument]⟩⟩ with
    | none => rfl
    | some endpoint =>
      obtain ⟨actual, finalStore⟩ := endpoint
      exact False.elim (impossible actual finalStore (evaluateClosedSourceExpression?_sound ran))

/-- Two supplied input runs and actual saved syntax bound one outer-call search.
This does not find child budgets or decide unsuccessful callee or argument inputs. -/
theorem boundedInputsLambda_evaluate_depth_none_iff_all_budgets :
    evaluateClosedSourceExpression? (boundedInputsLambdaDepthBound calleeBudget argumentBudget body)
      callerOwner callerNames callerCaptured initialStore ⟨callSpan, .call callee ⟨argumentsSpan, [argument]⟩⟩ = none ↔
    ∀ budget, evaluateClosedSourceExpression? budget callerOwner callerNames callerCaptured initialStore
      ⟨callSpan, .call callee ⟨argumentsSpan, [argument]⟩⟩ = none := by
  constructor
  · intro absent budget
    have impossible := (boundedInputsLambda_evaluate_depth_none_iff shape bodyFragment selected supplied
      (Nat.le_refl _)).mp absent
    cases ran : evaluateClosedSourceExpression? budget callerOwner callerNames callerCaptured initialStore
        ⟨callSpan, .call callee ⟨argumentsSpan, [argument]⟩⟩ with
    | none => rfl
    | some endpoint =>
      obtain ⟨actual, finalStore⟩ := endpoint
      exact False.elim (impossible actual finalStore (evaluateClosedSourceExpression?_sound ran))
  · intro absent
    exact absent _

end
end Solcore.Frontend
end

section
-- leanmerge: from Solcore.Frontend.CheckedDataExpressionOwnerProperties
/- A successful data-expression check supplies the original resolution and
lowering stages. Owner transport exposes those stages on both sides while the
checked Core expression and every mapped raw endpoint remain literal. -/
set_option autoImplicit false
namespace Solcore.Frontend

/-- A checked closed-data expression transports through every injective owner
map. Besides mapped checker and ID success, the witness records the original
and mapped resolution/lowering stages used by the complete endpoint image. -/
theorem ClosedSourceDataExpression.mapOwners_checked_core_evaluates_iff
    (mapping : Resolved.DeclarationId → Resolved.DeclarationId)
    (injective : Function.Injective mapping)
    {owner : Resolved.DeclarationId} {names : LocalNameTable}
    {context : Resolved.Context} {environment : Resolved.Environment}
    {initialStore : Core.Store} {source : Syntax.Expr} {core : Core.Expr}
    {type : Core.Ty} {actualValue : RuntimeValue} {actualFinal : List RuntimeValue}
    (fragment : ClosedSourceDataExpression source)
    (accepted : elaborateLocalExpression? names context source = some (core, type))
    (sameIds : Resolved.LocalScope.ids environment = Resolved.LocalScope.ids context) :
    elaborateLocalExpression?
        (LocalNameTable.mapIds (ownerLocalIdMap mapping) names)
        (Resolved.LocalScope.mapIds (ownerLocalIdMap mapping) context) source =
          some (core, type) ∧
      Resolved.LocalScope.ids
          (Resolved.LocalScope.mapIds (ownerLocalIdMap mapping) environment) =
        Resolved.LocalScope.ids
          (Resolved.LocalScope.mapIds (ownerLocalIdMap mapping) context) ∧
      ∃ resolved,
        ResolvesLocalExpression names source resolved ∧
        Resolved.Lowers (Resolved.LocalScope.ids environment) resolved core ∧
        ResolvesLocalExpression
          (LocalNameTable.mapIds (ownerLocalIdMap mapping) names) source
          (resolved.renameIds (ownerLocalIdMap mapping)) ∧
        Resolved.Lowers
          (Resolved.LocalScope.ids
            (Resolved.LocalScope.mapIds (ownerLocalIdMap mapping) environment))
          (resolved.renameIds (ownerLocalIdMap mapping)) core ∧
        (ClosedSourceExpressionEvaluates (mapping owner)
          (LocalNameTable.mapIds (ownerLocalIdMap mapping) names)
          ((Resolved.LocalScope.mapIds (ownerLocalIdMap mapping) environment).map
            (fun row => (row.1, RuntimeValue.ofCore row.2)))
          (initialStore.map RuntimeValue.ofCore) source actualValue actualFinal ↔
        ∃ value finalStore,
          actualValue = RuntimeValue.ofCore value ∧
          actualFinal = finalStore.map RuntimeValue.ofCore ∧
          Core.Evaluates (Resolved.LocalScope.values environment) initialStore
            core value finalStore) := by
  have mappedAccepted :=
    (elaborateLocalExpression?_mapIds (ownerLocalIdMap mapping)
      (ownerLocalIdMap_injective mapping injective) names context source).trans accepted
  have mappedSameIds : Resolved.LocalScope.ids
      (Resolved.LocalScope.mapIds (ownerLocalIdMap mapping) environment) =
      Resolved.LocalScope.ids
        (Resolved.LocalScope.mapIds (ownerLocalIdMap mapping) context) := by
    simpa only [Resolved.LocalScope.ids_mapIds] using
      congrArg (List.map (ownerLocalIdMap mapping)) sameIds
  obtain ⟨resolved, resolution, contextLowered, _⟩ :=
    elaborateLocalExpression?_sound accepted
  have environmentLowered : Resolved.Lowers
      (Resolved.LocalScope.ids environment) resolved core := by
    rw [sameIds]
    exact contextLowered
  have image := fragment.mapOwners_core_evaluates_iff mapping injective
    (owner := owner) (environment := environment) (initialStore := initialStore)
    (actualValue := actualValue) (actualFinal := actualFinal)
    resolution environmentLowered
  exact ⟨mappedAccepted, mappedSameIds, resolved, resolution, environmentLowered,
    image.1, image.2.1, image.2.2⟩

end Solcore.Frontend
end

section
-- leanmerge: from Solcore.Frontend.DataCalleeLambdaDepth
/- An independent original data-callee success selects the actual saved datum.
The explicit selection premise is not an unconditional callee decision. Caller
argument and fresh saved body retain every actual intermediate and final store. -/
set_option autoImplicit false
namespace Solcore.Frontend

/-- Sufficient depth using admitted data callee/argument syntax and the selected saved body. -/
def dataCalleeLambdaDepthBound (callee argument : Syntax.Expr) (body : Syntax.Block) : Nat :=
  max (closedSourceDataDepthBound callee)
    (max (closedSourceDataDepthBound argument) (closedSourceDataBodyDepthBound body)) + 1

/-- The independently selected callee fixes actual saved fields and callee store.
No argument or body success is assumed except inside the original whole endpoint. -/
theorem dataCalleeLambda_evaluates_at_depthBound
    {source callee argument : Syntax.Expr} {name : Syntax.Identifier} {body : Syntax.Block}
    (shape : SourceUnaryLambdaShape source name body)
    (calleeFragment : ClosedSourceDataExpression callee)
    (argumentFragment : ClosedSourceDataExpression argument)
    (bodyFragment : ClosedSourceDataBody body)
    {callerOwner savedOwner : Resolved.DeclarationId} {callerNames savedNames : LocalNameTable}
    {callerCaptured savedCaptured : Resolved.LocalScope RuntimeValue}
    {initialStore calleeStore finalStore : List RuntimeValue}
    (selected : ClosedSourceExpressionEvaluates callerOwner callerNames callerCaptured initialStore
      callee (.sourceClosure source savedOwner savedNames savedCaptured) calleeStore)
    {callSpan argumentsSpan : Syntax.SourceSpan} {actual : RuntimeValue}
    (original : ClosedSourceExpressionEvaluates callerOwner callerNames callerCaptured initialStore
      ⟨callSpan, .call callee ⟨argumentsSpan,[argument]⟩⟩ actual finalStore)
    {budget : Nat} (enough : dataCalleeLambdaDepthBound callee argument body ≤ budget) :
    evaluateClosedSourceExpression? budget callerOwner callerNames callerCaptured initialStore
      ⟨callSpan, .call callee ⟨argumentsSpan,[argument]⟩⟩ = some (actual,finalStore) := by
  unfold dataCalleeLambdaDepthBound at enough
  cases budget with
  | zero => omega
  | succ budget =>
    cases original with
    | creation impossible => cases impossible
    | call actualShape calleeEvaluation argumentEvaluation bodyEvaluation =>
      obtain ⟨sameCallee,sameStore⟩ := calleeEvaluation.deterministic selected
      cases sameCallee; cases sameStore
      obtain ⟨sameName,sameBody⟩ := Prod.mk.inj (Option.some.inj
        ((sourceUnaryLambdaShape?_iff.mpr actualShape).symm.trans
          (sourceUnaryLambdaShape?_iff.mpr shape)))
      cases sameName; cases sameBody
      have calleeRun := calleeFragment.evaluates_at_depthBound calleeEvaluation
        (by omega : closedSourceDataDepthBound callee ≤ budget)
      have argumentRun := argumentFragment.evaluates_at_depthBound argumentEvaluation
        (by omega : closedSourceDataDepthBound argument ≤ budget)
      have bodyRun := bodyFragment.evaluates_at_depthBound bodyEvaluation
        (by omega : closedSourceDataBodyDepthBound body ≤ budget)
      simpa only [evaluateClosedSourceExpression?,calleeRun,argumentRun,
        sourceUnaryLambdaShape?_iff.mpr shape,bind,Option.bind_some] using bodyRun

end Solcore.Frontend

/-!
## Consolidated module: `Solcore.Frontend.DataCalleeLambdaDepthDecisionProperties`
-/

/- Exact finite decisions under an independently successful data-callee selection.
No successful argument or body premise is required for these decision laws. -/
set_option autoImplicit false
namespace Solcore.Frontend

section
variable {source callee argument : Syntax.Expr} {name : Syntax.Identifier} {body : Syntax.Block}
variable (shape : SourceUnaryLambdaShape source name body)
variable (calleeFragment : ClosedSourceDataExpression callee)
variable (argumentFragment : ClosedSourceDataExpression argument)
variable (bodyFragment : ClosedSourceDataBody body)
variable {callerOwner savedOwner : Resolved.DeclarationId} {callerNames savedNames : LocalNameTable}
variable {callerCaptured savedCaptured : Resolved.LocalScope RuntimeValue}
variable {initialStore calleeStore : List RuntimeValue}
variable (selected : ClosedSourceExpressionEvaluates callerOwner callerNames callerCaptured initialStore
  callee (.sourceClosure source savedOwner savedNames savedCaptured) calleeStore)
variable {callSpan argumentsSpan : Syntax.SourceSpan}
include shape calleeFragment argumentFragment bodyFragment selected

/-- A sufficiently deep independently selected data-callee call returns exactly each original full endpoint. -/
theorem dataCalleeLambda_evaluate_at_depthBound_iff
    {actual : RuntimeValue} {finalStore : List RuntimeValue} {budget : Nat}
    (enough : dataCalleeLambdaDepthBound callee argument body ≤ budget) :
    evaluateClosedSourceExpression? budget callerOwner callerNames callerCaptured initialStore
      ⟨callSpan, .call callee ⟨argumentsSpan, [argument]⟩⟩ = some (actual, finalStore) ↔
    ClosedSourceExpressionEvaluates callerOwner callerNames callerCaptured initialStore
      ⟨callSpan, .call callee ⟨argumentsSpan, [argument]⟩⟩ actual finalStore :=
  ⟨evaluateClosedSourceExpression?_sound,
    fun original => dataCalleeLambda_evaluates_at_depthBound shape calleeFragment argumentFragment bodyFragment selected original enough⟩

/-- Whole Option stability includes argument and selected-body failure. -/
theorem dataCalleeLambda_evaluate_depth_stable
    {budget : Nat} (enough : dataCalleeLambdaDepthBound callee argument body ≤ budget) :
    evaluateClosedSourceExpression? budget callerOwner callerNames callerCaptured initialStore
      ⟨callSpan, .call callee ⟨argumentsSpan, [argument]⟩⟩ =
    evaluateClosedSourceExpression? (dataCalleeLambdaDepthBound callee argument body)
      callerOwner callerNames callerCaptured initialStore ⟨callSpan, .call callee ⟨argumentsSpan, [argument]⟩⟩ := by
  cases low : evaluateClosedSourceExpression? (dataCalleeLambdaDepthBound callee argument body)
      callerOwner callerNames callerCaptured initialStore ⟨callSpan, .call callee ⟨argumentsSpan, [argument]⟩⟩ with
  | none =>
    cases high : evaluateClosedSourceExpression? budget callerOwner callerNames callerCaptured initialStore
        ⟨callSpan, .call callee ⟨argumentsSpan, [argument]⟩⟩ with
    | none => rfl
    | some endpoint =>
      obtain ⟨actual, finalStore⟩ := endpoint
      have atBound := dataCalleeLambda_evaluates_at_depthBound shape calleeFragment argumentFragment bodyFragment selected
        (evaluateClosedSourceExpression?_sound high) (Nat.le_refl _)
      rw [low] at atBound
      cases atBound
  | some endpoint =>
    obtain ⟨actual, finalStore⟩ := endpoint
    exact evaluateClosedSourceExpression?_monotone enough low

/-- Sufficient-depth None excludes every original successful call endpoint,
without classifying its cause or assuming empty lexical inputs. -/
theorem dataCalleeLambda_evaluate_depth_none_iff
    {budget : Nat} (enough : dataCalleeLambdaDepthBound callee argument body ≤ budget) :
    evaluateClosedSourceExpression? budget callerOwner callerNames callerCaptured initialStore
      ⟨callSpan, .call callee ⟨argumentsSpan, [argument]⟩⟩ = none ↔
    ∀ actual finalStore, ¬ ClosedSourceExpressionEvaluates callerOwner callerNames callerCaptured initialStore
      ⟨callSpan, .call callee ⟨argumentsSpan, [argument]⟩⟩ actual finalStore := by
  constructor
  · intro absent actual finalStore original
    have accepted := dataCalleeLambda_evaluates_at_depthBound shape calleeFragment argumentFragment bodyFragment selected original enough
    rw [absent] at accepted
    cases accepted
  · intro impossible
    cases ran : evaluateClosedSourceExpression? budget callerOwner callerNames callerCaptured initialStore
        ⟨callSpan, .call callee ⟨argumentsSpan, [argument]⟩⟩ with
    | none => rfl
    | some endpoint =>
      obtain ⟨actual, finalStore⟩ := endpoint
      exact False.elim (impossible actual finalStore (evaluateClosedSourceExpression?_sound ran))

/-- One search bounded by the actual saved syntax decides whether any budget has a successful
endpoint for this independently selected data-callee application, not for arbitrary callees. -/
theorem dataCalleeLambda_evaluate_depth_none_iff_all_budgets :
    evaluateClosedSourceExpression? (dataCalleeLambdaDepthBound callee argument body)
      callerOwner callerNames callerCaptured initialStore ⟨callSpan, .call callee ⟨argumentsSpan, [argument]⟩⟩ = none ↔
    ∀ budget, evaluateClosedSourceExpression? budget callerOwner callerNames callerCaptured initialStore
      ⟨callSpan, .call callee ⟨argumentsSpan, [argument]⟩⟩ = none := by
  constructor
  · intro absent budget
    have impossible := (dataCalleeLambda_evaluate_depth_none_iff shape calleeFragment argumentFragment bodyFragment selected
      (Nat.le_refl _)).mp absent
    cases ran : evaluateClosedSourceExpression? budget callerOwner callerNames callerCaptured initialStore
        ⟨callSpan, .call callee ⟨argumentsSpan, [argument]⟩⟩ with
    | none => rfl
    | some endpoint =>
      obtain ⟨actual, finalStore⟩ := endpoint
      exact False.elim (impossible actual finalStore (evaluateClosedSourceExpression?_sound ran))
  · intro absent
    exact absent _

end
end Solcore.Frontend
end

section
-- leanmerge: from Solcore.Frontend.DirectDataLambdaDepth
/- A direct unary lambda creates its saved datum at depth one. The bound applies
only with the independent lambda shape and data argument/body gates. Captured
fields and actual intermediate/final stores remain literal, without typing. -/
set_option autoImplicit false
namespace Solcore.Frontend

/-- A source-only sufficient depth for direct unary application, not saved calls. -/
def directDataLambdaDepthBound (argument : Syntax.Expr) (body : Syntax.Block) : Nat :=
  max 1 (max (closedSourceDataDepthBound argument) (closedSourceDataBodyDepthBound body)) + 1

private theorem creation_at_positive_depth
    {source : Syntax.Expr} {name : Syntax.Identifier} {body : Syntax.Block}
    (shape : SourceUnaryLambdaShape source name body)
    (owner : Resolved.DeclarationId) (names : LocalNameTable)
    (captured : Resolved.LocalScope RuntimeValue) (store : List RuntimeValue)
    {budget : Nat} (positive : 0 < budget) :
    evaluateClosedSourceExpression? budget owner names captured store source =
      some (.sourceClosure source owner names captured, store) := by
  cases budget with
  | zero => omega
  | succ budget =>
      cases shape <;> simp only [evaluateClosedSourceExpression?, sourceUnaryLambdaShape?,
        bind, Option.bind_some, pure, Pure.pure]

/-- Every original direct application endpoint is found at the computable upper
depth under arbitrary caller rows, mixed values and complete actual stores. -/
theorem directDataLambda_evaluates_at_depthBound
    {source argument : Syntax.Expr} {name : Syntax.Identifier} {body : Syntax.Block}
    (shape : SourceUnaryLambdaShape source name body)
    (argumentFragment : ClosedSourceDataExpression argument)
    (bodyFragment : ClosedSourceDataBody body)
    {owner : Resolved.DeclarationId} {names : LocalNameTable}
    {captured : Resolved.LocalScope RuntimeValue} {initialStore finalStore : List RuntimeValue}
    {callSpan argumentsSpan : Syntax.SourceSpan} {actual : RuntimeValue}
    (original : ClosedSourceExpressionEvaluates owner names captured initialStore
      ⟨callSpan, .call source ⟨argumentsSpan, [argument]⟩⟩ actual finalStore)
    {budget : Nat} (enough : directDataLambdaDepthBound argument body ≤ budget) :
    evaluateClosedSourceExpression? budget owner names captured initialStore
      ⟨callSpan, .call source ⟨argumentsSpan, [argument]⟩⟩ = some (actual, finalStore) := by
  have created : ClosedSourceExpressionEvaluates owner names captured initialStore
      source (.sourceClosure source owner names captured) initialStore := .creation shape
  unfold directDataLambdaDepthBound at enough
  cases budget with
  | zero => omega
  | succ budget =>
    cases original with
    | creation impossible => cases impossible
    | call actualShape calleeEvaluation argumentEvaluation bodyEvaluation =>
      obtain ⟨sameCallee, sameStore⟩ := calleeEvaluation.deterministic created
      cases sameCallee; cases sameStore
      obtain ⟨sameName, sameBody⟩ := Prod.mk.inj (Option.some.inj
        ((sourceUnaryLambdaShape?_iff.mpr actualShape).symm.trans
          (sourceUnaryLambdaShape?_iff.mpr shape)))
      cases sameName; cases sameBody
      have calleeRun := creation_at_positive_depth shape owner names captured initialStore
        (by omega : 0 < budget)
      have argumentRun := argumentFragment.evaluates_at_depthBound argumentEvaluation
        (by omega : closedSourceDataDepthBound argument ≤ budget)
      have bodyRun := bodyFragment.evaluates_at_depthBound bodyEvaluation
        (by omega : closedSourceDataBodyDepthBound body ≤ budget)
      simpa only [evaluateClosedSourceExpression?, calleeRun, argumentRun,
        sourceUnaryLambdaShape?_iff.mpr shape, bind, Option.bind_some] using bodyRun

end Solcore.Frontend

/-!
## Consolidated module: `Solcore.Frontend.DirectDataLambdaDepthDecisionProperties`
-/

/- Exact finite decisions for direct unary syntax with separate data gates.
No successful argument or body premise is required for these decision laws. -/
set_option autoImplicit false
namespace Solcore.Frontend

section
variable {source argument : Syntax.Expr} {name : Syntax.Identifier} {body : Syntax.Block}
variable (shape : SourceUnaryLambdaShape source name body)
variable (argumentFragment : ClosedSourceDataExpression argument)
variable (bodyFragment : ClosedSourceDataBody body)
variable {owner : Resolved.DeclarationId} {names : LocalNameTable}
variable {captured : Resolved.LocalScope RuntimeValue} {initialStore : List RuntimeValue}
variable {callSpan argumentsSpan : Syntax.SourceSpan}
include shape argumentFragment bodyFragment

/-- A sufficiently deep direct call returns exactly each original full endpoint. -/
theorem directDataLambda_evaluate_at_depthBound_iff
    {actual : RuntimeValue} {finalStore : List RuntimeValue} {budget : Nat}
    (enough : directDataLambdaDepthBound argument body ≤ budget) :
    evaluateClosedSourceExpression? budget owner names captured initialStore
      ⟨callSpan, .call source ⟨argumentsSpan, [argument]⟩⟩ = some (actual, finalStore) ↔
    ClosedSourceExpressionEvaluates owner names captured initialStore
      ⟨callSpan, .call source ⟨argumentsSpan, [argument]⟩⟩ actual finalStore :=
  ⟨evaluateClosedSourceExpression?_sound,
    fun original => directDataLambda_evaluates_at_depthBound shape argumentFragment bodyFragment original enough⟩

/-- Whole Option stability includes argument and selected-body failure. -/
theorem directDataLambda_evaluate_depth_stable
    {budget : Nat} (enough : directDataLambdaDepthBound argument body ≤ budget) :
    evaluateClosedSourceExpression? budget owner names captured initialStore
      ⟨callSpan, .call source ⟨argumentsSpan, [argument]⟩⟩ =
    evaluateClosedSourceExpression? (directDataLambdaDepthBound argument body)
      owner names captured initialStore ⟨callSpan, .call source ⟨argumentsSpan, [argument]⟩⟩ := by
  cases low : evaluateClosedSourceExpression? (directDataLambdaDepthBound argument body)
      owner names captured initialStore ⟨callSpan, .call source ⟨argumentsSpan, [argument]⟩⟩ with
  | none =>
    cases high : evaluateClosedSourceExpression? budget owner names captured initialStore
        ⟨callSpan, .call source ⟨argumentsSpan, [argument]⟩⟩ with
    | none => rfl
    | some endpoint =>
      obtain ⟨actual, finalStore⟩ := endpoint
      have atBound := directDataLambda_evaluates_at_depthBound shape argumentFragment bodyFragment
        (evaluateClosedSourceExpression?_sound high) (Nat.le_refl _)
      rw [low] at atBound
      cases atBound
  | some endpoint =>
    obtain ⟨actual, finalStore⟩ := endpoint
    exact evaluateClosedSourceExpression?_monotone enough low

/-- Sufficient-depth None excludes every original successful call endpoint,
without classifying its cause or assuming empty lexical inputs. -/
theorem directDataLambda_evaluate_depth_none_iff
    {budget : Nat} (enough : directDataLambdaDepthBound argument body ≤ budget) :
    evaluateClosedSourceExpression? budget owner names captured initialStore
      ⟨callSpan, .call source ⟨argumentsSpan, [argument]⟩⟩ = none ↔
    ∀ actual finalStore, ¬ ClosedSourceExpressionEvaluates owner names captured initialStore
      ⟨callSpan, .call source ⟨argumentsSpan, [argument]⟩⟩ actual finalStore := by
  constructor
  · intro absent actual finalStore original
    have found := directDataLambda_evaluates_at_depthBound shape argumentFragment bodyFragment original enough
    rw [absent] at found
    cases found
  · intro impossible
    cases ran : evaluateClosedSourceExpression? budget owner names captured initialStore
        ⟨callSpan, .call source ⟨argumentsSpan, [argument]⟩⟩ with
    | none => rfl
    | some endpoint =>
      obtain ⟨actual, finalStore⟩ := endpoint
      exact False.elim (impossible actual finalStore (evaluateClosedSourceExpression?_sound ran))

/-- One syntax-bounded search decides whether any budget can return a successful
endpoint for this direct application, not for arbitrary saved callees. -/
theorem directDataLambda_evaluate_depth_none_iff_all_budgets :
    evaluateClosedSourceExpression? (directDataLambdaDepthBound argument body)
      owner names captured initialStore ⟨callSpan, .call source ⟨argumentsSpan, [argument]⟩⟩ = none ↔
    ∀ budget, evaluateClosedSourceExpression? budget owner names captured initialStore
      ⟨callSpan, .call source ⟨argumentsSpan, [argument]⟩⟩ = none := by
  constructor
  · intro absent budget
    have impossible := (directDataLambda_evaluate_depth_none_iff shape argumentFragment bodyFragment
      (Nat.le_refl _)).mp absent
    cases ran : evaluateClosedSourceExpression? budget owner names captured initialStore
        ⟨callSpan, .call source ⟨argumentsSpan, [argument]⟩⟩ with
    | none => rfl
    | some endpoint =>
      obtain ⟨actual, finalStore⟩ := endpoint
      exact False.elim (impossible actual finalStore (evaluateClosedSourceExpression?_sound ran))
  · intro absent
    exact absent _

end
end Solcore.Frontend
end

section
-- leanmerge: from Solcore.Frontend.SavedDataLambdaDepth
/- Reference lookup fixes the full saved datum. This bound includes the actual
saved source body, not only caller syntax. Argument evaluation uses caller rows;
body evaluation uses freshly extended saved rows and the actual current store. -/
set_option autoImplicit false
namespace Solcore.Frontend

/-- Sufficient reference-call depth given the actual saved body, not caller-only syntax. -/
def savedDataLambdaDepthBound (argument : Syntax.Expr) (body : Syntax.Block) : Nat :=
  max 1 (max (closedSourceDataDepthBound argument) (closedSourceDataBodyDepthBound body)) + 1

/-- First-match lookup and saved-body data admission bound every original full
endpoint without identifying caller and saved owners, rows, captures or stores. -/
theorem savedDataLambda_evaluates_at_depthBound
    {source argument : Syntax.Expr} {name calleeName : Syntax.Identifier} {body : Syntax.Block}
    (shape : SourceUnaryLambdaShape source name body)
    (argumentFragment : ClosedSourceDataExpression argument)
    (bodyFragment : ClosedSourceDataBody body)
    {callerOwner savedOwner : Resolved.DeclarationId} {callerNames savedNames : LocalNameTable}
    {callerCaptured savedCaptured : Resolved.LocalScope RuntimeValue}
    {calleeId : Resolved.LocalId}
    (named : LocalNameTable.Lookup callerNames calleeName.value calleeId)
    (found : Resolved.LocalScope.Lookup callerCaptured calleeId
      (.sourceClosure source savedOwner savedNames savedCaptured))
    {initialStore finalStore : List RuntimeValue}
    {callSpan calleeSpan argumentsSpan : Syntax.SourceSpan} {actual : RuntimeValue}
    (original : ClosedSourceExpressionEvaluates callerOwner callerNames callerCaptured initialStore
      ⟨callSpan, .call ⟨calleeSpan,.identifier calleeName⟩ ⟨argumentsSpan,[argument]⟩⟩ actual finalStore)
    {budget : Nat} (enough : savedDataLambdaDepthBound argument body ≤ budget) :
    evaluateClosedSourceExpression? budget callerOwner callerNames callerCaptured initialStore
      ⟨callSpan, .call ⟨calleeSpan,.identifier calleeName⟩ ⟨argumentsSpan,[argument]⟩⟩ =
        some (actual,finalStore) := by
  have picked : ClosedSourceExpressionEvaluates callerOwner callerNames callerCaptured initialStore
      ⟨calleeSpan,.identifier calleeName⟩ (.sourceClosure source savedOwner savedNames savedCaptured)
      initialStore := .reference named found
  unfold savedDataLambdaDepthBound at enough
  cases budget with
  | zero => omega
  | succ budget =>
    cases original with
    | creation impossible => cases impossible
    | call actualShape calleeEvaluation argumentEvaluation bodyEvaluation =>
      obtain ⟨sameCallee,sameStore⟩ := calleeEvaluation.deterministic picked
      cases sameCallee; cases sameStore
      obtain ⟨sameName,sameBody⟩ := Prod.mk.inj (Option.some.inj
        ((sourceUnaryLambdaShape?_iff.mpr actualShape).symm.trans
          (sourceUnaryLambdaShape?_iff.mpr shape)))
      cases sameName; cases sameBody
      have argumentRun := argumentFragment.evaluates_at_depthBound argumentEvaluation
        (by omega : closedSourceDataDepthBound argument ≤ budget)
      have bodyRun := bodyFragment.evaluates_at_depthBound bodyEvaluation
        (by omega : closedSourceDataBodyDepthBound body ≤ budget)
      have calleeRun : evaluateClosedSourceExpression? budget callerOwner callerNames callerCaptured
          initialStore ⟨calleeSpan,.identifier calleeName⟩ =
            some (.sourceClosure source savedOwner savedNames savedCaptured,initialStore) := by
        cases budget with
        | zero => omega
        | succ budget =>
          simp only [evaluateClosedSourceExpression?,LocalNameTable.lookup?_iff.mpr named,
            Resolved.LocalScope.lookup?_iff.mpr found,bind,Option.bind_some,pure,Pure.pure]
      simpa only [evaluateClosedSourceExpression?,calleeRun,argumentRun,
        sourceUnaryLambdaShape?_iff.mpr shape,bind,Option.bind_some] using bodyRun

end Solcore.Frontend

/-!
## Consolidated module: `Solcore.Frontend.SavedDataLambdaDepthDecisionProperties`
-/

/- Exact finite decisions for lookup-known saved unary syntax with separate data gates.
No successful argument or body premise is required for these decision laws. -/
set_option autoImplicit false
namespace Solcore.Frontend

section
variable {source argument : Syntax.Expr} {name calleeName : Syntax.Identifier} {body : Syntax.Block}
variable (shape : SourceUnaryLambdaShape source name body)
variable (argumentFragment : ClosedSourceDataExpression argument)
variable (bodyFragment : ClosedSourceDataBody body)
variable {callerOwner savedOwner : Resolved.DeclarationId} {callerNames savedNames : LocalNameTable}
variable {callerCaptured savedCaptured : Resolved.LocalScope RuntimeValue} {calleeId : Resolved.LocalId}
variable (named : LocalNameTable.Lookup callerNames calleeName.value calleeId)
variable (found : Resolved.LocalScope.Lookup callerCaptured calleeId
  (.sourceClosure source savedOwner savedNames savedCaptured))
variable {initialStore : List RuntimeValue}
variable {callSpan calleeSpan argumentsSpan : Syntax.SourceSpan}
include shape argumentFragment bodyFragment named found

/-- A sufficiently deep lookup-known saved call returns exactly each original full endpoint. -/
theorem savedDataLambda_evaluate_at_depthBound_iff
    {actual : RuntimeValue} {finalStore : List RuntimeValue} {budget : Nat}
    (enough : savedDataLambdaDepthBound argument body ≤ budget) :
    evaluateClosedSourceExpression? budget callerOwner callerNames callerCaptured initialStore
      ⟨callSpan, .call ⟨calleeSpan,.identifier calleeName⟩ ⟨argumentsSpan, [argument]⟩⟩ = some (actual, finalStore) ↔
    ClosedSourceExpressionEvaluates callerOwner callerNames callerCaptured initialStore
      ⟨callSpan, .call ⟨calleeSpan,.identifier calleeName⟩ ⟨argumentsSpan, [argument]⟩⟩ actual finalStore :=
  ⟨evaluateClosedSourceExpression?_sound,
    fun original => savedDataLambda_evaluates_at_depthBound shape argumentFragment bodyFragment named found original enough⟩

/-- Whole Option stability includes argument and selected-body failure. -/
theorem savedDataLambda_evaluate_depth_stable
    {budget : Nat} (enough : savedDataLambdaDepthBound argument body ≤ budget) :
    evaluateClosedSourceExpression? budget callerOwner callerNames callerCaptured initialStore
      ⟨callSpan, .call ⟨calleeSpan,.identifier calleeName⟩ ⟨argumentsSpan, [argument]⟩⟩ =
    evaluateClosedSourceExpression? (savedDataLambdaDepthBound argument body)
      callerOwner callerNames callerCaptured initialStore ⟨callSpan, .call ⟨calleeSpan,.identifier calleeName⟩ ⟨argumentsSpan, [argument]⟩⟩ := by
  cases low : evaluateClosedSourceExpression? (savedDataLambdaDepthBound argument body)
      callerOwner callerNames callerCaptured initialStore ⟨callSpan, .call ⟨calleeSpan,.identifier calleeName⟩ ⟨argumentsSpan, [argument]⟩⟩ with
  | none =>
    cases high : evaluateClosedSourceExpression? budget callerOwner callerNames callerCaptured initialStore
        ⟨callSpan, .call ⟨calleeSpan,.identifier calleeName⟩ ⟨argumentsSpan, [argument]⟩⟩ with
    | none => rfl
    | some endpoint =>
      obtain ⟨actual, finalStore⟩ := endpoint
      have atBound := savedDataLambda_evaluates_at_depthBound shape argumentFragment bodyFragment named found
        (evaluateClosedSourceExpression?_sound high) (Nat.le_refl _)
      rw [low] at atBound
      cases atBound
  | some endpoint =>
    obtain ⟨actual, finalStore⟩ := endpoint
    exact evaluateClosedSourceExpression?_monotone enough low

/-- Sufficient-depth None excludes every original successful call endpoint,
without classifying its cause or assuming empty lexical inputs. -/
theorem savedDataLambda_evaluate_depth_none_iff
    {budget : Nat} (enough : savedDataLambdaDepthBound argument body ≤ budget) :
    evaluateClosedSourceExpression? budget callerOwner callerNames callerCaptured initialStore
      ⟨callSpan, .call ⟨calleeSpan,.identifier calleeName⟩ ⟨argumentsSpan, [argument]⟩⟩ = none ↔
    ∀ actual finalStore, ¬ ClosedSourceExpressionEvaluates callerOwner callerNames callerCaptured initialStore
      ⟨callSpan, .call ⟨calleeSpan,.identifier calleeName⟩ ⟨argumentsSpan, [argument]⟩⟩ actual finalStore := by
  constructor
  · intro absent actual finalStore original
    have accepted := savedDataLambda_evaluates_at_depthBound shape argumentFragment bodyFragment named found original enough
    rw [absent] at accepted
    cases accepted
  · intro impossible
    cases ran : evaluateClosedSourceExpression? budget callerOwner callerNames callerCaptured initialStore
        ⟨callSpan, .call ⟨calleeSpan,.identifier calleeName⟩ ⟨argumentsSpan, [argument]⟩⟩ with
    | none => rfl
    | some endpoint =>
      obtain ⟨actual, finalStore⟩ := endpoint
      exact False.elim (impossible actual finalStore (evaluateClosedSourceExpression?_sound ran))

/-- One search bounded by the actual saved syntax decides whether any budget has a successful
endpoint for this lookup-known saved application, not for arbitrary callees. -/
theorem savedDataLambda_evaluate_depth_none_iff_all_budgets :
    evaluateClosedSourceExpression? (savedDataLambdaDepthBound argument body)
      callerOwner callerNames callerCaptured initialStore ⟨callSpan, .call ⟨calleeSpan,.identifier calleeName⟩ ⟨argumentsSpan, [argument]⟩⟩ = none ↔
    ∀ budget, evaluateClosedSourceExpression? budget callerOwner callerNames callerCaptured initialStore
      ⟨callSpan, .call ⟨calleeSpan,.identifier calleeName⟩ ⟨argumentsSpan, [argument]⟩⟩ = none := by
  constructor
  · intro absent budget
    have impossible := (savedDataLambda_evaluate_depth_none_iff shape argumentFragment bodyFragment named found
      (Nat.le_refl _)).mp absent
    cases ran : evaluateClosedSourceExpression? budget callerOwner callerNames callerCaptured initialStore
        ⟨callSpan, .call ⟨calleeSpan,.identifier calleeName⟩ ⟨argumentsSpan, [argument]⟩⟩ with
    | none => rfl
    | some endpoint =>
      obtain ⟨actual, finalStore⟩ := endpoint
      exact False.elim (impossible actual finalStore (evaluateClosedSourceExpression?_sound ran))
  · intro absent
    exact absent _

end
end Solcore.Frontend
end

section
-- leanmerge: from Solcore.Frontend.SelfApplication
/-! Self-application non-return results. -/

/-!
## Consolidated module: `Solcore.Frontend.SelfApplicationNonreturnProperties`
-/

/- Exact re-entry of a saved closure applied to itself. The runtime value is
finite: it captures the original rows, never its own fresh invocation binding.
This is a raw-source non-return boundary, not a runtime fault or typing claim. -/
set_option autoImplicit false
namespace Solcore.Frontend

/-- A return of two references with the parameter's spelling, preserving all spans. -/
inductive SourceSelfApplicationBody : Syntax.Block → Syntax.Identifier → Prop where
  | returning {blockSpan returnSpan callSpan argumentsSpan calleeSpan argumentSpan : Syntax.SourceSpan}
      {calleeName argumentName name : Syntax.Identifier}
      (callee : calleeName.value = name.value) (argument : argumentName.value = name.value) :
      SourceSelfApplicationBody
        ⟨blockSpan,[⟨returnSpan,.returnStmt (some
          ⟨callSpan,.call ⟨calleeSpan,.identifier calleeName⟩
            ⟨argumentsSpan,[⟨argumentSpan,.identifier argumentName⟩]⟩⟩)⟩]⟩ name

/-- Using the bound closure as both inputs enters its actual saved body, even when the
calling body's spans, parameter spelling and lexical fields are different. -/
theorem selfApplicationBody_calls_bound_closure
    {source : Syntax.Expr} {name parameter : Syntax.Identifier} {body invokedBody : Syntax.Block}
    (shape : SourceUnaryLambdaShape source name body) (self : SourceSelfApplicationBody invokedBody parameter)
    (owner savedOwner : Resolved.DeclarationId) (names savedNames : LocalNameTable)
    (captured savedCaptured : Resolved.LocalScope RuntimeValue) (store : List RuntimeValue) (n : Nat) :
    evaluateClosedSourceBody? (n+3) owner
      ((parameter.value,Resolved.freshLocalId owner (names.map Prod.snd))::names)
      ((Resolved.freshLocalId owner (names.map Prod.snd),.sourceClosure source savedOwner savedNames savedCaptured)::captured)
      store invokedBody =
    evaluateClosedSourceBody? (n+1) savedOwner
      ((name.value,Resolved.freshLocalId savedOwner (savedNames.map Prod.snd))::savedNames)
      ((Resolved.freshLocalId savedOwner (savedNames.map Prod.snd),.sourceClosure source savedOwner savedNames savedCaptured)::savedCaptured)
      store body := by
  cases self with
  | returning callee argument =>
    simp only [evaluateClosedSourceBody?,evaluateClosedSourceExpression?,LocalNameTable.lookup?,
      Resolved.LocalScope.lookup?,callee,argument,↓reduceIte,bind,Option.bind_some,pure,
      sourceUnaryLambdaShape?_iff.mpr shape]

section
variable {source : Syntax.Expr} {name : Syntax.Identifier} {body : Syntax.Block}
variable (shape : SourceUnaryLambdaShape source name body)
variable (self : SourceSelfApplicationBody body name)
variable (owner : Resolved.DeclarationId) (names : LocalNameTable)
variable (captured : Resolved.LocalScope RuntimeValue) (store : List RuntimeValue)
include shape self

/-- Two additional levels re-enter the same body with exactly the same saved fields. -/
theorem selfApplicationBody_depth_reentry (n : Nat) :
    evaluateClosedSourceBody? (n+3) owner
      ((name.value,Resolved.freshLocalId owner (names.map Prod.snd))::names)
      ((Resolved.freshLocalId owner (names.map Prod.snd),.sourceClosure source owner names captured)::captured)
      store body =
    evaluateClosedSourceBody? (n+1) owner
      ((name.value,Resolved.freshLocalId owner (names.map Prod.snd))::names)
      ((Resolved.freshLocalId owner (names.map Prod.snd),.sourceClosure source owner names captured)::captured)
      store body := by
  exact selfApplicationBody_calls_bound_closure shape self owner owner names names captured captured store n

/-- No finite depth returns from this exact saved self-application body. -/
theorem selfApplicationBody_none (budget : Nat) :
    evaluateClosedSourceBody? budget owner
      ((name.value,Resolved.freshLocalId owner (names.map Prod.snd))::names)
      ((Resolved.freshLocalId owner (names.map Prod.snd),.sourceClosure source owner names captured)::captured)
      store body = none := by
  induction budget using Nat.strongRecOn with
  | ind budget ih =>
    cases budget with
    | zero => simp [evaluateClosedSourceBody?]
    | succ k =>
      cases k with
      | zero => cases self <;> simp [evaluateClosedSourceBody?,evaluateClosedSourceExpression?]
      | succ k =>
        cases k with
        | zero => cases self <;> simp [evaluateClosedSourceBody?,evaluateClosedSourceExpression?]
        | succ k =>
          rw [selfApplicationBody_depth_reentry shape self owner names captured store k]
          exact ih (k+1) (by omega)

/-- An original successful derivation would give a finite run, contradicting re-entry. -/
theorem selfApplicationBody_no_original (value : RuntimeValue) (finalStore : List RuntimeValue) :
    ¬ ClosedSourceBodyEvaluates owner
      ((name.value,Resolved.freshLocalId owner (names.map Prod.snd))::names)
      ((Resolved.freshLocalId owner (names.map Prod.snd),.sourceClosure source owner names captured)::captured)
      store body value finalStore := by
  intro original
  obtain ⟨budget,ran⟩ := evaluateClosedSourceBody?_eventually_complete original
  have success := ran budget (Nat.le_refl budget)
  rw [selfApplicationBody_none shape self owner names captured store budget] at success
  cases success

end

/-- A different self-calling body also cannot return when bound to this looping closure. -/
theorem selfApplicationBody_boundSelf_none
    {source : Syntax.Expr} {name parameter : Syntax.Identifier} {body invokedBody : Syntax.Block}
    (shape : SourceUnaryLambdaShape source name body) (self : SourceSelfApplicationBody body name)
    (invokedSelf : SourceSelfApplicationBody invokedBody parameter)
    (owner savedOwner : Resolved.DeclarationId) (names savedNames : LocalNameTable)
    (captured savedCaptured : Resolved.LocalScope RuntimeValue) (store : List RuntimeValue) (budget : Nat) :
    evaluateClosedSourceBody? budget owner
      ((parameter.value,Resolved.freshLocalId owner (names.map Prod.snd))::names)
      ((Resolved.freshLocalId owner (names.map Prod.snd),.sourceClosure source savedOwner savedNames savedCaptured)::captured)
      store invokedBody = none := by
  cases budget with
  | zero => simp [evaluateClosedSourceBody?]
  | succ n =>
    cases n with
    | zero => cases invokedSelf <;> simp [evaluateClosedSourceBody?,evaluateClosedSourceExpression?]
    | succ n =>
      cases n with
      | zero => cases invokedSelf <;> simp [evaluateClosedSourceBody?,evaluateClosedSourceExpression?]
      | succ n =>
        rw [selfApplicationBody_calls_bound_closure shape invokedSelf owner savedOwner names savedNames
          captured savedCaptured store n]
        exact selfApplicationBody_none shape self savedOwner savedNames savedCaptured store (n+1)

end Solcore.Frontend

/-!
## Consolidated module: `Solcore.Frontend.SelfApplicationCallNonreturnProperties`
-/

/- Actual successful references select the same finite saved closure. The body
re-enters its saved scope; unrelated caller rows never become its captured rows. -/
set_option autoImplicit false
namespace Solcore.Frontend

section
variable {source : Syntax.Expr} {name : Syntax.Identifier} {body : Syntax.Block}
variable (shape : SourceUnaryLambdaShape source name body)
variable (self : SourceSelfApplicationBody body name)
variable (savedOwner : Resolved.DeclarationId) (savedNames : LocalNameTable)
variable (savedCaptured : Resolved.LocalScope RuntimeValue)
variable (callerOwner : Resolved.DeclarationId) (callerNames : LocalNameTable)
variable (callerCaptured : Resolved.LocalScope RuntimeValue) (store : List RuntimeValue)
variable (callSpan argumentsSpan calleeSpan argumentSpan : Syntax.SourceSpan)
variable (calleeName argumentName : Syntax.Identifier) (calleeId argumentId : Resolved.LocalId)
variable (calleeNamed : LocalNameTable.Lookup callerNames calleeName.value calleeId)
variable (calleeFound : Resolved.LocalScope.Lookup callerCaptured calleeId
  (.sourceClosure source savedOwner savedNames savedCaptured))
variable (argumentNamed : LocalNameTable.Lookup callerNames argumentName.value argumentId)
variable (argumentFound : Resolved.LocalScope.Lookup callerCaptured argumentId
  (.sourceClosure source savedOwner savedNames savedCaptured))
include shape self calleeNamed calleeFound argumentNamed argumentFound

/-- Both input references may succeed while the self-application has no finite result. -/
theorem savedSelfApplication_none (budget : Nat) :
    evaluateClosedSourceExpression? budget callerOwner callerNames callerCaptured store
      ⟨callSpan,.call ⟨calleeSpan,.identifier calleeName⟩
        ⟨argumentsSpan,[⟨argumentSpan,.identifier argumentName⟩]⟩⟩ = none := by
  cases budget with
  | zero => simp [evaluateClosedSourceExpression?]
  | succ n =>
    cases n with
    | zero => simp [evaluateClosedSourceExpression?]
    | succ n =>
      simp only [evaluateClosedSourceExpression?,LocalNameTable.lookup?_iff.mpr calleeNamed,
        LocalNameTable.lookup?_iff.mpr argumentNamed,Resolved.LocalScope.lookup?_iff.mpr calleeFound,
        Resolved.LocalScope.lookup?_iff.mpr argumentFound,bind,Option.bind_some,pure,
        sourceUnaryLambdaShape?_iff.mpr shape,
        selfApplicationBody_none shape self savedOwner savedNames savedCaptured store (n+1)]

/-- No finite original derivation can evaluate this exact saved self-application. -/
theorem savedSelfApplication_no_original (value : RuntimeValue) (finalStore : List RuntimeValue) :
    ¬ ClosedSourceExpressionEvaluates callerOwner callerNames callerCaptured store
      ⟨callSpan,.call ⟨calleeSpan,.identifier calleeName⟩
        ⟨argumentsSpan,[⟨argumentSpan,.identifier argumentName⟩]⟩⟩ value finalStore := by
  intro original
  obtain ⟨budget,ran⟩ := evaluateClosedSourceExpression?_eventually_complete original
  have success := ran budget (Nat.le_refl budget)
  rw [savedSelfApplication_none shape self savedOwner savedNames savedCaptured callerOwner callerNames
    callerCaptured store callSpan argumentsSpan calleeSpan argumentSpan calleeName argumentName
    calleeId argumentId calleeNamed calleeFound argumentNamed argumentFound budget] at success
  cases success

end

/-- Independently created closures with self-calling bodies do not return, even at distinct source occurrences. -/
theorem directSelfApplication_none
    {left right : Syntax.Expr} {leftName rightName : Syntax.Identifier} {leftBody rightBody : Syntax.Block}
    (leftShape : SourceUnaryLambdaShape left leftName leftBody) (leftSelf : SourceSelfApplicationBody leftBody leftName)
    (rightShape : SourceUnaryLambdaShape right rightName rightBody) (rightSelf : SourceSelfApplicationBody rightBody rightName)
    (owner : Resolved.DeclarationId) (names : LocalNameTable) (captured : Resolved.LocalScope RuntimeValue)
    (store : List RuntimeValue) (callSpan argumentsSpan : Syntax.SourceSpan) (budget : Nat) :
    evaluateClosedSourceExpression? budget owner names captured store
      ⟨callSpan,.call left ⟨argumentsSpan,[right]⟩⟩ = none := by
  have creation {source name body} (shape : SourceUnaryLambdaShape source name body) (n : Nat) :
      evaluateClosedSourceExpression? (n+1) owner names captured store source =
        some (.sourceClosure source owner names captured,store) := by
    cases shape <;> simp only [evaluateClosedSourceExpression?,sourceUnaryLambdaShape?,bind,Option.bind_some,pure]
  cases budget with
  | zero => simp [evaluateClosedSourceExpression?]
  | succ n =>
    cases n with
    | zero => simp [evaluateClosedSourceExpression?]
    | succ n =>
      simp only [evaluateClosedSourceExpression?,creation leftShape n,creation rightShape n,bind,Option.bind_some,
        sourceUnaryLambdaShape?_iff.mpr leftShape,
        selfApplicationBody_boundSelf_none rightShape rightSelf leftSelf owner owner names names captured captured store (n+1)]

/-- The direct raw self-call has no finite original successful endpoint. -/
theorem directSelfApplication_no_original
    {left right : Syntax.Expr} {leftName rightName : Syntax.Identifier} {leftBody rightBody : Syntax.Block}
    (leftShape : SourceUnaryLambdaShape left leftName leftBody) (leftSelf : SourceSelfApplicationBody leftBody leftName)
    (rightShape : SourceUnaryLambdaShape right rightName rightBody) (rightSelf : SourceSelfApplicationBody rightBody rightName)
    (owner : Resolved.DeclarationId) (names : LocalNameTable) (captured : Resolved.LocalScope RuntimeValue)
    (store : List RuntimeValue) (callSpan argumentsSpan : Syntax.SourceSpan)
    (value : RuntimeValue) (finalStore : List RuntimeValue) :
    ¬ ClosedSourceExpressionEvaluates owner names captured store
      ⟨callSpan,.call left ⟨argumentsSpan,[right]⟩⟩ value finalStore := by
  intro original
  obtain ⟨budget,ran⟩ := evaluateClosedSourceExpression?_eventually_complete original
  have success := ran budget (Nat.le_refl budget)
  rw [directSelfApplication_none leftShape leftSelf rightShape rightSelf owner names captured store callSpan argumentsSpan budget] at success
  cases success

end Solcore.Frontend
end
