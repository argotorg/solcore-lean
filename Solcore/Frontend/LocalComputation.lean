import Solcore.Frontend.LocalFunctionApplication
import Solcore.Core.LocalFragment
import Solcore.Frontend.StructuralType
import Solcore.Frontend.LocalTypeInputs
import Solcore.Resolved.LocalFragmentProperties
import Solcore.Frontend.TypedLetReturnTree
import Solcore.Resolved.FreshIdentity
import Solcore.Core.Renaming

/-! A nonrecursive union of the existing pure expression and root application
profiles. Original children are not reinterpreted recursively by this adapter. -/

set_option autoImplicit false

namespace Solcore.Frontend

def elaborateLocalComputation? (table : LocalNameTable) (context : Resolved.Context)
    (source : Syntax.Expr) : Option (Core.Expr × Core.Ty) :=
  match source.value with
  | .call _ _ => elaborateLocalFunctionApplication? table context source
  | _ => elaborateLocalExpression? table context source

inductive LocalComputationHasType (table : LocalNameTable) (context : Resolved.Context) :
    Syntax.Expr → Core.Ty → Prop where
  | pure {source : Syntax.Expr} {type : Core.Ty}
      (child : LocalExpressionHasType table context source type) :
      LocalComputationHasType table context source type
  | application {source : Syntax.Expr} {type : Core.Ty}
      (child : LocalFunctionApplicationHasType table context source type) :
      LocalComputationHasType table context source type

inductive LocalComputationElaborates (table : LocalNameTable) (context : Resolved.Context) :
    Syntax.Expr → Core.Expr → Core.Ty → Prop where
  | pure {source : Syntax.Expr} {resolved : Resolved.Expr} {core : Core.Expr} {type : Core.Ty}
      (resolution : ResolvesLocalExpression table source resolved)
      (lowered : Resolved.Lowers context.ids resolved core)
      (typing : Resolved.HasType context resolved type) :
      LocalComputationElaborates table context source core type
  | application {source : Syntax.Expr} {core : Core.Expr} {type : Core.Ty}
      (child : LocalFunctionApplicationElaborates table context source core type) :
      LocalComputationElaborates table context source core type

end Solcore.Frontend

/-!
## Consolidated module: `Solcore.Frontend.LocalComputationEvaluation`
-/

/-! Raw successful computation and its exact child cost. The two original
profiles are disjoint at the root; these wrappers add no machine transitions. -/

set_option autoImplicit false

namespace Solcore.Frontend

inductive LocalComputationEvaluates
    (table : LocalNameTable) (environment : Resolved.Environment) :
    Core.Store → Syntax.Expr → Core.Value → Core.Store → Prop where
  | pure {initialStore finalStore : Core.Store} {source : Syntax.Expr} {value : Core.Value}
      (child : LocalExpressionEvaluates table environment initialStore source value finalStore) :
      LocalComputationEvaluates table environment initialStore source value finalStore
  | application {initialStore finalStore : Core.Store} {source : Syntax.Expr} {value : Core.Value}
      (child : LocalFunctionApplicationEvaluates table environment initialStore source value finalStore) :
      LocalComputationEvaluates table environment initialStore source value finalStore

inductive LocalComputationEvaluatesWithCost
    (table : LocalNameTable) (environment : Resolved.Environment) :
    Core.Store → Syntax.Expr → Core.Value → Core.Store → Nat → Prop where
  | pure {initialStore finalStore : Core.Store} {source : Syntax.Expr}
      {value : Core.Value} {cost : Nat}
      (child : LocalExpressionEvaluatesWithCost table environment initialStore source value finalStore cost) :
      LocalComputationEvaluatesWithCost table environment initialStore source value finalStore cost
  | application {initialStore finalStore : Core.Store} {source : Syntax.Expr}
      {value : Core.Value} {cost : Nat}
      (child : LocalFunctionApplicationEvaluatesWithCost table environment initialStore source value finalStore cost) :
      LocalComputationEvaluatesWithCost table environment initialStore source value finalStore cost

end Solcore.Frontend

/-!
## Consolidated module: `Solcore.Frontend.LocalComputationEvaluationProperties`
-/

/-! The two original raw profiles keep their exact costs and outcomes.
Their root shapes are disjoint without any checker or typing premise. -/

set_option autoImplicit false

namespace Solcore.Frontend

theorem localComputationEvaluates_iff_exists_cost {table : LocalNameTable}
    {environment : Resolved.Environment} {initialStore finalStore : Core.Store}
    {source : Syntax.Expr} {value : Core.Value} :
    LocalComputationEvaluates table environment initialStore source value finalStore ↔
      ∃ cost, LocalComputationEvaluatesWithCost table environment
        initialStore source value finalStore cost := by
  constructor
  · intro evaluation
    cases evaluation with
    | pure child =>
        obtain ⟨cost, costed⟩ := child.exists_cost
        exact ⟨cost, .pure costed⟩
    | application child =>
        obtain ⟨cost, costed⟩ := child.exists_cost
        exact ⟨cost, .application costed⟩
  · rintro ⟨_, evaluation⟩
    cases evaluation with
    | pure child => exact .pure child.erase
    | application child => exact .application child.erase

theorem LocalComputationEvaluatesWithCost.deterministic {table : LocalNameTable}
    {environment : Resolved.Environment} {initialStore : Core.Store} {source : Syntax.Expr}
    {left right : Core.Value} {leftStore rightStore : Core.Store} {leftCost rightCost : Nat}
    (leftEvaluation : LocalComputationEvaluatesWithCost table environment
      initialStore source left leftStore leftCost)
    (rightEvaluation : LocalComputationEvaluatesWithCost table environment
      initialStore source right rightStore rightCost) :
    left = right ∧ leftStore = rightStore ∧ leftCost = rightCost := by
  cases leftEvaluation with
  | pure child =>
      cases rightEvaluation with
      | pure other => exact child.deterministic other
      | application other => cases other; cases child
  | application child =>
      cases rightEvaluation with
      | pure other => cases child; cases other
      | application other => exact child.deterministic other

end Solcore.Frontend

/-!
## Consolidated module: `Solcore.Frontend.LocalComputationExecutionProperties`
-/

/-! Exact original child provenance connects both computation branches to Core.
Only runtime ID order is shared; actual values, effects and pending frames are
not inferred from structural types. Root calls cannot be pure expressions. -/

set_option autoImplicit false

namespace Solcore.Frontend

theorem LocalComputationElaborates.evaluates_iff
    {table : LocalNameTable} {context : Resolved.Context} {environment : Resolved.Environment}
    {source : Syntax.Expr} {core : Core.Expr} {type : Core.Ty}
    (elaboration : LocalComputationElaborates table context source core type)
    (sameIds : Resolved.LocalScope.ids environment = Resolved.LocalScope.ids context)
    {initialStore finalStore : Core.Store} {value : Core.Value} :
    LocalComputationEvaluates table environment initialStore source value finalStore ↔
      Core.Evaluates (Resolved.LocalScope.values environment) initialStore core value finalStore := by
  cases elaboration with
  | pure resolution lowered _ =>
      rw [← sameIds] at lowered
      constructor
      · intro evaluation
        cases evaluation with
        | pure child => exact (resolution.core_evaluates_iff lowered).mp child
        | application child => cases child; cases resolution
      · intro evaluation
        exact .pure ((resolution.core_evaluates_iff lowered).mpr evaluation)
  | application child =>
      constructor
      · intro evaluation
        cases evaluation with
        | pure actual => cases child; cases actual
        | application actual => exact (child.evaluates_iff sameIds).mp actual
      · intro evaluation
        exact .application ((child.evaluates_iff sameIds).mpr evaluation)

/-- The supplied cost is fixed before the retained continuation. Its endpoint
need not be final, and any subsequent pending frames are not executed here. -/
theorem LocalComputationEvaluatesWithCost.toStepsWithContinuation
    {table : LocalNameTable} {context : Resolved.Context} {environment : Resolved.Environment}
    {initialStore finalStore : Core.Store} {source : Syntax.Expr}
    {value : Core.Value} {cost : Nat}
    (evaluation : LocalComputationEvaluatesWithCost table environment
      initialStore source value finalStore cost)
    {core : Core.Expr} {type : Core.Ty}
    (elaboration : LocalComputationElaborates table context source core type)
    (sameIds : Resolved.LocalScope.ids environment = Resolved.LocalScope.ids context)
    (continuation : List Core.Frame) :
    Core.Steps cost
      ⟨.eval core (Resolved.LocalScope.values environment), continuation, initialStore⟩
      ⟨.ret value, continuation, finalStore⟩ := by
  cases elaboration with
  | pure resolution lowered _ =>
      rw [← sameIds] at lowered
      cases evaluation with
      | pure child => exact child.toStepsWithContinuation resolution lowered continuation
      | application child => cases child; cases resolution
  | application child =>
      cases evaluation with
      | pure actual => cases child; cases actual
      | application actual => exact actual.toStepsWithContinuation child sameIds continuation

theorem LocalComputationElaborates.evaluatesWithCost_iff_steps
    {table : LocalNameTable} {context : Resolved.Context} {environment : Resolved.Environment}
    {source : Syntax.Expr} {core : Core.Expr} {type : Core.Ty}
    (elaboration : LocalComputationElaborates table context source core type)
    (sameIds : Resolved.LocalScope.ids environment = Resolved.LocalScope.ids context)
    {initialStore finalStore : Core.Store} {value : Core.Value} {cost : Nat} :
    LocalComputationEvaluatesWithCost table environment
      initialStore source value finalStore cost ↔
      Core.Steps cost (Core.State.initial core (Resolved.LocalScope.values environment) initialStore)
        (Core.State.final value finalStore) := by
  constructor
  · intro evaluation
    exact evaluation.toStepsWithContinuation elaboration sameIds []
  · intro path
    have evaluation := (elaboration.evaluates_iff sameIds).mpr (Core.steps_from_initial_sound path)
    obtain ⟨actualCost, actual⟩ := localComputationEvaluates_iff_exists_cost.mp evaluation
    have sameCost := (path.final_unique (actual.toStepsWithContinuation elaboration sameIds [])).1
    exact sameCost.symm ▸ actual

end Solcore.Frontend

/-!
## Consolidated module: `Solcore.Frontend.LocalComputationFragment`
-/

/-! Caller syntax for mixed local computations. Unlike the old pure fragment,
this boundary admits applications, but not source closure construction. The
body and captures of an actual called closure are not restricted by membership. -/

set_option autoImplicit false

namespace Solcore.Frontend

inductive LocalComputationFragment : Core.Expr → Prop where
  | pure {expr : Core.Expr} (child : expr.LocalFragment) : LocalComputationFragment expr
  | application {function argument : Core.Expr}
      (callee : function.LocalFragment) (operand : argument.LocalFragment) :
      LocalComputationFragment (.apply function argument)
  | letE {initializer body : Core.Expr}
      (head : LocalComputationFragment initializer) (tail : LocalComputationFragment body) :
      LocalComputationFragment (.letE initializer body)
  | ifE {condition thenBranch elseBranch : Core.Expr}
      (guard : LocalComputationFragment condition)
      (yes : LocalComputationFragment thenBranch) (no : LocalComputationFragment elseBranch) :
      LocalComputationFragment (.ifE condition thenBranch elseBranch)

end Solcore.Frontend

/-!
## Consolidated module: `Solcore.Frontend.LocalComputationFragmentInsertionPaths`
-/

/-! One shared cost precedes every outer continuation. Each caller retains its
own saved frames, while an actual closure's body path is reused unchanged. -/

set_option autoImplicit false

namespace Solcore.Frontend

theorem LocalComputationFragment.insertion_paths
    {expr : Core.Expr} (fragment : LocalComputationFragment expr)
    (leading suffix : Core.Environment) (inserted : Core.Value)
    {initialStore finalStore : Core.Store} {value : Core.Value}
    (evaluation : Core.Evaluates (leading ++ suffix) initialStore expr value finalStore) :
    ∃ cost, ∀ continuation,
      Core.Steps cost
        ⟨.eval expr (leading ++ suffix), continuation, initialStore⟩
        ⟨.ret value, continuation, finalStore⟩ ∧
      Core.Steps cost
        ⟨.eval (expr.weakenAt leading.length) (leading ++ inserted :: suffix), continuation, initialStore⟩
        ⟨.ret value, continuation, finalStore⟩ := by
  induction fragment generalizing leading initialStore finalStore value with
  | pure child => exact child.insertion_paths leading suffix inserted evaluation
  | application callee operand =>
      cases evaluation with
      | apply functionEvaluation argumentEvaluation bodyEvaluation =>
          obtain ⟨functionCost, functionPaths⟩ := callee.insertion_paths leading suffix inserted functionEvaluation
          obtain ⟨argumentCost, argumentPaths⟩ := operand.insertion_paths leading suffix inserted argumentEvaluation
          obtain ⟨bodyCost, bodyPath⟩ := bodyEvaluation.toSteps
          refine ⟨functionCost + argumentCost + bodyCost + 3, fun continuation => ?_⟩
          constructor
          · exact CostStepComposition.apply (functionPaths _).1 (argumentPaths _).1 bodyPath
          · simp only [Core.Expr.weakenAt]
            exact CostStepComposition.apply (functionPaths _).2 (argumentPaths _).2 bodyPath
  | letE _ _ headIH tailIH =>
      cases evaluation with
      | @letE _ _ _ _ _ _ boundValue _ head tail =>
          obtain ⟨headCost, headPaths⟩ := headIH leading head
          obtain ⟨tailCost, tailPaths⟩ := tailIH (boundValue :: leading) tail
          refine ⟨headCost + tailCost + 2, fun continuation => ?_⟩
          constructor
          · exact CostStepComposition.letE (headPaths _).1 (tailPaths _).1
          · simp only [Core.Expr.weakenAt]
            exact CostStepComposition.letE (headPaths _).2 (tailPaths _).2
  | ifE _ _ _ guardIH yesIH noIH =>
      cases evaluation with
      | ifTrue condition branch =>
          obtain ⟨conditionCost, conditionPaths⟩ := guardIH leading condition
          obtain ⟨branchCost, branchPaths⟩ := yesIH leading branch
          refine ⟨conditionCost + branchCost + 2, fun continuation => ?_⟩
          constructor
          · exact CostStepComposition.ifTrue (conditionPaths _).1 (branchPaths _).1
          · simp only [Core.Expr.weakenAt]
            exact CostStepComposition.ifTrue (conditionPaths _).2 (branchPaths _).2
      | ifFalse condition branch =>
          obtain ⟨conditionCost, conditionPaths⟩ := guardIH leading condition
          obtain ⟨branchCost, branchPaths⟩ := noIH leading branch
          refine ⟨conditionCost + branchCost + 2, fun continuation => ?_⟩
          constructor
          · exact CostStepComposition.ifFalse (conditionPaths _).1 (branchPaths _).1
          · simp only [Core.Expr.weakenAt]
            exact CostStepComposition.ifFalse (conditionPaths _).2 (branchPaths _).2

end Solcore.Frontend

/-!
## Consolidated module: `Solcore.Frontend.LocalComputationFragmentInsertionProperties`
-/

/-! Caller insertion preserves literal successful results and both stores.
Actual invoked bodies and captures are unchanged, not assumed pure or typed. -/

set_option autoImplicit false

namespace Solcore.Frontend

theorem LocalComputationFragment.evaluates_insert_iff
    {expr : Core.Expr} (fragment : LocalComputationFragment expr)
    (leading suffix : Core.Environment) (inserted : Core.Value)
    {initialStore finalStore : Core.Store} {value : Core.Value} :
    Core.Evaluates (leading ++ inserted :: suffix) initialStore
      (expr.weakenAt leading.length) value finalStore ↔
      Core.Evaluates (leading ++ suffix) initialStore expr value finalStore := by
  induction fragment generalizing leading initialStore finalStore value with
  | pure child => exact child.evaluates_insert_iff leading suffix inserted
  | application callee operand =>
      simp only [Core.Expr.weakenAt]
      constructor
      · intro evaluation
        cases evaluation with
        | apply functionEvaluation argumentEvaluation bodyEvaluation =>
            exact .apply ((callee.evaluates_insert_iff leading suffix inserted).mp functionEvaluation)
              ((operand.evaluates_insert_iff leading suffix inserted).mp argumentEvaluation) bodyEvaluation
      · intro evaluation
        cases evaluation with
        | apply functionEvaluation argumentEvaluation bodyEvaluation =>
            exact .apply ((callee.evaluates_insert_iff leading suffix inserted).mpr functionEvaluation)
              ((operand.evaluates_insert_iff leading suffix inserted).mpr argumentEvaluation) bodyEvaluation
  | letE _ _ headIH tailIH =>
      simp only [Core.Expr.weakenAt]
      constructor
      · intro evaluation
        cases evaluation with
        | @letE _ _ _ _ _ _ boundValue _ head tail =>
            exact .letE ((headIH leading).mp head) ((tailIH (boundValue :: leading)).mp tail)
      · intro evaluation
        cases evaluation with
        | @letE _ _ _ _ _ _ boundValue _ head tail =>
            exact .letE ((headIH leading).mpr head) ((tailIH (boundValue :: leading)).mpr tail)
  | ifE _ _ _ guardIH yesIH noIH =>
      simp only [Core.Expr.weakenAt]
      constructor
      · intro evaluation
        cases evaluation with
        | ifTrue condition branch => exact .ifTrue ((guardIH leading).mp condition) ((yesIH leading).mp branch)
        | ifFalse condition branch => exact .ifFalse ((guardIH leading).mp condition) ((noIH leading).mp branch)
      · intro evaluation
        cases evaluation with
        | ifTrue condition branch => exact .ifTrue ((guardIH leading).mpr condition) ((yesIH leading).mpr branch)
        | ifFalse condition branch => exact .ifFalse ((guardIH leading).mpr condition) ((noIH leading).mpr branch)

end Solcore.Frontend

/-!
## Consolidated module: `Solcore.Frontend.LocalComputationInsertionProperties`
-/

/-! The two computation branches share exact caller-insertion kernels.
These are leaf facts; enclosing body scopes still require their own induction. -/

set_option autoImplicit false

namespace Solcore.Frontend

theorem LocalComputationElaborates.core_hasType_insert_iff
    {table : LocalNameTable} {context : Resolved.Context}
    {source : Syntax.Expr} {core : Core.Expr} {type : Core.Ty}
    (elaboration : LocalComputationElaborates table context source core type)
    (leading suffix : Core.Context) (inserted : Core.Ty)
    {requestedType : Core.Ty} {definitions : Core.DataEnvironment} :
    Core.HasType (leading ++ inserted :: suffix) (core.weakenAt leading.length)
      requestedType definitions ↔
    Core.HasType (leading ++ suffix) core requestedType definitions := by
  cases elaboration with
  | pure _ lowered _ => exact lowered.localFragment.hasType_insert_iff leading suffix inserted
  | application child => exact child.core_hasType_insert_iff leading suffix inserted

theorem LocalComputationElaborates.core_evaluates_insert_iff
    {table : LocalNameTable} {context : Resolved.Context}
    {source : Syntax.Expr} {core : Core.Expr} {type : Core.Ty}
    (elaboration : LocalComputationElaborates table context source core type)
    (leading suffix : Core.Environment) (inserted : Core.Value)
    {initialStore finalStore : Core.Store} {value : Core.Value} :
    Core.Evaluates (leading ++ inserted :: suffix) initialStore
      (core.weakenAt leading.length) value finalStore ↔
    Core.Evaluates (leading ++ suffix) initialStore core value finalStore := by
  cases elaboration with
  | pure _ lowered _ => exact lowered.localFragment.evaluates_insert_iff leading suffix inserted
  | application child => exact child.core_evaluates_insert_iff leading suffix inserted

theorem LocalComputationElaborates.core_insertion_paths
    {table : LocalNameTable} {context : Resolved.Context}
    {source : Syntax.Expr} {core : Core.Expr} {type : Core.Ty}
    (elaboration : LocalComputationElaborates table context source core type)
    (leading suffix : Core.Environment) (inserted : Core.Value)
    {initialStore finalStore : Core.Store} {value : Core.Value}
    (evaluation : Core.Evaluates (leading ++ suffix) initialStore core value finalStore) :
    ∃ cost, ∀ continuation,
      Core.Steps cost
        ⟨.eval core (leading ++ suffix), continuation, initialStore⟩
        ⟨.ret value, continuation, finalStore⟩ ∧
      Core.Steps cost
        ⟨.eval (core.weakenAt leading.length) (leading ++ inserted :: suffix),
          continuation, initialStore⟩
        ⟨.ret value, continuation, finalStore⟩ := by
  cases elaboration with
  | pure _ lowered _ => exact lowered.localFragment.insertion_paths leading suffix inserted evaluation
  | application child => exact child.core_insertion_paths leading suffix inserted evaluation

end Solcore.Frontend

/-!
## Consolidated module: `Solcore.Frontend.LocalComputationProperties`
-/

/-! The original child relations determine exact computation provenance.
Pure resolution cannot have a root call, so dispatch loses no old success.
No runtime inhabitant, environment alignment or store premise is involved. -/

set_option autoImplicit false

namespace Solcore.Frontend

private theorem pure_dispatch {table : LocalNameTable} {context : Resolved.Context}
    {source : Syntax.Expr} {resolved : Resolved.Expr}
    (resolution : ResolvesLocalExpression table source resolved) :
    elaborateLocalComputation? table context source = elaborateLocalExpression? table context source := by
  cases resolution <;> rfl

theorem elaborateLocalComputation?_iff
    {table : LocalNameTable} {context : Resolved.Context}
    {source : Syntax.Expr} {core : Core.Expr} {type : Core.Ty} :
    elaborateLocalComputation? table context source = some (core, type) ↔
      LocalComputationElaborates table context source core type := by
  constructor
  · intro accepted
    unfold elaborateLocalComputation? at accepted
    split at accepted
    · exact .application (elaborateLocalFunctionApplication?_sound accepted)
    · obtain ⟨resolved, resolution, lowered, typing⟩ := elaborateLocalExpression?_sound accepted
      exact .pure resolution lowered typing
  · intro elaboration
    cases elaboration with
    | pure resolution lowered typing =>
        rw [pure_dispatch resolution]
        exact elaborateLocalExpression?_complete resolution lowered typing
    | application child =>
        have accepted := child.complete
        cases child
        exact accepted

theorem localComputationHasType_iff_elaborates
    {table : LocalNameTable} {context : Resolved.Context}
    {source : Syntax.Expr} {type : Core.Ty} :
    LocalComputationHasType table context source type ↔
      ∃ core, LocalComputationElaborates table context source core type := by
  constructor
  · intro typing
    cases typing with
    | pure child =>
        obtain ⟨resolved, resolution, resolvedTyped⟩ := child.resolves
        obtain ⟨core, lowered, _⟩ := resolvedTyped.lowers
        exact ⟨core, .pure resolution lowered resolvedTyped⟩
    | application child =>
        obtain ⟨core, elaboration⟩ := child.elaborates_exact
        exact ⟨core, .application elaboration⟩
  · rintro ⟨core, elaboration⟩
    cases elaboration with
    | pure resolution _ typing => exact .pure (resolution.reflects_type typing)
    | application child => exact .application child.hasType

theorem LocalComputationElaborates.core_hasType
    {table : LocalNameTable} {context : Resolved.Context}
    {source : Syntax.Expr} {core : Core.Expr} {type : Core.Ty}
    (elaboration : LocalComputationElaborates table context source core type) :
    Core.HasType context.values core type := by
  cases elaboration with
  | pure _ lowered typing => exact lowered.preserves_type typing
  | application child => exact child.core_hasType

end Solcore.Frontend

/-!
## Consolidated module: `Solcore.Frontend.LocalComputationReturnTree`
-/

/-! A separate mixed body profile. Named bindings extend source scope after
checking their initializer; strict discards keep source scope and insert only
a hidden Core slot. Returns and terminal lexical blocks retain their children. -/

set_option autoImplicit false

namespace Solcore.Frontend

def elaborateLocalComputationReturnTree? (types : TypeNameTable) (owner : Resolved.DeclarationId)
    (inputs : LocalTypeInputs) (body : Syntax.Block) : Option (Core.Expr × Core.Ty) :=
  match body with
  | ⟨_, [⟨_, .returnStmt none⟩]⟩ => some (.unit, .unit)
  | ⟨_, [⟨_, .returnStmt (some expression)⟩]⟩ =>
      elaborateLocalComputation? inputs.names inputs.context expression
  | ⟨_, [⟨innerSpan, .block statements⟩]⟩ =>
      elaborateLocalComputationReturnTree? types owner inputs ⟨innerSpan, statements⟩
  | ⟨blockSpan, ⟨_, .letDecl name (some annotation) (some initializer)⟩ :: rest⟩ =>
      if name.value ∉ inputs.names.map Prod.fst then do
        let declaredType ← interpretStructuralType? types annotation
        let (initializerCore, initializerType) ← elaborateLocalComputation? inputs.names inputs.context initializer
        if initializerType = declaredType then do
          let (tailCore, returnType) ← elaborateLocalComputationReturnTree? types owner
            (inputs.bindFresh owner name.value declaredType) ⟨blockSpan, rest⟩
          return (.letE initializerCore tailCore, returnType)
        else none
      else none
  | ⟨blockSpan, ⟨_, .letDecl name none (some initializer)⟩ :: rest⟩ =>
      if name.value ∉ inputs.names.map Prod.fst then do
        let (initializerCore, initializerType) ← elaborateLocalComputation? inputs.names inputs.context initializer
        let (tailCore, returnType) ← elaborateLocalComputationReturnTree? types owner
          (inputs.bindFresh owner name.value initializerType) ⟨blockSpan, rest⟩
        return (.letE initializerCore tailCore, returnType)
      else none
  | ⟨blockSpan, ⟨_, .expression expression true⟩ :: rest⟩ => do
      let (expressionCore, _) ← elaborateLocalComputation? inputs.names inputs.context expression
      let (tailCore, returnType) ← elaborateLocalComputationReturnTree? types owner inputs ⟨blockSpan, rest⟩
      return (.letE expressionCore (tailCore.weakenAt 0), returnType)
  | ⟨_, [⟨_, .ifThen condition thenBody (some elseBody)⟩]⟩ => do
      let (conditionCore, conditionType) ← elaborateLocalComputation? inputs.names inputs.context condition
      if conditionType = .bool then do
        let (thenCore, thenType) ← elaborateLocalComputationReturnTree? types owner inputs thenBody
        let (elseCore, elseType) ← elaborateLocalComputationReturnTree? types owner inputs elseBody
        if thenType = elseType then return (.ifE conditionCore thenCore elseCore, thenType)
        else none
      else none
  | _ => none
termination_by sizeOf body

inductive LocalComputationReturnTreeHasType (types : TypeNameTable) (owner : Resolved.DeclarationId) :
    LocalTypeInputs → Syntax.Block → Core.Ty → Prop where
  | bare {inputs : LocalTypeInputs} {blockSpan returnSpan : Syntax.SourceSpan} :
      LocalComputationReturnTreeHasType types owner inputs
        ⟨blockSpan, [⟨returnSpan, .returnStmt none⟩]⟩ .unit
  | expression {inputs : LocalTypeInputs} {blockSpan returnSpan : Syntax.SourceSpan}
      {source : Syntax.Expr} {type : Core.Ty}
      (child : LocalComputationHasType inputs.names inputs.context source type) :
      LocalComputationReturnTreeHasType types owner inputs
        ⟨blockSpan, [⟨returnSpan, .returnStmt (some source)⟩]⟩ type
  | block {inputs : LocalTypeInputs} {outerSpan innerSpan : Syntax.SourceSpan}
      {statements : List Syntax.Statement} {type : Core.Ty}
      (child : LocalComputationReturnTreeHasType types owner inputs ⟨innerSpan, statements⟩ type) :
      LocalComputationReturnTreeHasType types owner inputs
        ⟨outerSpan, [⟨innerSpan, .block statements⟩]⟩ type
  | binding {inputs : LocalTypeInputs} {blockSpan letSpan : Syntax.SourceSpan}
      {name : Syntax.Identifier} {annotation : Syntax.TypeExpr} {initializer : Syntax.Expr}
      {rest : List Syntax.Statement} {declaredType returnType : Core.Ty}
      (meaning : StructuralTypeDenotes types annotation declaredType)
      (unused : name.value ∉ inputs.names.map Prod.fst)
      (initializerTyping : LocalComputationHasType inputs.names inputs.context initializer declaredType)
      (tailTyping : LocalComputationReturnTreeHasType types owner
        (inputs.bindFresh owner name.value declaredType) ⟨blockSpan, rest⟩ returnType) :
      LocalComputationReturnTreeHasType types owner inputs
        ⟨blockSpan, ⟨letSpan, .letDecl name (some annotation) (some initializer)⟩ :: rest⟩ returnType
  | inferred {inputs : LocalTypeInputs} {blockSpan letSpan : Syntax.SourceSpan}
      {name : Syntax.Identifier} {initializer : Syntax.Expr} {rest : List Syntax.Statement}
      {inferredType returnType : Core.Ty}
      (unused : name.value ∉ inputs.names.map Prod.fst)
      (initializerTyping : LocalComputationHasType inputs.names inputs.context initializer inferredType)
      (tailTyping : LocalComputationReturnTreeHasType types owner
        (inputs.bindFresh owner name.value inferredType) ⟨blockSpan, rest⟩ returnType) :
      LocalComputationReturnTreeHasType types owner inputs
        ⟨blockSpan, ⟨letSpan, .letDecl name none (some initializer)⟩ :: rest⟩ returnType
  | discard {inputs : LocalTypeInputs} {blockSpan statementSpan : Syntax.SourceSpan}
      {expression : Syntax.Expr} {rest : List Syntax.Statement} {discardedType returnType : Core.Ty}
      (expressionTyping : LocalComputationHasType inputs.names inputs.context expression discardedType)
      (tailTyping : LocalComputationReturnTreeHasType types owner inputs ⟨blockSpan, rest⟩ returnType) :
      LocalComputationReturnTreeHasType types owner inputs
        ⟨blockSpan, ⟨statementSpan, .expression expression true⟩ :: rest⟩ returnType
  | conditional {inputs : LocalTypeInputs} {blockSpan ifSpan : Syntax.SourceSpan}
      {condition : Syntax.Expr} {thenBody elseBody : Syntax.Block} {type : Core.Ty}
      (conditionTyping : LocalComputationHasType inputs.names inputs.context condition .bool)
      (thenTyping : LocalComputationReturnTreeHasType types owner inputs thenBody type)
      (elseTyping : LocalComputationReturnTreeHasType types owner inputs elseBody type) :
      LocalComputationReturnTreeHasType types owner inputs
        ⟨blockSpan, [⟨ifSpan, .ifThen condition thenBody (some elseBody)⟩]⟩ type

inductive LocalComputationReturnTreeElaborates (types : TypeNameTable) (owner : Resolved.DeclarationId) :
    LocalTypeInputs → Syntax.Block → Core.Expr → Core.Ty → Prop where
  | bare {inputs : LocalTypeInputs} {blockSpan returnSpan : Syntax.SourceSpan} :
      LocalComputationReturnTreeElaborates types owner inputs
        ⟨blockSpan, [⟨returnSpan, .returnStmt none⟩]⟩ .unit .unit
  | expression {inputs : LocalTypeInputs} {blockSpan returnSpan : Syntax.SourceSpan}
      {source : Syntax.Expr} {core : Core.Expr} {type : Core.Ty}
      (child : LocalComputationElaborates inputs.names inputs.context source core type) :
      LocalComputationReturnTreeElaborates types owner inputs
        ⟨blockSpan, [⟨returnSpan, .returnStmt (some source)⟩]⟩ core type
  | block {inputs : LocalTypeInputs} {outerSpan innerSpan : Syntax.SourceSpan}
      {statements : List Syntax.Statement} {core : Core.Expr} {type : Core.Ty}
      (child : LocalComputationReturnTreeElaborates types owner inputs ⟨innerSpan, statements⟩ core type) :
      LocalComputationReturnTreeElaborates types owner inputs
        ⟨outerSpan, [⟨innerSpan, .block statements⟩]⟩ core type
  | binding {inputs : LocalTypeInputs} {blockSpan letSpan : Syntax.SourceSpan}
      {name : Syntax.Identifier} {annotation : Syntax.TypeExpr} {initializer : Syntax.Expr}
      {rest : List Syntax.Statement} {declaredType returnType : Core.Ty} {initializerCore tailCore : Core.Expr}
      (meaning : StructuralTypeDenotes types annotation declaredType)
      (unused : name.value ∉ inputs.names.map Prod.fst)
      (initializerElaboration : LocalComputationElaborates inputs.names inputs.context initializer initializerCore declaredType)
      (tailElaboration : LocalComputationReturnTreeElaborates types owner
        (inputs.bindFresh owner name.value declaredType) ⟨blockSpan, rest⟩ tailCore returnType) :
      LocalComputationReturnTreeElaborates types owner inputs
        ⟨blockSpan, ⟨letSpan, .letDecl name (some annotation) (some initializer)⟩ :: rest⟩
        (.letE initializerCore tailCore) returnType
  | inferred {inputs : LocalTypeInputs} {blockSpan letSpan : Syntax.SourceSpan}
      {name : Syntax.Identifier} {initializer : Syntax.Expr} {rest : List Syntax.Statement}
      {inferredType returnType : Core.Ty} {initializerCore tailCore : Core.Expr}
      (unused : name.value ∉ inputs.names.map Prod.fst)
      (initializerElaboration : LocalComputationElaborates inputs.names inputs.context initializer initializerCore inferredType)
      (tailElaboration : LocalComputationReturnTreeElaborates types owner
        (inputs.bindFresh owner name.value inferredType) ⟨blockSpan, rest⟩ tailCore returnType) :
      LocalComputationReturnTreeElaborates types owner inputs
        ⟨blockSpan, ⟨letSpan, .letDecl name none (some initializer)⟩ :: rest⟩
        (.letE initializerCore tailCore) returnType
  | discard {inputs : LocalTypeInputs} {blockSpan statementSpan : Syntax.SourceSpan}
      {expression : Syntax.Expr} {rest : List Syntax.Statement} {discardedType returnType : Core.Ty}
      {expressionCore tailCore : Core.Expr}
      (expressionElaboration : LocalComputationElaborates inputs.names inputs.context expression expressionCore discardedType)
      (tailElaboration : LocalComputationReturnTreeElaborates types owner inputs ⟨blockSpan, rest⟩ tailCore returnType) :
      LocalComputationReturnTreeElaborates types owner inputs
        ⟨blockSpan, ⟨statementSpan, .expression expression true⟩ :: rest⟩
        (.letE expressionCore (tailCore.weakenAt 0)) returnType
  | conditional {inputs : LocalTypeInputs} {blockSpan ifSpan : Syntax.SourceSpan}
      {condition : Syntax.Expr} {thenBody elseBody : Syntax.Block}
      {conditionCore thenCore elseCore : Core.Expr} {type : Core.Ty}
      (conditionElaboration : LocalComputationElaborates inputs.names inputs.context condition conditionCore .bool)
      (thenElaboration : LocalComputationReturnTreeElaborates types owner inputs thenBody thenCore type)
      (elseElaboration : LocalComputationReturnTreeElaborates types owner inputs elseBody elseCore type) :
      LocalComputationReturnTreeElaborates types owner inputs
        ⟨blockSpan, [⟨ifSpan, .ifThen condition thenBody (some elseBody)⟩]⟩
        (.ifE conditionCore thenCore elseCore) type

end Solcore.Frontend

/-!
## Consolidated module: `Solcore.Frontend.LocalComputationFragmentProperties`
-/

/-! Structural membership follows exact original lowering. Hidden discard
binders require closure of the entire mixed tail, including earlier weakenings. -/

set_option autoImplicit false

namespace Solcore.Frontend

theorem LocalComputationFragment.weakenAt {expr : Core.Expr}
    (fragment : LocalComputationFragment expr) (cutoff : Nat) :
    LocalComputationFragment (expr.weakenAt cutoff) := by
  induction fragment generalizing cutoff with
  | pure child => exact .pure (child.weakenAt cutoff)
  | application callee operand =>
      simp only [Core.Expr.weakenAt]
      exact .application (callee.weakenAt cutoff) (operand.weakenAt cutoff)
  | letE _ _ headIH tailIH =>
      simp only [Core.Expr.weakenAt]
      exact .letE (headIH cutoff) (tailIH (cutoff + 1))
  | ifE _ _ _ guardIH yesIH noIH =>
      simp only [Core.Expr.weakenAt]
      exact .ifE (guardIH cutoff) (yesIH cutoff) (noIH cutoff)

theorem LocalComputationElaborates.core_fragment
    {table : LocalNameTable} {context : Resolved.Context} {source : Syntax.Expr}
    {core : Core.Expr} {type : Core.Ty}
    (elaboration : LocalComputationElaborates table context source core type) :
    LocalComputationFragment core := by
  cases elaboration with
  | pure _ lowered _ => exact .pure lowered.localFragment
  | application child =>
      cases child with
      | call _ callee _ _ operand _ => exact .application callee.localFragment operand.localFragment

theorem LocalComputationReturnTreeElaborates.core_fragment
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {inputs : LocalTypeInputs}
    {body : Syntax.Block} {core : Core.Expr} {type : Core.Ty}
    (elaboration : LocalComputationReturnTreeElaborates types owner inputs body core type) :
    LocalComputationFragment core := by
  induction elaboration with
  | bare => exact .pure .unit
  | expression child => exact child.core_fragment
  | block _ ih => exact ih
  | binding _ _ child _ ih => exact .letE child.core_fragment ih
  | inferred _ child _ ih => exact .letE child.core_fragment ih
  | discard child _ ih => exact .letE child.core_fragment (ih.weakenAt 0)
  | conditional guard _ _ yesIH noIH => exact .ifE guard.core_fragment yesIH noIH

end Solcore.Frontend

/-!
## Consolidated module: `Solcore.Frontend.LocalComputationReturnTreeEmbeddingProperties`
-/

/-! Old pure provenance embeds with exactly the same syntax, scope, Core and
type. This one-way proof changes no old checker and uses no old runtime law. -/

set_option autoImplicit false

namespace Solcore.Frontend

theorem TypedLetReturnTreeElaborates.toLocalComputationReturnTree
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {inputs : LocalTypeInputs}
    {body : Syntax.Block} {core : Core.Expr} {type : Core.Ty}
    (elaboration : TypedLetReturnTreeElaborates types owner inputs body core type) :
    LocalComputationReturnTreeElaborates types owner inputs body core type := by
  induction elaboration with
  | single child =>
      cases child with
      | bare => exact .bare
      | expression resolution lowered typing => exact .expression (.pure resolution lowered typing)
  | block _ ih => exact .block ih
  | binding meaning unused resolution lowered typing _ ih =>
      exact .binding meaning unused
        (.pure resolution (by simpa only [LocalTypeInputs.context_ids] using lowered) typing) ih
  | inferred unused resolution lowered typing _ ih =>
      exact .inferred unused
        (.pure resolution (by simpa only [LocalTypeInputs.context_ids] using lowered) typing) ih
  | discard resolution lowered typing _ ih =>
      exact .discard
        (.pure resolution (by simpa only [LocalTypeInputs.context_ids] using lowered) typing) ih
  | conditional resolution lowered typing _ _ thenIH elseIH =>
      exact .conditional
        (.pure resolution (by simpa only [LocalTypeInputs.context_ids] using lowered) typing) thenIH elseIH

end Solcore.Frontend

/-!
## Consolidated module: `Solcore.Frontend.LocalComputationReturnTreeEvaluation`
-/

/-! Independent mixed-body paths thread actual stores through strict children.
Named initializers use the old scope before allocating from the name table;
discards retain the same source scope and selected guards retain their effects.
No checking, annotation meaning, unused-name or runtime typing is required. -/

set_option autoImplicit false

namespace Solcore.Frontend

inductive LocalComputationReturnTreeEvaluates (owner : Resolved.DeclarationId) :
    LocalNameTable → Resolved.Environment → Core.Store → Syntax.Block → Core.Value → Core.Store → Prop where
  | bare {table : LocalNameTable} {environment : Resolved.Environment}
      {blockSpan returnSpan : Syntax.SourceSpan} {store : Core.Store} :
      LocalComputationReturnTreeEvaluates owner table environment store
        ⟨blockSpan, [⟨returnSpan, .returnStmt none⟩]⟩ .unit store
  | expression {table : LocalNameTable} {environment : Resolved.Environment}
      {blockSpan returnSpan : Syntax.SourceSpan} {source : Syntax.Expr}
      {initialStore finalStore : Core.Store} {value : Core.Value}
      (child : LocalComputationEvaluates table environment initialStore source value finalStore) :
      LocalComputationReturnTreeEvaluates owner table environment initialStore
        ⟨blockSpan, [⟨returnSpan, .returnStmt (some source)⟩]⟩ value finalStore
  | block {table : LocalNameTable} {environment : Resolved.Environment}
      {outerSpan innerSpan : Syntax.SourceSpan} {statements : List Syntax.Statement}
      {initialStore finalStore : Core.Store} {value : Core.Value}
      (child : LocalComputationReturnTreeEvaluates owner table environment initialStore
        ⟨innerSpan, statements⟩ value finalStore) :
      LocalComputationReturnTreeEvaluates owner table environment initialStore
        ⟨outerSpan, [⟨innerSpan, .block statements⟩]⟩ value finalStore
  | binding {table : LocalNameTable} {environment : Resolved.Environment}
      {blockSpan letSpan : Syntax.SourceSpan} {name : Syntax.Identifier}
      {annotation : Syntax.TypeExpr} {initializer : Syntax.Expr} {rest : List Syntax.Statement}
      {initialStore middleStore finalStore : Core.Store} {boundValue value : Core.Value}
      (initializerEvaluation : LocalComputationEvaluates table environment initialStore initializer boundValue middleStore)
      (tailEvaluation : LocalComputationReturnTreeEvaluates owner
        ((name.value, Resolved.freshLocalId owner (table.map Prod.snd)) :: table)
        ((Resolved.freshLocalId owner (table.map Prod.snd), boundValue) :: environment)
        middleStore ⟨blockSpan, rest⟩ value finalStore) :
      LocalComputationReturnTreeEvaluates owner table environment initialStore
        ⟨blockSpan, ⟨letSpan, .letDecl name (some annotation) (some initializer)⟩ :: rest⟩ value finalStore
  | inferred {table : LocalNameTable} {environment : Resolved.Environment}
      {blockSpan letSpan : Syntax.SourceSpan} {name : Syntax.Identifier}
      {initializer : Syntax.Expr} {rest : List Syntax.Statement}
      {initialStore middleStore finalStore : Core.Store} {boundValue value : Core.Value}
      (initializerEvaluation : LocalComputationEvaluates table environment initialStore initializer boundValue middleStore)
      (tailEvaluation : LocalComputationReturnTreeEvaluates owner
        ((name.value, Resolved.freshLocalId owner (table.map Prod.snd)) :: table)
        ((Resolved.freshLocalId owner (table.map Prod.snd), boundValue) :: environment)
        middleStore ⟨blockSpan, rest⟩ value finalStore) :
      LocalComputationReturnTreeEvaluates owner table environment initialStore
        ⟨blockSpan, ⟨letSpan, .letDecl name none (some initializer)⟩ :: rest⟩ value finalStore
  | discard {table : LocalNameTable} {environment : Resolved.Environment}
      {blockSpan statementSpan : Syntax.SourceSpan} {expression : Syntax.Expr} {rest : List Syntax.Statement}
      {initialStore middleStore finalStore : Core.Store} {discardedValue value : Core.Value}
      (expressionEvaluation : LocalComputationEvaluates table environment initialStore expression discardedValue middleStore)
      (tailEvaluation : LocalComputationReturnTreeEvaluates owner table environment middleStore
        ⟨blockSpan, rest⟩ value finalStore) :
      LocalComputationReturnTreeEvaluates owner table environment initialStore
        ⟨blockSpan, ⟨statementSpan, .expression expression true⟩ :: rest⟩ value finalStore
  | ifTrue {table : LocalNameTable} {environment : Resolved.Environment}
      {blockSpan ifSpan : Syntax.SourceSpan} {condition : Syntax.Expr}
      {thenBody elseBody : Syntax.Block} {initialStore middleStore finalStore : Core.Store} {value : Core.Value}
      (conditionEvaluation : LocalComputationEvaluates table environment initialStore condition (.bool true) middleStore)
      (branchEvaluation : LocalComputationReturnTreeEvaluates owner table environment middleStore thenBody value finalStore) :
      LocalComputationReturnTreeEvaluates owner table environment initialStore
        ⟨blockSpan, [⟨ifSpan, .ifThen condition thenBody (some elseBody)⟩]⟩ value finalStore
  | ifFalse {table : LocalNameTable} {environment : Resolved.Environment}
      {blockSpan ifSpan : Syntax.SourceSpan} {condition : Syntax.Expr}
      {thenBody elseBody : Syntax.Block} {initialStore middleStore finalStore : Core.Store} {value : Core.Value}
      (conditionEvaluation : LocalComputationEvaluates table environment initialStore condition (.bool false) middleStore)
      (branchEvaluation : LocalComputationReturnTreeEvaluates owner table environment middleStore elseBody value finalStore) :
      LocalComputationReturnTreeEvaluates owner table environment initialStore
        ⟨blockSpan, [⟨ifSpan, .ifThen condition thenBody (some elseBody)⟩]⟩ value finalStore

/-- Selected lets, discards and conditionals each add two existing Core transitions.
An unused initializer or discarded expression still contributes its complete cost.
Bare return costs one; expression return and terminal blocks keep child costs.
These paths do not impose store independence on an actual called body. -/
inductive LocalComputationReturnTreeEvaluatesWithCost (owner : Resolved.DeclarationId) :
    LocalNameTable → Resolved.Environment → Core.Store → Syntax.Block → Core.Value → Core.Store → Nat → Prop where
  | bare {table : LocalNameTable} {environment : Resolved.Environment}
      {blockSpan returnSpan : Syntax.SourceSpan} {store : Core.Store} :
      LocalComputationReturnTreeEvaluatesWithCost owner table environment store
        ⟨blockSpan, [⟨returnSpan, .returnStmt none⟩]⟩ .unit store 1
  | expression {table : LocalNameTable} {environment : Resolved.Environment}
      {blockSpan returnSpan : Syntax.SourceSpan} {source : Syntax.Expr}
      {initialStore finalStore : Core.Store} {value : Core.Value} {cost : Nat}
      (child : LocalComputationEvaluatesWithCost table environment initialStore source value finalStore cost) :
      LocalComputationReturnTreeEvaluatesWithCost owner table environment initialStore
        ⟨blockSpan, [⟨returnSpan, .returnStmt (some source)⟩]⟩ value finalStore cost
  | block {table : LocalNameTable} {environment : Resolved.Environment}
      {outerSpan innerSpan : Syntax.SourceSpan} {statements : List Syntax.Statement}
      {initialStore finalStore : Core.Store} {value : Core.Value} {cost : Nat}
      (child : LocalComputationReturnTreeEvaluatesWithCost owner table environment initialStore
        ⟨innerSpan, statements⟩ value finalStore cost) :
      LocalComputationReturnTreeEvaluatesWithCost owner table environment initialStore
        ⟨outerSpan, [⟨innerSpan, .block statements⟩]⟩ value finalStore cost
  | binding {table : LocalNameTable} {environment : Resolved.Environment}
      {blockSpan letSpan : Syntax.SourceSpan} {name : Syntax.Identifier}
      {annotation : Syntax.TypeExpr} {initializer : Syntax.Expr} {rest : List Syntax.Statement}
      {initialStore middleStore finalStore : Core.Store} {boundValue value : Core.Value}
      {initializerCost tailCost : Nat}
      (initializerEvaluation : LocalComputationEvaluatesWithCost table environment
        initialStore initializer boundValue middleStore initializerCost)
      (tailEvaluation : LocalComputationReturnTreeEvaluatesWithCost owner
        ((name.value, Resolved.freshLocalId owner (table.map Prod.snd)) :: table)
        ((Resolved.freshLocalId owner (table.map Prod.snd), boundValue) :: environment)
        middleStore ⟨blockSpan, rest⟩ value finalStore tailCost) :
      LocalComputationReturnTreeEvaluatesWithCost owner table environment initialStore
        ⟨blockSpan, ⟨letSpan, .letDecl name (some annotation) (some initializer)⟩ :: rest⟩
        value finalStore (initializerCost + tailCost + 2)
  | inferred {table : LocalNameTable} {environment : Resolved.Environment}
      {blockSpan letSpan : Syntax.SourceSpan} {name : Syntax.Identifier}
      {initializer : Syntax.Expr} {rest : List Syntax.Statement}
      {initialStore middleStore finalStore : Core.Store} {boundValue value : Core.Value}
      {initializerCost tailCost : Nat}
      (initializerEvaluation : LocalComputationEvaluatesWithCost table environment
        initialStore initializer boundValue middleStore initializerCost)
      (tailEvaluation : LocalComputationReturnTreeEvaluatesWithCost owner
        ((name.value, Resolved.freshLocalId owner (table.map Prod.snd)) :: table)
        ((Resolved.freshLocalId owner (table.map Prod.snd), boundValue) :: environment)
        middleStore ⟨blockSpan, rest⟩ value finalStore tailCost) :
      LocalComputationReturnTreeEvaluatesWithCost owner table environment initialStore
        ⟨blockSpan, ⟨letSpan, .letDecl name none (some initializer)⟩ :: rest⟩
        value finalStore (initializerCost + tailCost + 2)
  | discard {table : LocalNameTable} {environment : Resolved.Environment}
      {blockSpan statementSpan : Syntax.SourceSpan} {expression : Syntax.Expr} {rest : List Syntax.Statement}
      {initialStore middleStore finalStore : Core.Store} {discardedValue value : Core.Value}
      {expressionCost tailCost : Nat}
      (expressionEvaluation : LocalComputationEvaluatesWithCost table environment
        initialStore expression discardedValue middleStore expressionCost)
      (tailEvaluation : LocalComputationReturnTreeEvaluatesWithCost owner table environment
        middleStore ⟨blockSpan, rest⟩ value finalStore tailCost) :
      LocalComputationReturnTreeEvaluatesWithCost owner table environment initialStore
        ⟨blockSpan, ⟨statementSpan, .expression expression true⟩ :: rest⟩
        value finalStore (expressionCost + tailCost + 2)
  | ifTrue {table : LocalNameTable} {environment : Resolved.Environment}
      {blockSpan ifSpan : Syntax.SourceSpan} {condition : Syntax.Expr}
      {thenBody elseBody : Syntax.Block} {initialStore middleStore finalStore : Core.Store}
      {value : Core.Value} {conditionCost branchCost : Nat}
      (conditionEvaluation : LocalComputationEvaluatesWithCost table environment
        initialStore condition (.bool true) middleStore conditionCost)
      (branchEvaluation : LocalComputationReturnTreeEvaluatesWithCost owner table environment
        middleStore thenBody value finalStore branchCost) :
      LocalComputationReturnTreeEvaluatesWithCost owner table environment initialStore
        ⟨blockSpan, [⟨ifSpan, .ifThen condition thenBody (some elseBody)⟩]⟩
        value finalStore (conditionCost + branchCost + 2)
  | ifFalse {table : LocalNameTable} {environment : Resolved.Environment}
      {blockSpan ifSpan : Syntax.SourceSpan} {condition : Syntax.Expr}
      {thenBody elseBody : Syntax.Block} {initialStore middleStore finalStore : Core.Store}
      {value : Core.Value} {conditionCost branchCost : Nat}
      (conditionEvaluation : LocalComputationEvaluatesWithCost table environment
        initialStore condition (.bool false) middleStore conditionCost)
      (branchEvaluation : LocalComputationReturnTreeEvaluatesWithCost owner table environment
        middleStore elseBody value finalStore branchCost) :
      LocalComputationReturnTreeEvaluatesWithCost owner table environment initialStore
        ⟨blockSpan, [⟨ifSpan, .ifThen condition thenBody (some elseBody)⟩]⟩
        value finalStore (conditionCost + branchCost + 2)

end Solcore.Frontend

/-!
## Consolidated module: `Solcore.Frontend.LocalComputationReturnTreeEvaluationProperties`
-/

/-! Existence and joint determinism retain real intermediate stores and actual
bound values. No static body acceptance, type, or store invariance is assumed. -/

set_option autoImplicit false

namespace Solcore.Frontend

private theorem erase_cost
    {owner : Resolved.DeclarationId} {table : LocalNameTable} {environment : Resolved.Environment}
    {initialStore finalStore : Core.Store} {body : Syntax.Block} {value : Core.Value} {cost : Nat}
    (evaluation : LocalComputationReturnTreeEvaluatesWithCost owner table environment
      initialStore body value finalStore cost) :
    LocalComputationReturnTreeEvaluates owner table environment initialStore body value finalStore := by
  induction evaluation with
  | bare => exact .bare
  | expression child => exact .expression (localComputationEvaluates_iff_exists_cost.mpr ⟨_, child⟩)
  | block _ ih => exact .block ih
  | binding initializer _ ih =>
      exact .binding (localComputationEvaluates_iff_exists_cost.mpr ⟨_, initializer⟩) ih
  | inferred initializer _ ih =>
      exact .inferred (localComputationEvaluates_iff_exists_cost.mpr ⟨_, initializer⟩) ih
  | discard expression _ ih =>
      exact .discard (localComputationEvaluates_iff_exists_cost.mpr ⟨_, expression⟩) ih
  | ifTrue condition _ ih =>
      exact .ifTrue (localComputationEvaluates_iff_exists_cost.mpr ⟨_, condition⟩) ih
  | ifFalse condition _ ih =>
      exact .ifFalse (localComputationEvaluates_iff_exists_cost.mpr ⟨_, condition⟩) ih

private theorem cost_exists
    {owner : Resolved.DeclarationId} {table : LocalNameTable} {environment : Resolved.Environment}
    {initialStore finalStore : Core.Store} {body : Syntax.Block} {value : Core.Value}
    (evaluation : LocalComputationReturnTreeEvaluates owner table environment
      initialStore body value finalStore) :
    ∃ cost, LocalComputationReturnTreeEvaluatesWithCost owner table environment
      initialStore body value finalStore cost := by
  induction evaluation with
  | bare => exact ⟨1, .bare⟩
  | expression child =>
      obtain ⟨_, costed⟩ := localComputationEvaluates_iff_exists_cost.mp child
      exact ⟨_, .expression costed⟩
  | block _ ih =>
      obtain ⟨_, costed⟩ := ih
      exact ⟨_, .block costed⟩
  | binding initializer _ ih =>
      obtain ⟨_, childCost⟩ := localComputationEvaluates_iff_exists_cost.mp initializer
      obtain ⟨_, tailCost⟩ := ih
      exact ⟨_, .binding childCost tailCost⟩
  | inferred initializer _ ih =>
      obtain ⟨_, childCost⟩ := localComputationEvaluates_iff_exists_cost.mp initializer
      obtain ⟨_, tailCost⟩ := ih
      exact ⟨_, .inferred childCost tailCost⟩
  | discard expression _ ih =>
      obtain ⟨_, childCost⟩ := localComputationEvaluates_iff_exists_cost.mp expression
      obtain ⟨_, tailCost⟩ := ih
      exact ⟨_, .discard childCost tailCost⟩
  | ifTrue condition _ ih =>
      obtain ⟨_, childCost⟩ := localComputationEvaluates_iff_exists_cost.mp condition
      obtain ⟨_, branchCost⟩ := ih
      exact ⟨_, .ifTrue childCost branchCost⟩
  | ifFalse condition _ ih =>
      obtain ⟨_, childCost⟩ := localComputationEvaluates_iff_exists_cost.mp condition
      obtain ⟨_, branchCost⟩ := ih
      exact ⟨_, .ifFalse childCost branchCost⟩

theorem localComputationReturnTreeEvaluates_iff_exists_cost
    {owner : Resolved.DeclarationId} {table : LocalNameTable} {environment : Resolved.Environment}
    {initialStore finalStore : Core.Store} {body : Syntax.Block} {value : Core.Value} :
    LocalComputationReturnTreeEvaluates owner table environment initialStore body value finalStore ↔
      ∃ cost, LocalComputationReturnTreeEvaluatesWithCost owner table environment
        initialStore body value finalStore cost :=
  ⟨cost_exists, fun ⟨_, evaluation⟩ => erase_cost evaluation⟩

theorem LocalComputationReturnTreeEvaluatesWithCost.deterministic
    {owner : Resolved.DeclarationId} {table : LocalNameTable} {environment : Resolved.Environment}
    {initialStore : Core.Store} {body : Syntax.Block} {left right : Core.Value}
    {leftStore rightStore : Core.Store} {leftCost rightCost : Nat}
    (first : LocalComputationReturnTreeEvaluatesWithCost owner table environment
      initialStore body left leftStore leftCost)
    (second : LocalComputationReturnTreeEvaluatesWithCost owner table environment
      initialStore body right rightStore rightCost) :
    left = right ∧ leftStore = rightStore ∧ leftCost = rightCost := by
  induction first generalizing right rightStore rightCost with
  | bare => cases second; exact ⟨rfl, rfl, rfl⟩
  | expression child =>
      cases second with
      | expression other => exact child.deterministic other
  | block _ ih =>
      cases second with
      | block other => exact ih other
  | binding initializer _ ih =>
      cases second with
      | binding otherInitializer otherTail =>
          obtain ⟨rfl, rfl, rfl⟩ := initializer.deterministic otherInitializer
          obtain ⟨rfl, rfl, rfl⟩ := ih otherTail
          exact ⟨rfl, rfl, rfl⟩
  | inferred initializer _ ih =>
      cases second with
      | inferred otherInitializer otherTail =>
          obtain ⟨rfl, rfl, rfl⟩ := initializer.deterministic otherInitializer
          obtain ⟨rfl, rfl, rfl⟩ := ih otherTail
          exact ⟨rfl, rfl, rfl⟩
  | discard expression _ ih =>
      cases second with
      | discard otherExpression otherTail =>
          obtain ⟨_, rfl, rfl⟩ := expression.deterministic otherExpression
          obtain ⟨rfl, rfl, rfl⟩ := ih otherTail
          exact ⟨rfl, rfl, rfl⟩
  | ifTrue condition _ ih =>
      cases second with
      | ifTrue otherCondition otherBranch =>
          obtain ⟨_, rfl, rfl⟩ := condition.deterministic otherCondition
          obtain ⟨rfl, rfl, rfl⟩ := ih otherBranch
          exact ⟨rfl, rfl, rfl⟩
      | ifFalse otherCondition _ => cases (condition.deterministic otherCondition).1
  | ifFalse condition _ ih =>
      cases second with
      | ifTrue otherCondition _ => cases (condition.deterministic otherCondition).1
      | ifFalse otherCondition otherBranch =>
          obtain ⟨_, rfl, rfl⟩ := condition.deterministic otherCondition
          obtain ⟨rfl, rfl, rfl⟩ := ih otherBranch
          exact ⟨rfl, rfl, rfl⟩

end Solcore.Frontend

/-!
## Consolidated module: `Solcore.Frontend.LocalComputationReturnTreeExecutionProperties`
-/

/-! Exact mixed-body correspondence needs the original ordered IDs, not typed
runtime values. Every strict child passes its actual store to its continuation. -/

set_option autoImplicit false

namespace Solcore.Frontend

theorem LocalComputationReturnTreeElaborates.evaluates_iff
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {inputs : LocalTypeInputs}
    {environment : Resolved.Environment} {body : Syntax.Block} {core : Core.Expr} {type : Core.Ty}
    (elaboration : LocalComputationReturnTreeElaborates types owner inputs body core type)
    (sameIds : environment.ids = inputs.context.ids)
    {initialStore finalStore : Core.Store} {value : Core.Value} :
    LocalComputationReturnTreeEvaluates owner inputs.names environment initialStore body value finalStore ↔
      Core.Evaluates environment.values initialStore core value finalStore := by
  induction elaboration generalizing environment initialStore finalStore value with
  | bare =>
      constructor <;> intro evaluation <;> cases evaluation <;> constructor
  | expression child =>
      constructor
      · intro evaluation
        cases evaluation with
        | expression evaluated => exact (child.evaluates_iff sameIds).mp evaluated
      · intro evaluation
        exact .expression ((child.evaluates_iff sameIds).mpr evaluation)
  | block _ ih =>
      constructor
      · intro evaluation
        cases evaluation with
        | block evaluated => exact (ih sameIds).mp evaluated
      · intro evaluation
        exact .block ((ih sameIds).mpr evaluation)
  | @binding inputs _ _ name _ _ _ declaredType _ _ _ _ _ child _ ih =>
      constructor
      · intro evaluation
        cases evaluation with
        | binding initializer tail =>
            rename_i middleStore boundValue
            refine .letE ((child.evaluates_iff sameIds).mp initializer) ?_
            apply (ih (environment := (Resolved.freshLocalId owner inputs.ids, boundValue) :: environment) ?_).mp
            · simpa only [LocalTypeInputs.bindFresh_names, LocalTypeInputs.names_ids] using tail
            · simpa only [LocalTypeInputs.bindFresh_context, Resolved.LocalScope.ids, List.map_cons]
                using congrArg (List.cons _) sameIds
      · intro evaluation
        cases evaluation with
        | letE initializer tail =>
            rename_i bodyStore boundValue
            apply LocalComputationReturnTreeEvaluates.binding ((child.evaluates_iff sameIds).mpr initializer)
            have evaluated := (ih (environment := (Resolved.freshLocalId owner inputs.ids, boundValue) :: environment) ?_).mpr tail
            · simpa only [LocalTypeInputs.bindFresh_names, LocalTypeInputs.names_ids] using evaluated
            · simpa only [LocalTypeInputs.bindFresh_context, Resolved.LocalScope.ids, List.map_cons]
                using congrArg (List.cons _) sameIds
  | @inferred inputs _ _ name _ _ inferredType _ _ _ _ child _ ih =>
      constructor
      · intro evaluation
        cases evaluation with
        | inferred initializer tail =>
            rename_i middleStore boundValue
            refine .letE ((child.evaluates_iff sameIds).mp initializer) ?_
            apply (ih (environment := (Resolved.freshLocalId owner inputs.ids, boundValue) :: environment) ?_).mp
            · simpa only [LocalTypeInputs.bindFresh_names, LocalTypeInputs.names_ids] using tail
            · simpa only [LocalTypeInputs.bindFresh_context, Resolved.LocalScope.ids, List.map_cons]
                using congrArg (List.cons _) sameIds
      · intro evaluation
        cases evaluation with
        | letE initializer tail =>
            rename_i bodyStore boundValue
            apply LocalComputationReturnTreeEvaluates.inferred ((child.evaluates_iff sameIds).mpr initializer)
            have evaluated := (ih (environment := (Resolved.freshLocalId owner inputs.ids, boundValue) :: environment) ?_).mpr tail
            · simpa only [LocalTypeInputs.bindFresh_names, LocalTypeInputs.names_ids] using evaluated
            · simpa only [LocalTypeInputs.bindFresh_context, Resolved.LocalScope.ids, List.map_cons]
                using congrArg (List.cons _) sameIds
  | discard child tailElaboration ih =>
      constructor
      · intro evaluation
        cases evaluation with
        | discard head tail =>
            rename_i middleStore discardedValue
            exact .letE ((child.evaluates_iff sameIds).mp head)
              ((tailElaboration.core_fragment.evaluates_insert_iff [] environment.values discardedValue).mpr
                ((ih sameIds).mp tail))
      · intro evaluation
        cases evaluation with
        | letE head tail =>
            exact .discard ((child.evaluates_iff sameIds).mpr head)
              ((ih sameIds).mpr ((tailElaboration.core_fragment.evaluates_insert_iff [] environment.values _).mp tail))
  | conditional guard _ _ thenIH elseIH =>
      constructor
      · intro evaluation
        cases evaluation with
        | ifTrue condition branch =>
            exact .ifTrue ((guard.evaluates_iff sameIds).mp condition) ((thenIH sameIds).mp branch)
        | ifFalse condition branch =>
            exact .ifFalse ((guard.evaluates_iff sameIds).mp condition) ((elseIH sameIds).mp branch)
      · intro evaluation
        cases evaluation with
        | ifTrue condition branch =>
            exact .ifTrue ((guard.evaluates_iff sameIds).mpr condition) ((thenIH sameIds).mpr branch)
        | ifFalse condition branch =>
            exact .ifFalse ((guard.evaluates_iff sameIds).mpr condition) ((elseIH sameIds).mpr branch)

end Solcore.Frontend

/-!
## Consolidated module: `Solcore.Frontend.LocalComputationReturnTreeCostProperties`
-/

/-! Supplied actual costs compose through mixed statements. A hidden discard
slot preserves the complete tail path, including its effects and actual captures. -/

set_option autoImplicit false

namespace Solcore.Frontend

private theorem insert_zero_path {expr : Core.Expr} (fragment : LocalComputationFragment expr)
    {environment : Core.Environment} {initialStore finalStore : Core.Store}
    {value : Core.Value} {cost : Nat}
    (path : Core.Steps cost (.initial expr environment initialStore) (.final value finalStore))
    (inserted : Core.Value) (continuation : List Core.Frame) :
    Core.Steps cost ⟨.eval (expr.weakenAt 0) (inserted :: environment), continuation, initialStore⟩
      ⟨.ret value, continuation, finalStore⟩ := by
  obtain ⟨commonCost, paths⟩ := fragment.insertion_paths [] environment inserted (Core.steps_from_initial_sound path)
  have sameCost := (path.final_unique (paths []).1).1
  exact sameCost.symm ▸ (paths continuation).2

theorem LocalComputationReturnTreeEvaluatesWithCost.toStepsWithContinuation
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {inputs : LocalTypeInputs}
    {environment : Resolved.Environment} {initialStore finalStore : Core.Store}
    {body : Syntax.Block} {value : Core.Value} {cost : Nat}
    (evaluation : LocalComputationReturnTreeEvaluatesWithCost owner inputs.names environment
      initialStore body value finalStore cost)
    {core : Core.Expr} {type : Core.Ty}
    (elaboration : LocalComputationReturnTreeElaborates types owner inputs body core type)
    (sameIds : environment.ids = inputs.context.ids) (continuation : List Core.Frame) :
    Core.Steps cost ⟨.eval core environment.values, continuation, initialStore⟩
      ⟨.ret value, continuation, finalStore⟩ := by
  induction elaboration generalizing environment initialStore finalStore value cost continuation with
  | bare => cases evaluation; exact .cons .unit .refl
  | expression child =>
      cases evaluation with
      | expression actual => exact actual.toStepsWithContinuation child sameIds continuation
  | block _ ih =>
      cases evaluation with
      | block actual => exact ih actual sameIds continuation
  | @binding inputs _ _ _ _ _ _ _ _ _ _ _ _ child _ ih =>
      cases evaluation with
      | binding initializer tail =>
          rename_i middleStore boundValue initializerCost tailCost
          apply CostStepComposition.letE (initializer.toStepsWithContinuation child sameIds _)
          apply ih (environment := (Resolved.freshLocalId owner inputs.ids, boundValue) :: environment)
          · simpa only [LocalTypeInputs.bindFresh_names, LocalTypeInputs.names_ids] using tail
          · simpa only [LocalTypeInputs.bindFresh_context, Resolved.LocalScope.ids, List.map_cons]
              using congrArg (List.cons _) sameIds
  | @inferred inputs _ _ _ _ _ _ _ _ _ _ child _ ih =>
      cases evaluation with
      | inferred initializer tail =>
          rename_i middleStore boundValue initializerCost tailCost
          apply CostStepComposition.letE (initializer.toStepsWithContinuation child sameIds _)
          apply ih (environment := (Resolved.freshLocalId owner inputs.ids, boundValue) :: environment)
          · simpa only [LocalTypeInputs.bindFresh_names, LocalTypeInputs.names_ids] using tail
          · simpa only [LocalTypeInputs.bindFresh_context, Resolved.LocalScope.ids, List.map_cons]
              using congrArg (List.cons _) sameIds
  | discard child tailElaboration ih =>
      cases evaluation with
      | discard expression tail =>
          rename_i middleStore discardedValue expressionCost tailCost
          exact CostStepComposition.letE (expression.toStepsWithContinuation child sameIds _)
            (insert_zero_path tailElaboration.core_fragment (ih tail sameIds []) discardedValue continuation)
  | conditional guard _ _ thenIH elseIH =>
      cases evaluation with
      | ifTrue condition branch =>
          exact CostStepComposition.ifTrue (condition.toStepsWithContinuation guard sameIds _)
            (thenIH branch sameIds continuation)
      | ifFalse condition branch =>
          exact CostStepComposition.ifFalse (condition.toStepsWithContinuation guard sameIds _)
            (elseIH branch sameIds continuation)

theorem LocalComputationReturnTreeElaborates.evaluatesWithCost_iff_steps
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {inputs : LocalTypeInputs}
    {environment : Resolved.Environment} {body : Syntax.Block} {core : Core.Expr} {type : Core.Ty}
    (elaboration : LocalComputationReturnTreeElaborates types owner inputs body core type)
    (sameIds : environment.ids = inputs.context.ids)
    {initialStore finalStore : Core.Store} {value : Core.Value} {cost : Nat} :
    LocalComputationReturnTreeEvaluatesWithCost owner inputs.names environment
      initialStore body value finalStore cost ↔
      Core.Steps cost (.initial core environment.values initialStore) (.final value finalStore) := by
  constructor
  · intro evaluation
    exact evaluation.toStepsWithContinuation elaboration sameIds []
  · intro path
    have evaluation := (elaboration.evaluates_iff sameIds).mpr (Core.steps_from_initial_sound path)
    obtain ⟨actualCost, actual⟩ := localComputationReturnTreeEvaluates_iff_exists_cost.mp evaluation
    have sameCost := (path.final_unique (actual.toStepsWithContinuation elaboration sameIds [])).1
    exact sameCost.symm ▸ actual

end Solcore.Frontend

/-!
## Consolidated module: `Solcore.Frontend.LocalComputationReturnTreeProperties`
-/

/-! Whole mixed-body checking is equivalent to independent exact provenance.
The recursive calls retain the original tail and branch syntax and input scope. -/

set_option autoImplicit false

namespace Solcore.Frontend

private theorem binding_children
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {inputs : LocalTypeInputs}
    {blockSpan letSpan : Syntax.SourceSpan} {name : Syntax.Identifier}
    {annotation : Syntax.TypeExpr} {initializer : Syntax.Expr} {rest : List Syntax.Statement}
    {core : Core.Expr} {type : Core.Ty}
    (accepted : elaborateLocalComputationReturnTree? types owner inputs
      ⟨blockSpan, ⟨letSpan, .letDecl name (some annotation) (some initializer)⟩ :: rest⟩ = some (core, type)) :
    ∃ declaredType initializerCore tailCore,
      name.value ∉ inputs.names.map Prod.fst ∧ interpretStructuralType? types annotation = some declaredType ∧
      elaborateLocalComputation? inputs.names inputs.context initializer = some (initializerCore, declaredType) ∧
      elaborateLocalComputationReturnTree? types owner (inputs.bindFresh owner name.value declaredType)
        ⟨blockSpan, rest⟩ = some (tailCore, type) ∧ core = .letE initializerCore tailCore := by
  rw [elaborateLocalComputationReturnTree?] at accepted
  split at accepted
  next unused =>
    simp only [bind, Option.bind_eq_some_iff] at accepted
    obtain ⟨declaredType, meaning, ⟨initializerCore, initializerType⟩, initializerAccepted, remaining⟩ := accepted
    split at remaining
    next sameType =>
      change initializerType = declaredType at sameType
      subst initializerType
      simp only [Option.bind_eq_some_iff] at remaining
      obtain ⟨⟨tailCore, returnType⟩, tailAccepted, result⟩ := remaining
      change some (.letE initializerCore tailCore, returnType) = some (core, type) at result
      simp only [Option.some.injEq, Prod.mk.injEq] at result
      rcases result with ⟨rfl, rfl⟩
      exact ⟨declaredType, initializerCore, tailCore, unused, meaning, initializerAccepted, tailAccepted, rfl⟩
    next different => cases remaining
  next used => cases accepted

private theorem inferred_children
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {inputs : LocalTypeInputs}
    {blockSpan letSpan : Syntax.SourceSpan} {name : Syntax.Identifier}
    {initializer : Syntax.Expr} {rest : List Syntax.Statement} {core : Core.Expr} {type : Core.Ty}
    (accepted : elaborateLocalComputationReturnTree? types owner inputs
      ⟨blockSpan, ⟨letSpan, .letDecl name none (some initializer)⟩ :: rest⟩ = some (core, type)) :
    ∃ initializerType initializerCore tailCore,
      name.value ∉ inputs.names.map Prod.fst ∧
      elaborateLocalComputation? inputs.names inputs.context initializer = some (initializerCore, initializerType) ∧
      elaborateLocalComputationReturnTree? types owner (inputs.bindFresh owner name.value initializerType)
        ⟨blockSpan, rest⟩ = some (tailCore, type) ∧ core = .letE initializerCore tailCore := by
  rw [elaborateLocalComputationReturnTree?] at accepted
  split at accepted
  next unused =>
    simp only [bind, Option.bind_eq_some_iff] at accepted
    obtain ⟨⟨initializerCore, initializerType⟩, initializerAccepted,
      ⟨tailCore, returnType⟩, tailAccepted, result⟩ := accepted
    change some (.letE initializerCore tailCore, returnType) = some (core, type) at result
    simp only [Option.some.injEq, Prod.mk.injEq] at result
    rcases result with ⟨rfl, rfl⟩
    exact ⟨initializerType, initializerCore, tailCore, unused, initializerAccepted, tailAccepted, rfl⟩
  next used => cases accepted

private theorem conditional_children
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {inputs : LocalTypeInputs}
    {blockSpan ifSpan : Syntax.SourceSpan} {condition : Syntax.Expr}
    {thenBody elseBody : Syntax.Block} {core : Core.Expr} {type : Core.Ty}
    (accepted : elaborateLocalComputationReturnTree? types owner inputs
      ⟨blockSpan, [⟨ifSpan, .ifThen condition thenBody (some elseBody)⟩]⟩ = some (core, type)) :
    ∃ conditionCore thenCore elseCore,
      elaborateLocalComputation? inputs.names inputs.context condition = some (conditionCore, .bool) ∧
      elaborateLocalComputationReturnTree? types owner inputs thenBody = some (thenCore, type) ∧
      elaborateLocalComputationReturnTree? types owner inputs elseBody = some (elseCore, type) ∧
      core = .ifE conditionCore thenCore elseCore := by
  rw [elaborateLocalComputationReturnTree?] at accepted
  simp only [bind, Option.bind_eq_some_iff] at accepted
  obtain ⟨⟨conditionCore, conditionType⟩, conditionAccepted, remaining⟩ := accepted
  split at remaining
  next conditionBool =>
    change conditionType = .bool at conditionBool
    subst conditionType
    simp only [Option.bind_eq_some_iff] at remaining
    obtain ⟨⟨thenCore, thenType⟩, thenAccepted, ⟨elseCore, elseType⟩, elseAccepted, result⟩ := remaining
    split at result
    next sameType =>
      change thenType = elseType at sameType
      subst elseType
      change some (.ifE conditionCore thenCore elseCore, thenType) = some (core, type) at result
      simp only [Option.some.injEq, Prod.mk.injEq] at result
      rcases result with ⟨rfl, rfl⟩
      exact ⟨conditionCore, thenCore, elseCore, conditionAccepted, thenAccepted, elseAccepted, rfl⟩
    next different => cases result
  next notBool => cases remaining

private theorem discard_children
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {inputs : LocalTypeInputs}
    {blockSpan statementSpan : Syntax.SourceSpan} {source : Syntax.Expr}
    {rest : List Syntax.Statement} {core : Core.Expr} {type : Core.Ty}
    (accepted : elaborateLocalComputationReturnTree? types owner inputs
      ⟨blockSpan, ⟨statementSpan, .expression source true⟩ :: rest⟩ = some (core, type)) :
    ∃ expressionType expressionCore tailCore,
      elaborateLocalComputation? inputs.names inputs.context source = some (expressionCore, expressionType) ∧
      elaborateLocalComputationReturnTree? types owner inputs ⟨blockSpan, rest⟩ = some (tailCore, type) ∧
      core = .letE expressionCore (tailCore.weakenAt 0) := by
  rw [elaborateLocalComputationReturnTree?] at accepted
  simp only [bind, Option.bind_eq_some_iff] at accepted
  obtain ⟨⟨expressionCore, expressionType⟩, expressionAccepted,
    ⟨tailCore, returnType⟩, tailAccepted, result⟩ := accepted
  change some (.letE expressionCore (tailCore.weakenAt 0), returnType) = some (core, type) at result
  simp only [Option.some.injEq, Prod.mk.injEq] at result
  rcases result with ⟨rfl, rfl⟩
  exact ⟨expressionType, expressionCore, tailCore, expressionAccepted, tailAccepted, rfl⟩

private theorem complete
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {inputs : LocalTypeInputs}
    {body : Syntax.Block} {core : Core.Expr} {type : Core.Ty}
    (elaboration : LocalComputationReturnTreeElaborates types owner inputs body core type) :
    elaborateLocalComputationReturnTree? types owner inputs body = some (core, type) := by
  induction elaboration with
  | bare => simp only [elaborateLocalComputationReturnTree?]
  | expression child =>
      simpa only [elaborateLocalComputationReturnTree?] using elaborateLocalComputation?_iff.mpr child
  | block _ ih => simpa only [elaborateLocalComputationReturnTree?] using ih
  | binding meaning unused initializer _ ih =>
      rw [elaborateLocalComputationReturnTree?]
      simp only [if_pos unused, meaning.complete, elaborateLocalComputation?_iff.mpr initializer,
        ih, bind, Option.bind_some, ite_true, pure, Pure.pure]
  | inferred unused initializer _ ih =>
      rw [elaborateLocalComputationReturnTree?]
      simp only [if_pos unused, elaborateLocalComputation?_iff.mpr initializer,
        ih, bind, Option.bind_some, pure, Pure.pure]
  | discard expression _ ih =>
      rw [elaborateLocalComputationReturnTree?]
      simp only [elaborateLocalComputation?_iff.mpr expression, ih, bind, Option.bind_some, pure, Pure.pure]
  | conditional condition _ _ thenIH elseIH =>
      rw [elaborateLocalComputationReturnTree?]
      simp [elaborateLocalComputation?_iff.mpr condition, thenIH, elseIH]

private theorem sound
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {inputs : LocalTypeInputs}
    {body : Syntax.Block} {core : Core.Expr} {type : Core.Ty}
    (accepted : elaborateLocalComputationReturnTree? types owner inputs body = some (core, type)) :
    LocalComputationReturnTreeElaborates types owner inputs body core type := by
  cases body with
  | mk blockSpan statements =>
      cases statements with
      | nil => simp only [elaborateLocalComputationReturnTree?, reduceCtorEq] at accepted
      | cons statement rest =>
          cases statement with
          | mk statementSpan payload =>
              cases payload <;> try simp only [elaborateLocalComputationReturnTree?, reduceCtorEq] at accepted
              case returnStmt returned =>
                cases rest with
                | nil =>
                    cases returned with
                    | none =>
                        simp only [elaborateLocalComputationReturnTree?, Option.some.injEq, Prod.mk.injEq] at accepted
                        rcases accepted with ⟨rfl, rfl⟩
                        exact .bare
                    | some source => exact .expression (elaborateLocalComputation?_iff.mp
                        (by simpa only [elaborateLocalComputationReturnTree?] using accepted))
                | cons _ _ => simp only [elaborateLocalComputationReturnTree?, reduceCtorEq] at accepted
              case block statements =>
                cases rest with
                | nil => exact .block (sound
                    (by simpa only [elaborateLocalComputationReturnTree?] using accepted))
                | cons _ _ => simp only [elaborateLocalComputationReturnTree?, reduceCtorEq] at accepted
              case letDecl name optionalType optionalInitializer =>
                cases optionalType with
                | none =>
                    cases optionalInitializer with
                    | none => simp only [elaborateLocalComputationReturnTree?, reduceCtorEq] at accepted
                    | some initializer =>
                        obtain ⟨initializerType, initializerCore, tailCore, unused,
                          initializerAccepted, tailAccepted, rfl⟩ := inferred_children accepted
                        exact .inferred unused (elaborateLocalComputation?_iff.mp initializerAccepted)
                          (sound tailAccepted)
                | some annotation =>
                    cases optionalInitializer with
                    | none => simp only [elaborateLocalComputationReturnTree?, reduceCtorEq] at accepted
                    | some initializer =>
                        obtain ⟨declaredType, initializerCore, tailCore, unused, meaning,
                          initializerAccepted, tailAccepted, rfl⟩ := binding_children accepted
                        exact .binding (interpretStructuralType?_sound meaning) unused
                          (elaborateLocalComputation?_iff.mp initializerAccepted) (sound tailAccepted)
              case ifThen condition thenBody optionalElse =>
                cases rest with
                | cons _ _ => simp only [elaborateLocalComputationReturnTree?, reduceCtorEq] at accepted
                | nil =>
                    cases optionalElse with
                    | none => simp only [elaborateLocalComputationReturnTree?, reduceCtorEq] at accepted
                    | some elseBody =>
                        obtain ⟨conditionCore, thenCore, elseCore, conditionAccepted,
                          thenAccepted, elseAccepted, rfl⟩ := conditional_children accepted
                        exact .conditional (elaborateLocalComputation?_iff.mp conditionAccepted)
                          (sound thenAccepted) (sound elseAccepted)
              case expression source trailingSemicolon =>
                cases trailingSemicolon with
                | false => simp only [elaborateLocalComputationReturnTree?, reduceCtorEq] at accepted
                | true =>
                    obtain ⟨expressionType, expressionCore, tailCore,
                      expressionAccepted, tailAccepted, rfl⟩ := discard_children accepted
                    exact .discard (elaborateLocalComputation?_iff.mp expressionAccepted) (sound tailAccepted)
termination_by sizeOf body

theorem elaborateLocalComputationReturnTree?_iff
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {inputs : LocalTypeInputs}
    {body : Syntax.Block} {core : Core.Expr} {type : Core.Ty} :
    elaborateLocalComputationReturnTree? types owner inputs body = some (core, type) ↔
      LocalComputationReturnTreeElaborates types owner inputs body core type :=
  ⟨sound, complete⟩

end Solcore.Frontend

/-!
## Consolidated module: `Solcore.Frontend.LocalComputationReturnTreeTypingProperties`
-/

/-! Independent mixed-body typing needs no actual inhabitants or runtime world.
Hidden discard slots use general Core typing weakening, not a pure-fragment law. -/

set_option autoImplicit false

namespace Solcore.Frontend

private theorem hasType
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {inputs : LocalTypeInputs}
    {body : Syntax.Block} {core : Core.Expr} {type : Core.Ty}
    (elaboration : LocalComputationReturnTreeElaborates types owner inputs body core type) :
    LocalComputationReturnTreeHasType types owner inputs body type := by
  induction elaboration with
  | bare => exact .bare
  | expression child => exact .expression (localComputationHasType_iff_elaborates.mpr ⟨_, child⟩)
  | block _ ih => exact .block ih
  | binding meaning unused initializer _ ih =>
      exact .binding meaning unused (localComputationHasType_iff_elaborates.mpr ⟨_, initializer⟩) ih
  | inferred unused initializer _ ih =>
      exact .inferred unused (localComputationHasType_iff_elaborates.mpr ⟨_, initializer⟩) ih
  | discard expression _ ih =>
      exact .discard (localComputationHasType_iff_elaborates.mpr ⟨_, expression⟩) ih
  | conditional condition _ _ thenIH elseIH =>
      exact .conditional (localComputationHasType_iff_elaborates.mpr ⟨_, condition⟩) thenIH elseIH

private theorem elaborates
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {inputs : LocalTypeInputs}
    {body : Syntax.Block} {type : Core.Ty}
    (typing : LocalComputationReturnTreeHasType types owner inputs body type) :
    ∃ core, LocalComputationReturnTreeElaborates types owner inputs body core type := by
  induction typing with
  | bare => exact ⟨.unit, .bare⟩
  | expression child =>
      obtain ⟨core, elaboration⟩ := localComputationHasType_iff_elaborates.mp child
      exact ⟨core, .expression elaboration⟩
  | block _ ih =>
      obtain ⟨core, elaboration⟩ := ih
      exact ⟨core, .block elaboration⟩
  | binding meaning unused initializer _ ih =>
      obtain ⟨initializerCore, initializerElaboration⟩ := localComputationHasType_iff_elaborates.mp initializer
      obtain ⟨tailCore, tailElaboration⟩ := ih
      exact ⟨.letE initializerCore tailCore, .binding meaning unused initializerElaboration tailElaboration⟩
  | inferred unused initializer _ ih =>
      obtain ⟨initializerCore, initializerElaboration⟩ := localComputationHasType_iff_elaborates.mp initializer
      obtain ⟨tailCore, tailElaboration⟩ := ih
      exact ⟨.letE initializerCore tailCore, .inferred unused initializerElaboration tailElaboration⟩
  | discard expression _ ih =>
      obtain ⟨expressionCore, expressionElaboration⟩ := localComputationHasType_iff_elaborates.mp expression
      obtain ⟨tailCore, tailElaboration⟩ := ih
      exact ⟨.letE expressionCore (tailCore.weakenAt 0), .discard expressionElaboration tailElaboration⟩
  | conditional condition _ _ thenIH elseIH =>
      obtain ⟨conditionCore, conditionElaboration⟩ := localComputationHasType_iff_elaborates.mp condition
      obtain ⟨thenCore, thenElaboration⟩ := thenIH
      obtain ⟨elseCore, elseElaboration⟩ := elseIH
      exact ⟨.ifE conditionCore thenCore elseCore, .conditional conditionElaboration thenElaboration elseElaboration⟩

theorem localComputationReturnTreeHasType_iff_elaborates
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {inputs : LocalTypeInputs}
    {body : Syntax.Block} {type : Core.Ty} :
    LocalComputationReturnTreeHasType types owner inputs body type ↔
      ∃ core, LocalComputationReturnTreeElaborates types owner inputs body core type :=
  ⟨elaborates, fun ⟨_, elaboration⟩ => hasType elaboration⟩

theorem LocalComputationReturnTreeElaborates.core_hasType
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {inputs : LocalTypeInputs}
    {body : Syntax.Block} {core : Core.Expr} {type : Core.Ty}
    (elaboration : LocalComputationReturnTreeElaborates types owner inputs body core type) :
    Core.HasType inputs.context.values core type := by
  induction elaboration with
  | bare => exact .unit
  | expression child => exact child.core_hasType
  | block _ ih => exact ih
  | binding _ _ initializer _ ih | inferred _ initializer _ ih =>
      exact .letE initializer.core_hasType
        (by simpa only [LocalTypeInputs.bindFresh_context, Resolved.LocalScope.values, List.map_cons, Prod.snd] using ih)
  | discard expression _ ih =>
      exact .letE expression.core_hasType (by simpa only [Core.Context.insertAt] using ih.weakenAt 0)
  | conditional condition _ _ thenIH elseIH => exact .ifE condition.core_hasType thenIH elseIH

end Solcore.Frontend
