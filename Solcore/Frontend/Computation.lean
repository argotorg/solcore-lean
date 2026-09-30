import Solcore.Syntax.Term
import Solcore.Core.Syntax
import Solcore.Frontend.LocalFunctionApplication
import Solcore.Core.LocalFragment
import Solcore.Core.Eval
import Solcore.Core.BoundedSafety
import Solcore.Core.Renaming
import Solcore.Frontend.StructuralType
import Solcore.Frontend.LocalTypeInputs
import Solcore.Frontend.WordMatch
import Solcore.Frontend.RuntimeFunction
import Solcore.Frontend.LocalReference
import Solcore.Resolved.Eval
import Solcore.Resolved.FreshIdentity
import Solcore.Core.ExactFuelProperties
import Solcore.Frontend.RuntimeParameterDeclarations
import Solcore.Frontend.RuntimeParameters
import Solcore.Frontend.LocalName
import Solcore.Frontend.LocalOwnerRenaming
import Solcore.Resolved.Renaming
import Solcore.Core.Safety

/-! Computation bodies, return trees, compiled functions, and their proof support. -/

/-!
## Consolidated module: `Solcore.Frontend.ComputationBindingScope`
-/

/-! Source-only let-name exposure for the supported computation-body profile.
Explicit blocks and match arms are scope barriers; bare if branches are not. -/

set_option autoImplicit false

namespace Solcore.Frontend

inductive ExposesComputationLetName (name : String) : Syntax.Block → Prop where
  | binding {blockSpan letSpan : Syntax.SourceSpan} {identifier : Syntax.Identifier}
      {annotation : Option Syntax.TypeExpr} {initializer : Option Syntax.Expr}
      {rest : List Syntax.Statement} (spelling : identifier.value = name) :
      ExposesComputationLetName name
        ⟨blockSpan, ⟨letSpan, .letDecl identifier annotation initializer⟩ :: rest⟩
  | tail {blockSpan : Syntax.SourceSpan} {statement : Syntax.Statement}
      {rest : List Syntax.Statement}
      (exposed : ExposesComputationLetName name ⟨blockSpan, rest⟩) :
      ExposesComputationLetName name ⟨blockSpan, statement :: rest⟩
  | thenBranch {blockSpan ifSpan : Syntax.SourceSpan} {condition : Syntax.Expr}
      {thenBody : Syntax.Block} {elseBody : Option Syntax.Block} {rest : List Syntax.Statement}
      (exposed : ExposesComputationLetName name thenBody) :
      ExposesComputationLetName name
        ⟨blockSpan, ⟨ifSpan, .ifThen condition thenBody elseBody⟩ :: rest⟩
  | elseBranch {blockSpan ifSpan : Syntax.SourceSpan} {condition : Syntax.Expr}
      {thenBody elseBody : Syntax.Block} {rest : List Syntax.Statement}
      (exposed : ExposesComputationLetName name elseBody) :
      ExposesComputationLetName name
        ⟨blockSpan, ⟨ifSpan, .ifThen condition thenBody (some elseBody)⟩ :: rest⟩

def ComputationNamesProtected (names : List String) (body : Syntax.Block) : Prop :=
  ∀ name, ExposesComputationLetName name body → name ∉ names

def computationBlockPreservesNames (names : List String) (body : Syntax.Block) : Bool :=
  match body with
  | ⟨_, []⟩ => true
  | ⟨span, ⟨_, .letDecl identifier _ _⟩ :: rest⟩ =>
      decide (identifier.value ∉ names) && computationBlockPreservesNames names ⟨span, rest⟩
  | ⟨span, ⟨_, .ifThen _ thenBody none⟩ :: rest⟩ =>
      computationBlockPreservesNames names thenBody &&
        computationBlockPreservesNames names ⟨span, rest⟩
  | ⟨span, ⟨_, .ifThen _ thenBody (some elseBody)⟩ :: rest⟩ =>
      computationBlockPreservesNames names thenBody &&
        computationBlockPreservesNames names elseBody &&
        computationBlockPreservesNames names ⟨span, rest⟩
  | ⟨span, _ :: rest⟩ => computationBlockPreservesNames names ⟨span, rest⟩
termination_by sizeOf body
decreasing_by all_goals simp_wf; all_goals omega

end Solcore.Frontend

/-!
## Consolidated module: `Solcore.Frontend.ComputationBindingScopeProperties`
-/

/-! Exact source-only name protection, including rejection and restriction to
fewer protected names. No child checker, typing or runtime law is assumed. -/

set_option autoImplicit false

namespace Solcore.Frontend

private theorem preserves_tail {names : List String} {span : Syntax.SourceSpan}
    {statement : Syntax.Statement} {rest : List Syntax.Statement}
    (accepted : computationBlockPreservesNames names ⟨span, statement :: rest⟩ = true) :
    computationBlockPreservesNames names ⟨span, rest⟩ = true := by
  rcases statement with ⟨statementSpan, payload⟩
  cases payload with
  | ifThen condition thenBody elseBody =>
      cases elseBody <;> simp_all only [computationBlockPreservesNames, Bool.and_eq_true]
  | _ => simp_all only [computationBlockPreservesNames, Bool.and_eq_true]

private theorem bindingScope_sound {names : List String} {body : Syntax.Block}
    (accepted : computationBlockPreservesNames names body = true) :
    ComputationNamesProtected names body := by
  intro name exposed
  induction exposed with
  | binding spelling =>
      subst name
      simp only [computationBlockPreservesNames, Bool.and_eq_true, decide_eq_true_eq] at accepted
      exact accepted.1
  | tail exposed ih => exact ih (preserves_tail accepted)
  | @thenBranch blockSpan ifSpan condition thenBody elseBody rest exposed ih =>
      cases elseBody <;> simp only [computationBlockPreservesNames, Bool.and_eq_true] at accepted
      · exact ih accepted.1
      · exact ih accepted.1.1
  | elseBranch exposed ih =>
      simp only [computationBlockPreservesNames, Bool.and_eq_true] at accepted
      exact ih accepted.1.2

private theorem bindingScope_complete {names : List String} {body : Syntax.Block}
    (protection : ComputationNamesProtected names body) :
    computationBlockPreservesNames names body = true := by
  match body with
  | ⟨_, []⟩ => simp only [computationBlockPreservesNames]
  | ⟨span, statement :: rest⟩ =>
      have tail : ComputationNamesProtected names ⟨span, rest⟩ :=
        fun name exposed => protection name (.tail exposed)
      cases statementShape : statement with
      | mk statementSpan payload =>
          cases payloadShape : payload with
          | letDecl identifier annotation initializer =>
              simp only [statementShape, payloadShape] at protection
              simp only [computationBlockPreservesNames, Bool.and_eq_true, decide_eq_true_eq]
              exact ⟨protection identifier.value (.binding rfl), bindingScope_complete tail⟩
          | ifThen condition thenBody elseBody =>
              simp only [statementShape, payloadShape] at protection
              have yes : ComputationNamesProtected names thenBody :=
                fun name exposed => protection name (.thenBranch exposed)
              cases elseBody with
              | none =>
                  simp only [computationBlockPreservesNames, Bool.and_eq_true]
                  exact ⟨bindingScope_complete yes, bindingScope_complete tail⟩
              | some noBody =>
                  have no : ComputationNamesProtected names noBody :=
                    fun name exposed => protection name (.elseBranch exposed)
                  simp only [computationBlockPreservesNames, Bool.and_eq_true]
                  exact ⟨⟨bindingScope_complete yes, bindingScope_complete no⟩,
                    bindingScope_complete tail⟩
          | _ => simpa only [computationBlockPreservesNames] using
              bindingScope_complete (body := ⟨span, rest⟩) tail
termination_by sizeOf body
decreasing_by all_goals simp_wf; all_goals simp_all; all_goals omega

/-- Acceptance is exactly absence of an exposed original let spelling from the
protected list, regardless of source spans or unsupported child expressions. -/
theorem computationBlockPreservesNames_iff {names : List String} {body : Syntax.Block} :
    computationBlockPreservesNames names body = true ↔ ComputationNamesProtected names body :=
  ⟨bindingScope_sound, bindingScope_complete⟩

/-- A rejected guard has an actual exposed source occurrence of a protected name. -/
theorem computationBlockPreservesNames_eq_false_iff {names : List String} {body : Syntax.Block} :
    computationBlockPreservesNames names body = false ↔
      ∃ name, name ∈ names ∧ ExposesComputationLetName name body := by
  rw [Bool.eq_false_iff]
  change (¬ computationBlockPreservesNames names body = true) ↔ _
  rw [computationBlockPreservesNames_iff]
  constructor
  · intro rejected
    apply Classical.byContradiction
    intro noWitness
    exact rejected (fun name exposed member => noWitness ⟨name, member, exposed⟩)
  · rintro ⟨name, member, exposed⟩ protection
    exact protection name exposed member

/-- Protection persists for any list whose spellings occur in the protected list. -/
theorem ComputationNamesProtected.subset {small large : List String} {body : Syntax.Block}
    (protection : ComputationNamesProtected large body) (included : small ⊆ large) :
    ComputationNamesProtected small body :=
  fun name exposed member => protection name exposed (included member)

end Solcore.Frontend

/-!
## Consolidated module: `Solcore.Frontend.ComputationBodyFragment`
-/

/-! Whole caller bodies close an arbitrary child predicate under unit, lets,
conditionals and generated Word tests. Membership imposes no runtime contract. -/

set_option autoImplicit false

namespace Solcore.Frontend

inductive ComputationBodyFragment (F : Core.Expr → Prop) : Core.Expr → Prop where
  | unit : ComputationBodyFragment F .unit
  | leaf {expr : Core.Expr} (child : F expr) : ComputationBodyFragment F expr
  | letE {initializer body : Core.Expr}
      (head : ComputationBodyFragment F initializer) (tail : ComputationBodyFragment F body) :
      ComputationBodyFragment F (.letE initializer body)
  | ifE {condition thenBranch elseBranch : Core.Expr}
      (guard : ComputationBodyFragment F condition)
      (yes : ComputationBodyFragment F thenBranch) (no : ComputationBodyFragment F elseBranch) :
      ComputationBodyFragment F (.ifE condition thenBranch elseBranch)
  | wordTest {index : Nat} {word : Core.Word} :
      ComputationBodyFragment F (.binary .wordEq (.var index) (.word word))

end Solcore.Frontend

/-!
## Consolidated module: `Solcore.Frontend.ComputationBodyFragmentInsertionPaths`
-/

/-! One literal outcome and one cost are shared before every continuation.
Only the child's paired-path law is required, not its typing or raw insertion. -/

set_option autoImplicit false

namespace Solcore.Frontend

theorem ComputationBodyFragment.insertion_paths {F : Core.Expr → Prop}
    (childPaths : ∀ {expr}, F expr → ∀ (leading suffix : Core.Environment) (inserted : Core.Value),
      ∀ {initialStore finalStore value},
        Core.Evaluates (leading ++ suffix) initialStore expr value finalStore →
        ∃ cost, ∀ continuation,
          Core.Steps cost ⟨.eval expr (leading ++ suffix), continuation, initialStore⟩
            ⟨.ret value, continuation, finalStore⟩ ∧
          Core.Steps cost
            ⟨.eval (expr.weakenAt leading.length) (leading ++ inserted :: suffix), continuation, initialStore⟩
            ⟨.ret value, continuation, finalStore⟩)
    {expr : Core.Expr} (fragment : ComputationBodyFragment F expr)
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
  | wordTest =>
      exact (Core.Expr.LocalFragment.binary .var .word).insertion_paths leading suffix inserted evaluation
  | unit =>
      cases evaluation
      exact ⟨1, fun _ => ⟨.cons .unit .refl, by simpa only [Core.Expr.weakenAt] using (Core.Steps.cons Core.Transition.unit .refl)⟩⟩
  | leaf child => exact childPaths child leading suffix inserted evaluation
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
## Consolidated module: `Solcore.Frontend.ComputationBodyFragmentInsertionProperties`
-/

/-! Literal child insertion lifts through the whole body. Actual bound values
extend the retained prefix; no typing or closure reconstruction is required. -/

set_option autoImplicit false

namespace Solcore.Frontend

theorem ComputationBodyFragment.evaluates_insert_iff {F : Core.Expr → Prop}
    (childInsert : ∀ {expr}, F expr → ∀ (leading suffix : Core.Environment) (inserted : Core.Value),
      ∀ {initialStore finalStore value},
        Core.Evaluates (leading ++ inserted :: suffix) initialStore
          (expr.weakenAt leading.length) value finalStore ↔
          Core.Evaluates (leading ++ suffix) initialStore expr value finalStore)
    {expr : Core.Expr} (fragment : ComputationBodyFragment F expr)
    (leading suffix : Core.Environment) (inserted : Core.Value)
    {initialStore finalStore : Core.Store} {value : Core.Value} :
    Core.Evaluates (leading ++ inserted :: suffix) initialStore
      (expr.weakenAt leading.length) value finalStore ↔
      Core.Evaluates (leading ++ suffix) initialStore expr value finalStore := by
  induction fragment generalizing leading initialStore finalStore value with
  | wordTest =>
      exact (Core.Expr.LocalFragment.binary .var .word).evaluates_insert_iff leading suffix inserted
  | unit =>
      simp only [Core.Expr.weakenAt]
      constructor <;> intro evaluation <;> cases evaluation <;> exact .unit
  | leaf child => exact childInsert child leading suffix inserted
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
## Consolidated module: `Solcore.Frontend.ComputationBodyFragmentProperties`
-/

/-! Whole-tail weakening needs only weakening of the supplied child predicate.
The retained prefix gains one slot underneath each actual Core let binder. -/

set_option autoImplicit false

namespace Solcore.Frontend

theorem ComputationBodyFragment.weakenAt {F : Core.Expr → Prop}
    (childWeakens : ∀ {expr}, F expr → ∀ cutoff, F (expr.weakenAt cutoff))
    {expr : Core.Expr} (fragment : ComputationBodyFragment F expr) (cutoff : Nat) :
    ComputationBodyFragment F (expr.weakenAt cutoff) := by
  induction fragment generalizing cutoff with
  | unit => simpa only [Core.Expr.weakenAt] using (ComputationBodyFragment.unit (F := F))
  | wordTest =>
      simp only [Core.Expr.weakenAt]
      split <;> exact .wordTest
  | leaf child => exact .leaf (childWeakens child cutoff)
  | letE _ _ headIH tailIH =>
      simp only [Core.Expr.weakenAt]
      exact .letE (headIH cutoff) (tailIH (cutoff + 1))
  | ifE _ _ _ guardIH yesIH noIH =>
      simp only [Core.Expr.weakenAt]
      exact .ifE (guardIH cutoff) (yesIH cutoff) (noIH cutoff)

end Solcore.Frontend

/-!
## Consolidated module: `Solcore.Frontend.ComputationReturnTree`
-/

/-! Shared mixed bodies parameterize only their child expression operations.
Checker, typing and exact elaboration remain independent interfaces. -/

set_option autoImplicit false

namespace Solcore.Frontend

def elaborateComputationReturnTree?
    (checkChild : LocalNameTable → Resolved.Context → Syntax.Expr → Option (Core.Expr × Core.Ty))
    (types : TypeNameTable) (owner : Resolved.DeclarationId)
    (inputs : LocalTypeInputs) (body : Syntax.Block) : Option (Core.Expr × Core.Ty) :=
  match body with
  | ⟨_, [⟨_, .returnStmt none⟩]⟩ => some (.unit, .unit)
  | ⟨_, [⟨_, .returnStmt (some expression)⟩]⟩ =>
      checkChild inputs.names inputs.context expression
  | ⟨_, [⟨innerSpan, .block statements⟩]⟩ =>
      elaborateComputationReturnTree? checkChild types owner inputs ⟨innerSpan, statements⟩
  | ⟨blockSpan, ⟨_, .letDecl name (some annotation) (some initializer)⟩ :: rest⟩ => do
      let declaredType ← interpretStructuralType? types annotation
      let (initializerCore, initializerType) ← checkChild inputs.names inputs.context initializer
      if initializerType = declaredType then do
        let (tailCore, returnType) ← elaborateComputationReturnTree? checkChild types owner
          (inputs.bindFresh owner name.value declaredType) ⟨blockSpan, rest⟩
        return (.letE initializerCore tailCore, returnType)
      else none
  | ⟨blockSpan, ⟨_, .letDecl name none (some initializer)⟩ :: rest⟩ => do
      let (initializerCore, initializerType) ← checkChild inputs.names inputs.context initializer
      let (tailCore, returnType) ← elaborateComputationReturnTree? checkChild types owner
        (inputs.bindFresh owner name.value initializerType) ⟨blockSpan, rest⟩
      return (.letE initializerCore tailCore, returnType)
  | ⟨blockSpan, ⟨_, .expression expression true⟩ :: rest⟩ => do
      let (expressionCore, _) ← checkChild inputs.names inputs.context expression
      let (tailCore, returnType) ← elaborateComputationReturnTree? checkChild types owner inputs ⟨blockSpan, rest⟩
      return (.letE expressionCore (tailCore.weakenAt 0), returnType)
  | ⟨_, [⟨_, .ifThen condition thenBody (some elseBody)⟩]⟩ => do
      let (conditionCore, conditionType) ← checkChild inputs.names inputs.context condition
      if conditionType = .bool ∧ computationBlockPreservesNames (inputs.names.map Prod.fst) thenBody = true then do
        let (thenCore, thenType) ← elaborateComputationReturnTree? checkChild types owner inputs thenBody
        let (elseCore, elseType) ← elaborateComputationReturnTree? checkChild types owner inputs elseBody
        if thenType = elseType then return (.ifE conditionCore thenCore elseCore, thenType)
        else none
      else none
  | ⟨_, [⟨_, .matchWith ⟨_, ⟨scrutinee, []⟩⟩ ⟨_, ⟨cases, defaultBody⟩⟩⟩]⟩ => do
      let (scrutineeCore, scrutineeType) ← checkChild inputs.names inputs.context scrutinee
      let defaultChecked : Option (Syntax.Block × (Core.Expr × Core.Ty)) ← match defaultBody with
        | none => some none
        | some source => do
            let branch ← elaborateComputationReturnTree? checkChild types owner inputs source
            pure (some (source, branch))
      let checked : List (Syntax.MatchCase × (Option Core.Word × (Core.Expr × Core.Ty))) ← cases.attach.mapM fun arm => do
        let tag ← interpretWordMatchPattern? arm.val.value.pattern
        let branch ← elaborateComputationReturnTree? checkChild types owner inputs arm.val.value.body
        return (arm.val, tag, branch)
      if scrutineeType = .word ∨ checked.all (fun entry => entry.2.1.isNone) = true then do
        let returnType ← match defaultChecked with
          | some entry => some entry.2.2
          | none => checked.head?.map (fun entry => entry.2.2.2)
        if checked.all (fun entry => entry.2.2.2 == returnType) then do
          let entries := checked.map (fun entry => (entry.1, entry.2.1, entry.2.2.1))
          let defaultEntry := defaultChecked.map (fun entry => (entry.1, entry.2.1))
          let bodyCore ← entries.foldr
            (fun entry tail => match entry.2.1 with
              | none => some (entry.2.2.weakenAt 0)
              | some word => tail.map (fun core =>
                  .ifE (.binary .wordEq (.var 0) (.word word)) (entry.2.2.weakenAt 0) core))
            (defaultEntry.map (fun entry => entry.2.weakenAt 0))
          return (.letE scrutineeCore bodyCore, returnType)
        else none
      else none
  | _ => none
termination_by sizeOf body
decreasing_by
  all_goals simp_wf
  all_goals try omega
  have member := List.sizeOf_lt_of_mem arm.property
  have child : sizeOf arm.val.value.body < sizeOf arm.val := by
    rcases arm.val with ⟨span, ⟨pattern, body⟩⟩
    simp
    omega
  omega

inductive ComputationReturnTreeHasType
    (ChildHasType : LocalNameTable → Resolved.Context → Syntax.Expr → Core.Ty → Prop)
    (types : TypeNameTable) (owner : Resolved.DeclarationId) :
    LocalTypeInputs → Syntax.Block → Core.Ty → Prop where
  | bare {inputs : LocalTypeInputs} {blockSpan returnSpan : Syntax.SourceSpan} :
      ComputationReturnTreeHasType ChildHasType types owner inputs
        ⟨blockSpan, [⟨returnSpan, .returnStmt none⟩]⟩ .unit
  | expression {inputs : LocalTypeInputs} {blockSpan returnSpan : Syntax.SourceSpan}
      {source : Syntax.Expr} {type : Core.Ty}
      (child : ChildHasType inputs.names inputs.context source type) :
      ComputationReturnTreeHasType ChildHasType types owner inputs
        ⟨blockSpan, [⟨returnSpan, .returnStmt (some source)⟩]⟩ type
  | block {inputs : LocalTypeInputs} {outerSpan innerSpan : Syntax.SourceSpan}
      {statements : List Syntax.Statement} {type : Core.Ty}
      (child : ComputationReturnTreeHasType ChildHasType types owner inputs ⟨innerSpan, statements⟩ type) :
      ComputationReturnTreeHasType ChildHasType types owner inputs
        ⟨outerSpan, [⟨innerSpan, .block statements⟩]⟩ type
  | binding {inputs : LocalTypeInputs} {blockSpan letSpan : Syntax.SourceSpan}
      {name : Syntax.Identifier} {annotation : Syntax.TypeExpr} {initializer : Syntax.Expr}
      {rest : List Syntax.Statement} {declaredType returnType : Core.Ty}
      (meaning : StructuralTypeDenotes types annotation declaredType)
      (initializerTyping : ChildHasType inputs.names inputs.context initializer declaredType)
      (tailTyping : ComputationReturnTreeHasType ChildHasType types owner
        (inputs.bindFresh owner name.value declaredType) ⟨blockSpan, rest⟩ returnType) :
      ComputationReturnTreeHasType ChildHasType types owner inputs
        ⟨blockSpan, ⟨letSpan, .letDecl name (some annotation) (some initializer)⟩ :: rest⟩ returnType
  | inferred {inputs : LocalTypeInputs} {blockSpan letSpan : Syntax.SourceSpan}
      {name : Syntax.Identifier} {initializer : Syntax.Expr} {rest : List Syntax.Statement}
      {inferredType returnType : Core.Ty}
      (initializerTyping : ChildHasType inputs.names inputs.context initializer inferredType)
      (tailTyping : ComputationReturnTreeHasType ChildHasType types owner
        (inputs.bindFresh owner name.value inferredType) ⟨blockSpan, rest⟩ returnType) :
      ComputationReturnTreeHasType ChildHasType types owner inputs
        ⟨blockSpan, ⟨letSpan, .letDecl name none (some initializer)⟩ :: rest⟩ returnType
  | discard {inputs : LocalTypeInputs} {blockSpan statementSpan : Syntax.SourceSpan}
      {expression : Syntax.Expr} {rest : List Syntax.Statement} {discardedType returnType : Core.Ty}
      (expressionTyping : ChildHasType inputs.names inputs.context expression discardedType)
      (tailTyping : ComputationReturnTreeHasType ChildHasType types owner inputs ⟨blockSpan, rest⟩ returnType) :
      ComputationReturnTreeHasType ChildHasType types owner inputs
        ⟨blockSpan, ⟨statementSpan, .expression expression true⟩ :: rest⟩ returnType
  | conditional {inputs : LocalTypeInputs} {blockSpan ifSpan : Syntax.SourceSpan}
      {condition : Syntax.Expr} {thenBody elseBody : Syntax.Block} {type : Core.Ty}
      (conditionTyping : ChildHasType inputs.names inputs.context condition .bool)
      (nameProtection : ComputationNamesProtected (inputs.names.map Prod.fst) thenBody)
      (thenTyping : ComputationReturnTreeHasType ChildHasType types owner inputs thenBody type)
      (elseTyping : ComputationReturnTreeHasType ChildHasType types owner inputs elseBody type) :
      ComputationReturnTreeHasType ChildHasType types owner inputs
        ⟨blockSpan, [⟨ifSpan, .ifThen condition thenBody (some elseBody)⟩]⟩ type
  | wordMatch {inputs : LocalTypeInputs} {blockSpan matchSpan scrutineeSpan armsSpan : Syntax.SourceSpan}
      {scrutinee : Syntax.Expr} {cases : List Syntax.MatchCase} {defaultBody : Option Syntax.Block}
      {scrutineeType type : Core.Ty}
      (scrutineeTyping : ChildHasType inputs.names inputs.context scrutinee scrutineeType)
      (patterns : ∀ arm ∈ cases, ∃ tag, WordMatchPatternClassifies arm.value.pattern tag)
      (compatible : scrutineeType = .word ∨
        ∀ arm ∈ cases, WordMatchPatternClassifies arm.value.pattern none)
      (covered : defaultBody.isSome = true ∨
        ∃ arm ∈ cases, WordMatchPatternClassifies arm.value.pattern none)
      (branches : ∀ arm ∈ cases, ComputationReturnTreeHasType ChildHasType types owner inputs arm.value.body type)
      (defaultTyping : ∀ source ∈ defaultBody.toList,
        ComputationReturnTreeHasType ChildHasType types owner inputs source type) :
      ComputationReturnTreeHasType ChildHasType types owner inputs
        ⟨blockSpan, [⟨matchSpan, .matchWith ⟨scrutineeSpan, ⟨scrutinee, []⟩⟩ ⟨armsSpan, ⟨cases, defaultBody⟩⟩⟩]⟩ type

inductive ComputationReturnTreeElaborates
    (ChildElab : LocalNameTable → Resolved.Context → Syntax.Expr → Core.Expr → Core.Ty → Prop)
    (types : TypeNameTable) (owner : Resolved.DeclarationId) :
    LocalTypeInputs → Syntax.Block → Core.Expr → Core.Ty → Prop where
  | bare {inputs : LocalTypeInputs} {blockSpan returnSpan : Syntax.SourceSpan} :
      ComputationReturnTreeElaborates ChildElab types owner inputs
        ⟨blockSpan, [⟨returnSpan, .returnStmt none⟩]⟩ .unit .unit
  | expression {inputs : LocalTypeInputs} {blockSpan returnSpan : Syntax.SourceSpan}
      {source : Syntax.Expr} {core : Core.Expr} {type : Core.Ty}
      (child : ChildElab inputs.names inputs.context source core type) :
      ComputationReturnTreeElaborates ChildElab types owner inputs
        ⟨blockSpan, [⟨returnSpan, .returnStmt (some source)⟩]⟩ core type
  | block {inputs : LocalTypeInputs} {outerSpan innerSpan : Syntax.SourceSpan}
      {statements : List Syntax.Statement} {core : Core.Expr} {type : Core.Ty}
      (child : ComputationReturnTreeElaborates ChildElab types owner inputs ⟨innerSpan, statements⟩ core type) :
      ComputationReturnTreeElaborates ChildElab types owner inputs
        ⟨outerSpan, [⟨innerSpan, .block statements⟩]⟩ core type
  | binding {inputs : LocalTypeInputs} {blockSpan letSpan : Syntax.SourceSpan}
      {name : Syntax.Identifier} {annotation : Syntax.TypeExpr} {initializer : Syntax.Expr}
      {rest : List Syntax.Statement} {declaredType returnType : Core.Ty} {initializerCore tailCore : Core.Expr}
      (meaning : StructuralTypeDenotes types annotation declaredType)
      (initializerElaboration : ChildElab inputs.names inputs.context initializer initializerCore declaredType)
      (tailElaboration : ComputationReturnTreeElaborates ChildElab types owner
        (inputs.bindFresh owner name.value declaredType) ⟨blockSpan, rest⟩ tailCore returnType) :
      ComputationReturnTreeElaborates ChildElab types owner inputs
        ⟨blockSpan, ⟨letSpan, .letDecl name (some annotation) (some initializer)⟩ :: rest⟩
        (.letE initializerCore tailCore) returnType
  | inferred {inputs : LocalTypeInputs} {blockSpan letSpan : Syntax.SourceSpan}
      {name : Syntax.Identifier} {initializer : Syntax.Expr} {rest : List Syntax.Statement}
      {inferredType returnType : Core.Ty} {initializerCore tailCore : Core.Expr}
      (initializerElaboration : ChildElab inputs.names inputs.context initializer initializerCore inferredType)
      (tailElaboration : ComputationReturnTreeElaborates ChildElab types owner
        (inputs.bindFresh owner name.value inferredType) ⟨blockSpan, rest⟩ tailCore returnType) :
      ComputationReturnTreeElaborates ChildElab types owner inputs
        ⟨blockSpan, ⟨letSpan, .letDecl name none (some initializer)⟩ :: rest⟩
        (.letE initializerCore tailCore) returnType
  | discard {inputs : LocalTypeInputs} {blockSpan statementSpan : Syntax.SourceSpan}
      {expression : Syntax.Expr} {rest : List Syntax.Statement} {discardedType returnType : Core.Ty}
      {expressionCore tailCore : Core.Expr}
      (expressionElaboration : ChildElab inputs.names inputs.context expression expressionCore discardedType)
      (tailElaboration : ComputationReturnTreeElaborates ChildElab types owner inputs ⟨blockSpan, rest⟩ tailCore returnType) :
      ComputationReturnTreeElaborates ChildElab types owner inputs
        ⟨blockSpan, ⟨statementSpan, .expression expression true⟩ :: rest⟩
        (.letE expressionCore (tailCore.weakenAt 0)) returnType
  | conditional {inputs : LocalTypeInputs} {blockSpan ifSpan : Syntax.SourceSpan}
      {condition : Syntax.Expr} {thenBody elseBody : Syntax.Block}
      {conditionCore thenCore elseCore : Core.Expr} {type : Core.Ty}
      (conditionElaboration : ChildElab inputs.names inputs.context condition conditionCore .bool)
      (nameProtection : ComputationNamesProtected (inputs.names.map Prod.fst) thenBody)
      (thenElaboration : ComputationReturnTreeElaborates ChildElab types owner inputs thenBody thenCore type)
      (elseElaboration : ComputationReturnTreeElaborates ChildElab types owner inputs elseBody elseCore type) :
      ComputationReturnTreeElaborates ChildElab types owner inputs
        ⟨blockSpan, [⟨ifSpan, .ifThen condition thenBody (some elseBody)⟩]⟩
        (.ifE conditionCore thenCore elseCore) type
  | wordMatch {inputs : LocalTypeInputs} {blockSpan matchSpan scrutineeSpan armsSpan : Syntax.SourceSpan}
      {scrutinee : Syntax.Expr} {cases : List Syntax.MatchCase} {defaultBody : Option Syntax.Block}
      {scrutineeCore bodyCore : Core.Expr} {scrutineeType type : Core.Ty}
      {entries : List (Syntax.MatchCase × (Option Core.Word × Core.Expr))}
      {defaultEntry : Option (Syntax.Block × Core.Expr)}
      (scrutineeElaboration : ChildElab inputs.names inputs.context scrutinee scrutineeCore scrutineeType)
      (ordered : entries.map Prod.fst = cases)
      (patterns : ∀ entry ∈ entries, WordMatchPatternClassifies entry.1.value.pattern entry.2.1)
      (compatible : scrutineeType = .word ∨ ∀ entry ∈ entries, entry.2.1 = none)
      (branches : ∀ entry ∈ entries,
        ComputationReturnTreeElaborates ChildElab types owner inputs entry.1.value.body entry.2.2 type)
      (defaultOrdered : defaultEntry.map Prod.fst = defaultBody)
      (defaultElaboration : ∀ entry ∈ defaultEntry.toList,
        ComputationReturnTreeElaborates ChildElab types owner inputs entry.1 entry.2 type)
      (lowered : entries.foldr
          (fun entry tail => match entry.2.1 with
            | none => some (entry.2.2.weakenAt 0)
            | some word => tail.map (fun core =>
                .ifE (.binary .wordEq (.var 0) (.word word)) (entry.2.2.weakenAt 0) core))
          (defaultEntry.map (fun entry => entry.2.weakenAt 0)) = some bodyCore) :
      ComputationReturnTreeElaborates ChildElab types owner inputs
        ⟨blockSpan, [⟨matchSpan, .matchWith ⟨scrutineeSpan, ⟨scrutinee, []⟩⟩ ⟨armsSpan, ⟨cases, defaultBody⟩⟩⟩]⟩
        (.letE scrutineeCore bodyCore) type

end Solcore.Frontend

/-!
## Consolidated module: `Solcore.Frontend.ComputationFunctionCompilation`
-/

set_option autoImplicit false

namespace Solcore.Frontend

/-! Value-free compilation of original mixed bodies under the unchanged header
and parameter policy. Reusing an output record does not grant old provenance. -/

structure ComputationFunctionCompiles (ChildElab : LocalNameTable → Resolved.Context → Syntax.Expr → Core.Expr → Core.Ty → Prop)
    (types : TypeNameTable) (owner : Resolved.DeclarationId)
    (declaration : Syntax.FunctionDecl) (compiled : CompiledRuntimeFunction) : Prop where
  header : RuntimeFunctionHeader types declaration.value.signature compiled.returnType
  parameters : RuntimeParametersDeclare types owner declaration.value.signature.parameters.elements
    compiled.inputs
  body : ComputationReturnTreeElaborates ChildElab types owner compiled.inputs
    declaration.value.body compiled.core compiled.returnType

def compileComputationFunction? (checkChild : LocalNameTable → Resolved.Context → Syntax.Expr → Option (Core.Expr × Core.Ty))
    (types : TypeNameTable) (owner : Resolved.DeclarationId)
    (declaration : Syntax.FunctionDecl) : Option CompiledRuntimeFunction := do
  let returnType ← interpretRuntimeFunctionHeader? types declaration.value.signature
  let inputs ← declareRuntimeParameters? types owner declaration.value.signature.parameters.elements
  let (core, inferredType) ← elaborateComputationReturnTree? checkChild types owner inputs declaration.value.body
  if inferredType = returnType then return { inputs, core, returnType }
  else none

end Solcore.Frontend

/-!
## Consolidated module: `Solcore.Frontend.ComputationFunctionEntry`
-/

set_option autoImplicit false

namespace Solcore.Frontend

/-! Original actual arguments prepare a separate mixed-body entry. The same
input record supplies the type-only view and the actual runtime environment. -/

structure ComputationFunctionPrepares (ChildElab : LocalNameTable → Resolved.Context → Syntax.Expr → Core.Expr → Core.Ty → Prop)
    (types : TypeNameTable) (owner : Resolved.DeclarationId)
    (declaration : Syntax.FunctionDecl) (arguments : List TypedRuntimeArgument)
    (prepared : PreparedRuntimeFunction) : Prop where
  header : RuntimeFunctionHeader types declaration.value.signature prepared.returnType
  parameters : RuntimeParametersBind types owner declaration.value.signature.parameters.elements
    arguments prepared.inputs
  body : ComputationReturnTreeElaborates ChildElab types owner prepared.inputs.toTypeInputs
    declaration.value.body prepared.core prepared.returnType

def prepareComputationFunction? (checkChild : LocalNameTable → Resolved.Context → Syntax.Expr → Option (Core.Expr × Core.Ty))
    (types : TypeNameTable) (owner : Resolved.DeclarationId)
    (declaration : Syntax.FunctionDecl) (arguments : List TypedRuntimeArgument) :
    Option PreparedRuntimeFunction := do
  let returnType ← interpretRuntimeFunctionHeader? types declaration.value.signature
  let inputs ← bindRuntimeParameters? types owner declaration.value.signature.parameters.elements arguments
  let (core, inferredType) ← elaborateComputationReturnTree? checkChild types owner inputs.toTypeInputs declaration.value.body
  if inferredType = returnType then return { inputs, core, returnType }
  else none

/-- The separately supplied store is not checked by structural preparation.
Keep every present Core result, including faults and actual suspended states. -/
def runComputationFunction? (checkChild : LocalNameTable → Resolved.Context → Syntax.Expr → Option (Core.Expr × Core.Ty))
    (types : TypeNameTable) (owner : Resolved.DeclarationId)
    (declaration : Syntax.FunctionDecl) (arguments : List TypedRuntimeArgument)
    (fuel : Nat) (store : Core.Store) : Option (Core.Ty × Core.StatefulRunResult) := do
  let prepared ← prepareComputationFunction? checkChild types owner declaration arguments
  return (prepared.returnType, Core.runStateful fuel
    (Core.State.initial prepared.core prepared.inputs.environment.values store))

end Solcore.Frontend

/-!
## Consolidated module: `Solcore.Frontend.ComputationFunctionArgumentProperties`
-/

/-! Independent preparation and compilation factor through the supplied actual
arguments for the same arbitrary child elaboration. Preserve original values,
captures and argument order without a checker, invented inhabitants or runtime world. -/

set_option autoImplicit false
namespace Solcore.Frontend
variable {ChildElab : LocalNameTable → Resolved.Context → Syntax.Expr → Core.Expr → Core.Ty → Prop}
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {declaration : Syntax.FunctionDecl}

/-- Erasing actual values preserves independent compilation of the exact record. -/
theorem ComputationFunctionPrepares.compiles {arguments : List TypedRuntimeArgument}
    {prepared : PreparedRuntimeFunction}
    (preparation : ComputationFunctionPrepares ChildElab types owner declaration arguments prepared) :
    ComputationFunctionCompiles ChildElab types owner declaration prepared.toCompiled :=
  ⟨preparation.header, preparation.parameters.erase_values, preparation.body⟩

/-- Reconstruct preparation from the supplied typed arguments, preserving the
compiled projection. The type equation fixes arity and original argument order. -/
theorem ComputationFunctionCompiles.prepare_arguments {compiled : CompiledRuntimeFunction}
    (compilation : ComputationFunctionCompiles ChildElab types owner declaration compiled)
    (arguments : List TypedRuntimeArgument)
    (matching : arguments.map (·.type) = compiled.inputs.context.values.reverse) :
    ∃ prepared, ComputationFunctionPrepares ChildElab types owner declaration arguments prepared ∧
      prepared.toCompiled = compiled := by
  obtain ⟨inputs, bound, erased⟩ := compilation.parameters.bind_typed_arguments arguments matching
  refine ⟨⟨inputs, compiled.core, compiled.returnType⟩, ⟨compilation.header, bound, ?_⟩, ?_⟩
  · simpa only [erased] using compilation.body
  · simp only [PreparedRuntimeFunction.toCompiled, erased]

/-- A fixed compiled projection is preparable exactly when independent compilation
holds and the supplied argument types match; the record alone is insufficient. -/
theorem computationFunctionPrepares_toCompiled_iff {arguments : List TypedRuntimeArgument}
    {compiled : CompiledRuntimeFunction} :
    (∃ prepared, ComputationFunctionPrepares ChildElab types owner declaration arguments prepared ∧
      prepared.toCompiled = compiled) ↔
    ComputationFunctionCompiles ChildElab types owner declaration compiled ∧
      arguments.map (·.type) = compiled.inputs.context.values.reverse := by
  constructor
  · rintro ⟨prepared, preparation, rfl⟩
    refine ⟨preparation.compiles, ?_⟩
    have layout := congrArg List.reverse preparation.parameters.argument_types.symm
    simpa only [PreparedRuntimeFunction.toCompiled, LocalInputs.toTypeInputs_context,
      Resolved.LocalScope.values, LocalInputs.context, List.map_map, Function.comp_def,
      List.map_reverse, List.reverse_reverse] using layout
  · rintro ⟨compilation, matching⟩
    exact compilation.prepare_arguments arguments matching

/-- Preparation retains the supplied actual values and captures, reversed once
into the input environment. -/
theorem ComputationFunctionPrepares.argument_values {arguments : List TypedRuntimeArgument}
    {prepared : PreparedRuntimeFunction}
    (preparation : ComputationFunctionPrepares ChildElab types owner declaration arguments prepared) :
    prepared.inputs.environment.values = arguments.reverse.map (·.value) := by
  simpa only [LocalInputs.environment, Resolved.LocalScope.values, List.map_map, Function.comp_def]
    using preparation.parameters.argument_values

/-- For the same actual arguments, equal compiled projections give equal prepared
records. No uniqueness of the arbitrary child elaboration is assumed. -/
theorem ComputationFunctionPrepares.unique_of_toCompiled_eq {arguments : List TypedRuntimeArgument}
    {left right : PreparedRuntimeFunction}
    (first : ComputationFunctionPrepares ChildElab types owner declaration arguments left)
    (second : ComputationFunctionPrepares ChildElab types owner declaration arguments right)
    (erased : left.toCompiled = right.toCompiled) : left = right := by
  have sameInputs := RuntimeParametersBindFrom.result_unique first.parameters second.parameters
  have sameCore : left.core = right.core := congrArg CompiledRuntimeFunction.core erased
  have sameType : left.returnType = right.returnType := congrArg CompiledRuntimeFunction.returnType erased
  cases left; cases right; cases sameInputs; cases sameCore; cases sameType; rfl

end Solcore.Frontend

/-!
## Consolidated module: `Solcore.Frontend.ComputationReturnTreeCheckingProperties`
-/

/-! Exact optional-match checking preserves original case/default provenance.
No elaboration, typing or runtime law is assumed. -/

set_option autoImplicit false

namespace Solcore.Frontend

variable {checkChild : LocalNameTable → Resolved.Context → Syntax.Expr → Option (Core.Expr × Core.Ty)}
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {inputs : LocalTypeInputs}

private def check_arm (check : Syntax.Block → Option (Core.Expr × Core.Ty))
    (arm : Syntax.MatchCase) : Option (Option Core.Word × (Core.Expr × Core.Ty)) := do
  let tag ← interpretWordMatchPattern? arm.value.pattern
  let branch ← check arm.value.body
  return (tag, branch)

private theorem check_arm_map {check : Syntax.Block → Option (Core.Expr × Core.Ty)}
    {arm : Syntax.MatchCase} :
    (check_arm check arm).map (arm, ·) = (do
      let tag ← interpretWordMatchPattern? arm.value.pattern
      let branch ← check arm.value.body
      return (arm, tag, branch)) := by
  simp [check_arm, bind, Option.map_bind, Function.comp_def]

private theorem check_arm_iff {check : Syntax.Block → Option (Core.Expr × Core.Ty)}
    {type : Core.Ty} {arm : Syntax.MatchCase} {tag : Option Core.Word} {core : Core.Expr} :
    check_arm check arm = some (tag, core, type) ↔
      WordMatchPatternClassifies arm.value.pattern tag ∧ check arm.value.body = some (core, type) := by
  simp [check_arm, bind, Option.bind_eq_some_iff, Prod.mk.injEq, interpretWordMatchPattern?_iff]

private theorem entries_check_iff {α β : Type} {check : α → Option β}
    {cases : List α} {entries : List (α × β)} :
    cases.attach.mapM (fun arm => (check arm.val).map (arm.val, ·)) = some entries ↔
      entries.map Prod.fst = cases ∧ ∀ entry ∈ entries, check entry.1 = some entry.2 := by
  change cases.attach.mapM ((fun arm => (check arm).map (arm, ·)) ∘ Subtype.val) = some entries ↔ _
  rw [← List.mapM_map, List.attach_map_subtype_val]
  induction cases generalizing entries with
  | nil => cases entries <;> simp
  | cons arm rest ih =>
      cases entries with
      | nil => simp [List.mapM_cons, bind, Option.bind_eq_some_iff]
      | cons entry entries =>
          simp only [List.mapM_cons, bind, Option.bind_eq_some_iff, Option.map_eq_some_iff,
            pure, Option.some.injEq, List.cons.injEq, List.map_cons,
            List.mem_cons, forall_eq_or_imp, ih]
          constructor
          · rintro ⟨_, ⟨value, accepted, rfl⟩, _, ⟨ordered, checked⟩, rfl, rfl⟩
            exact ⟨⟨rfl, ordered⟩, accepted, checked⟩
          · rintro ⟨⟨rfl, ordered⟩, accepted, checked⟩
            exact ⟨entry, ⟨entry.2, accepted, by cases entry; rfl⟩, entries,
              ⟨ordered, checked⟩, rfl, rfl⟩

private def check_default (check : Syntax.Block → Option (Core.Expr × Core.Ty)) (source : Option Syntax.Block) :=
  source.mapM (fun body => (check body).map (body, ·))

private theorem check_default_iff {check : Syntax.Block → Option (Core.Expr × Core.Ty)}
    {source : Option Syntax.Block} {checked : Option (Syntax.Block × (Core.Expr × Core.Ty))} :
    check_default check source = some checked ↔ checked.map Prod.fst = source ∧
      ∀ entry ∈ checked.toList, check entry.1 = some entry.2 := by
  cases source <;> cases checked <;> simp [check_default, Option.map_eq_some_iff]
  constructor
  · rintro ⟨_, _, found, rfl⟩; exact ⟨rfl, found⟩
  · rintro ⟨rfl, found⟩; exact ⟨_, _, found, by rfl⟩

private def anchor (defaultChecked : Option (Syntax.Block × (Core.Expr × Core.Ty)))
    (checked : List (Syntax.MatchCase × (Option Core.Word × (Core.Expr × Core.Ty)))) : Option Core.Ty :=
  match defaultChecked with | some entry => some entry.2.2 | none => checked.head?.map (fun entry => entry.2.2.2)

private def check_match (check : Syntax.Block → Option (Core.Expr × Core.Ty)) (scrutineeCore : Core.Expr)
    (scrutineeType : Core.Ty) (cases : List Syntax.MatchCase) (defaultBody : Option Syntax.Block) : Option (Core.Expr × Core.Ty) := do
  let defaultChecked ← check_default check defaultBody
  let checked ← cases.attach.mapM (fun arm => (check_arm check arm.val).map (arm.val, ·))
  if scrutineeType = .word ∨ checked.all (fun entry => entry.2.1.isNone) = true then do
    let type ← anchor defaultChecked checked
    if checked.all (fun entry => entry.2.2.2 == type) then do
      let core ← (checked.map (fun entry => (entry.1, entry.2.1, entry.2.2.1))).foldr
        (fun entry tail => match entry.2.1 with
          | none => some (entry.2.2.weakenAt 0)
          | some word => tail.map (fun core => .ifE (.binary .wordEq (.var 0) (.word word)) (entry.2.2.weakenAt 0) core))
        ((defaultChecked.map (fun entry => (entry.1, entry.2.1))).map (fun entry => entry.2.weakenAt 0))
      return (.letE scrutineeCore core, type)
    else none
  else none

private theorem type_beq (left right : Core.Ty) : (left == right) = true ↔ left = right := by
  induction left generalizing right <;> cases right <;>
    simp_all [BEq.beq, Core.instBEqTy.beq, Core.instBEqDataTypeId.beq]
  rename_i left right
  cases left; cases right; simp_all

private theorem check_match_iff {check : Syntax.Block → Option (Core.Expr × Core.Ty)}
    {scrutineeCore core : Core.Expr} {scrutineeType type : Core.Ty} {cases : List Syntax.MatchCase} {defaultBody : Option Syntax.Block} :
    check_match check scrutineeCore scrutineeType cases defaultBody = some (core, type) ↔
    ∃ (bodyCore : Core.Expr) (entries : List (Syntax.MatchCase × (Option Core.Word × Core.Expr)))
      (defaultEntry : Option (Syntax.Block × Core.Expr)), entries.map Prod.fst = cases ∧
      (∀ entry ∈ entries, WordMatchPatternClassifies entry.1.value.pattern entry.2.1) ∧
      (scrutineeType = .word ∨ ∀ entry ∈ entries, entry.2.1 = none) ∧
      (∀ entry ∈ entries, check entry.1.value.body = some (entry.2.2, type)) ∧
      defaultEntry.map Prod.fst = defaultBody ∧ (∀ entry ∈ defaultEntry.toList, check entry.1 = some (entry.2, type)) ∧
      entries.foldr (fun entry tail => match entry.2.1 with
        | none => some (entry.2.2.weakenAt 0)
        | some word => tail.map (fun core => .ifE (.binary .wordEq (.var 0) (.word word)) (entry.2.2.weakenAt 0) core))
        (defaultEntry.map (fun entry => entry.2.weakenAt 0)) = some bodyCore ∧ core = .letE scrutineeCore bodyCore := by
  simp only [check_match, bind, Option.bind_eq_some_iff]
  constructor
  · rintro ⟨defaults, defaultChecked, checked, entriesChecked, accepted⟩
    split at accepted
    next compatible =>
      simp only [Option.bind_eq_some_iff] at accepted
      obtain ⟨actualType, anchored, accepted⟩ := accepted
      split at accepted
      next sameTypes =>
        simp only [Option.bind_eq_some_iff, pure, Option.some.injEq, Prod.mk.injEq] at accepted
        obtain ⟨bodyCore, lowered, rfl, rfl⟩ := accepted
        have ds := check_default_iff.mp defaultChecked
        have cs := entries_check_iff.mp entriesChecked
        refine ⟨bodyCore, checked.map (fun e => (e.1, e.2.1, e.2.2.1)),
          defaults.map (fun e => (e.1, e.2.1)), ?_, ?_, ?_, ?_, ?_, ?_, lowered, rfl⟩
        · simpa only [List.map_map, Function.comp_def] using cs.1
        · intro entry member; obtain ⟨row, rowMember, rfl⟩ := List.mem_map.mp member
          exact (check_arm_iff.mp (cs.2 row rowMember)).1
        · rcases compatible with word | allNone
          · exact .inl word
          · right; intro entry member
            obtain ⟨row, rowMember, rfl⟩ := List.mem_map.mp member
            exact Option.isNone_iff_eq_none.mp (List.all_eq_true.mp allNone row rowMember)
        · intro entry member; obtain ⟨row, rowMember, rfl⟩ := List.mem_map.mp member
          have same : row.2.2.2 = actualType := type_beq _ _ |>.mp (List.all_eq_true.mp sameTypes row rowMember)
          simpa only [same] using (check_arm_iff.mp (cs.2 row rowMember)).2
        · simpa only [Option.map_map, Function.comp_def] using ds.1
        · intro entry member
          rw [Option.toList_map] at member
          obtain ⟨row, rowMember, rfl⟩ := List.mem_map.mp member
          have source := Option.mem_toList.mp rowMember
          have same : row.2.2 = actualType := by simpa only [anchor, source, Option.some.injEq] using anchored
          have found := ds.2 row rowMember
          change check row.1 = some (row.2.1, row.2.2) at found
          simpa only [same] using found
      next different => cases accepted
    next incompatible => cases accepted
  · rintro ⟨bodyCore, entries, defaults, ordered, patterns, compatible, branches, defaultOrdered, defaultBranches, lowered, rfl⟩
    let ds := defaults.map (fun e => (e.1, e.2, type))
    let cs := entries.map (fun e => (e.1, e.2.1, e.2.2, type))
    refine ⟨ds, check_default_iff.mpr ⟨?_, ?_⟩, cs, entries_check_iff.mpr ⟨?_, ?_⟩, ?_⟩
    · simpa only [ds, Option.map_map, Function.comp_def] using defaultOrdered
    · intro entry member
      rw [Option.toList_map] at member
      obtain ⟨row, rowMember, rfl⟩ := List.mem_map.mp member
      exact defaultBranches row rowMember
    · simpa only [cs, List.map_map, Function.comp_def] using ordered
    · intro entry member; obtain ⟨row, rowMember, rfl⟩ := List.mem_map.mp member
      exact check_arm_iff.mpr ⟨patterns row rowMember, branches row rowMember⟩
    · have compatibleChecked : scrutineeType = .word ∨ cs.all (fun entry => entry.2.1.isNone) = true := by
        rcases compatible with word | allNone
        · exact .inl word
        · right; simpa only [cs, List.all_map, Function.comp_def, List.all_eq_true, Option.isNone_iff_eq_none] using allNone
      rw [if_pos compatibleChecked]
      simp only [Option.bind_eq_some_iff]
      refine ⟨type, ?_, ?_⟩
      · cases defaults with
        | some entry => rfl
        | none => cases entries with
          | nil => simp at lowered
          | cons entry rest => rfl
      · have same : cs.all (fun e => e.2.2.2 == type) = true := by simp [cs, type_beq]
        simp only [same, ite_true, Option.bind_eq_some_iff, pure, Option.some.injEq, Prod.mk.injEq]
        refine ⟨bodyCore, ?_, rfl, True.intro⟩
        simp only [cs, ds, List.map_map, Option.map_map, Function.comp_def]
        change (entries.map id).foldr _ _ = some bodyCore
        simpa only [List.map_id] using lowered

/-- Exact checker decomposition of one original optional-default terminal match. -/
theorem ComputationReturnTreeChecking.match_iff
    {blockSpan matchSpan scrutineeSpan armsSpan : Syntax.SourceSpan}
    {scrutinee : Syntax.Expr} {cases : List Syntax.MatchCase} {defaultBody : Option Syntax.Block}
    {core : Core.Expr} {type : Core.Ty} :
    elaborateComputationReturnTree? checkChild types owner inputs
      ⟨blockSpan, [⟨matchSpan, .matchWith ⟨scrutineeSpan, ⟨scrutinee, []⟩⟩ ⟨armsSpan, ⟨cases, defaultBody⟩⟩⟩]⟩ =
        some (core, type) ↔
    ∃ scrutineeCore scrutineeType, checkChild inputs.names inputs.context scrutinee = some (scrutineeCore, scrutineeType) ∧
    ∃ (bodyCore : Core.Expr) (entries : List (Syntax.MatchCase × (Option Core.Word × Core.Expr)))
      (defaultEntry : Option (Syntax.Block × Core.Expr)), entries.map Prod.fst = cases ∧
      (∀ entry ∈ entries, WordMatchPatternClassifies entry.1.value.pattern entry.2.1) ∧
      (scrutineeType = .word ∨ ∀ entry ∈ entries, entry.2.1 = none) ∧
      (∀ entry ∈ entries, elaborateComputationReturnTree? checkChild types owner inputs entry.1.value.body =
        some (entry.2.2, type)) ∧ defaultEntry.map Prod.fst = defaultBody ∧
      (∀ entry ∈ defaultEntry.toList, elaborateComputationReturnTree? checkChild types owner inputs entry.1 =
        some (entry.2, type)) ∧
      entries.foldr (fun entry tail => match entry.2.1 with
        | none => some (entry.2.2.weakenAt 0)
        | some word => tail.map (fun core => .ifE (.binary .wordEq (.var 0) (.word word))
          (entry.2.2.weakenAt 0) core))
        (defaultEntry.map (fun entry => entry.2.weakenAt 0)) = some bodyCore ∧ core = .letE scrutineeCore bodyCore := by
  rw [elaborateComputationReturnTree?]
  constructor
  · intro accepted
    simp only [bind, Option.bind_eq_some_iff] at accepted
    obtain ⟨⟨scrutineeCore, scrutineeType⟩, scrutineeAccepted, remaining⟩ := accepted
    refine ⟨scrutineeCore, scrutineeType, scrutineeAccepted, check_match_iff.mp ?_⟩
    simp only [check_match, check_arm_map]
    cases defaultBody <;>
      simp [check_default, anchor, bind, Option.mapM, Option.map_eq_bind, Option.bind_assoc] at remaining ⊢
    all_goals refine Eq.trans ?_ remaining
    all_goals congr 3
  · rintro ⟨scrutineeCore, scrutineeType, scrutineeAccepted, rest⟩
    simp only [scrutineeAccepted, bind, Option.bind_some]
    have checked := (check_match_iff (scrutineeCore := scrutineeCore) (scrutineeType := scrutineeType)).mpr rest
    simp only [check_match, check_arm_map] at checked
    cases defaultBody <;>
      simp [check_default, anchor, bind, Option.mapM, Option.map_eq_bind, Option.bind_assoc] at checked ⊢
    all_goals refine Eq.trans ?_ checked
    all_goals congr 3

end Solcore.Frontend

/-!
## Consolidated module: `Solcore.Frontend.ComputationReturnTreeEvaluation`
-/

/-! Shared raw body rules depend only on the supplied raw child relation;
cost rules depend only on the supplied cost relation. Neither invokes a checker. -/

set_option autoImplicit false

namespace Solcore.Frontend

inductive ComputationReturnTreeEvaluates
    (ChildEval : LocalNameTable → Resolved.Environment → Core.Store → Syntax.Expr → Core.Value → Core.Store → Prop)
    (owner : Resolved.DeclarationId) :
    LocalNameTable → Resolved.Environment → Core.Store → Syntax.Block → Core.Value → Core.Store → Prop where
  | bare {table : LocalNameTable} {environment : Resolved.Environment}
      {blockSpan returnSpan : Syntax.SourceSpan} {store : Core.Store} :
      ComputationReturnTreeEvaluates ChildEval owner table environment store
        ⟨blockSpan, [⟨returnSpan, .returnStmt none⟩]⟩ .unit store
  | expression {table : LocalNameTable} {environment : Resolved.Environment}
      {blockSpan returnSpan : Syntax.SourceSpan} {source : Syntax.Expr}
      {initialStore finalStore : Core.Store} {value : Core.Value}
      (child : ChildEval table environment initialStore source value finalStore) :
      ComputationReturnTreeEvaluates ChildEval owner table environment initialStore
        ⟨blockSpan, [⟨returnSpan, .returnStmt (some source)⟩]⟩ value finalStore
  | block {table : LocalNameTable} {environment : Resolved.Environment}
      {outerSpan innerSpan : Syntax.SourceSpan} {statements : List Syntax.Statement}
      {initialStore finalStore : Core.Store} {value : Core.Value}
      (child : ComputationReturnTreeEvaluates ChildEval owner table environment initialStore
        ⟨innerSpan, statements⟩ value finalStore) :
      ComputationReturnTreeEvaluates ChildEval owner table environment initialStore
        ⟨outerSpan, [⟨innerSpan, .block statements⟩]⟩ value finalStore
  | binding {table : LocalNameTable} {environment : Resolved.Environment}
      {blockSpan letSpan : Syntax.SourceSpan} {name : Syntax.Identifier}
      {annotation : Syntax.TypeExpr} {initializer : Syntax.Expr} {rest : List Syntax.Statement}
      {initialStore middleStore finalStore : Core.Store} {boundValue value : Core.Value}
      (initializerEvaluation : ChildEval table environment initialStore initializer boundValue middleStore)
      (tailEvaluation : ComputationReturnTreeEvaluates ChildEval owner
        ((name.value, Resolved.freshLocalId owner (table.map Prod.snd)) :: table)
        ((Resolved.freshLocalId owner (table.map Prod.snd), boundValue) :: environment)
        middleStore ⟨blockSpan, rest⟩ value finalStore) :
      ComputationReturnTreeEvaluates ChildEval owner table environment initialStore
        ⟨blockSpan, ⟨letSpan, .letDecl name (some annotation) (some initializer)⟩ :: rest⟩ value finalStore
  | inferred {table : LocalNameTable} {environment : Resolved.Environment}
      {blockSpan letSpan : Syntax.SourceSpan} {name : Syntax.Identifier}
      {initializer : Syntax.Expr} {rest : List Syntax.Statement}
      {initialStore middleStore finalStore : Core.Store} {boundValue value : Core.Value}
      (initializerEvaluation : ChildEval table environment initialStore initializer boundValue middleStore)
      (tailEvaluation : ComputationReturnTreeEvaluates ChildEval owner
        ((name.value, Resolved.freshLocalId owner (table.map Prod.snd)) :: table)
        ((Resolved.freshLocalId owner (table.map Prod.snd), boundValue) :: environment)
        middleStore ⟨blockSpan, rest⟩ value finalStore) :
      ComputationReturnTreeEvaluates ChildEval owner table environment initialStore
        ⟨blockSpan, ⟨letSpan, .letDecl name none (some initializer)⟩ :: rest⟩ value finalStore
  | discard {table : LocalNameTable} {environment : Resolved.Environment}
      {blockSpan statementSpan : Syntax.SourceSpan} {expression : Syntax.Expr} {rest : List Syntax.Statement}
      {initialStore middleStore finalStore : Core.Store} {discardedValue value : Core.Value}
      (expressionEvaluation : ChildEval table environment initialStore expression discardedValue middleStore)
      (tailEvaluation : ComputationReturnTreeEvaluates ChildEval owner table environment middleStore
        ⟨blockSpan, rest⟩ value finalStore) :
      ComputationReturnTreeEvaluates ChildEval owner table environment initialStore
        ⟨blockSpan, ⟨statementSpan, .expression expression true⟩ :: rest⟩ value finalStore
  | ifTrue {table : LocalNameTable} {environment : Resolved.Environment}
      {blockSpan ifSpan : Syntax.SourceSpan} {condition : Syntax.Expr}
      {thenBody elseBody : Syntax.Block} {initialStore middleStore finalStore : Core.Store} {value : Core.Value}
      (conditionEvaluation : ChildEval table environment initialStore condition (.bool true) middleStore)
      (branchEvaluation : ComputationReturnTreeEvaluates ChildEval owner table environment middleStore thenBody value finalStore) :
      ComputationReturnTreeEvaluates ChildEval owner table environment initialStore
        ⟨blockSpan, [⟨ifSpan, .ifThen condition thenBody (some elseBody)⟩]⟩ value finalStore
  | ifFalse {table : LocalNameTable} {environment : Resolved.Environment}
      {blockSpan ifSpan : Syntax.SourceSpan} {condition : Syntax.Expr}
      {thenBody elseBody : Syntax.Block} {initialStore middleStore finalStore : Core.Store} {value : Core.Value}
      (conditionEvaluation : ChildEval table environment initialStore condition (.bool false) middleStore)
      (branchEvaluation : ComputationReturnTreeEvaluates ChildEval owner table environment middleStore elseBody value finalStore) :
      ComputationReturnTreeEvaluates ChildEval owner table environment initialStore
        ⟨blockSpan, [⟨ifSpan, .ifThen condition thenBody (some elseBody)⟩]⟩ value finalStore

  | wordMatch {table : LocalNameTable} {environment : Resolved.Environment}
      {blockSpan matchSpan scrutineeSpan armsSpan : Syntax.SourceSpan}
      {scrutinee : Syntax.Expr} {cases : List Syntax.MatchCase}
      {defaultBody : Option Syntax.Block} {selected : Syntax.Block}
      {initialStore middleStore finalStore : Core.Store} {scrutineeValue value : Core.Value} {tests : Nat}
      (scrutineeEvaluation : ChildEval table environment initialStore scrutinee scrutineeValue middleStore)
      (choice : WordMatchChooses scrutineeValue cases defaultBody selected tests)
      (branchEvaluation : ComputationReturnTreeEvaluates ChildEval owner table environment
        middleStore selected value finalStore) :
      ComputationReturnTreeEvaluates ChildEval owner table environment initialStore
        ⟨blockSpan, [⟨matchSpan, .matchWith ⟨scrutineeSpan, ⟨scrutinee, []⟩⟩
          ⟨armsSpan, ⟨cases, defaultBody⟩⟩⟩]⟩ value finalStore

/-- Selected lets, discards and conditionals each add two existing Core transitions.
An unused initializer or discarded expression still contributes its complete cost.
Bare return costs one; expression return and terminal blocks keep child costs.
Word matches add two for the hidden let and seven per visited comparison.
These paths do not impose store independence on an actual called body. -/
inductive ComputationReturnTreeEvaluatesWithCost
    (ChildCost : LocalNameTable → Resolved.Environment → Core.Store → Syntax.Expr → Core.Value → Core.Store → Nat → Prop)
    (owner : Resolved.DeclarationId) :
    LocalNameTable → Resolved.Environment → Core.Store → Syntax.Block → Core.Value → Core.Store → Nat → Prop where
  | bare {table : LocalNameTable} {environment : Resolved.Environment}
      {blockSpan returnSpan : Syntax.SourceSpan} {store : Core.Store} :
      ComputationReturnTreeEvaluatesWithCost ChildCost owner table environment store
        ⟨blockSpan, [⟨returnSpan, .returnStmt none⟩]⟩ .unit store 1
  | expression {table : LocalNameTable} {environment : Resolved.Environment}
      {blockSpan returnSpan : Syntax.SourceSpan} {source : Syntax.Expr}
      {initialStore finalStore : Core.Store} {value : Core.Value} {cost : Nat}
      (child : ChildCost table environment initialStore source value finalStore cost) :
      ComputationReturnTreeEvaluatesWithCost ChildCost owner table environment initialStore
        ⟨blockSpan, [⟨returnSpan, .returnStmt (some source)⟩]⟩ value finalStore cost
  | block {table : LocalNameTable} {environment : Resolved.Environment}
      {outerSpan innerSpan : Syntax.SourceSpan} {statements : List Syntax.Statement}
      {initialStore finalStore : Core.Store} {value : Core.Value} {cost : Nat}
      (child : ComputationReturnTreeEvaluatesWithCost ChildCost owner table environment initialStore
        ⟨innerSpan, statements⟩ value finalStore cost) :
      ComputationReturnTreeEvaluatesWithCost ChildCost owner table environment initialStore
        ⟨outerSpan, [⟨innerSpan, .block statements⟩]⟩ value finalStore cost
  | binding {table : LocalNameTable} {environment : Resolved.Environment}
      {blockSpan letSpan : Syntax.SourceSpan} {name : Syntax.Identifier}
      {annotation : Syntax.TypeExpr} {initializer : Syntax.Expr} {rest : List Syntax.Statement}
      {initialStore middleStore finalStore : Core.Store} {boundValue value : Core.Value}
      {initializerCost tailCost : Nat}
      (initializerEvaluation : ChildCost table environment
        initialStore initializer boundValue middleStore initializerCost)
      (tailEvaluation : ComputationReturnTreeEvaluatesWithCost ChildCost owner
        ((name.value, Resolved.freshLocalId owner (table.map Prod.snd)) :: table)
        ((Resolved.freshLocalId owner (table.map Prod.snd), boundValue) :: environment)
        middleStore ⟨blockSpan, rest⟩ value finalStore tailCost) :
      ComputationReturnTreeEvaluatesWithCost ChildCost owner table environment initialStore
        ⟨blockSpan, ⟨letSpan, .letDecl name (some annotation) (some initializer)⟩ :: rest⟩
        value finalStore (initializerCost + tailCost + 2)
  | inferred {table : LocalNameTable} {environment : Resolved.Environment}
      {blockSpan letSpan : Syntax.SourceSpan} {name : Syntax.Identifier}
      {initializer : Syntax.Expr} {rest : List Syntax.Statement}
      {initialStore middleStore finalStore : Core.Store} {boundValue value : Core.Value}
      {initializerCost tailCost : Nat}
      (initializerEvaluation : ChildCost table environment
        initialStore initializer boundValue middleStore initializerCost)
      (tailEvaluation : ComputationReturnTreeEvaluatesWithCost ChildCost owner
        ((name.value, Resolved.freshLocalId owner (table.map Prod.snd)) :: table)
        ((Resolved.freshLocalId owner (table.map Prod.snd), boundValue) :: environment)
        middleStore ⟨blockSpan, rest⟩ value finalStore tailCost) :
      ComputationReturnTreeEvaluatesWithCost ChildCost owner table environment initialStore
        ⟨blockSpan, ⟨letSpan, .letDecl name none (some initializer)⟩ :: rest⟩
        value finalStore (initializerCost + tailCost + 2)
  | discard {table : LocalNameTable} {environment : Resolved.Environment}
      {blockSpan statementSpan : Syntax.SourceSpan} {expression : Syntax.Expr} {rest : List Syntax.Statement}
      {initialStore middleStore finalStore : Core.Store} {discardedValue value : Core.Value}
      {expressionCost tailCost : Nat}
      (expressionEvaluation : ChildCost table environment
        initialStore expression discardedValue middleStore expressionCost)
      (tailEvaluation : ComputationReturnTreeEvaluatesWithCost ChildCost owner table environment
        middleStore ⟨blockSpan, rest⟩ value finalStore tailCost) :
      ComputationReturnTreeEvaluatesWithCost ChildCost owner table environment initialStore
        ⟨blockSpan, ⟨statementSpan, .expression expression true⟩ :: rest⟩
        value finalStore (expressionCost + tailCost + 2)
  | ifTrue {table : LocalNameTable} {environment : Resolved.Environment}
      {blockSpan ifSpan : Syntax.SourceSpan} {condition : Syntax.Expr}
      {thenBody elseBody : Syntax.Block} {initialStore middleStore finalStore : Core.Store}
      {value : Core.Value} {conditionCost branchCost : Nat}
      (conditionEvaluation : ChildCost table environment
        initialStore condition (.bool true) middleStore conditionCost)
      (branchEvaluation : ComputationReturnTreeEvaluatesWithCost ChildCost owner table environment
        middleStore thenBody value finalStore branchCost) :
      ComputationReturnTreeEvaluatesWithCost ChildCost owner table environment initialStore
        ⟨blockSpan, [⟨ifSpan, .ifThen condition thenBody (some elseBody)⟩]⟩
        value finalStore (conditionCost + branchCost + 2)
  | ifFalse {table : LocalNameTable} {environment : Resolved.Environment}
      {blockSpan ifSpan : Syntax.SourceSpan} {condition : Syntax.Expr}
      {thenBody elseBody : Syntax.Block} {initialStore middleStore finalStore : Core.Store}
      {value : Core.Value} {conditionCost branchCost : Nat}
      (conditionEvaluation : ChildCost table environment
        initialStore condition (.bool false) middleStore conditionCost)
      (branchEvaluation : ComputationReturnTreeEvaluatesWithCost ChildCost owner table environment
        middleStore elseBody value finalStore branchCost) :
      ComputationReturnTreeEvaluatesWithCost ChildCost owner table environment initialStore
        ⟨blockSpan, [⟨ifSpan, .ifThen condition thenBody (some elseBody)⟩]⟩
        value finalStore (conditionCost + branchCost + 2)

  | wordMatch {table : LocalNameTable} {environment : Resolved.Environment}
      {blockSpan matchSpan scrutineeSpan armsSpan : Syntax.SourceSpan}
      {scrutinee : Syntax.Expr} {cases : List Syntax.MatchCase}
      {defaultBody : Option Syntax.Block} {selected : Syntax.Block}
      {initialStore middleStore finalStore : Core.Store} {scrutineeValue value : Core.Value}
      {scrutineeCost branchCost tests : Nat}
      (scrutineeEvaluation : ChildCost table environment
        initialStore scrutinee scrutineeValue middleStore scrutineeCost)
      (choice : WordMatchChooses scrutineeValue cases defaultBody selected tests)
      (branchEvaluation : ComputationReturnTreeEvaluatesWithCost ChildCost owner table environment
        middleStore selected value finalStore branchCost) :
      ComputationReturnTreeEvaluatesWithCost ChildCost owner table environment initialStore
        ⟨blockSpan, [⟨matchSpan, .matchWith ⟨scrutineeSpan, ⟨scrutinee, []⟩⟩
          ⟨armsSpan, ⟨cases, defaultBody⟩⟩⟩]⟩
        value finalStore (scrutineeCost + branchCost + 2 + 7 * tests)

end Solcore.Frontend

/-!
## Consolidated module: `Solcore.Frontend.ComputationReturnTreeEvaluationProperties`
-/

/-! Child laws lift through original mixed-body constructors. Raw cost
existence and joint determinism remain independent of checking and typing. -/

set_option autoImplicit false

namespace Solcore.Frontend

private theorem erase_cost
    {ChildEval : LocalNameTable → Resolved.Environment → Core.Store → Syntax.Expr → Core.Value → Core.Store → Prop}
    {ChildCost : LocalNameTable → Resolved.Environment → Core.Store → Syntax.Expr → Core.Value → Core.Store → Nat → Prop}
    (childCostIff : ∀ {table environment initialStore source value finalStore},
      ChildEval table environment initialStore source value finalStore ↔
        ∃ cost, ChildCost table environment initialStore source value finalStore cost)
    {owner : Resolved.DeclarationId} {table : LocalNameTable} {environment : Resolved.Environment}
    {initialStore finalStore : Core.Store} {body : Syntax.Block} {value : Core.Value} {cost : Nat}
    (evaluation : ComputationReturnTreeEvaluatesWithCost ChildCost owner table environment
      initialStore body value finalStore cost) :
    ComputationReturnTreeEvaluates ChildEval owner table environment initialStore body value finalStore := by
  induction evaluation with
  | bare => exact .bare
  | expression child => exact .expression (childCostIff.mpr ⟨_, child⟩)
  | block _ ih => exact .block ih
  | binding initializer _ ih =>
      exact .binding (childCostIff.mpr ⟨_, initializer⟩) ih
  | inferred initializer _ ih =>
      exact .inferred (childCostIff.mpr ⟨_, initializer⟩) ih
  | discard expression _ ih =>
      exact .discard (childCostIff.mpr ⟨_, expression⟩) ih
  | ifTrue condition _ ih =>
      exact .ifTrue (childCostIff.mpr ⟨_, condition⟩) ih
  | ifFalse condition _ ih =>
      exact .ifFalse (childCostIff.mpr ⟨_, condition⟩) ih

  | wordMatch scrutinee choice _ ih =>
      exact .wordMatch (childCostIff.mpr ⟨_, scrutinee⟩) choice ih

private theorem cost_exists
    {ChildEval : LocalNameTable → Resolved.Environment → Core.Store → Syntax.Expr → Core.Value → Core.Store → Prop}
    {ChildCost : LocalNameTable → Resolved.Environment → Core.Store → Syntax.Expr → Core.Value → Core.Store → Nat → Prop}
    (childCostIff : ∀ {table environment initialStore source value finalStore},
      ChildEval table environment initialStore source value finalStore ↔
        ∃ cost, ChildCost table environment initialStore source value finalStore cost)
    {owner : Resolved.DeclarationId} {table : LocalNameTable} {environment : Resolved.Environment}
    {initialStore finalStore : Core.Store} {body : Syntax.Block} {value : Core.Value}
    (evaluation : ComputationReturnTreeEvaluates ChildEval owner table environment
      initialStore body value finalStore) :
    ∃ cost, ComputationReturnTreeEvaluatesWithCost ChildCost owner table environment
      initialStore body value finalStore cost := by
  induction evaluation with
  | bare => exact ⟨1, .bare⟩
  | expression child =>
      obtain ⟨_, costed⟩ := childCostIff.mp child
      exact ⟨_, .expression costed⟩
  | block _ ih =>
      obtain ⟨_, costed⟩ := ih
      exact ⟨_, .block costed⟩
  | binding initializer _ ih =>
      obtain ⟨_, childCost⟩ := childCostIff.mp initializer
      obtain ⟨_, tailCost⟩ := ih
      exact ⟨_, .binding childCost tailCost⟩
  | inferred initializer _ ih =>
      obtain ⟨_, childCost⟩ := childCostIff.mp initializer
      obtain ⟨_, tailCost⟩ := ih
      exact ⟨_, .inferred childCost tailCost⟩
  | discard expression _ ih =>
      obtain ⟨_, childCost⟩ := childCostIff.mp expression
      obtain ⟨_, tailCost⟩ := ih
      exact ⟨_, .discard childCost tailCost⟩
  | ifTrue condition _ ih =>
      obtain ⟨_, childCost⟩ := childCostIff.mp condition
      obtain ⟨_, branchCost⟩ := ih
      exact ⟨_, .ifTrue childCost branchCost⟩
  | ifFalse condition _ ih =>
      obtain ⟨_, childCost⟩ := childCostIff.mp condition
      obtain ⟨_, branchCost⟩ := ih
      exact ⟨_, .ifFalse childCost branchCost⟩

  | wordMatch scrutinee choice _ ih =>
      obtain ⟨_, childCost⟩ := childCostIff.mp scrutinee
      obtain ⟨_, branchCost⟩ := ih
      exact ⟨_, .wordMatch childCost choice branchCost⟩

theorem computationReturnTreeEvaluates_iff_exists_cost
    {ChildEval : LocalNameTable → Resolved.Environment → Core.Store → Syntax.Expr → Core.Value → Core.Store → Prop}
    {ChildCost : LocalNameTable → Resolved.Environment → Core.Store → Syntax.Expr → Core.Value → Core.Store → Nat → Prop}
    (childCostIff : ∀ {table environment initialStore source value finalStore},
      ChildEval table environment initialStore source value finalStore ↔
        ∃ cost, ChildCost table environment initialStore source value finalStore cost)
    {owner : Resolved.DeclarationId} {table : LocalNameTable} {environment : Resolved.Environment}
    {initialStore finalStore : Core.Store} {body : Syntax.Block} {value : Core.Value} :
    ComputationReturnTreeEvaluates ChildEval owner table environment initialStore body value finalStore ↔
      ∃ cost, ComputationReturnTreeEvaluatesWithCost ChildCost owner table environment
        initialStore body value finalStore cost :=
  ⟨cost_exists childCostIff, fun ⟨_, evaluation⟩ => erase_cost childCostIff evaluation⟩

theorem ComputationReturnTreeEvaluatesWithCost.deterministic
    {ChildCost : LocalNameTable → Resolved.Environment → Core.Store → Syntax.Expr → Core.Value → Core.Store → Nat → Prop}
    (childDeterministic : ∀ {table environment initialStore source left right leftStore rightStore leftCost rightCost},
      ChildCost table environment initialStore source left leftStore leftCost →
      ChildCost table environment initialStore source right rightStore rightCost →
      left = right ∧ leftStore = rightStore ∧ leftCost = rightCost)
    {owner : Resolved.DeclarationId} {table : LocalNameTable} {environment : Resolved.Environment}
    {initialStore : Core.Store} {body : Syntax.Block} {left right : Core.Value}
    {leftStore rightStore : Core.Store} {leftCost rightCost : Nat}
    (first : ComputationReturnTreeEvaluatesWithCost ChildCost owner table environment
      initialStore body left leftStore leftCost)
    (second : ComputationReturnTreeEvaluatesWithCost ChildCost owner table environment
      initialStore body right rightStore rightCost) :
    left = right ∧ leftStore = rightStore ∧ leftCost = rightCost := by
  induction first generalizing right rightStore rightCost with
  | bare => cases second; exact ⟨rfl, rfl, rfl⟩
  | expression child =>
      cases second with
      | expression other => exact childDeterministic child other
  | block _ ih =>
      cases second with
      | block other => exact ih other
  | binding initializer _ ih =>
      cases second with
      | binding otherInitializer otherTail =>
          obtain ⟨rfl, rfl, rfl⟩ := childDeterministic initializer otherInitializer
          obtain ⟨rfl, rfl, rfl⟩ := ih otherTail
          exact ⟨rfl, rfl, rfl⟩
  | inferred initializer _ ih =>
      cases second with
      | inferred otherInitializer otherTail =>
          obtain ⟨rfl, rfl, rfl⟩ := childDeterministic initializer otherInitializer
          obtain ⟨rfl, rfl, rfl⟩ := ih otherTail
          exact ⟨rfl, rfl, rfl⟩
  | discard expression _ ih =>
      cases second with
      | discard otherExpression otherTail =>
          obtain ⟨_, rfl, rfl⟩ := childDeterministic expression otherExpression
          obtain ⟨rfl, rfl, rfl⟩ := ih otherTail
          exact ⟨rfl, rfl, rfl⟩
  | ifTrue condition _ ih =>
      cases second with
      | ifTrue otherCondition otherBranch =>
          obtain ⟨_, rfl, rfl⟩ := childDeterministic condition otherCondition
          obtain ⟨rfl, rfl, rfl⟩ := ih otherBranch
          exact ⟨rfl, rfl, rfl⟩
      | ifFalse otherCondition _ => cases (childDeterministic condition otherCondition).1
  | ifFalse condition _ ih =>
      cases second with
      | ifTrue otherCondition _ => cases (childDeterministic condition otherCondition).1
      | ifFalse otherCondition otherBranch =>
          obtain ⟨_, rfl, rfl⟩ := childDeterministic condition otherCondition
          obtain ⟨rfl, rfl, rfl⟩ := ih otherBranch
          exact ⟨rfl, rfl, rfl⟩

  | wordMatch scrutinee choice _ ih =>
      cases second with
      | wordMatch otherScrutinee otherChoice otherBranch =>
          obtain ⟨rfl, rfl, rfl⟩ := childDeterministic scrutinee otherScrutinee
          obtain ⟨rfl, rfl⟩ := choice.deterministic otherChoice
          obtain ⟨rfl, rfl, rfl⟩ := ih otherBranch
          exact ⟨rfl, rfl, rfl⟩

end Solcore.Frontend

/-!
## Consolidated module: `Solcore.Frontend.ComputationReturnTreeFragmentProperties`
-/

/-! Exact body provenance closes child membership through all hidden binders.
Only the child's syntactic membership and weakening laws are required. -/

set_option autoImplicit false

namespace Solcore.Frontend

private theorem fold_fragment {F : Core.Expr → Prop}
    (childWeakening : ∀ {core}, F core → ∀ cutoff, F (core.weakenAt cutoff))
    (entries : List (Syntax.MatchCase × (Option Core.Word × Core.Expr)))
    (defaultEntry : Option (Syntax.Block × Core.Expr))
    (branches : ∀ entry ∈ entries, ComputationBodyFragment F entry.2.2)
    (fallback : ∀ entry ∈ defaultEntry.toList, ComputationBodyFragment F entry.2)
    {core : Core.Expr}
    (lowered : entries.foldr
      (fun entry tail => match entry.2.1 with
        | none => some (entry.2.2.weakenAt 0)
        | some word => tail.map fun body => .ifE (.binary .wordEq (.var 0) (.word word)) (entry.2.2.weakenAt 0) body)
      (defaultEntry.map fun entry => entry.2.weakenAt 0) = some core) :
    ComputationBodyFragment F core := by
  induction entries generalizing core with
  | nil =>
      cases defaultEntry with
      | none => simp at lowered
      | some entry =>
          simp only [List.foldr_nil, Option.map_some, Option.some.injEq] at lowered
          subst core
          exact (fallback entry (by simp)).weakenAt childWeakening 0
  | cons entry rest ih =>
      cases tag : entry.2.1 with
      | none =>
          simp only [List.foldr_cons, tag, Option.some.injEq] at lowered
          subst core
          exact (branches entry (by simp)).weakenAt childWeakening 0
      | some word =>
          simp only [List.foldr_cons, tag, Option.map_eq_some_iff] at lowered
          obtain ⟨body, tail, rfl⟩ := lowered
          exact .ifE .wordTest ((branches entry (by simp)).weakenAt childWeakening 0)
            (ih (fun item member => branches item (by simp [member])) tail)

theorem ComputationReturnTreeElaborates.core_fragment
    {ChildElab : LocalNameTable → Resolved.Context → Syntax.Expr → Core.Expr → Core.Ty → Prop}
    {F : Core.Expr → Prop}
    (childMembership : ∀ {table context source core type}, ChildElab table context source core type → F core)
    (childWeakening : ∀ {core}, F core → ∀ cutoff, F (core.weakenAt cutoff))
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {inputs : LocalTypeInputs}
    {body : Syntax.Block} {core : Core.Expr} {type : Core.Ty}
    (elaboration : ComputationReturnTreeElaborates ChildElab types owner inputs body core type) :
    ComputationBodyFragment F core := by
  induction elaboration with
  | bare => exact .unit
  | expression child => exact .leaf (childMembership child)
  | block _ ih => exact ih
  | binding _ child _ ih => exact .letE (.leaf (childMembership child)) ih
  | inferred child _ ih => exact .letE (.leaf (childMembership child)) ih
  | discard child _ ih => exact .letE (.leaf (childMembership child)) (ComputationBodyFragment.weakenAt childWeakening ih 0)
  | conditional guard _ _ _ yesIH noIH => exact .ifE (.leaf (childMembership guard)) yesIH noIH
  | wordMatch scrutinee _ _ _ _ _ _ lowered branchesIH defaultIH =>
      exact .letE (.leaf (childMembership scrutinee))
        (fold_fragment childWeakening _ _ branchesIH defaultIH lowered)

end Solcore.Frontend

/-!
## Consolidated module: `Solcore.Frontend.ComputationReturnTreeExecutionProperties`
-/

/-! Whole-body Core correspondence uses separate child execution and insertion
laws at every original scope. Actual values and intermediate stores are retained. -/

set_option autoImplicit false

namespace Solcore.Frontend

private theorem word_test_iff {environment : Core.Environment} {actual : Core.Value}
    {literal : Core.Word} {initialStore finalStore : Core.Store} {decision : Bool} :
    Core.Evaluates (actual :: environment) initialStore
      (.binary .wordEq (.var 0) (.word literal)) (.bool decision) finalStore ↔
      ∃ word, actual = .word word ∧ (word == literal) = decision ∧ finalStore = initialStore := by
  constructor
  · intro evaluation
    cases evaluation with
    | binary left right applied =>
        cases left with
        | var found =>
            simp only [List.getElem?_cons_zero, Option.some.injEq] at found
            subst found
            cases right
            cases actual <;> simp_all [Core.BinaryOp.apply]
  · rintro ⟨word, rfl, rfl, rfl⟩
    exact .binary (.var rfl) .word rfl

private theorem fold_evaluates_iff
    (entries : List (Syntax.MatchCase × (Option Core.Word × Core.Expr)))
    (defaultEntry : Option (Syntax.Block × Core.Expr))
    {environment : Core.Environment} {actual value : Core.Value}
    {initialStore finalStore : Core.Store}
    {E : Syntax.Block → Prop}
    (patterns : ∀ entry ∈ entries, WordMatchPatternClassifies entry.1.value.pattern entry.2.1)
    (branches : ∀ entry ∈ entries, Core.Evaluates (actual :: environment) initialStore
      (entry.2.2.weakenAt 0) value finalStore ↔ E entry.1.value.body)
    (fallback : ∀ entry ∈ defaultEntry.toList, Core.Evaluates (actual :: environment) initialStore
      (entry.2.weakenAt 0) value finalStore ↔ E entry.1) :
    ∀ {core : Core.Expr},
      entries.foldr (fun entry tail => match entry.2.1 with
        | none => some (entry.2.2.weakenAt 0)
        | some word => tail.map (fun tailCore => .ifE (.binary .wordEq (.var 0) (.word word))
            (entry.2.2.weakenAt 0) tailCore)) (defaultEntry.map (fun entry => entry.2.weakenAt 0)) = some core →
      (Core.Evaluates (actual :: environment) initialStore core value finalStore ↔
        ∃ selected tests, WordMatchChooses actual (entries.map Prod.fst)
          (defaultEntry.map Prod.fst) selected tests ∧ E selected) := by
  revert patterns branches
  induction entries with
  | nil =>
      intro _ _ core lowered
      obtain ⟨entry, found, rfl⟩ := Option.map_eq_some_iff.mp lowered
      have branch := fallback entry (by simp [found])
      simp only [List.map_nil, found, Option.map_some]
      constructor
      · intro evaluation; exact ⟨_, 0, .fallback, branch.mp evaluation⟩
      · rintro ⟨_, _, choice, evaluated⟩; cases choice; exact branch.mpr evaluated
  | cons entry rest ih =>
      intro patterns branches core lowered
      have meaning := patterns entry (List.mem_cons_self)
      have branch := branches entry (List.mem_cons_self)
      cases tag : entry.2.1 with
      | none =>
          simp only [tag] at meaning
          have same : entry.2.2.weakenAt 0 = core := by
            simpa only [List.foldr_cons, tag, Option.some.injEq] using lowered
          subst core
          constructor
          · intro evaluation; exact ⟨_, 0, .wildcard meaning, branch.mp evaluation⟩
          · rintro ⟨selected, tests, choice, evaluated⟩
            cases choice with
            | wildcard _ => exact branch.mpr evaluated
            | hit other => cases meaning.tag_unique other
            | miss other _ _ => cases meaning.tag_unique other
      | some literal =>
          simp only [tag] at meaning
          simp only [List.foldr_cons, tag] at lowered
          obtain ⟨tailCore, tailLowered, rfl⟩ := Option.map_eq_some_iff.mp lowered
          have tail := ih (fun item member => patterns item (List.mem_cons_of_mem entry member))
            (fun item member => branches item (List.mem_cons_of_mem entry member)) tailLowered
          constructor
          · intro evaluation
            cases evaluation with
            | ifTrue guard evaluated =>
                obtain ⟨word, rfl, equal, rfl⟩ := word_test_iff.mp guard
                have same : word = literal := by simpa using equal
                subst word
                exact ⟨_, 1, .hit meaning, branch.mp evaluated⟩
            | ifFalse guard evaluated =>
                obtain ⟨word, rfl, different, rfl⟩ := word_test_iff.mp guard
                have unequal : word ≠ literal := by simpa using different
                obtain ⟨selected, tests, choice, selectedBranch⟩ := tail.mp evaluated
                exact ⟨selected, tests + 1, .miss meaning unequal choice, selectedBranch⟩
          · rintro ⟨selected, tests, choice, evaluated⟩
            cases choice with
            | wildcard other => cases meaning.tag_unique other
            | hit actualMeaning =>
                have same := actualMeaning.value_unique meaning
                subst same
                exact .ifTrue (word_test_iff.mpr ⟨_, rfl, by simp, rfl⟩) (branch.mpr evaluated)
            | miss otherMeaning different choice =>
                have same := otherMeaning.value_unique meaning
                subst same
                exact .ifFalse (word_test_iff.mpr ⟨_, rfl, by simpa using different, rfl⟩)
                  (tail.mpr ⟨_, _, choice, evaluated⟩)

theorem ComputationReturnTreeElaborates.evaluates_iff
    {ChildElab : LocalNameTable → Resolved.Context → Syntax.Expr → Core.Expr → Core.Ty → Prop}
    {ChildEval : LocalNameTable → Resolved.Environment → Core.Store → Syntax.Expr → Core.Value → Core.Store → Prop}
    {F : Core.Expr → Prop}
    (childMembership : ∀ {table context source core type}, ChildElab table context source core type → F core)
    (childWeakening : ∀ {core}, F core → ∀ cutoff, F (core.weakenAt cutoff))
    (childInserts : ∀ {core}, F core → ∀ leading suffix inserted {initialStore finalStore value},
      Core.Evaluates (leading ++ inserted :: suffix) initialStore (core.weakenAt leading.length) value finalStore ↔
        Core.Evaluates (leading ++ suffix) initialStore core value finalStore)
    (childExecution : ∀ {table context environment source core type},
      ChildElab table context source core type → environment.ids = context.ids →
      ∀ {initialStore finalStore value}, ChildEval table environment initialStore source value finalStore ↔
        Core.Evaluates environment.values initialStore core value finalStore)
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {inputs : LocalTypeInputs}
    {environment : Resolved.Environment} {body : Syntax.Block} {core : Core.Expr} {type : Core.Ty}
    (elaboration : ComputationReturnTreeElaborates ChildElab types owner inputs body core type)
    (sameIds : environment.ids = inputs.context.ids)
    {initialStore finalStore : Core.Store} {value : Core.Value} :
    ComputationReturnTreeEvaluates ChildEval owner inputs.names environment initialStore body value finalStore ↔
      Core.Evaluates environment.values initialStore core value finalStore := by
  induction elaboration generalizing environment initialStore finalStore value with
  | bare =>
      constructor <;> intro evaluation <;> cases evaluation <;> constructor
  | expression child =>
      constructor
      · intro evaluation
        cases evaluation with
        | expression evaluated => exact (childExecution child sameIds).mp evaluated
      · intro evaluation
        exact .expression ((childExecution child sameIds).mpr evaluation)
  | block _ ih =>
      constructor
      · intro evaluation
        cases evaluation with
        | block evaluated => exact (ih sameIds).mp evaluated
      · intro evaluation
        exact .block ((ih sameIds).mpr evaluation)
  | @binding inputs _ _ name _ _ _ declaredType _ _ _ _ child _ ih =>
      constructor
      · intro evaluation
        cases evaluation with
        | binding initializer tail =>
            rename_i middleStore boundValue
            refine .letE ((childExecution child sameIds).mp initializer) ?_
            apply (ih (environment := (Resolved.freshLocalId owner inputs.ids, boundValue) :: environment) ?_).mp
            · simpa only [LocalTypeInputs.bindFresh_names, LocalTypeInputs.names_ids] using tail
            · simpa only [LocalTypeInputs.bindFresh_context, Resolved.LocalScope.ids, List.map_cons]
                using congrArg (List.cons _) sameIds
      · intro evaluation
        cases evaluation with
        | letE initializer tail =>
            rename_i bodyStore boundValue
            apply ComputationReturnTreeEvaluates.binding ((childExecution child sameIds).mpr initializer)
            have evaluated := (ih (environment := (Resolved.freshLocalId owner inputs.ids, boundValue) :: environment) ?_).mpr tail
            · simpa only [LocalTypeInputs.bindFresh_names, LocalTypeInputs.names_ids] using evaluated
            · simpa only [LocalTypeInputs.bindFresh_context, Resolved.LocalScope.ids, List.map_cons]
                using congrArg (List.cons _) sameIds
  | @inferred inputs _ _ name _ _ inferredType _ _ _ child _ ih =>
      constructor
      · intro evaluation
        cases evaluation with
        | inferred initializer tail =>
            rename_i middleStore boundValue
            refine .letE ((childExecution child sameIds).mp initializer) ?_
            apply (ih (environment := (Resolved.freshLocalId owner inputs.ids, boundValue) :: environment) ?_).mp
            · simpa only [LocalTypeInputs.bindFresh_names, LocalTypeInputs.names_ids] using tail
            · simpa only [LocalTypeInputs.bindFresh_context, Resolved.LocalScope.ids, List.map_cons]
                using congrArg (List.cons _) sameIds
      · intro evaluation
        cases evaluation with
        | letE initializer tail =>
            rename_i bodyStore boundValue
            apply ComputationReturnTreeEvaluates.inferred ((childExecution child sameIds).mpr initializer)
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
            exact .letE ((childExecution child sameIds).mp head)
              ((ComputationBodyFragment.evaluates_insert_iff (F := F) childInserts
                (ComputationReturnTreeElaborates.core_fragment (F := F) childMembership childWeakening tailElaboration) [] environment.values discardedValue).mpr
                ((ih sameIds).mp tail))
      · intro evaluation
        cases evaluation with
        | letE head tail =>
            exact .discard ((childExecution child sameIds).mpr head)
              ((ih sameIds).mpr ((ComputationBodyFragment.evaluates_insert_iff (F := F) childInserts
                (ComputationReturnTreeElaborates.core_fragment (F := F) childMembership childWeakening tailElaboration) [] environment.values _).mp tail))
  | conditional guard _ _ _ thenIH elseIH =>
      constructor
      · intro evaluation
        cases evaluation with
        | ifTrue condition branch =>
            exact .ifTrue ((childExecution guard sameIds).mp condition) ((thenIH sameIds).mp branch)
        | ifFalse condition branch =>
            exact .ifFalse ((childExecution guard sameIds).mp condition) ((elseIH sameIds).mp branch)
      · intro evaluation
        cases evaluation with
        | ifTrue condition branch =>
            exact .ifTrue ((childExecution guard sameIds).mpr condition) ((thenIH sameIds).mpr branch)
        | ifFalse condition branch =>
            exact .ifFalse ((childExecution guard sameIds).mpr condition) ((elseIH sameIds).mpr branch)
  | @wordMatch inputs _ _ _ _ _ _ _ _ _ _ _ _ _ scrutinee ordered patterns _ branches defaultOrdered defaults lowered branchIH defaultIH =>
      subst ordered
      subst defaultOrdered
      have folded {actual : Core.Value} {store : Core.Store} := fold_evaluates_iff _ _
        (actual := actual) (initialStore := store) (finalStore := finalStore) (value := value)
        (E := fun selected => ComputationReturnTreeEvaluates ChildEval owner inputs.names
          environment store selected value finalStore) patterns
        (fun entry member => (ComputationBodyFragment.evaluates_insert_iff (F := F) childInserts
          (ComputationReturnTreeElaborates.core_fragment (F := F) childMembership childWeakening
            (branches entry member)) [] environment.values actual).trans ((branchIH entry member sameIds).symm))
        (fun entry member => (ComputationBodyFragment.evaluates_insert_iff (F := F) childInserts
          (ComputationReturnTreeElaborates.core_fragment (F := F) childMembership childWeakening
            (defaults entry member)) [] environment.values actual).trans ((defaultIH entry member sameIds).symm)) lowered
      constructor
      · intro evaluation
        cases evaluation with
        | wordMatch head choice tail =>
            exact .letE ((childExecution scrutinee sameIds).mp head) (folded.mpr ⟨_, _, choice, tail⟩)
      · intro evaluation
        cases evaluation with
        | letE head tail =>
            obtain ⟨selected, tests, choice, branch⟩ := folded.mp tail
            exact .wordMatch ((childExecution scrutinee sameIds).mpr head) choice branch

end Solcore.Frontend

/-!
## Consolidated module: `Solcore.Frontend.ComputationReturnTreeCostProperties`
-/

/-! Supplied actual costs compose through mixed statements. A hidden discard
slot preserves the complete tail path, including its effects and actual captures. -/

set_option autoImplicit false

namespace Solcore.Frontend

private theorem insert_zero_path {F : Core.Expr → Prop}
    (childPaths : ∀ {expr}, F expr → ∀ (leading suffix : Core.Environment) (inserted : Core.Value),
      ∀ {initialStore finalStore value},
        Core.Evaluates (leading ++ suffix) initialStore expr value finalStore →
        ∃ cost, ∀ continuation,
          Core.Steps cost ⟨.eval expr (leading ++ suffix), continuation, initialStore⟩
            ⟨.ret value, continuation, finalStore⟩ ∧
          Core.Steps cost
            ⟨.eval (expr.weakenAt leading.length) (leading ++ inserted :: suffix), continuation, initialStore⟩
            ⟨.ret value, continuation, finalStore⟩)
    {expr : Core.Expr} (fragment : ComputationBodyFragment F expr)
    {environment : Core.Environment} {initialStore finalStore : Core.Store}
    {value : Core.Value} {cost : Nat}
    (path : Core.Steps cost (.initial expr environment initialStore) (.final value finalStore))
    (inserted : Core.Value) (continuation : List Core.Frame) :
    Core.Steps cost ⟨.eval (expr.weakenAt 0) (inserted :: environment), continuation, initialStore⟩
      ⟨.ret value, continuation, finalStore⟩ := by
  obtain ⟨commonCost, paths⟩ := ComputationBodyFragment.insertion_paths (F := F) childPaths fragment [] environment inserted (Core.steps_from_initial_sound path)
  have sameCost := (path.final_unique (paths []).1).1
  exact sameCost.symm ▸ (paths continuation).2

private theorem fold_path
    (entries : List (Syntax.MatchCase × (Option Core.Word × Core.Expr)))
    (defaultEntry : Option (Syntax.Block × Core.Expr))
    {actual value : Core.Value} {environment : Core.Environment} {initialStore finalStore : Core.Store}
    {selected : Syntax.Block} {tests branchCost : Nat} {core : Core.Expr}
    (patterns : ∀ entry ∈ entries, WordMatchPatternClassifies entry.1.value.pattern entry.2.1)
    (choice : WordMatchChooses actual (entries.map Prod.fst) (defaultEntry.map Prod.fst) selected tests)
    (branches : ∀ entry ∈ entries, entry.1.value.body = selected → ∀ continuation,
      Core.Steps branchCost ⟨.eval (entry.2.2.weakenAt 0) (actual :: environment), continuation, initialStore⟩
        ⟨.ret value, continuation, finalStore⟩)
    (fallback : ∀ entry ∈ defaultEntry.toList, entry.1 = selected → ∀ continuation,
      Core.Steps branchCost ⟨.eval (entry.2.weakenAt 0) (actual :: environment), continuation, initialStore⟩
        ⟨.ret value, continuation, finalStore⟩)
    (lowered : entries.foldr
      (fun entry tail => match entry.2.1 with
        | none => some (entry.2.2.weakenAt 0)
        | some word => tail.map fun body => .ifE (.binary .wordEq (.var 0) (.word word)) (entry.2.2.weakenAt 0) body)
      (defaultEntry.map fun entry => entry.2.weakenAt 0) = some core)
    (continuation : List Core.Frame) :
    Core.Steps (branchCost + 7 * tests)
      ⟨.eval core (actual :: environment), continuation, initialStore⟩
      ⟨.ret value, continuation, finalStore⟩ := by
  induction entries generalizing actual selected tests core with
  | nil =>
      cases defaultEntry with
      | none => simp at lowered
      | some entry =>
          simp only [List.foldr_nil, Option.map_some, Option.some.injEq] at lowered
          subst core
          cases choice
          simpa using fallback entry (by simp) rfl continuation
  | cons entry rest ih =>
      rcases entry with ⟨arm, tag, branchCore⟩
      have pattern := patterns ⟨arm, tag, branchCore⟩ (by simp)
      cases tag with
      | none =>
          simp only [List.foldr_cons, Option.some.injEq] at lowered
          subst core
          cases choice with
          | wildcard _ => simpa using branches ⟨arm, none, branchCore⟩ (by simp) rfl continuation
          | hit meaning | miss meaning _ _ =>
              cases meaning.tag_unique pattern
      | some literal =>
          simp only [List.foldr_cons, Option.map_eq_some_iff] at lowered
          obtain ⟨tailCore, tailLowered, rfl⟩ := lowered
          cases choice with
          | wildcard meaning => cases meaning.tag_unique pattern
          | hit meaning =>
              have equal := meaning.value_unique pattern
              subst_vars
              rename_i literal
              have guard (k) : Core.Steps 5
                  ⟨.eval (.binary .wordEq (.var 0) (.word literal)) (.word literal :: environment), k, initialStore⟩
                  ⟨.ret (.bool true), k, initialStore⟩ :=
                CostStepComposition.binary (.cons (.var rfl) .refl) (.cons .word .refl) (by simp [Core.BinaryOp.apply])
              have costEq : 5 + branchCost + 2 = branchCost + 7 * 1 := by omega
              rw [← costEq]
              exact CostStepComposition.ifTrue (guard _) (branches ⟨arm, some literal, branchCore⟩ (by simp) rfl continuation)
          | miss meaning different tail =>
              have equal := meaning.value_unique pattern
              subst_vars
              rename_i word literal tests
              have guard (k) : Core.Steps 5
                  ⟨.eval (.binary .wordEq (.var 0) (.word literal)) (.word word :: environment), k, initialStore⟩
                  ⟨.ret (.bool false), k, initialStore⟩ :=
                CostStepComposition.binary (.cons (.var rfl) .refl) (.cons .word .refl) (by simp [Core.BinaryOp.apply, different])
              have restPath := ih (fun item member => patterns item (by simp [member])) tail
                (fun item member => branches item (by simp [member])) fallback tailLowered
              have costEq : 5 + (branchCost + 7 * tests) + 2 = branchCost + 7 * (tests + 1) := by omega
              rw [← costEq]
              exact CostStepComposition.ifFalse (guard _) restPath

theorem ComputationReturnTreeEvaluatesWithCost.toStepsWithContinuation
    {ChildElab : LocalNameTable → Resolved.Context → Syntax.Expr → Core.Expr → Core.Ty → Prop}
    {ChildCost : LocalNameTable → Resolved.Environment → Core.Store → Syntax.Expr → Core.Value → Core.Store → Nat → Prop}
    {F : Core.Expr → Prop}
    (childMembership : ∀ {table context source core type}, ChildElab table context source core type → F core)
    (childWeakening : ∀ {core}, F core → ∀ cutoff, F (core.weakenAt cutoff))
    (childPaths : ∀ {expr}, F expr → ∀ (leading suffix : Core.Environment) (inserted : Core.Value),
      ∀ {initialStore finalStore value},
        Core.Evaluates (leading ++ suffix) initialStore expr value finalStore →
        ∃ cost, ∀ continuation,
          Core.Steps cost ⟨.eval expr (leading ++ suffix), continuation, initialStore⟩
            ⟨.ret value, continuation, finalStore⟩ ∧
          Core.Steps cost
            ⟨.eval (expr.weakenAt leading.length) (leading ++ inserted :: suffix), continuation, initialStore⟩
            ⟨.ret value, continuation, finalStore⟩)
    (childSteps : ∀ {table context environment initialStore finalStore source value cost},
      ChildCost table environment initialStore source value finalStore cost →
      ∀ {core type}, ChildElab table context source core type → environment.ids = context.ids →
      ∀ continuation, Core.Steps cost ⟨.eval core environment.values, continuation, initialStore⟩
        ⟨.ret value, continuation, finalStore⟩)
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {inputs : LocalTypeInputs}
    {environment : Resolved.Environment} {initialStore finalStore : Core.Store}
    {body : Syntax.Block} {value : Core.Value} {cost : Nat}
    (evaluation : ComputationReturnTreeEvaluatesWithCost ChildCost owner inputs.names environment
      initialStore body value finalStore cost)
    {core : Core.Expr} {type : Core.Ty}
    (elaboration : ComputationReturnTreeElaborates ChildElab types owner inputs body core type)
    (sameIds : environment.ids = inputs.context.ids) (continuation : List Core.Frame) :
    Core.Steps cost ⟨.eval core environment.values, continuation, initialStore⟩
      ⟨.ret value, continuation, finalStore⟩ := by
  induction elaboration generalizing environment initialStore finalStore value cost continuation with
  | bare => cases evaluation; exact .cons .unit .refl
  | expression child =>
      cases evaluation with
      | expression actual => exact childSteps actual child sameIds continuation
  | block _ ih =>
      cases evaluation with
      | block actual => exact ih actual sameIds continuation
  | @binding inputs _ _ _ _ _ _ _ _ _ _ _ child _ ih =>
      cases evaluation with
      | binding initializer tail =>
          rename_i middleStore boundValue initializerCost tailCost
          apply CostStepComposition.letE (childSteps initializer child sameIds _)
          apply ih (environment := (Resolved.freshLocalId owner inputs.ids, boundValue) :: environment)
          · simpa only [LocalTypeInputs.bindFresh_names, LocalTypeInputs.names_ids] using tail
          · simpa only [LocalTypeInputs.bindFresh_context, Resolved.LocalScope.ids, List.map_cons]
              using congrArg (List.cons _) sameIds
  | @inferred inputs _ _ _ _ _ _ _ _ _ child _ ih =>
      cases evaluation with
      | inferred initializer tail =>
          rename_i middleStore boundValue initializerCost tailCost
          apply CostStepComposition.letE (childSteps initializer child sameIds _)
          apply ih (environment := (Resolved.freshLocalId owner inputs.ids, boundValue) :: environment)
          · simpa only [LocalTypeInputs.bindFresh_names, LocalTypeInputs.names_ids] using tail
          · simpa only [LocalTypeInputs.bindFresh_context, Resolved.LocalScope.ids, List.map_cons]
              using congrArg (List.cons _) sameIds
  | discard child tailElaboration ih =>
      cases evaluation with
      | discard expression tail =>
          rename_i middleStore discardedValue expressionCost tailCost
          exact CostStepComposition.letE (childSteps expression child sameIds _)
            (insert_zero_path (F := F) childPaths
              (ComputationReturnTreeElaborates.core_fragment (F := F) childMembership childWeakening tailElaboration) (ih tail sameIds []) discardedValue continuation)
  | conditional guard _ _ _ thenIH elseIH =>
      cases evaluation with
      | ifTrue condition branch =>
          exact CostStepComposition.ifTrue (childSteps condition guard sameIds _)
            (thenIH branch sameIds continuation)
      | ifFalse condition branch =>
          exact CostStepComposition.ifFalse (childSteps condition guard sameIds _)
            (elseIH branch sameIds continuation)
  | wordMatch scrutinee ordered patterns _ branches defaultOrdered fallback lowered branchIH defaultIH =>
      cases evaluation with
      | wordMatch initializer choice branch =>
          rw [← ordered, ← defaultOrdered] at choice
          have selectedPath := fold_path _ _ patterns choice
            (fun entry member selectedEq k => by
              have actual := branch
              rw [← selectedEq] at actual
              exact insert_zero_path (F := F) childPaths
                (ComputationReturnTreeElaborates.core_fragment (F := F) childMembership childWeakening (branches entry member))
                (branchIH entry member actual sameIds []) _ k)
            (fun entry member selectedEq k => by
              have actual := branch
              rw [← selectedEq] at actual
              exact insert_zero_path (F := F) childPaths
                (ComputationReturnTreeElaborates.core_fragment (F := F) childMembership childWeakening (fallback entry member))
                (defaultIH entry member actual sameIds []) _ k) lowered continuation
          have path := CostStepComposition.letE (childSteps initializer scrutinee sameIds _) selectedPath
          simp only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] at path ⊢
          exact path

theorem ComputationReturnTreeElaborates.evaluatesWithCost_iff_steps
    {ChildElab : LocalNameTable → Resolved.Context → Syntax.Expr → Core.Expr → Core.Ty → Prop}
    {ChildEval : LocalNameTable → Resolved.Environment → Core.Store → Syntax.Expr → Core.Value → Core.Store → Prop}
    {ChildCost : LocalNameTable → Resolved.Environment → Core.Store → Syntax.Expr → Core.Value → Core.Store → Nat → Prop}
    {F : Core.Expr → Prop}
    (childMembership : ∀ {table context source core type}, ChildElab table context source core type → F core)
    (childWeakening : ∀ {core}, F core → ∀ cutoff, F (core.weakenAt cutoff))
    (childInserts : ∀ {core}, F core → ∀ leading suffix inserted {initialStore finalStore value},
      Core.Evaluates (leading ++ inserted :: suffix) initialStore (core.weakenAt leading.length) value finalStore ↔
        Core.Evaluates (leading ++ suffix) initialStore core value finalStore)
    (childExecution : ∀ {table context environment source core type},
      ChildElab table context source core type → environment.ids = context.ids →
      ∀ {initialStore finalStore value}, ChildEval table environment initialStore source value finalStore ↔
        Core.Evaluates environment.values initialStore core value finalStore)
    (childCostIff : ∀ {table environment initialStore source value finalStore},
      ChildEval table environment initialStore source value finalStore ↔
        ∃ cost, ChildCost table environment initialStore source value finalStore cost)
    (childPaths : ∀ {expr}, F expr → ∀ (leading suffix : Core.Environment) (inserted : Core.Value),
      ∀ {initialStore finalStore value},
        Core.Evaluates (leading ++ suffix) initialStore expr value finalStore →
        ∃ cost, ∀ continuation,
          Core.Steps cost ⟨.eval expr (leading ++ suffix), continuation, initialStore⟩
            ⟨.ret value, continuation, finalStore⟩ ∧
          Core.Steps cost
            ⟨.eval (expr.weakenAt leading.length) (leading ++ inserted :: suffix), continuation, initialStore⟩
            ⟨.ret value, continuation, finalStore⟩)
    (childSteps : ∀ {table context environment initialStore finalStore source value cost},
      ChildCost table environment initialStore source value finalStore cost →
      ∀ {core type}, ChildElab table context source core type → environment.ids = context.ids →
      ∀ continuation, Core.Steps cost ⟨.eval core environment.values, continuation, initialStore⟩
        ⟨.ret value, continuation, finalStore⟩)
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {inputs : LocalTypeInputs}
    {environment : Resolved.Environment} {body : Syntax.Block} {core : Core.Expr} {type : Core.Ty}
    (elaboration : ComputationReturnTreeElaborates ChildElab types owner inputs body core type)
    (sameIds : environment.ids = inputs.context.ids)
    {initialStore finalStore : Core.Store} {value : Core.Value} {cost : Nat} :
    ComputationReturnTreeEvaluatesWithCost ChildCost owner inputs.names environment
      initialStore body value finalStore cost ↔
      Core.Steps cost (.initial core environment.values initialStore) (.final value finalStore) := by
  constructor
  · intro evaluation
    exact ComputationReturnTreeEvaluatesWithCost.toStepsWithContinuation (F := F)
      childMembership childWeakening childPaths childSteps evaluation elaboration sameIds []
  · intro path
    have evaluation := (ComputationReturnTreeElaborates.evaluates_iff (F := F) (ChildElab := ChildElab) (ChildEval := ChildEval)
      childMembership childWeakening childInserts childExecution elaboration sameIds).mpr (Core.steps_from_initial_sound path)
    obtain ⟨actualCost, actual⟩ := (computationReturnTreeEvaluates_iff_exists_cost (ChildEval := ChildEval) (ChildCost := ChildCost) childCostIff).mp evaluation
    have sameCost := (path.final_unique (ComputationReturnTreeEvaluatesWithCost.toStepsWithContinuation (F := F)
      childMembership childWeakening childPaths childSteps actual elaboration sameIds [])).1
    exact sameCost.symm ▸ actual

end Solcore.Frontend

/-!
## Consolidated module: `Solcore.Frontend.ComputationReturnTreeProperties`
-/

/-! Shared checking uses only the child's exact checker correspondence.
Original tails, branches and fresh scopes stay independent of runtime laws. -/

set_option autoImplicit false

namespace Solcore.Frontend

variable {checkChild : LocalNameTable → Resolved.Context → Syntax.Expr → Option (Core.Expr × Core.Ty)}
    {ChildElab : LocalNameTable → Resolved.Context → Syntax.Expr → Core.Expr → Core.Ty → Prop}
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {inputs : LocalTypeInputs}

private theorem binding_children
    {blockSpan letSpan : Syntax.SourceSpan} {name : Syntax.Identifier}
    {annotation : Syntax.TypeExpr} {initializer : Syntax.Expr} {rest : List Syntax.Statement}
    {core : Core.Expr} {type : Core.Ty}
    (accepted : elaborateComputationReturnTree? checkChild types owner inputs
      ⟨blockSpan, ⟨letSpan, .letDecl name (some annotation) (some initializer)⟩ :: rest⟩ = some (core, type)) :
    ∃ declaredType initializerCore tailCore,
      interpretStructuralType? types annotation = some declaredType ∧
      checkChild inputs.names inputs.context initializer = some (initializerCore, declaredType) ∧
      elaborateComputationReturnTree? checkChild types owner (inputs.bindFresh owner name.value declaredType)
        ⟨blockSpan, rest⟩ = some (tailCore, type) ∧ core = .letE initializerCore tailCore := by
  rw [elaborateComputationReturnTree?] at accepted
  simp only [bind, Option.bind_eq_some_iff] at accepted
  obtain ⟨declaredType, meaning, ⟨initializerCore, initializerType⟩, initializerAccepted, remaining⟩ := accepted
  split at remaining
  next sameType =>
    change initializerType = declaredType at sameType; subst initializerType
    simp only [Option.bind_eq_some_iff, pure, Option.some.injEq, Prod.mk.injEq] at remaining
    obtain ⟨⟨tailCore, returnType⟩, tailAccepted, rfl, rfl⟩ := remaining
    exact ⟨declaredType, initializerCore, tailCore, meaning, initializerAccepted, tailAccepted, rfl⟩
  next different => cases remaining

private theorem conditional_children
    {blockSpan ifSpan : Syntax.SourceSpan} {condition : Syntax.Expr}
    {thenBody elseBody : Syntax.Block} {core : Core.Expr} {type : Core.Ty}
    (accepted : elaborateComputationReturnTree? checkChild types owner inputs
      ⟨blockSpan, [⟨ifSpan, .ifThen condition thenBody (some elseBody)⟩]⟩ = some (core, type)) :
    ∃ conditionCore thenCore elseCore,
      checkChild inputs.names inputs.context condition = some (conditionCore, .bool) ∧
      ComputationNamesProtected (inputs.names.map Prod.fst) thenBody ∧
      elaborateComputationReturnTree? checkChild types owner inputs thenBody = some (thenCore, type) ∧
      elaborateComputationReturnTree? checkChild types owner inputs elseBody = some (elseCore, type) ∧
      core = .ifE conditionCore thenCore elseCore := by
  rw [elaborateComputationReturnTree?] at accepted
  simp only [bind, Option.bind_eq_some_iff] at accepted
  obtain ⟨⟨conditionCore, conditionType⟩, conditionAccepted, remaining⟩ := accepted
  split at remaining
  next conditionGuard =>
    obtain ⟨conditionBool, namesGuard⟩ := conditionGuard
    change conditionType = .bool at conditionBool; subst conditionType
    simp only [Option.bind_eq_some_iff] at remaining
    obtain ⟨⟨thenCore, thenType⟩, thenAccepted, ⟨elseCore, elseType⟩, elseAccepted, result⟩ := remaining
    split at result
    next sameType =>
      change thenType = elseType at sameType; subst elseType
      simp only [pure, Option.some.injEq, Prod.mk.injEq] at result
      rcases result with ⟨rfl, rfl⟩
      exact ⟨conditionCore, thenCore, elseCore, conditionAccepted,
        computationBlockPreservesNames_iff.mp namesGuard, thenAccepted, elseAccepted, rfl⟩
    next different => cases result
  next notBool => cases remaining

private theorem returnTree_complete
    (childCorrect : ∀ {table context source core type},
      checkChild table context source = some (core, type) ↔ ChildElab table context source core type)
    {body : Syntax.Block} {core : Core.Expr} {type : Core.Ty}
    (elaboration : ComputationReturnTreeElaborates ChildElab types owner inputs body core type) :
    elaborateComputationReturnTree? checkChild types owner inputs body = some (core, type) := by
  induction elaboration with
  | bare => simp only [elaborateComputationReturnTree?]
  | expression child => simpa only [elaborateComputationReturnTree?] using childCorrect.mpr child
  | block _ ih => simpa only [elaborateComputationReturnTree?] using ih
  | binding meaning initializer _ ih =>
      rw [elaborateComputationReturnTree?]
      simp [meaning.complete, childCorrect.mpr initializer, ih]
  | inferred initializer _ ih =>
      rw [elaborateComputationReturnTree?]
      simp [childCorrect.mpr initializer, ih]
  | discard expression _ ih =>
      rw [elaborateComputationReturnTree?]
      simp only [childCorrect.mpr expression, ih, bind, Option.bind_some, pure, Pure.pure]
  | conditional condition protection _ _ thenIH elseIH =>
      rw [elaborateComputationReturnTree?]
      simp [childCorrect.mpr condition, computationBlockPreservesNames_iff.mpr protection, thenIH, elseIH]
  | wordMatch scrutinee ordered patterns compatible _ defaultOrdered _ lowered branchIH defaultIH =>
      exact ComputationReturnTreeChecking.match_iff.mpr
        ⟨_, _, childCorrect.mpr scrutinee, _, _, _, ordered, patterns, compatible, branchIH, defaultOrdered, defaultIH, lowered, rfl⟩

private theorem returnTree_sound
    (childCorrect : ∀ {table context source core type},
      checkChild table context source = some (core, type) ↔ ChildElab table context source core type)
    {inputs : LocalTypeInputs} {body : Syntax.Block} {core : Core.Expr} {type : Core.Ty}
    (accepted : elaborateComputationReturnTree? checkChild types owner inputs body = some (core, type)) :
    ComputationReturnTreeElaborates ChildElab types owner inputs body core type := by
  cases body with
  | mk blockSpan statements =>
      cases statements with
      | nil => simp only [elaborateComputationReturnTree?, reduceCtorEq] at accepted
      | cons statement rest =>
          cases statement with
          | mk statementSpan payload =>
              cases payload <;> try simp only [elaborateComputationReturnTree?, reduceCtorEq] at accepted
              case returnStmt returned =>
                cases rest with
                | nil =>
                    cases returned with
                    | none =>
                        simp only [elaborateComputationReturnTree?, Option.some.injEq, Prod.mk.injEq] at accepted
                        rcases accepted with ⟨rfl, rfl⟩
                        exact .bare
                    | some source => exact .expression (childCorrect.mp
                        (by simpa only [elaborateComputationReturnTree?] using accepted))
                | cons _ _ => simp only [elaborateComputationReturnTree?, reduceCtorEq] at accepted
              case block statements =>
                cases rest with
                | nil => exact .block (returnTree_sound childCorrect
                    (by simpa only [elaborateComputationReturnTree?] using accepted))
                | cons _ _ => simp only [elaborateComputationReturnTree?, reduceCtorEq] at accepted
              case letDecl name optionalType optionalInitializer =>
                cases optionalInitializer with
                | none => cases optionalType <;> simp only [elaborateComputationReturnTree?, reduceCtorEq] at accepted
                | some initializer =>
                    cases optionalType with
                    | none =>
                        rw [elaborateComputationReturnTree?] at accepted
                        simp only [bind, Option.bind_eq_some_iff, pure, Option.some.injEq, Prod.mk.injEq] at accepted
                        obtain ⟨⟨initializerCore, initializerType⟩, initializerAccepted,
                          ⟨tailCore, returnType⟩, tailAccepted, rfl, rfl⟩ := accepted
                        exact .inferred (childCorrect.mp initializerAccepted)
                          (returnTree_sound childCorrect tailAccepted)
                    | some annotation =>
                        obtain ⟨declaredType, initializerCore, tailCore, meaning,
                          initializerAccepted, tailAccepted, rfl⟩ := binding_children accepted
                        exact .binding (interpretStructuralType?_sound meaning)
                          (childCorrect.mp initializerAccepted)
                          (returnTree_sound childCorrect tailAccepted)
              case ifThen condition thenBody optionalElse =>
                cases rest with
                | cons _ _ => simp only [elaborateComputationReturnTree?, reduceCtorEq] at accepted
                | nil =>
                    cases optionalElse with
                    | none => simp only [elaborateComputationReturnTree?, reduceCtorEq] at accepted
                    | some elseBody =>
                        obtain ⟨conditionCore, thenCore, elseCore, conditionAccepted, protection,
                          thenAccepted, elseAccepted, rfl⟩ := conditional_children accepted
                        exact .conditional (childCorrect.mp conditionAccepted) protection
                          (returnTree_sound childCorrect thenAccepted)
                          (returnTree_sound childCorrect elseAccepted)
              case expression source trailingSemicolon =>
                cases trailingSemicolon with
                | false => simp only [elaborateComputationReturnTree?, reduceCtorEq] at accepted
                | true =>
                    rw [elaborateComputationReturnTree?] at accepted
                    simp only [bind, Option.bind_eq_some_iff, pure, Option.some.injEq, Prod.mk.injEq] at accepted
                    obtain ⟨⟨expressionCore, expressionType⟩, expressionAccepted,
                      ⟨tailCore, returnType⟩, tailAccepted, rfl, rfl⟩ := accepted
                    exact .discard (childCorrect.mp expressionAccepted)
                      (returnTree_sound childCorrect tailAccepted)
              case matchWith scrutinees arms =>
                rcases scrutineeShape : scrutinees with ⟨scrutineeSpan, elements⟩
                rcases elementsShape : elements with ⟨scrutinee, scrutineeRest⟩
                rcases armsShape : arms with ⟨armsSpan, armValues⟩
                rcases valuesShape : armValues with ⟨cases, optionalDefault⟩
                rw [scrutineeShape, elementsShape, armsShape, valuesShape] at accepted
                cases rest <;> cases scrutineeRest <;>
                  try (solve | simp only [elaborateComputationReturnTree?, reduceCtorEq] at accepted)
                obtain ⟨scrutineeCore, scrutineeType, scrutineeAccepted, bodyCore, entries, defaults, ordered, patterns,
                  compatible, branches, defaultOrdered, defaultBranches, lowered, rfl⟩ :=
                    ComputationReturnTreeChecking.match_iff.mp accepted
                refine .wordMatch (childCorrect.mp scrutineeAccepted) ordered patterns compatible ?_ defaultOrdered ?_ lowered
                · intro entry member
                  have originalMember : entry.1 ∈ cases := ordered ▸ List.mem_map.mpr ⟨entry, member, rfl⟩
                  exact returnTree_sound childCorrect (branches entry member)
                · intro entry member
                  have originalDefault : optionalDefault = some entry.1 := by
                    rw [← defaultOrdered, Option.mem_toList.mp member]; rfl
                  exact returnTree_sound childCorrect (defaultBranches entry member)
termination_by sizeOf body
decreasing_by
  all_goals simp_all
  all_goals try omega
  have member := List.sizeOf_lt_of_mem originalMember
  have child : sizeOf entry.1.value.body < sizeOf entry.1 := by
    rcases entry.1 with ⟨span, ⟨pattern, body⟩⟩; simp; omega
  omega

theorem elaborateComputationReturnTree?_iff
    (childCorrect : ∀ {table context source core type},
      checkChild table context source = some (core, type) ↔ ChildElab table context source core type)
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {inputs : LocalTypeInputs}
    {body : Syntax.Block} {core : Core.Expr} {type : Core.Ty} :
    elaborateComputationReturnTree? checkChild types owner inputs body = some (core, type) ↔
      ComputationReturnTreeElaborates ChildElab types owner inputs body core type :=
  ⟨returnTree_sound childCorrect, returnTree_complete childCorrect⟩

end Solcore.Frontend

/-!
## Consolidated module: `Solcore.Frontend.ComputationFunctionProperties`
-/

set_option autoImplicit false

namespace Solcore.Frontend

/-! Exact whole-record success is characterized by this profile's independent
header, parameter and mixed-body evidence. Actual preparation retains its own
input record; neither erasure nor old entry provenance supplies runtime values. -/

theorem compileComputationFunction?_iff
    {checkChild : LocalNameTable → Resolved.Context → Syntax.Expr → Option (Core.Expr × Core.Ty)}
    {ChildElab : LocalNameTable → Resolved.Context → Syntax.Expr → Core.Expr → Core.Ty → Prop}
    (childCorrect : ∀ {table context source core type},
      checkChild table context source = some (core, type) ↔ ChildElab table context source core type)
    {types : TypeNameTable} {owner : Resolved.DeclarationId}
    {declaration : Syntax.FunctionDecl} {compiled : CompiledRuntimeFunction} :
    compileComputationFunction? checkChild types owner declaration = some compiled ↔
      ComputationFunctionCompiles ChildElab types owner declaration compiled := by
  constructor
  · intro accepted
    simp only [compileComputationFunction?, bind, Option.bind_eq_some_iff, pure] at accepted
    obtain ⟨returnType, header, inputs, parameters, ⟨core, inferredType⟩, body, result⟩ := accepted
    split at result
    next same =>
      change inferredType = returnType at same
      subst inferredType
      cases result
      exact ⟨interpretRuntimeFunctionHeader?_iff.mp header, declareRuntimeParameters?_sound parameters,
        (elaborateComputationReturnTree?_iff (checkChild := checkChild) (ChildElab := ChildElab) childCorrect).mp body⟩
    next => cases result
  · intro compilation
    simp only [compileComputationFunction?, interpretRuntimeFunctionHeader?_iff.mpr compilation.header,
      compilation.parameters.complete, (elaborateComputationReturnTree?_iff (checkChild := checkChild) (ChildElab := ChildElab) childCorrect).mpr compilation.body,
      bind, Option.bind_some, ↓reduceIte, pure]

theorem prepareComputationFunction?_iff
    {checkChild : LocalNameTable → Resolved.Context → Syntax.Expr → Option (Core.Expr × Core.Ty)}
    {ChildElab : LocalNameTable → Resolved.Context → Syntax.Expr → Core.Expr → Core.Ty → Prop}
    (childCorrect : ∀ {table context source core type},
      checkChild table context source = some (core, type) ↔ ChildElab table context source core type)
    {types : TypeNameTable} {owner : Resolved.DeclarationId}
    {declaration : Syntax.FunctionDecl} {arguments : List TypedRuntimeArgument}
    {prepared : PreparedRuntimeFunction} :
    prepareComputationFunction? checkChild types owner declaration arguments = some prepared ↔
      ComputationFunctionPrepares ChildElab types owner declaration arguments prepared := by
  constructor
  · intro accepted
    simp only [prepareComputationFunction?, bind, Option.bind_eq_some_iff, pure] at accepted
    obtain ⟨returnType, header, inputs, parameters, ⟨core, inferredType⟩, body, result⟩ := accepted
    split at result
    next same =>
      change inferredType = returnType at same
      subst inferredType
      cases result
      exact ⟨interpretRuntimeFunctionHeader?_iff.mp header, bindRuntimeParameters?_sound parameters,
        (elaborateComputationReturnTree?_iff (checkChild := checkChild) (ChildElab := ChildElab) childCorrect).mp body⟩
    next => cases result
  · intro preparation
    simp only [prepareComputationFunction?, interpretRuntimeFunctionHeader?_iff.mpr preparation.header,
      preparation.parameters.complete, (elaborateComputationReturnTree?_iff (checkChild := checkChild) (ChildElab := ChildElab) childCorrect).mpr preparation.body,
      bind, Option.bind_some, ↓reduceIte, pure]

end Solcore.Frontend

/-!
## Consolidated module: `Solcore.Frontend.ComputationFunctionFactorizationProperties`
-/

/-! Operational factorization holds for every child checker. The private graph
supports these equations, not independent source semantics. Actual arguments
and every Core result for the separately supplied store are retained. -/

set_option autoImplicit false

namespace Solcore.Frontend

private def FactorizationCheckGraph
    (checkChild : LocalNameTable → Resolved.Context → Syntax.Expr → Option (Core.Expr × Core.Ty))
    (table : LocalNameTable) (context : Resolved.Context) (source : Syntax.Expr)
    (core : Core.Expr) (type : Core.Ty) : Prop := checkChild table context source = some (core, type)

variable {checkChild : LocalNameTable → Resolved.Context → Syntax.Expr → Option (Core.Expr × Core.Ty)}

private theorem checked_compile_iff {types : TypeNameTable} {owner : Resolved.DeclarationId}
    {declaration : Syntax.FunctionDecl} {compiled : CompiledRuntimeFunction} :
    compileComputationFunction? checkChild types owner declaration = some compiled ↔
      ComputationFunctionCompiles (FactorizationCheckGraph checkChild) types owner declaration compiled :=
  compileComputationFunction?_iff (checkChild := checkChild)
    (ChildElab := FactorizationCheckGraph checkChild) Iff.rfl

private theorem checked_prepare_iff {types : TypeNameTable} {owner : Resolved.DeclarationId}
    {declaration : Syntax.FunctionDecl} {arguments : List TypedRuntimeArgument}
    {prepared : PreparedRuntimeFunction} :
    prepareComputationFunction? checkChild types owner declaration arguments = some prepared ↔
      ComputationFunctionPrepares (FactorizationCheckGraph checkChild) types owner declaration arguments prepared :=
  prepareComputationFunction?_iff (checkChild := checkChild)
    (ChildElab := FactorizationCheckGraph checkChild) Iff.rfl

private theorem compiles_of_prepares
    {types : TypeNameTable} {owner : Resolved.DeclarationId}
    {declaration : Syntax.FunctionDecl} {arguments : List TypedRuntimeArgument}
    {prepared : PreparedRuntimeFunction}
    (preparation : ComputationFunctionPrepares (FactorizationCheckGraph checkChild)
      types owner declaration arguments prepared) :
    ComputationFunctionCompiles (FactorizationCheckGraph checkChild)
      types owner declaration prepared.toCompiled :=
  ⟨preparation.header, preparation.parameters.erase_values, preparation.body⟩

private theorem compilation_unique
    {types : TypeNameTable} {owner : Resolved.DeclarationId}
    {declaration : Syntax.FunctionDecl} {left right : CompiledRuntimeFunction}
    (first : ComputationFunctionCompiles (FactorizationCheckGraph checkChild)
      types owner declaration left)
    (second : ComputationFunctionCompiles (FactorizationCheckGraph checkChild)
      types owner declaration right) : left = right :=
  Option.some.inj ((checked_compile_iff.mpr first).symm.trans
    (checked_compile_iff.mpr second))

private theorem reconstruct
    {types : TypeNameTable} {owner : Resolved.DeclarationId}
    {declaration : Syntax.FunctionDecl} {compiled : CompiledRuntimeFunction}
    (compilation : ComputationFunctionCompiles (FactorizationCheckGraph checkChild)
      types owner declaration compiled)
    (arguments : List TypedRuntimeArgument)
    (matching : arguments.map (·.type) = compiled.inputs.context.values.reverse) :
    ∃ prepared, ComputationFunctionPrepares (FactorizationCheckGraph checkChild)
      types owner declaration arguments prepared ∧
      prepared.toCompiled = compiled := by
  obtain ⟨inputs, bound, erased⟩ := compilation.parameters.bind_typed_arguments arguments matching
  refine ⟨⟨inputs, compiled.core, compiled.returnType⟩,
    ⟨compilation.header, bound, ?_⟩, ?_⟩
  · simpa only [erased] using compilation.body
  · simp only [PreparedRuntimeFunction.toCompiled, erased]

private theorem matching_of_prepares
    {types : TypeNameTable} {owner : Resolved.DeclarationId}
    {declaration : Syntax.FunctionDecl} {arguments : List TypedRuntimeArgument}
    {prepared : PreparedRuntimeFunction}
    (preparation : ComputationFunctionPrepares (FactorizationCheckGraph checkChild)
      types owner declaration arguments prepared) :
    arguments.map (·.type) = prepared.toCompiled.inputs.context.values.reverse := by
  have layout := congrArg List.reverse preparation.parameters.argument_types.symm
  simpa only [PreparedRuntimeFunction.toCompiled, LocalInputs.toTypeInputs_context,
    Resolved.LocalScope.values, LocalInputs.context, List.map_map, Function.comp_def,
    List.map_reverse, List.reverse_reverse] using layout

private theorem reject_of_compile_none
    {types : TypeNameTable} {owner : Resolved.DeclarationId}
    {declaration : Syntax.FunctionDecl} (arguments : List TypedRuntimeArgument)
    (rejected : compileComputationFunction? checkChild types owner declaration = none) :
    prepareComputationFunction? checkChild types owner declaration arguments = none := by
  cases accepted : prepareComputationFunction? checkChild types owner declaration arguments with
  | none => rfl
  | some prepared =>
      have compilation := compiles_of_prepares (checked_prepare_iff.mp accepted)
      have compiled := checked_compile_iff.mpr compilation
      rw [rejected] at compiled
      cases compiled

private theorem reject_of_mismatch
    {types : TypeNameTable} {owner : Resolved.DeclarationId}
    {declaration : Syntax.FunctionDecl} {compiled : CompiledRuntimeFunction}
    (compilation : ComputationFunctionCompiles (FactorizationCheckGraph checkChild)
      types owner declaration compiled)
    (arguments : List TypedRuntimeArgument)
    (mismatch : arguments.map (·.type) ≠ compiled.inputs.context.values.reverse) :
    prepareComputationFunction? checkChild types owner declaration arguments = none := by
  cases accepted : prepareComputationFunction? checkChild types owner declaration arguments with
  | none => rfl
  | some prepared =>
      have preparation := checked_prepare_iff.mp accepted
      have erased := compilation_unique (compiles_of_prepares preparation) compilation
      have matching := matching_of_prepares preparation
      rw [erased] at matching
      exact False.elim (mismatch matching)

theorem prepareComputationFunction?_factorization
    (checkChild : LocalNameTable → Resolved.Context → Syntax.Expr → Option (Core.Expr × Core.Ty))
    (types : TypeNameTable) (owner : Resolved.DeclarationId)
    (declaration : Syntax.FunctionDecl) (arguments : List TypedRuntimeArgument) :
    (prepareComputationFunction? checkChild types owner declaration arguments).map PreparedRuntimeFunction.toCompiled =
      (do
        let compiled ← compileComputationFunction? checkChild types owner declaration
        if arguments.map (·.type) = compiled.inputs.context.values.reverse then
          some compiled
        else none) := by
  cases compiledResult : compileComputationFunction? checkChild types owner declaration with
  | none =>
      simp only [reject_of_compile_none arguments compiledResult, Option.map_none, bind, Option.bind_none]
  | some compiled =>
      have compilation := checked_compile_iff.mp compiledResult
      by_cases matching : arguments.map (·.type) = compiled.inputs.context.values.reverse
      · obtain ⟨prepared, preparation, erased⟩ := reconstruct compilation arguments matching
        simp only [checked_prepare_iff.mpr preparation, Option.map_some,
          erased, bind, Option.bind_some, matching, ↓reduceIte]
      · simp only [reject_of_mismatch compilation arguments matching, Option.map_none,
          bind, Option.bind_some, matching, ↓reduceIte]

/-- The type guard does not reject same-typed value swaps. Actual arguments,
not their erased projection, determine the full runtime result and checkpoint. -/
theorem runComputationFunction?_factorization
    (checkChild : LocalNameTable → Resolved.Context → Syntax.Expr → Option (Core.Expr × Core.Ty))
    (types : TypeNameTable) (owner : Resolved.DeclarationId)
    (declaration : Syntax.FunctionDecl) (arguments : List TypedRuntimeArgument)
    (fuel : Nat) (store : Core.Store) :
    runComputationFunction? checkChild types owner declaration arguments fuel store =
      (do
        let compiled ← compileComputationFunction? checkChild types owner declaration
        if arguments.map (·.type) = compiled.inputs.context.values.reverse then
          some (compiled.returnType, Core.runStateful fuel
            (Core.State.initial compiled.core (arguments.reverse.map (·.value)) store))
        else none) := by
  cases compiledResult : compileComputationFunction? checkChild types owner declaration with
  | none =>
      simp only [runComputationFunction?, reject_of_compile_none arguments compiledResult,
        bind, Option.bind_none]
  | some compiled =>
      have compilation := checked_compile_iff.mp compiledResult
      by_cases matching : arguments.map (·.type) = compiled.inputs.context.values.reverse
      · obtain ⟨prepared, preparation, erased⟩ := reconstruct compilation arguments matching
        have coreEq : prepared.core = compiled.core := congrArg CompiledRuntimeFunction.core erased
        have typeEq : prepared.returnType = compiled.returnType := congrArg CompiledRuntimeFunction.returnType erased
        have valuesEq : prepared.inputs.environment.values = arguments.reverse.map (·.value) := by
          simpa only [LocalInputs.environment, Resolved.LocalScope.values, List.map_map, Function.comp_def]
            using preparation.parameters.argument_values
        simp only [runComputationFunction?, checked_prepare_iff.mpr preparation,
          bind, Option.bind_some, pure, coreEq, typeEq, valuesEq, matching, ↓reduceIte]
      · simp only [runComputationFunction?, reject_of_mismatch compilation arguments matching,
          bind, Option.bind_none, Option.bind_some, matching, ↓reduceIte]

end Solcore.Frontend

/-!
## Consolidated module: `Solcore.Frontend.ComputationReturnTreeOwnerProperties`
-/

/-! Owner-only relabeling preserves independent shared-body evidence and the
whole optional checker result. Reflection remembers the original supplied
inputs; fresh tails use existing commutation, without an inverse owner map. -/

set_option autoImplicit false
namespace Solcore.Frontend

variable (mapping : Resolved.DeclarationId → Resolved.DeclarationId)
    (injective : Function.Injective mapping)
    {ChildElab : LocalNameTable → Resolved.Context → Syntax.Expr → Core.Expr → Core.Ty → Prop}

private theorem child_iff
    (covariance : ∀ {table context source core type},
      ChildElab (LocalNameTable.mapIds (ownerLocalIdMap mapping) table)
          (Resolved.LocalScope.mapIds (ownerLocalIdMap mapping) context) source core type ↔
        ChildElab table context source core type)
    {inputs : LocalTypeInputs} {source : Syntax.Expr} {core : Core.Expr} {type : Core.Ty} :
    ChildElab (inputs.mapIds (ownerLocalIdMap mapping) (ownerLocalIdMap_injective mapping injective)).names
        (inputs.mapIds (ownerLocalIdMap mapping) (ownerLocalIdMap_injective mapping injective)).context source core type ↔
      ChildElab inputs.names inputs.context source core type := by
  simpa only [LocalTypeInputs.mapIds_names, LocalTypeInputs.mapIds_context] using covariance

private theorem tail_preimage {original renamed : LocalTypeInputs}
    {owner : Resolved.DeclarationId} {name : String} {type : Core.Ty}
    (same : renamed = original.mapIds (ownerLocalIdMap mapping) (ownerLocalIdMap_injective mapping injective)) :
    renamed.bindFresh (mapping owner) name type =
      (original.bindFresh owner name type).mapIds (ownerLocalIdMap mapping)
        (ownerLocalIdMap_injective mapping injective) := by
  rw [same]
  exact (LocalTypeInputs.bindFresh_mapOwner original owner mapping injective name type).symm

private theorem elab_reflect
    (covariance : ∀ {table context source core type},
      ChildElab (LocalNameTable.mapIds (ownerLocalIdMap mapping) table)
          (Resolved.LocalScope.mapIds (ownerLocalIdMap mapping) context) source core type ↔
        ChildElab table context source core type)
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {renamed : LocalTypeInputs}
    {body : Syntax.Block} {core : Core.Expr} {type : Core.Ty}
    (elaboration : ComputationReturnTreeElaborates ChildElab types (mapping owner) renamed body core type) :
    ∀ original : LocalTypeInputs,
      renamed = original.mapIds (ownerLocalIdMap mapping) (ownerLocalIdMap_injective mapping injective) →
      ComputationReturnTreeElaborates ChildElab types owner original body core type := by
  induction elaboration with
  | bare => intro original same; exact .bare
  | expression child =>
      intro original same
      exact .expression ((child_iff mapping injective covariance).mp (same ▸ child))
  | block _ ih => intro original same; exact .block (ih original same)
  | binding meaning initializer _ ih =>
      intro original same
      exact .binding meaning ((child_iff mapping injective covariance).mp (same ▸ initializer))
        (ih _ (tail_preimage mapping injective same))
  | inferred initializer _ ih =>
      intro original same
      exact .inferred ((child_iff mapping injective covariance).mp (same ▸ initializer))
        (ih _ (tail_preimage mapping injective same))
  | discard child _ ih =>
      intro original same
      exact .discard ((child_iff mapping injective covariance).mp (same ▸ child)) (ih original same)
  | conditional condition protection _ _ thenIH elseIH =>
      intro original same
      refine .conditional ((child_iff mapping injective covariance).mp (same ▸ condition)) ?_
        (thenIH original same) (elseIH original same)
      rw [same] at protection
      simpa only [LocalTypeInputs.mapIds_names, LocalNameTable.mapIds, List.map_map,
        Function.comp_def] using protection
  | wordMatch scrutinee ordered patterns compatible _ defaultOrdered _ lowered branchIH defaultIH =>
      intro original same
      exact .wordMatch ((child_iff mapping injective covariance).mp (same ▸ scrutinee))
        ordered patterns compatible (fun entry member => branchIH entry member original same)
        defaultOrdered (fun entry member => defaultIH entry member original same) lowered

/-- All original branches and exact lowering survive in both directions under
the same child's independent covariance, including non-surjective owner maps. -/
theorem computationReturnTreeElaborates_mapOwner_iff
    (covariance : ∀ {table context source core type},
      ChildElab (LocalNameTable.mapIds (ownerLocalIdMap mapping) table)
          (Resolved.LocalScope.mapIds (ownerLocalIdMap mapping) context) source core type ↔
        ChildElab table context source core type)
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {inputs : LocalTypeInputs}
    {body : Syntax.Block} {core : Core.Expr} {type : Core.Ty} :
    ComputationReturnTreeElaborates ChildElab types (mapping owner)
        (inputs.mapIds (ownerLocalIdMap mapping) (ownerLocalIdMap_injective mapping injective)) body core type ↔
      ComputationReturnTreeElaborates ChildElab types owner inputs body core type := by
  constructor
  · intro elaboration
    exact elab_reflect mapping injective covariance elaboration inputs rfl
  · intro elaboration
    induction elaboration with
    | bare => exact .bare
    | expression child => exact .expression ((child_iff mapping injective covariance).mpr child)
    | block _ ih => exact .block ih
    | binding meaning initializer _ ih =>
        refine .binding meaning ((child_iff mapping injective covariance).mpr initializer) ?_
        simpa only [LocalTypeInputs.bindFresh_mapOwner _ owner mapping injective] using ih
    | inferred initializer _ ih =>
        refine .inferred ((child_iff mapping injective covariance).mpr initializer) ?_
        simpa only [LocalTypeInputs.bindFresh_mapOwner _ owner mapping injective] using ih
    | discard child _ ih => exact .discard ((child_iff mapping injective covariance).mpr child) ih
    | conditional condition protection _ _ thenIH elseIH =>
        refine .conditional ((child_iff mapping injective covariance).mpr condition) ?_ thenIH elseIH
        simpa only [LocalTypeInputs.mapIds_names, LocalNameTable.mapIds, List.map_map,
          Function.comp_def] using protection
    | wordMatch scrutinee ordered patterns compatible _ defaultOrdered _ lowered branchIH defaultIH =>
        exact .wordMatch ((child_iff mapping injective covariance).mpr scrutinee)
          ordered patterns compatible branchIH defaultOrdered defaultIH lowered

variable {ChildHasType : LocalNameTable → Resolved.Context → Syntax.Expr → Core.Ty → Prop}

private theorem type_child_iff
    (covariance : ∀ {table context source type},
      ChildHasType (LocalNameTable.mapIds (ownerLocalIdMap mapping) table)
          (Resolved.LocalScope.mapIds (ownerLocalIdMap mapping) context) source type ↔
        ChildHasType table context source type)
    {inputs : LocalTypeInputs} {source : Syntax.Expr} {type : Core.Ty} :
    ChildHasType (inputs.mapIds (ownerLocalIdMap mapping) (ownerLocalIdMap_injective mapping injective)).names
        (inputs.mapIds (ownerLocalIdMap mapping) (ownerLocalIdMap_injective mapping injective)).context source type ↔
      ChildHasType inputs.names inputs.context source type := by
  simpa only [LocalTypeInputs.mapIds_names, LocalTypeInputs.mapIds_context] using covariance

private theorem type_reflect
    (covariance : ∀ {table context source type},
      ChildHasType (LocalNameTable.mapIds (ownerLocalIdMap mapping) table)
          (Resolved.LocalScope.mapIds (ownerLocalIdMap mapping) context) source type ↔
        ChildHasType table context source type)
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {renamed : LocalTypeInputs}
    {body : Syntax.Block} {type : Core.Ty}
    (typing : ComputationReturnTreeHasType ChildHasType types (mapping owner) renamed body type) :
    ∀ original : LocalTypeInputs,
      renamed = original.mapIds (ownerLocalIdMap mapping) (ownerLocalIdMap_injective mapping injective) →
      ComputationReturnTreeHasType ChildHasType types owner original body type := by
  induction typing with
  | bare => intro original same; exact .bare
  | expression child =>
      intro original same
      exact .expression ((type_child_iff mapping injective covariance).mp (same ▸ child))
  | block _ ih => intro original same; exact .block (ih original same)
  | binding meaning initializer _ ih =>
      intro original same
      exact .binding meaning ((type_child_iff mapping injective covariance).mp (same ▸ initializer))
        (ih _ (tail_preimage mapping injective same))
  | inferred initializer _ ih =>
      intro original same
      exact .inferred ((type_child_iff mapping injective covariance).mp (same ▸ initializer))
        (ih _ (tail_preimage mapping injective same))
  | discard child _ ih =>
      intro original same
      exact .discard ((type_child_iff mapping injective covariance).mp (same ▸ child)) (ih original same)
  | conditional condition protection _ _ thenIH elseIH =>
      intro original same
      refine .conditional ((type_child_iff mapping injective covariance).mp (same ▸ condition)) ?_
        (thenIH original same) (elseIH original same)
      rw [same] at protection
      simpa only [LocalTypeInputs.mapIds_names, LocalNameTable.mapIds, List.map_map,
        Function.comp_def] using protection
  | wordMatch scrutinee patterns compatible covered _ _ branchIH defaultIH =>
      intro original same
      exact .wordMatch ((type_child_iff mapping injective covariance).mp (same ▸ scrutinee))
        patterns compatible covered (fun arm member => branchIH arm member original same)
        (fun source member => defaultIH source member original same)

/-- Independent typing transport needs only child typing covariance, not child
elaboration existence, checking or inhabitants for the original input types. -/
theorem computationReturnTreeHasType_mapOwner_iff
    (covariance : ∀ {table context source type},
      ChildHasType (LocalNameTable.mapIds (ownerLocalIdMap mapping) table)
          (Resolved.LocalScope.mapIds (ownerLocalIdMap mapping) context) source type ↔
        ChildHasType table context source type)
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {inputs : LocalTypeInputs}
    {body : Syntax.Block} {type : Core.Ty} :
    ComputationReturnTreeHasType ChildHasType types (mapping owner)
        (inputs.mapIds (ownerLocalIdMap mapping) (ownerLocalIdMap_injective mapping injective)) body type ↔
      ComputationReturnTreeHasType ChildHasType types owner inputs body type := by
  constructor
  · intro typing
    exact type_reflect mapping injective covariance typing inputs rfl
  · intro typing
    induction typing with
    | bare => exact .bare
    | expression child => exact .expression ((type_child_iff mapping injective covariance).mpr child)
    | block _ ih => exact .block ih
    | binding meaning initializer _ ih =>
        refine .binding meaning ((type_child_iff mapping injective covariance).mpr initializer) ?_
        simpa only [LocalTypeInputs.bindFresh_mapOwner _ owner mapping injective] using ih
    | inferred initializer _ ih =>
        refine .inferred ((type_child_iff mapping injective covariance).mpr initializer) ?_
        simpa only [LocalTypeInputs.bindFresh_mapOwner _ owner mapping injective] using ih
    | discard child _ ih => exact .discard ((type_child_iff mapping injective covariance).mpr child) ih
    | conditional condition protection _ _ thenIH elseIH =>
        refine .conditional ((type_child_iff mapping injective covariance).mpr condition) ?_ thenIH elseIH
        simpa only [LocalTypeInputs.mapIds_names, LocalNameTable.mapIds, List.map_map,
          Function.comp_def] using protection
    | wordMatch scrutinee patterns compatible covered _ _ branchIH defaultIH =>
        exact .wordMatch ((type_child_iff mapping injective covariance).mpr scrutinee)
          patterns compatible covered branchIH defaultIH

/-- The same fixed child operation supplies complete covariance. Its local
success graph is used only to transport the entire optional checker result. -/
theorem elaborateComputationReturnTree?_mapOwner
    (checkChild : LocalNameTable → Resolved.Context → Syntax.Expr → Option (Core.Expr × Core.Ty))
    (covariance : ∀ table context source,
      checkChild (LocalNameTable.mapIds (ownerLocalIdMap mapping) table)
          (Resolved.LocalScope.mapIds (ownerLocalIdMap mapping) context) source =
        checkChild table context source)
    (types : TypeNameTable) (owner : Resolved.DeclarationId) (inputs : LocalTypeInputs) (body : Syntax.Block) :
    elaborateComputationReturnTree? checkChild types (mapping owner)
        (inputs.mapIds (ownerLocalIdMap mapping) (ownerLocalIdMap_injective mapping injective)) body =
      elaborateComputationReturnTree? checkChild types owner inputs body := by
  let Graph := fun table context source core type => checkChild table context source = some (core, type)
  have graphCovariance : ∀ {table context source core type},
      Graph (LocalNameTable.mapIds (ownerLocalIdMap mapping) table)
          (Resolved.LocalScope.mapIds (ownerLocalIdMap mapping) context) source core type ↔
        Graph table context source core type := by
    intro table context source core type
    dsimp only [Graph]
    rw [covariance]
  have accepted_iff {core type} :
      elaborateComputationReturnTree? checkChild types (mapping owner)
          (inputs.mapIds (ownerLocalIdMap mapping) (ownerLocalIdMap_injective mapping injective)) body = some (core, type) ↔
        elaborateComputationReturnTree? checkChild types owner inputs body = some (core, type) :=
    (elaborateComputationReturnTree?_iff (ChildElab := Graph) Iff.rfl).trans
      ((computationReturnTreeElaborates_mapOwner_iff mapping injective graphCovariance).trans
        (elaborateComputationReturnTree?_iff (ChildElab := Graph) Iff.rfl).symm)
  cases original : elaborateComputationReturnTree? checkChild types owner inputs body with
  | none =>
      cases renamed : elaborateComputationReturnTree? checkChild types (mapping owner)
          (inputs.mapIds (ownerLocalIdMap mapping) (ownerLocalIdMap_injective mapping injective)) body with
      | none => rfl
      | some result =>
          obtain ⟨core, type⟩ := result
          have impossible := accepted_iff.mp renamed
          rw [original] at impossible
          cases impossible
  | some result =>
      obtain ⟨core, type⟩ := result
      exact accepted_iff.mpr original

end Solcore.Frontend

/-!
## Consolidated module: `Solcore.Frontend.ComputationFunctionOwnerProperties`
-/

/-! One injective owner map preserves independent shared function evidence,
exact optional compiled/prepared records, and every full Core run result.
Parameter reflection retains original inputs; only IDs change, never values. -/

set_option autoImplicit false
namespace Solcore.Frontend
variable (mapping : Resolved.DeclarationId → Resolved.DeclarationId)
    (injective : Function.Injective mapping)
include injective

private theorem inputs_bindFresh (inputs : LocalInputs) (owner : Resolved.DeclarationId)
    (name : String) (type : Core.Ty) (value : Core.Value) (typed : Core.ValueHasType value type) :
    (inputs.bindFresh owner name type value typed).mapIds (ownerLocalIdMap mapping)
        (ownerLocalIdMap_injective mapping injective) =
      (inputs.mapIds (ownerLocalIdMap mapping) (ownerLocalIdMap_injective mapping injective)).bindFresh
        (mapping owner) name type value typed := by
  have sameFresh : Resolved.freshLocalId (mapping owner)
      (inputs.mapIds (ownerLocalIdMap mapping) (ownerLocalIdMap_injective mapping injective)).ids =
      ownerLocalIdMap mapping (Resolved.freshLocalId owner inputs.ids) := by
    rw [LocalInputs.mapIds_ids]
    exact Resolved.freshLocalId_map_owner mapping injective owner inputs.ids
  cases inputs
  simp only [LocalInputs.mapIds, LocalInputs.bindFresh, List.map_cons,
    TypedLocalBinding.mapIds, LocalInputs.mk.injEq]
  congr 2
  exact sameFresh.symm

private theorem declare_reflect {types : TypeNameTable} {owner : Resolved.DeclarationId}
    {renamed output : LocalTypeInputs} {params : List Syntax.FunctionParameter}
    (declared : RuntimeParametersDeclareFrom types (mapping owner) renamed params output) :
    ∀ original : LocalTypeInputs,
      renamed = original.mapIds (ownerLocalIdMap mapping) (ownerLocalIdMap_injective mapping injective) →
      ∃ previous, RuntimeParametersDeclareFrom types owner original params previous ∧
        output = previous.mapIds (ownerLocalIdMap mapping) (ownerLocalIdMap_injective mapping injective) := by
  induction declared with
  | nil => intro original same; exact ⟨original, .nil, same⟩
  | cons meaning unused _ ih =>
      intro original same
      have unusedOriginal := unused
      rw [same] at unusedOriginal
      simp only [LocalTypeInputs.mapIds_names, LocalNameTable.mapIds, List.map_map,
        Function.comp_def] at unusedOriginal
      obtain ⟨previous, tail, mapped⟩ := ih (original.bindFresh owner _ _) (by
        rw [same]; exact (LocalTypeInputs.bindFresh_mapOwner original owner mapping injective _ _).symm)
      exact ⟨previous, .cons meaning unusedOriginal tail, mapped⟩

private theorem bind_reflect {types : TypeNameTable} {owner : Resolved.DeclarationId}
    {renamed output : LocalInputs} {params : List Syntax.FunctionParameter}
    {arguments : List TypedRuntimeArgument}
    (bound : RuntimeParametersBindFrom types (mapping owner) renamed params arguments output) :
    ∀ original : LocalInputs,
      renamed = original.mapIds (ownerLocalIdMap mapping) (ownerLocalIdMap_injective mapping injective) →
      ∃ previous, RuntimeParametersBindFrom types owner original params arguments previous ∧
        output = previous.mapIds (ownerLocalIdMap mapping) (ownerLocalIdMap_injective mapping injective) := by
  induction bound with
  | nil => intro original same; exact ⟨original, .nil, same⟩
  | cons meaning unused _ ih =>
      intro original same
      have unusedOriginal := unused
      rw [same] at unusedOriginal
      simp only [LocalInputs.mapIds_names, LocalNameTable.mapIds, List.map_map,
        Function.comp_def] at unusedOriginal
      obtain ⟨previous, tail, mapped⟩ := ih (original.bindFresh owner _ _ _ _) (by
        rw [same]; exact (inputs_bindFresh mapping injective original owner _ _ _ _).symm)
      exact ⟨previous, .cons meaning unusedOriginal tail, mapped⟩

private theorem declareRuntimeParameters?_mapOwner (types : TypeNameTable) (owner : Resolved.DeclarationId)
    (params : List Syntax.FunctionParameter) :
    declareRuntimeParameters? types (mapping owner) params =
      (declareRuntimeParameters? types owner params).map
        (fun inputs => inputs.mapIds (ownerLocalIdMap mapping) (ownerLocalIdMap_injective mapping injective)) := by
  cases old : declareRuntimeParameters? types owner params with
  | some inputs =>
      simpa only [old, Option.map_some] using
        ((declareRuntimeParameters?_sound old).map_owner mapping injective).complete
  | none =>
      cases next : declareRuntimeParameters? types (mapping owner) params with
      | none => rfl
      | some output =>
          obtain ⟨previous, declared, _⟩ := declare_reflect mapping injective (declareRuntimeParameters?_sound next) .empty rfl
          have contradiction := RuntimeParametersDeclare.complete declared
          rw [old] at contradiction
          cases contradiction

private theorem bindRuntimeParameters?_mapOwner (types : TypeNameTable) (owner : Resolved.DeclarationId)
    (params : List Syntax.FunctionParameter) (arguments : List TypedRuntimeArgument) :
    bindRuntimeParameters? types (mapping owner) params arguments =
      (bindRuntimeParameters? types owner params arguments).map
        (fun inputs => inputs.mapIds (ownerLocalIdMap mapping) (ownerLocalIdMap_injective mapping injective)) := by
  cases old : bindRuntimeParameters? types owner params arguments with
  | some inputs =>
      simpa only [old, Option.map_some] using
        (bindRuntimeParameters?_iff.mpr ((bindRuntimeParameters?_iff.mp old).map_owner mapping injective))
  | none =>
      cases next : bindRuntimeParameters? types (mapping owner) params arguments with
      | none => rfl
      | some output =>
          obtain ⟨previous, bound, _⟩ := bind_reflect mapping injective (bindRuntimeParameters?_iff.mp next) .empty rfl
          have contradiction := bindRuntimeParameters?_iff.mpr bound
          rw [old] at contradiction
          cases contradiction

private theorem typeMap_injective : Function.Injective (fun inputs : LocalTypeInputs =>
    inputs.mapIds (ownerLocalIdMap mapping) (ownerLocalIdMap_injective mapping injective)) := by
  have rowsInjective : Function.Injective (LocalTypeBinding.mapIds (ownerLocalIdMap mapping)) := by
    rintro ⟨a,i,t⟩ ⟨b,j,u⟩ same
    simpa only [LocalTypeBinding.mapIds, LocalTypeBinding.mk.injEq,
      (ownerLocalIdMap_injective mapping injective).eq_iff] using same
  intro left right same
  have rows := (List.map_inj_right rowsInjective).mp (congrArg LocalTypeInputs.bindings same)
  cases left; cases right; cases rows; rfl

private theorem inputsMap_injective : Function.Injective (fun inputs : LocalInputs =>
    inputs.mapIds (ownerLocalIdMap mapping) (ownerLocalIdMap_injective mapping injective)) := by
  have rowsInjective : Function.Injective (TypedLocalBinding.mapIds (ownerLocalIdMap mapping)) := by
    rintro ⟨a,i,t,v,h⟩ ⟨b,j,u,w,g⟩ same
    simpa only [TypedLocalBinding.mapIds, TypedLocalBinding.mk.injEq,
      (ownerLocalIdMap_injective mapping injective).eq_iff] using same
  intro left right same
  have rows := (List.map_inj_right rowsInjective).mp (congrArg LocalInputs.bindings same)
  cases left; cases right; cases rows; rfl

private theorem runtimeParametersDeclare_mapOwner_iff {types : TypeNameTable} {owner : Resolved.DeclarationId}
    {params : List Syntax.FunctionParameter} {inputs : LocalTypeInputs} :
    RuntimeParametersDeclare types (mapping owner) params
        (inputs.mapIds (ownerLocalIdMap mapping) (ownerLocalIdMap_injective mapping injective)) ↔
      RuntimeParametersDeclare types owner params inputs := by
  constructor
  · intro declared
    obtain ⟨previous, original, same⟩ := declare_reflect mapping injective declared .empty rfl
    have inputsSame := typeMap_injective mapping injective same
    exact inputsSame ▸ original
  · intro declared
    exact declared.map_owner mapping injective

private theorem runtimeParametersBind_mapOwner_iff {types : TypeNameTable} {owner : Resolved.DeclarationId}
    {params : List Syntax.FunctionParameter} {arguments : List TypedRuntimeArgument} {inputs : LocalInputs} :
    RuntimeParametersBind types (mapping owner) params arguments
        (inputs.mapIds (ownerLocalIdMap mapping) (ownerLocalIdMap_injective mapping injective)) ↔
      RuntimeParametersBind types owner params arguments inputs := by
  constructor
  · intro bound
    obtain ⟨previous, original, same⟩ := bind_reflect mapping injective bound .empty rfl
    have inputsSame := inputsMap_injective mapping injective same
    exact inputsSame ▸ original
  · intro bound
    exact bound.map_owner mapping injective

variable {ChildElab : LocalNameTable → Resolved.Context → Syntax.Expr → Core.Expr → Core.Ty → Prop}

/-- Independent value-free compilation preserves the exact mapped record
under the same child's elaboration covariance, without a checker premise. -/
theorem computationFunctionCompiles_mapOwner_iff
    (covariance : ∀ {table context source core type},
      ChildElab (LocalNameTable.mapIds (ownerLocalIdMap mapping) table)
          (Resolved.LocalScope.mapIds (ownerLocalIdMap mapping) context) source core type ↔
        ChildElab table context source core type)
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {declaration : Syntax.FunctionDecl}
    {compiled : CompiledRuntimeFunction} :
    ComputationFunctionCompiles ChildElab types (mapping owner) declaration
        {compiled with inputs := compiled.inputs.mapIds (ownerLocalIdMap mapping) (ownerLocalIdMap_injective mapping injective)} ↔
      ComputationFunctionCompiles ChildElab types owner declaration compiled := by
  constructor
  · intro evidence
    exact ⟨evidence.header, (runtimeParametersDeclare_mapOwner_iff mapping injective).mp evidence.parameters,
      (computationReturnTreeElaborates_mapOwner_iff mapping injective covariance).mp evidence.body⟩
  · intro evidence
    exact ⟨evidence.header, (runtimeParametersDeclare_mapOwner_iff mapping injective).mpr evidence.parameters,
      (computationReturnTreeElaborates_mapOwner_iff mapping injective covariance).mpr evidence.body⟩

/-- Independent preparation keeps the original actual arguments and every
record field except the explicitly relabeled local input identities. -/
theorem computationFunctionPrepares_mapOwner_iff
    (covariance : ∀ {table context source core type},
      ChildElab (LocalNameTable.mapIds (ownerLocalIdMap mapping) table)
          (Resolved.LocalScope.mapIds (ownerLocalIdMap mapping) context) source core type ↔
        ChildElab table context source core type)
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {declaration : Syntax.FunctionDecl}
    {arguments : List TypedRuntimeArgument} {prepared : PreparedRuntimeFunction} :
    ComputationFunctionPrepares ChildElab types (mapping owner) declaration arguments
        {prepared with inputs := prepared.inputs.mapIds (ownerLocalIdMap mapping) (ownerLocalIdMap_injective mapping injective)} ↔
      ComputationFunctionPrepares ChildElab types owner declaration arguments prepared := by
  constructor
  · intro evidence
    refine ⟨evidence.header, (runtimeParametersBind_mapOwner_iff mapping injective).mp evidence.parameters, ?_⟩
    exact (computationReturnTreeElaborates_mapOwner_iff mapping injective covariance).mp
      (by simpa only [LocalInputs.toTypeInputs_mapIds] using evidence.body)
  · intro evidence
    refine ⟨evidence.header, (runtimeParametersBind_mapOwner_iff mapping injective).mpr evidence.parameters, ?_⟩
    simpa only [LocalInputs.toTypeInputs_mapIds] using
      (computationReturnTreeElaborates_mapOwner_iff mapping injective covariance).mpr evidence.body

variable (checkChild : LocalNameTable → Resolved.Context → Syntax.Expr → Option (Core.Expr × Core.Ty))
    (covariance : ∀ table context source,
      checkChild (LocalNameTable.mapIds (ownerLocalIdMap mapping) table)
          (Resolved.LocalScope.mapIds (ownerLocalIdMap mapping) context) source =
        checkChild table context source)
include covariance

/-- Complete optional compilation is mapped, including absence; the same
arbitrary child checker supplies covariance only for this owner map. -/
theorem compileComputationFunction?_mapOwner (types : TypeNameTable) (owner : Resolved.DeclarationId)
    (declaration : Syntax.FunctionDecl) :
    compileComputationFunction? checkChild types (mapping owner) declaration =
      (compileComputationFunction? checkChild types owner declaration).map
        (fun compiled => {compiled with inputs := (compiled.inputs.mapIds (ownerLocalIdMap mapping)
          (ownerLocalIdMap_injective mapping injective))}) := by
  unfold compileComputationFunction?
  rw [declareRuntimeParameters?_mapOwner mapping injective]
  cases interpretRuntimeFunctionHeader? types declaration.value.signature <;>
    cases declareRuntimeParameters? types owner declaration.value.signature.parameters.elements <;>
    simp only [bind, Option.bind_none, Option.bind_some, Option.map_none, Option.map_some]
  rw [elaborateComputationReturnTree?_mapOwner mapping injective checkChild covariance]
  cases elaborateComputationReturnTree? checkChild types owner _ declaration.value.body with
  | none => rfl
  | some result => rcases result with ⟨core,type⟩; dsimp; split <;> rfl

/-- Complete optional preparation preserves actual bound rows and captures.
No structural argument value or parameter inhabitant is reconstructed. -/
theorem prepareComputationFunction?_mapOwner (types : TypeNameTable) (owner : Resolved.DeclarationId)
    (declaration : Syntax.FunctionDecl) (arguments : List TypedRuntimeArgument) :
    prepareComputationFunction? checkChild types (mapping owner) declaration arguments =
      (prepareComputationFunction? checkChild types owner declaration arguments).map
        (fun prepared => {prepared with inputs := (prepared.inputs.mapIds (ownerLocalIdMap mapping)
          (ownerLocalIdMap_injective mapping injective))}) := by
  unfold prepareComputationFunction?
  rw [bindRuntimeParameters?_mapOwner mapping injective]
  cases interpretRuntimeFunctionHeader? types declaration.value.signature <;>
    cases bindRuntimeParameters? types owner declaration.value.signature.parameters.elements arguments <;>
    simp only [bind, Option.bind_none, Option.bind_some, Option.map_none, Option.map_some]
  rw [LocalInputs.toTypeInputs_mapIds, elaborateComputationReturnTree?_mapOwner mapping injective checkChild covariance]
  cases elaborateComputationReturnTree? checkChild types owner _ declaration.value.body with
  | none => rfl
  | some result => rcases result with ⟨core,type⟩; dsimp; split <;> rfl

/-- Equal Core and actual value sequences retain the full result at the same
fuel and store, including faults and checkpoints; this is not a safety claim. -/
theorem runComputationFunction?_mapOwner (types : TypeNameTable) (owner : Resolved.DeclarationId)
    (declaration : Syntax.FunctionDecl) (arguments : List TypedRuntimeArgument) (fuel : Nat) (store : Core.Store) :
    runComputationFunction? checkChild types (mapping owner) declaration arguments fuel store =
      runComputationFunction? checkChild types owner declaration arguments fuel store := by
  unfold runComputationFunction?
  rw [prepareComputationFunction?_mapOwner mapping injective checkChild covariance]
  cases prepareComputationFunction? checkChild types owner declaration arguments <;>
    simp only [Option.map_none, Option.map_some, bind, Option.bind_none, Option.bind_some,
      LocalInputs.mapIds_environment, Resolved.LocalScope.values_mapIds]

end Solcore.Frontend

/-!
## Consolidated module: `Solcore.Frontend.ComputationReturnTreeRawOwnerProperties`
-/

/-! Owner-only relabeling preserves shared raw evidence and exact costs.
The two child relations have independent covariance premises. Reflection keeps
both original raw tables; neither alignment nor runtime typing is required. -/

set_option autoImplicit false
namespace Solcore.Frontend

variable (mapping : Resolved.DeclarationId → Resolved.DeclarationId)
    (injective : Function.Injective mapping)
include injective

private theorem fresh_mapOwner (owner : Resolved.DeclarationId) (table : LocalNameTable) :
    Resolved.freshLocalId (mapping owner)
        ((LocalNameTable.mapIds (ownerLocalIdMap mapping) table).map Prod.snd) =
      ownerLocalIdMap mapping (Resolved.freshLocalId owner (table.map Prod.snd)) := by
  simpa only [LocalNameTable.mapIds, List.map_map, Function.comp_def, ownerLocalIdMap,
    Resolved.freshLocalId_owner] using
    Resolved.freshLocalId_map_owner mapping injective owner (table.map Prod.snd)

variable {ChildEval : LocalNameTable → Resolved.Environment → Core.Store → Syntax.Expr → Core.Value → Core.Store → Prop}

private theorem eval_reflect
    (covariance : ∀ {table environment initialStore source value finalStore},
      ChildEval (LocalNameTable.mapIds (ownerLocalIdMap mapping) table)
          (Resolved.LocalScope.mapIds (ownerLocalIdMap mapping) environment) initialStore source value finalStore ↔
        ChildEval table environment initialStore source value finalStore)
    {owner : Resolved.DeclarationId} {renamedTable : LocalNameTable}
    {renamedEnvironment : Resolved.Environment} {initialStore finalStore : Core.Store}
    {body : Syntax.Block} {value : Core.Value}
    (evaluation : ComputationReturnTreeEvaluates ChildEval (mapping owner)
      renamedTable renamedEnvironment initialStore body value finalStore) :
    ∀ (table : LocalNameTable) (environment : Resolved.Environment),
      renamedTable = LocalNameTable.mapIds (ownerLocalIdMap mapping) table →
      renamedEnvironment = Resolved.LocalScope.mapIds (ownerLocalIdMap mapping) environment →
      ComputationReturnTreeEvaluates ChildEval owner table environment initialStore body value finalStore := by
  induction evaluation with
  | bare => intro table environment tableSame environmentSame; exact .bare
  | expression child =>
      intro table environment tableSame environmentSame
      exact .expression (covariance.mp (tableSame ▸ environmentSame ▸ child))
  | block _ ih =>
      intro table environment tableSame environmentSame
      exact .block (ih table environment tableSame environmentSame)
  | binding initializer _ ih =>
      intro table environment tableSame environmentSame
      refine .binding (covariance.mp (tableSame ▸ environmentSame ▸ initializer)) (ih _ _ ?_ ?_)
      · rw [tableSame, fresh_mapOwner mapping injective]; rfl
      · rw [tableSame, environmentSame, fresh_mapOwner mapping injective]; rfl
  | inferred initializer _ ih =>
      intro table environment tableSame environmentSame
      refine .inferred (covariance.mp (tableSame ▸ environmentSame ▸ initializer)) (ih _ _ ?_ ?_)
      · rw [tableSame, fresh_mapOwner mapping injective]; rfl
      · rw [tableSame, environmentSame, fresh_mapOwner mapping injective]; rfl
  | discard child _ ih =>
      intro table environment tableSame environmentSame
      exact .discard (covariance.mp (tableSame ▸ environmentSame ▸ child)) (ih table environment tableSame environmentSame)
  | ifTrue child _ ih =>
      intro table environment tableSame environmentSame
      exact .ifTrue (covariance.mp (tableSame ▸ environmentSame ▸ child)) (ih table environment tableSame environmentSame)
  | ifFalse child _ ih =>
      intro table environment tableSame environmentSame
      exact .ifFalse (covariance.mp (tableSame ▸ environmentSame ▸ child)) (ih table environment tableSame environmentSame)
  | wordMatch child choice _ ih =>
      intro table environment tableSame environmentSame
      exact .wordMatch (covariance.mp (tableSame ▸ environmentSame ▸ child)) choice
        (ih table environment tableSame environmentSame)

/-- The same child's raw covariance preserves and reflects the original body
on arbitrary ordered rows, including duplicates and environment-only IDs. -/
theorem computationReturnTreeEvaluates_mapOwner_iff
    (covariance : ∀ {table environment initialStore source value finalStore},
      ChildEval (LocalNameTable.mapIds (ownerLocalIdMap mapping) table)
          (Resolved.LocalScope.mapIds (ownerLocalIdMap mapping) environment) initialStore source value finalStore ↔
        ChildEval table environment initialStore source value finalStore)
    {owner : Resolved.DeclarationId} {table : LocalNameTable} {environment : Resolved.Environment}
    {initialStore finalStore : Core.Store} {body : Syntax.Block} {value : Core.Value} :
    ComputationReturnTreeEvaluates ChildEval (mapping owner)
        (LocalNameTable.mapIds (ownerLocalIdMap mapping) table)
        (Resolved.LocalScope.mapIds (ownerLocalIdMap mapping) environment) initialStore body value finalStore ↔
      ComputationReturnTreeEvaluates ChildEval owner table environment initialStore body value finalStore := by
  constructor
  · intro evaluation
    exact eval_reflect mapping injective covariance evaluation table environment rfl rfl
  · intro evaluation
    induction evaluation with
    | bare => exact .bare
    | expression child => exact .expression (covariance.mpr child)
    | block _ ih => exact .block ih
    | binding initializer _ ih =>
        refine .binding (covariance.mpr initializer) ?_
        rw [fresh_mapOwner mapping injective]
        exact ih
    | inferred initializer _ ih =>
        refine .inferred (covariance.mpr initializer) ?_
        rw [fresh_mapOwner mapping injective]
        exact ih
    | discard child _ ih => exact .discard (covariance.mpr child) ih
    | ifTrue child _ ih => exact .ifTrue (covariance.mpr child) ih
    | ifFalse child _ ih => exact .ifFalse (covariance.mpr child) ih
    | wordMatch child choice _ ih => exact .wordMatch (covariance.mpr child) choice ih

variable {ChildCost : LocalNameTable → Resolved.Environment → Core.Store → Syntax.Expr → Core.Value → Core.Store → Nat → Prop}

private theorem cost_reflect
    (covariance : ∀ {table environment initialStore source value finalStore cost},
      ChildCost (LocalNameTable.mapIds (ownerLocalIdMap mapping) table)
          (Resolved.LocalScope.mapIds (ownerLocalIdMap mapping) environment) initialStore source value finalStore cost ↔
        ChildCost table environment initialStore source value finalStore cost)
    {owner : Resolved.DeclarationId} {renamedTable : LocalNameTable}
    {renamedEnvironment : Resolved.Environment} {initialStore finalStore : Core.Store}
    {body : Syntax.Block} {value : Core.Value} {cost : Nat}
    (evaluation : ComputationReturnTreeEvaluatesWithCost ChildCost (mapping owner)
      renamedTable renamedEnvironment initialStore body value finalStore cost) :
    ∀ (table : LocalNameTable) (environment : Resolved.Environment),
      renamedTable = LocalNameTable.mapIds (ownerLocalIdMap mapping) table →
      renamedEnvironment = Resolved.LocalScope.mapIds (ownerLocalIdMap mapping) environment →
      ComputationReturnTreeEvaluatesWithCost ChildCost owner table environment initialStore body value finalStore cost := by
  induction evaluation with
  | bare => intro table environment tableSame environmentSame; exact .bare
  | expression child =>
      intro table environment tableSame environmentSame
      exact .expression (covariance.mp (tableSame ▸ environmentSame ▸ child))
  | block _ ih =>
      intro table environment tableSame environmentSame
      exact .block (ih table environment tableSame environmentSame)
  | binding initializer _ ih =>
      intro table environment tableSame environmentSame
      refine .binding (covariance.mp (tableSame ▸ environmentSame ▸ initializer)) (ih _ _ ?_ ?_)
      · rw [tableSame, fresh_mapOwner mapping injective]; rfl
      · rw [tableSame, environmentSame, fresh_mapOwner mapping injective]; rfl
  | inferred initializer _ ih =>
      intro table environment tableSame environmentSame
      refine .inferred (covariance.mp (tableSame ▸ environmentSame ▸ initializer)) (ih _ _ ?_ ?_)
      · rw [tableSame, fresh_mapOwner mapping injective]; rfl
      · rw [tableSame, environmentSame, fresh_mapOwner mapping injective]; rfl
  | discard child _ ih =>
      intro table environment tableSame environmentSame
      exact .discard (covariance.mp (tableSame ▸ environmentSame ▸ child)) (ih table environment tableSame environmentSame)
  | ifTrue child _ ih =>
      intro table environment tableSame environmentSame
      exact .ifTrue (covariance.mp (tableSame ▸ environmentSame ▸ child)) (ih table environment tableSame environmentSame)
  | ifFalse child _ ih =>
      intro table environment tableSame environmentSame
      exact .ifFalse (covariance.mp (tableSame ▸ environmentSame ▸ child)) (ih table environment tableSame environmentSame)
  | wordMatch child choice _ ih =>
      intro table environment tableSame environmentSame
      exact .wordMatch (covariance.mp (tableSame ▸ environmentSame ▸ child)) choice
        (ih table environment tableSame environmentSame)

/-- The same child's exact-cost covariance preserves all stores, selected
branches and costs independently of any uncosted/cost-existence bridge. -/
theorem computationReturnTreeEvaluatesWithCost_mapOwner_iff
    (covariance : ∀ {table environment initialStore source value finalStore cost},
      ChildCost (LocalNameTable.mapIds (ownerLocalIdMap mapping) table)
          (Resolved.LocalScope.mapIds (ownerLocalIdMap mapping) environment) initialStore source value finalStore cost ↔
        ChildCost table environment initialStore source value finalStore cost)
    {owner : Resolved.DeclarationId} {table : LocalNameTable} {environment : Resolved.Environment}
    {initialStore finalStore : Core.Store} {body : Syntax.Block} {value : Core.Value} {cost : Nat} :
    ComputationReturnTreeEvaluatesWithCost ChildCost (mapping owner)
        (LocalNameTable.mapIds (ownerLocalIdMap mapping) table)
        (Resolved.LocalScope.mapIds (ownerLocalIdMap mapping) environment) initialStore body value finalStore cost ↔
      ComputationReturnTreeEvaluatesWithCost ChildCost owner table environment initialStore body value finalStore cost := by
  constructor
  · intro evaluation
    exact cost_reflect mapping injective covariance evaluation table environment rfl rfl
  · intro evaluation
    induction evaluation with
    | bare => exact .bare
    | expression child => exact .expression (covariance.mpr child)
    | block _ ih => exact .block ih
    | binding initializer _ ih =>
        refine .binding (covariance.mpr initializer) ?_
        rw [fresh_mapOwner mapping injective]
        exact ih
    | inferred initializer _ ih =>
        refine .inferred (covariance.mpr initializer) ?_
        rw [fresh_mapOwner mapping injective]
        exact ih
    | discard child _ ih => exact .discard (covariance.mpr child) ih
    | ifTrue child _ ih => exact .ifTrue (covariance.mpr child) ih
    | ifFalse child _ ih => exact .ifFalse (covariance.mpr child) ih
    | wordMatch child choice _ ih => exact .wordMatch (covariance.mpr child) choice ih

end Solcore.Frontend

/-!
## Consolidated module: `Solcore.Frontend.ComputationReturnTreeTypeExtensionProperties`
-/

/-! Meaning-preserving tables retain independent evidence for every original
branch and the exact generated Core. The private checker graph supports only
operational equations for a fixed child operation, not source semantics. -/

set_option autoImplicit false

namespace Solcore.Frontend

theorem ComputationReturnTreeHasType.extend_types
    {ChildHasType : LocalNameTable → Resolved.Context → Syntax.Expr → Core.Ty → Prop}
    {old new : TypeNameTable} {owner : Resolved.DeclarationId} {inputs : LocalTypeInputs}
    {body : Syntax.Block} {type : Core.Ty}
    (typing : ComputationReturnTreeHasType ChildHasType old owner inputs body type)
    (extension : TypeNameTable.Extends old new) :
    ComputationReturnTreeHasType ChildHasType new owner inputs body type := by
  induction typing with
  | bare => exact .bare
  | expression child => exact .expression child
  | block _ ih => exact .block ih
  | binding meaning initializer _ ih => exact .binding (meaning.extend_types extension) initializer ih
  | inferred initializer _ ih => exact .inferred initializer ih
  | discard expression _ ih => exact .discard expression ih
  | conditional condition protection _ _ thenIH elseIH =>
      exact .conditional condition protection thenIH elseIH
  | wordMatch scrutinee patterns compatible covered _ _ branchIH defaultIH =>
      exact .wordMatch scrutinee patterns compatible covered branchIH defaultIH

theorem ComputationReturnTreeElaborates.extend_types
    {ChildElab : LocalNameTable → Resolved.Context → Syntax.Expr → Core.Expr → Core.Ty → Prop}
    {old new : TypeNameTable} {owner : Resolved.DeclarationId} {inputs : LocalTypeInputs}
    {body : Syntax.Block} {core : Core.Expr} {type : Core.Ty}
    (elaboration : ComputationReturnTreeElaborates ChildElab old owner inputs body core type)
    (extension : TypeNameTable.Extends old new) :
    ComputationReturnTreeElaborates ChildElab new owner inputs body core type := by
  induction elaboration with
  | bare => exact .bare
  | expression child => exact .expression child
  | block _ ih => exact .block ih
  | binding meaning initializer _ ih => exact .binding (meaning.extend_types extension) initializer ih
  | inferred initializer _ ih => exact .inferred initializer ih
  | discard expression _ ih => exact .discard expression ih
  | conditional condition protection _ _ thenIH elseIH =>
      exact .conditional condition protection thenIH elseIH
  | wordMatch scrutinee ordered patterns compatible _ defaultOrdered _ lowered branchIH defaultIH =>
      exact .wordMatch scrutinee ordered patterns compatible branchIH defaultOrdered defaultIH lowered

private def ReturnTreeTypeExtensionCheckGraph
    (checkChild : LocalNameTable → Resolved.Context → Syntax.Expr → Option (Core.Expr × Core.Ty))
    (table : LocalNameTable) (context : Resolved.Context) (source : Syntax.Expr)
    (core : Core.Expr) (type : Core.Ty) : Prop := checkChild table context source = some (core, type)

variable {checkChild : LocalNameTable → Resolved.Context → Syntax.Expr → Option (Core.Expr × Core.Ty)}

private theorem checked_body_iff {types : TypeNameTable} {owner : Resolved.DeclarationId}
    {inputs : LocalTypeInputs} {body : Syntax.Block} {core : Core.Expr} {type : Core.Ty} :
    elaborateComputationReturnTree? checkChild types owner inputs body = some (core, type) ↔
      ComputationReturnTreeElaborates (ReturnTreeTypeExtensionCheckGraph checkChild)
        types owner inputs body core type :=
  elaborateComputationReturnTree?_iff (checkChild := checkChild)
    (ChildElab := ReturnTreeTypeExtensionCheckGraph checkChild) Iff.rfl

theorem elaborateComputationReturnTree?_some_of_extends
    {old new : TypeNameTable} {owner : Resolved.DeclarationId} {inputs : LocalTypeInputs}
    {body : Syntax.Block} {core : Core.Expr} {type : Core.Ty}
    (extension : TypeNameTable.Extends old new)
    (accepted : elaborateComputationReturnTree? checkChild old owner inputs body = some (core, type)) :
    elaborateComputationReturnTree? checkChild new owner inputs body = some (core, type) :=
  checked_body_iff.mpr ((checked_body_iff.mp accepted).extend_types extension)

/-- A one-way extension may repair an unknown annotation, even in an unselected
branch. Mutual extension also retains absence, hence every optional result. -/
theorem elaborateComputationReturnTree?_eq_of_mutual_extends
    {old new : TypeNameTable} (forward : TypeNameTable.Extends old new)
    (backward : TypeNameTable.Extends new old) (owner : Resolved.DeclarationId)
    (inputs : LocalTypeInputs) (body : Syntax.Block) :
    elaborateComputationReturnTree? checkChild old owner inputs body =
      elaborateComputationReturnTree? checkChild new owner inputs body := by
  cases oldResult : elaborateComputationReturnTree? checkChild old owner inputs body with
  | none =>
      cases newResult : elaborateComputationReturnTree? checkChild new owner inputs body with
      | none => rfl
      | some pair =>
          rcases pair with ⟨core, type⟩
          have preserved := elaborateComputationReturnTree?_some_of_extends backward newResult
          rw [oldResult] at preserved
          cases preserved
  | some pair =>
      rcases pair with ⟨core, type⟩
      exact (elaborateComputationReturnTree?_some_of_extends forward oldResult).symm

end Solcore.Frontend

/-!
## Consolidated module: `Solcore.Frontend.ComputationFunctionTypeExtensionProperties`
-/

/-! Meaning-preserving caller tables retain independent function provenance,
complete actual preparations and every present run result. Executable laws use
the same arbitrary child operation, without a child correctness hypothesis. -/

set_option autoImplicit false

namespace Solcore.Frontend

private def FunctionTypeExtensionCheckGraph
    (checkChild : LocalNameTable → Resolved.Context → Syntax.Expr → Option (Core.Expr × Core.Ty))
    (table : LocalNameTable) (context : Resolved.Context) (source : Syntax.Expr)
    (core : Core.Expr) (type : Core.Ty) : Prop :=
  checkChild table context source = some (core, type)

theorem ComputationFunctionCompiles.extend_types
    {ChildElab : LocalNameTable → Resolved.Context → Syntax.Expr → Core.Expr → Core.Ty → Prop}
    {old new : TypeNameTable} {owner : Resolved.DeclarationId}
    {declaration : Syntax.FunctionDecl} {compiled : CompiledRuntimeFunction}
    (compilation : ComputationFunctionCompiles ChildElab old owner declaration compiled)
    (extension : TypeNameTable.Extends old new) :
    ComputationFunctionCompiles ChildElab new owner declaration compiled :=
  ⟨compilation.header.extend_types extension,
    RuntimeParametersDeclare.extend_types compilation.parameters extension,
    compilation.body.extend_types extension⟩

/-- Preserve the original value-bearing record, not merely its erased view. -/
theorem ComputationFunctionPrepares.extend_types
    {ChildElab : LocalNameTable → Resolved.Context → Syntax.Expr → Core.Expr → Core.Ty → Prop}
    {old new : TypeNameTable} {owner : Resolved.DeclarationId}
    {declaration : Syntax.FunctionDecl} {arguments : List TypedRuntimeArgument}
    {prepared : PreparedRuntimeFunction}
    (preparation : ComputationFunctionPrepares ChildElab old owner declaration arguments prepared)
    (extension : TypeNameTable.Extends old new) :
    ComputationFunctionPrepares ChildElab new owner declaration arguments prepared :=
  ⟨preparation.header.extend_types extension,
    RuntimeParametersBind.extend_types preparation.parameters extension,
    preparation.body.extend_types extension⟩

theorem compileComputationFunction?_some_of_extends
    {checkChild : LocalNameTable → Resolved.Context → Syntax.Expr → Option (Core.Expr × Core.Ty)}
    {old new : TypeNameTable} {owner : Resolved.DeclarationId}
    {declaration : Syntax.FunctionDecl} {compiled : CompiledRuntimeFunction}
    (extension : TypeNameTable.Extends old new)
    (accepted : compileComputationFunction? checkChild old owner declaration = some compiled) :
    compileComputationFunction? checkChild new owner declaration = some compiled := by
  have compilation := (compileComputationFunction?_iff
    (checkChild := checkChild) (ChildElab := FunctionTypeExtensionCheckGraph checkChild) Iff.rfl).mp accepted
  exact (compileComputationFunction?_iff
    (checkChild := checkChild) (ChildElab := FunctionTypeExtensionCheckGraph checkChild) Iff.rfl).mpr
      (compilation.extend_types extension)

theorem prepareComputationFunction?_some_of_extends
    {checkChild : LocalNameTable → Resolved.Context → Syntax.Expr → Option (Core.Expr × Core.Ty)}
    {old new : TypeNameTable} {owner : Resolved.DeclarationId}
    {declaration : Syntax.FunctionDecl} {arguments : List TypedRuntimeArgument}
    {prepared : PreparedRuntimeFunction} (extension : TypeNameTable.Extends old new)
    (accepted : prepareComputationFunction? checkChild old owner declaration arguments = some prepared) :
    prepareComputationFunction? checkChild new owner declaration arguments = some prepared := by
  have preparation := (prepareComputationFunction?_iff
    (checkChild := checkChild) (ChildElab := FunctionTypeExtensionCheckGraph checkChild) Iff.rfl).mp accepted
  exact (prepareComputationFunction?_iff
    (checkChild := checkChild) (ChildElab := FunctionTypeExtensionCheckGraph checkChild) Iff.rfl).mpr
      (preparation.extend_types extension)

/-- Absence is retained only when both directions preserve named meanings. -/
theorem compileComputationFunction?_eq_of_mutual_extends
    {checkChild : LocalNameTable → Resolved.Context → Syntax.Expr → Option (Core.Expr × Core.Ty)}
    {old new : TypeNameTable}
    (forward : TypeNameTable.Extends old new) (backward : TypeNameTable.Extends new old)
    (owner : Resolved.DeclarationId) (declaration : Syntax.FunctionDecl) :
    compileComputationFunction? checkChild old owner declaration =
      compileComputationFunction? checkChild new owner declaration := by
  cases oldResult : compileComputationFunction? checkChild old owner declaration with
  | none =>
      cases newResult : compileComputationFunction? checkChild new owner declaration with
      | none => rfl
      | some compiled =>
          have preserved := compileComputationFunction?_some_of_extends backward newResult
          rw [oldResult] at preserved
          cases preserved
  | some compiled => exact (compileComputationFunction?_some_of_extends forward oldResult).symm

/-- Equality includes all actual input values and retained captures. -/
theorem prepareComputationFunction?_eq_of_mutual_extends
    {checkChild : LocalNameTable → Resolved.Context → Syntax.Expr → Option (Core.Expr × Core.Ty)}
    {old new : TypeNameTable}
    (forward : TypeNameTable.Extends old new) (backward : TypeNameTable.Extends new old)
    (owner : Resolved.DeclarationId) (declaration : Syntax.FunctionDecl)
    (arguments : List TypedRuntimeArgument) :
    prepareComputationFunction? checkChild old owner declaration arguments =
      prepareComputationFunction? checkChild new owner declaration arguments := by
  cases oldResult : prepareComputationFunction? checkChild old owner declaration arguments with
  | none =>
      cases newResult : prepareComputationFunction? checkChild new owner declaration arguments with
      | none => rfl
      | some prepared =>
          have preserved := prepareComputationFunction?_some_of_extends backward newResult
          rw [oldResult] at preserved
          cases preserved
  | some prepared => exact (prepareComputationFunction?_some_of_extends forward oldResult).symm

/-- Present faults and exhaustion retain their exact stores and saved states;
this is transport, not a safety or runtime-validation assertion. -/
theorem runComputationFunction?_some_of_extends
    {checkChild : LocalNameTable → Resolved.Context → Syntax.Expr → Option (Core.Expr × Core.Ty)}
    {old new : TypeNameTable} {owner : Resolved.DeclarationId}
    {declaration : Syntax.FunctionDecl} {arguments : List TypedRuntimeArgument}
    {fuel : Nat} {store : Core.Store} {outcome : Core.Ty × Core.StatefulRunResult}
    (extension : TypeNameTable.Extends old new)
    (accepted : runComputationFunction? checkChild old owner declaration arguments fuel store = some outcome) :
    runComputationFunction? checkChild new owner declaration arguments fuel store = some outcome := by
  cases preparedResult : prepareComputationFunction? checkChild old owner declaration arguments with
  | none => simp only [runComputationFunction?, preparedResult, bind, Option.bind_none,
      reduceCtorEq] at accepted
  | some prepared =>
      have preserved := prepareComputationFunction?_some_of_extends extension preparedResult
      simpa only [runComputationFunction?, preparedResult, preserved] using accepted

theorem runComputationFunction?_eq_of_mutual_extends
    {checkChild : LocalNameTable → Resolved.Context → Syntax.Expr → Option (Core.Expr × Core.Ty)}
    {old new : TypeNameTable}
    (forward : TypeNameTable.Extends old new) (backward : TypeNameTable.Extends new old)
    (owner : Resolved.DeclarationId) (declaration : Syntax.FunctionDecl)
    (arguments : List TypedRuntimeArgument) (fuel : Nat) (store : Core.Store) :
    runComputationFunction? checkChild old owner declaration arguments fuel store =
      runComputationFunction? checkChild new owner declaration arguments fuel store := by
  simp only [runComputationFunction?,
    prepareComputationFunction?_eq_of_mutual_extends forward backward owner declaration arguments]

end Solcore.Frontend

/-!
## Consolidated module: `Solcore.Frontend.ComputationReturnTreeTypingProperties`
-/

/-! Independent body typing uses only the corresponding child typing law.
Core typing needs only child Core typing and general positional weakening. -/

set_option autoImplicit false

namespace Solcore.Frontend

variable {ChildHasType : LocalNameTable → Resolved.Context → Syntax.Expr → Core.Ty → Prop}
    {ChildElab : LocalNameTable → Resolved.Context → Syntax.Expr → Core.Expr → Core.Ty → Prop}

private theorem fold_coverage {entries : List (Syntax.MatchCase × (Option Core.Word × Core.Expr))}
    {defaultEntry : Option (Syntax.Block × Core.Expr)}
    (patterns : ∀ entry ∈ entries, WordMatchPatternClassifies entry.1.value.pattern entry.2.1) :
    (entries.foldr (fun entry tail => match entry.2.1 with
      | none => some (entry.2.2.weakenAt 0)
      | some word => tail.map (fun core =>
          .ifE (.binary .wordEq (.var 0) (.word word)) (entry.2.2.weakenAt 0) core))
      (defaultEntry.map (fun entry => entry.2.weakenAt 0))).isSome = true ↔
    defaultEntry.isSome = true ∨ ∃ entry ∈ entries, WordMatchPatternClassifies entry.1.value.pattern none := by
  induction entries with
  | nil => simp
  | cons entry rest ih =>
      have meaning := patterns entry (by simp)
      cases tag : entry.2.1 with
      | none =>
          simp only [tag] at meaning
          simp [tag, meaning]
      | some word =>
          simp only [tag] at meaning
          have notCatchAll : ¬ WordMatchPatternClassifies entry.1.value.pattern none := by
            intro caught
            have impossible := meaning.tag_unique caught
            cases impossible
          simpa [tag, notCatchAll] using ih (fun item member => patterns item (by simp [member]))

private theorem hasType
    (childTyping : ∀ {table context source type},
      ChildHasType table context source type ↔ ∃ core, ChildElab table context source core type)
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {inputs : LocalTypeInputs}
    {body : Syntax.Block} {core : Core.Expr} {type : Core.Ty}
    (elaboration : ComputationReturnTreeElaborates ChildElab types owner inputs body core type) :
    ComputationReturnTreeHasType ChildHasType types owner inputs body type := by
  induction elaboration with
  | bare => exact .bare
  | expression child => exact .expression (childTyping.mpr ⟨_, child⟩)
  | block _ ih => exact .block ih
  | binding meaning initializer _ ih =>
      exact .binding meaning (childTyping.mpr ⟨_, initializer⟩) ih
  | inferred initializer _ ih =>
      exact .inferred (childTyping.mpr ⟨_, initializer⟩) ih
  | discard expression _ ih =>
      exact .discard (childTyping.mpr ⟨_, expression⟩) ih
  | conditional condition protection _ _ thenIH elseIH =>
      exact .conditional (childTyping.mpr ⟨_, condition⟩) protection thenIH elseIH
  | wordMatch scrutinee ordered patterns compatible _ defaultOrdered _ lowered branchIH defaultIH =>
      refine .wordMatch (childTyping.mpr ⟨_, scrutinee⟩) ?_ ?_ ?_ ?_ ?_
      · intro arm member
        rw [← ordered] at member
        obtain ⟨entry, entryMember, rfl⟩ := List.mem_map.mp member
        exact ⟨entry.2.1, patterns entry entryMember⟩
      · rcases compatible with word | allNone
        · exact .inl word
        · right; intro arm member
          rw [← ordered] at member
          obtain ⟨entry, entryMember, rfl⟩ := List.mem_map.mp member
          simpa only [allNone entry entryMember] using patterns entry entryMember
      · rcases (fold_coverage patterns).mp (congrArg Option.isSome lowered) with present | ⟨entry, member, meaning⟩
        · left; rw [← defaultOrdered]; simpa using present
        · exact .inr ⟨entry.1, ordered ▸ List.mem_map.mpr ⟨entry, member, rfl⟩, meaning⟩
      · intro arm member
        rw [← ordered] at member
        obtain ⟨entry, entryMember, rfl⟩ := List.mem_map.mp member
        exact branchIH entry entryMember
      · intro source member
        rw [← defaultOrdered, Option.toList_map] at member
        obtain ⟨entry, entryMember, rfl⟩ := List.mem_map.mp member
        exact defaultIH entry entryMember

private theorem entries_exist {cases : List Syntax.MatchCase} {P : Syntax.Block → Core.Expr → Prop}
    (patterns : ∀ arm ∈ cases, ∃ tag, WordMatchPatternClassifies arm.value.pattern tag)
    (branches : ∀ arm ∈ cases, ∃ core, P arm.value.body core) :
    ∃ entries : List (Syntax.MatchCase × (Option Core.Word × Core.Expr)), entries.map Prod.fst = cases ∧
      (∀ entry ∈ entries, WordMatchPatternClassifies entry.1.value.pattern entry.2.1) ∧
      (∀ entry ∈ entries, P entry.1.value.body entry.2.2) := by
  induction cases with
  | nil => exact ⟨[], rfl, by simp, by simp⟩
  | cons arm rest ih =>
      obtain ⟨word, meaning⟩ := patterns arm (by simp)
      obtain ⟨core, elaboration⟩ := branches arm (by simp)
      obtain ⟨entries, ordered, meanings, elaborations⟩ := ih
        (fun arm member => patterns arm (by simp [member]))
        (fun arm member => branches arm (by simp [member]))
      refine ⟨(arm, word, core) :: entries, by simp [ordered], ?_, ?_⟩
      · intro entry member
        rcases List.mem_cons.mp member with rfl | member
        · exact meaning
        · exact meanings entry member
      · intro entry member
        rcases List.mem_cons.mp member with rfl | member
        · exact elaboration
        · exact elaborations entry member

private theorem elaborates
    (childTyping : ∀ {table context source type},
      ChildHasType table context source type ↔ ∃ core, ChildElab table context source core type)
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {inputs : LocalTypeInputs}
    {body : Syntax.Block} {type : Core.Ty}
    (typing : ComputationReturnTreeHasType ChildHasType types owner inputs body type) :
    ∃ core, ComputationReturnTreeElaborates ChildElab types owner inputs body core type := by
  induction typing with
  | bare => exact ⟨.unit, .bare⟩
  | expression child =>
      obtain ⟨core, elaboration⟩ := childTyping.mp child
      exact ⟨core, .expression elaboration⟩
  | block _ ih =>
      obtain ⟨core, elaboration⟩ := ih
      exact ⟨core, .block elaboration⟩
  | binding meaning initializer _ ih =>
      obtain ⟨initializerCore, initializerElaboration⟩ := childTyping.mp initializer
      obtain ⟨tailCore, tailElaboration⟩ := ih
      exact ⟨.letE initializerCore tailCore, .binding meaning initializerElaboration tailElaboration⟩
  | inferred initializer _ ih =>
      obtain ⟨initializerCore, initializerElaboration⟩ := childTyping.mp initializer
      obtain ⟨tailCore, tailElaboration⟩ := ih
      exact ⟨.letE initializerCore tailCore, .inferred initializerElaboration tailElaboration⟩
  | discard expression _ ih =>
      obtain ⟨expressionCore, expressionElaboration⟩ := childTyping.mp expression
      obtain ⟨tailCore, tailElaboration⟩ := ih
      exact ⟨.letE expressionCore (tailCore.weakenAt 0), .discard expressionElaboration tailElaboration⟩
  | conditional condition protection _ _ thenIH elseIH =>
      obtain ⟨conditionCore, conditionElaboration⟩ := childTyping.mp condition
      obtain ⟨thenCore, thenElaboration⟩ := thenIH
      obtain ⟨elseCore, elseElaboration⟩ := elseIH
      exact ⟨.ifE conditionCore thenCore elseCore, .conditional conditionElaboration protection thenElaboration elseElaboration⟩
  | @wordMatch inputs _ _ _ _ _ _ defaultBody scrutineeType type scrutinee patterns compatible covered _ _ branchIH defaultIH =>
      obtain ⟨scrutineeCore, scrutineeElaboration⟩ := childTyping.mp scrutinee
      obtain ⟨entries, ordered, meanings, elaborations⟩ :=
        entries_exist (P := fun body core => ComputationReturnTreeElaborates ChildElab types owner inputs body core type)
          patterns branchIH
      have compatibleEntries : scrutineeType = .word ∨ ∀ entry ∈ entries, entry.2.1 = none := by
        rcases compatible with word | allNone
        · exact .inl word
        · exact .inr (fun entry member => (meanings entry member).tag_unique
            (allNone entry.1 (ordered ▸ List.mem_map.mpr ⟨entry, member, rfl⟩)))
      have defaults : ∃ defaultEntry : Option (Syntax.Block × Core.Expr), defaultEntry.map Prod.fst = defaultBody ∧
          ∀ entry ∈ defaultEntry.toList, ComputationReturnTreeElaborates ChildElab types owner inputs entry.1 entry.2 type := by
        cases defaultBody with
        | none => exact ⟨none, rfl, by simp⟩
        | some source =>
            obtain ⟨core, elaboration⟩ := defaultIH source (by simp)
            exact ⟨some (source, core), rfl, by intro entry member; simpa using (List.mem_singleton.mp member ▸ elaboration)⟩
      obtain ⟨defaultEntry, defaultOrdered, defaults⟩ := defaults
      have coveredFold : defaultEntry.isSome = true ∨ ∃ entry ∈ entries, WordMatchPatternClassifies entry.1.value.pattern none := by
        rcases covered with present | ⟨arm, member, meaning⟩
        · left; rw [← defaultOrdered] at present; simpa using present
        · rw [← ordered] at member
          obtain ⟨entry, entryMember, rfl⟩ := List.mem_map.mp member
          exact .inr ⟨entry, entryMember, meaning⟩
      obtain ⟨bodyCore, lowered⟩ := Option.isSome_iff_exists.mp ((fold_coverage meanings).mpr coveredFold)
      exact ⟨_, .wordMatch scrutineeElaboration ordered meanings compatibleEntries elaborations defaultOrdered defaults lowered⟩

theorem computationReturnTreeHasType_iff_elaborates
    (childTyping : ∀ {table context source type},
      ChildHasType table context source type ↔ ∃ core, ChildElab table context source core type)
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {inputs : LocalTypeInputs}
    {body : Syntax.Block} {type : Core.Ty} :
    ComputationReturnTreeHasType ChildHasType types owner inputs body type ↔
      ∃ core, ComputationReturnTreeElaborates ChildElab types owner inputs body core type :=
  ⟨elaborates childTyping, fun ⟨_, elaboration⟩ => hasType childTyping elaboration⟩

private theorem fold_hasType {context : Core.Context} {scrutineeType type : Core.Ty} {bodyCore : Core.Expr}
    {defaultEntry : Option (Syntax.Block × Core.Expr)}
    {entries : List (Syntax.MatchCase × (Option Core.Word × Core.Expr))}
    (fallback : ∀ entry ∈ defaultEntry.toList, Core.HasType context entry.2 type)
    (branches : ∀ entry ∈ entries, Core.HasType context entry.2.2 type)
    (compatible : scrutineeType = .word ∨ ∀ entry ∈ entries, entry.2.1 = none)
    (lowered : entries.foldr
      (fun entry tail => match entry.2.1 with
        | none => some (entry.2.2.weakenAt 0)
        | some word => tail.map (fun core => .ifE (.binary .wordEq (.var 0) (.word word)) (entry.2.2.weakenAt 0) core))
      (defaultEntry.map (fun entry => entry.2.weakenAt 0)) = some bodyCore) :
    Core.HasType (scrutineeType :: context) bodyCore type := by
  induction entries generalizing bodyCore with
  | nil =>
      obtain ⟨entry, member, rfl⟩ := Option.map_eq_some_iff.mp lowered
      simpa only [Core.Context.insertAt] using (fallback entry (Option.mem_toList.mpr member)).weakenAt 0
  | cons entry rest ih =>
      have head : Core.HasType (scrutineeType :: context) (entry.2.2.weakenAt 0) type := by
        simpa only [Core.Context.insertAt] using (branches entry (by simp)).weakenAt 0
      cases tag : entry.2.1 with
      | none => simp only [List.foldr_cons, tag, Option.some.injEq] at lowered; exact lowered ▸ head
      | some word =>
          simp only [List.foldr_cons, tag] at lowered
          obtain ⟨tail, found, rfl⟩ := Option.map_eq_some_iff.mp lowered
          rcases compatible with rfl | allNone
          · exact .ifE (.binary (.var rfl) (.word)) head
              (ih (fun row member => branches row (by simp [member])) (.inl rfl) found)
          · have impossible := allNone entry (by simp)
            rw [tag] at impossible
            cases impossible

theorem ComputationReturnTreeElaborates.core_hasType
    (childCoreType : ∀ {table context source core type},
      ChildElab table context source core type → Core.HasType context.values core type)
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {inputs : LocalTypeInputs}
    {body : Syntax.Block} {core : Core.Expr} {type : Core.Ty}
    (elaboration : ComputationReturnTreeElaborates ChildElab types owner inputs body core type) :
    Core.HasType inputs.context.values core type := by
  induction elaboration with
  | bare => exact .unit
  | expression child => exact childCoreType child
  | block _ ih => exact ih
  | binding _ initializer _ ih | inferred initializer _ ih =>
      exact .letE (childCoreType initializer)
        (by simpa only [LocalTypeInputs.bindFresh_context, Resolved.LocalScope.values, List.map_cons, Prod.snd] using ih)
  | discard expression _ ih =>
      exact .letE (childCoreType expression) (by simpa only [Core.Context.insertAt] using ih.weakenAt 0)
  | conditional condition _ _ _ thenIH elseIH => exact .ifE (childCoreType condition) thenIH elseIH
  | wordMatch scrutinee _ _ compatible _ _ _ lowered branchIH defaultIH =>
      exact .letE (childCoreType scrutinee) (fold_hasType defaultIH branchIH compatible lowered)

end Solcore.Frontend

/-!
## Consolidated module: `Solcore.Frontend.ComputationReturnTreeRuntimeCheckpointProperties`
-/

/-! Original body typing supplies safety only with the actual environment,
store and pending frames typed in one world. Saved states remain exact; their
world is existential in StateHasType. Positional state safety needs no source
ID alignment or child execution, cost or fragment law. -/

set_option autoImplicit false

namespace Solcore.Frontend

theorem ComputationReturnTreeElaborates.runtime_checkpoint_safety
    {ChildElab : LocalNameTable → Resolved.Context → Syntax.Expr → Core.Expr → Core.Ty → Prop}
    (childCoreType : ∀ {table context source core type},
      ChildElab table context source core type → Core.HasType context.values core type)
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {inputs : LocalTypeInputs}
    {body : Syntax.Block} {core : Core.Expr} {type : Core.Ty}
    (elaboration : ComputationReturnTreeElaborates ChildElab types owner inputs body core type)
    {world : Core.StoreTyping} {environment : Core.Environment} {store : Core.Store}
    (environmentTyped : Core.RuntimeEnvironmentHasTypes world environment inputs.context.values)
    (storeTyped : Core.StoreHasTypes world store)
    {continuation : List Core.Frame} {resultType : Core.Ty}
    (continuationTyped : Core.ContinuationHasType world continuation type resultType) :
    Core.StateHasType ⟨.eval core environment, continuation, store⟩ resultType ∧
      (∀ fuel error faultState, Core.runStateful fuel
        ⟨.eval core environment, continuation, store⟩ ≠ .fault error faultState) ∧
      ∀ {spent checkpoint}, Core.runStateful spent
        ⟨.eval core environment, continuation, store⟩ = .outOfFuel checkpoint →
        Core.StateHasType checkpoint resultType ∧
          ∀ additional error faultState,
            Core.runStateful additional checkpoint ≠ .fault error faultState := by
  have initial : Core.StateHasType ⟨.eval core environment, continuation, store⟩ resultType :=
    .eval storeTyped.toRuntime environmentTyped (elaboration.core_hasType childCoreType) continuationTyped
  refine ⟨initial, fun _ _ _ => Core.well_typed_runStateful_never_faults initial, ?_⟩
  intro spent checkpoint exhausted
  have saved := (Core.runStateful_outOfFuel_sound exhausted).1.preserve_state_type initial
  exact ⟨saved, fun _ _ _ => Core.well_typed_runStateful_never_faults saved⟩

end Solcore.Frontend

/-!
## Consolidated module: `Solcore.Frontend.ComputationReturnTreeRuntimeSafetyProperties`
-/

/-! Runtime-world safety for the original shared body. The actual environment
and store share one world; the exact successful cost is not a source bound.
Pending continuations receive local paths, not an untyped completion claim. -/

set_option autoImplicit false

namespace Solcore.Frontend

theorem ComputationReturnTreeElaborates.runtime_typed_execution
    {ChildElab : LocalNameTable → Resolved.Context → Syntax.Expr → Core.Expr → Core.Ty → Prop}
    {ChildEval : LocalNameTable → Resolved.Environment → Core.Store → Syntax.Expr → Core.Value → Core.Store → Prop}
    {ChildCost : LocalNameTable → Resolved.Environment → Core.Store → Syntax.Expr → Core.Value → Core.Store → Nat → Prop}
    {F : Core.Expr → Prop}
    (childCoreType : ∀ {table context source core type},
      ChildElab table context source core type → Core.HasType context.values core type)
    (childMembership : ∀ {table context source core type}, ChildElab table context source core type → F core)
    (childWeakening : ∀ {core}, F core → ∀ cutoff, F (core.weakenAt cutoff))
    (childInserts : ∀ {core}, F core → ∀ leading suffix inserted {initialStore finalStore value},
      Core.Evaluates (leading ++ inserted :: suffix) initialStore (core.weakenAt leading.length) value finalStore ↔
        Core.Evaluates (leading ++ suffix) initialStore core value finalStore)
    (childExecution : ∀ {table context environment source core type},
      ChildElab table context source core type → environment.ids = context.ids →
      ∀ {initialStore finalStore value}, ChildEval table environment initialStore source value finalStore ↔
        Core.Evaluates environment.values initialStore core value finalStore)
    (childCostIff : ∀ {table environment initialStore source value finalStore},
      ChildEval table environment initialStore source value finalStore ↔
        ∃ cost, ChildCost table environment initialStore source value finalStore cost)
    (childPaths : ∀ {expr}, F expr → ∀ (leading suffix : Core.Environment) (inserted : Core.Value),
      ∀ {initialStore finalStore value},
        Core.Evaluates (leading ++ suffix) initialStore expr value finalStore →
        ∃ cost, ∀ continuation,
          Core.Steps cost ⟨.eval expr (leading ++ suffix), continuation, initialStore⟩
            ⟨.ret value, continuation, finalStore⟩ ∧
          Core.Steps cost
            ⟨.eval (expr.weakenAt leading.length) (leading ++ inserted :: suffix), continuation, initialStore⟩
            ⟨.ret value, continuation, finalStore⟩)
    (childSteps : ∀ {table context environment initialStore finalStore source value cost},
      ChildCost table environment initialStore source value finalStore cost →
      ∀ {core type}, ChildElab table context source core type → environment.ids = context.ids →
      ∀ continuation, Core.Steps cost ⟨.eval core environment.values, continuation, initialStore⟩
        ⟨.ret value, continuation, finalStore⟩)
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {inputs : LocalTypeInputs}
    {environment : Resolved.Environment} {body : Syntax.Block} {core : Core.Expr} {type : Core.Ty}
    (elaboration : ComputationReturnTreeElaborates ChildElab types owner inputs body core type)
    (sameIds : environment.ids = inputs.context.ids)
    {world : Core.StoreTyping} {store : Core.Store}
    (environmentTyped : Core.RuntimeEnvironmentHasTypes world environment.values inputs.context.values)
    (storeTyped : Core.StoreHasTypes world store)
    (finite : ∃ value finalStore,
      Core.Evaluates environment.values store core value finalStore) :
    ∃ finalWorld finalStore value cost, Core.WorldExtends world finalWorld ∧
      Core.RuntimeStoreHasTypes finalWorld finalStore ∧ Core.RuntimeValueHasType finalWorld value type ∧
      ComputationReturnTreeEvaluatesWithCost ChildCost owner inputs.names environment
        store body value finalStore cost ∧
      (∀ continuation : List Core.Frame, Core.Steps cost
        ⟨.eval core environment.values, continuation, store⟩
        ⟨.ret value, continuation, finalStore⟩) ∧
      ∀ fuel, (Core.runStateful fuel (.initial core environment.values store) =
          .done value finalStore ↔ cost ≤ fuel) ∧
        ((∃ checkpoint, Core.runStateful fuel (.initial core environment.values store) =
          .outOfFuel checkpoint) ↔ fuel < cost) := by
  obtain ⟨value, finalStore, evaluated⟩ := finite
  obtain ⟨finalWorld, extension, finalTyped, valueTyped⟩ :=
    Core.evaluation_preserves_type evaluated (elaboration.core_hasType childCoreType)
      environmentTyped storeTyped.toRuntime
  have raw := (ComputationReturnTreeElaborates.evaluates_iff (F := F)
    (ChildElab := ChildElab) (ChildEval := ChildEval)
    childMembership childWeakening childInserts childExecution elaboration sameIds).mpr evaluated
  obtain ⟨cost, counted⟩ := (computationReturnTreeEvaluates_iff_exists_cost
    (ChildEval := ChildEval) (ChildCost := ChildCost) childCostIff).mp raw
  have paths := ComputationReturnTreeEvaluatesWithCost.toStepsWithContinuation (F := F)
    childMembership childWeakening childPaths childSteps counted elaboration sameIds
  exact ⟨finalWorld, finalStore, value, cost, extension, finalTyped, valueTyped, counted,
    paths, fun _ => ⟨(paths []).runStateful_done_iff, (paths []).runStateful_outOfFuel_iff⟩⟩

end Solcore.Frontend

/-!
## Consolidated module: `Solcore.Frontend.ComputationFunctionRuntimeSafetyProperties`
-/

/-! Original actual arguments and the supplied store share one runtime world.
Structural input records alone do not provide these premises. Preparation and
all runner outcomes retain the same exact record and reverse-once values. -/

set_option autoImplicit false

namespace Solcore.Frontend

private theorem safety_arguments_runtime_environment {world : Core.StoreTyping}
    (arguments : List TypedRuntimeArgument)
    (typed : ∀ argument ∈ arguments, Core.RuntimeValueHasType world argument.value argument.type) :
    Core.RuntimeEnvironmentHasTypes world (arguments.map (·.value)) (arguments.map (·.type)) := by
  revert typed
  induction arguments with
  | nil => intro _; exact .nil
  | cons argument arguments ih =>
      intro typed
      exact .cons (typed argument (by simp)) (ih (fun value member => typed value (by simp [member])))

private theorem safety_prepared_runtime_environment {world : Core.StoreTyping}
    {types : TypeNameTable} {owner : Resolved.DeclarationId}
    {parameters : List Syntax.FunctionParameter} {arguments : List TypedRuntimeArgument}
    {inputs : LocalInputs} (bound : RuntimeParametersBind types owner parameters arguments inputs)
    (typed : ∀ argument ∈ arguments, Core.RuntimeValueHasType world argument.value argument.type) :
    Core.RuntimeEnvironmentHasTypes world inputs.environment.values inputs.context.values := by
  have reversed := safety_arguments_runtime_environment arguments.reverse
    (fun argument member => typed argument (List.mem_reverse.mp member))
  simpa only [LocalInputs.environment, LocalInputs.context, Resolved.LocalScope.values,
    List.map_map, Function.comp_def, bound.argument_values, bound.argument_types] using reversed

theorem ComputationFunctionPrepares.runtime_typed_execution
    {checkChild : LocalNameTable → Resolved.Context → Syntax.Expr → Option (Core.Expr × Core.Ty)}
    {ChildElab : LocalNameTable → Resolved.Context → Syntax.Expr → Core.Expr → Core.Ty → Prop}
    {ChildEval : LocalNameTable → Resolved.Environment → Core.Store → Syntax.Expr → Core.Value → Core.Store → Prop}
    {ChildCost : LocalNameTable → Resolved.Environment → Core.Store → Syntax.Expr → Core.Value → Core.Store → Nat → Prop}
    {F : Core.Expr → Prop}
    (childCoreType : ∀ {table context source core type},
      ChildElab table context source core type → Core.HasType context.values core type)
    (childMembership : ∀ {table context source core type}, ChildElab table context source core type → F core)
    (childWeakening : ∀ {core}, F core → ∀ cutoff, F (core.weakenAt cutoff))
    (childInserts : ∀ {core}, F core → ∀ leading suffix inserted {initialStore finalStore value},
      Core.Evaluates (leading ++ inserted :: suffix) initialStore (core.weakenAt leading.length) value finalStore ↔
        Core.Evaluates (leading ++ suffix) initialStore core value finalStore)
    (childExecution : ∀ {table context environment source core type},
      ChildElab table context source core type → environment.ids = context.ids →
      ∀ {initialStore finalStore value}, ChildEval table environment initialStore source value finalStore ↔
        Core.Evaluates environment.values initialStore core value finalStore)
    (childCostIff : ∀ {table environment initialStore source value finalStore},
      ChildEval table environment initialStore source value finalStore ↔
        ∃ cost, ChildCost table environment initialStore source value finalStore cost)
    (childPaths : ∀ {expr}, F expr → ∀ (leading suffix : Core.Environment) (inserted : Core.Value),
      ∀ {initialStore finalStore value},
        Core.Evaluates (leading ++ suffix) initialStore expr value finalStore →
        ∃ cost, ∀ continuation,
          Core.Steps cost ⟨.eval expr (leading ++ suffix), continuation, initialStore⟩
            ⟨.ret value, continuation, finalStore⟩ ∧
          Core.Steps cost
            ⟨.eval (expr.weakenAt leading.length) (leading ++ inserted :: suffix), continuation, initialStore⟩
            ⟨.ret value, continuation, finalStore⟩)
    (childSteps : ∀ {table context environment initialStore finalStore source value cost},
      ChildCost table environment initialStore source value finalStore cost →
      ∀ {core type}, ChildElab table context source core type → environment.ids = context.ids →
      ∀ continuation, Core.Steps cost ⟨.eval core environment.values, continuation, initialStore⟩
        ⟨.ret value, continuation, finalStore⟩)
    (childCorrect : ∀ {table context source core type},
      checkChild table context source = some (core, type) ↔ ChildElab table context source core type)
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {declaration : Syntax.FunctionDecl}
    {arguments : List TypedRuntimeArgument} {prepared : PreparedRuntimeFunction}
    (preparation : ComputationFunctionPrepares ChildElab types owner declaration arguments prepared)
    {world : Core.StoreTyping} {store : Core.Store}
    (argumentsTyped : ∀ argument ∈ arguments, Core.RuntimeValueHasType world argument.value argument.type)
    (storeTyped : Core.StoreHasTypes world store)
    (finite : ∃ value finalStore, Core.Evaluates prepared.inputs.environment.values
      store prepared.core value finalStore) :
    prepareComputationFunction? checkChild types owner declaration arguments = some prepared ∧
    ∃ finalWorld finalStore value cost,
      Core.WorldExtends world finalWorld ∧ Core.RuntimeStoreHasTypes finalWorld finalStore ∧
      Core.RuntimeValueHasType finalWorld value prepared.returnType ∧
      ComputationReturnTreeEvaluatesWithCost ChildCost owner prepared.inputs.names prepared.inputs.environment
        store declaration.value.body value finalStore cost ∧
      (∀ continuation, Core.Steps cost
        ⟨.eval prepared.core prepared.inputs.environment.values, continuation, store⟩
        ⟨.ret value, continuation, finalStore⟩) ∧
      (∀ fuel, (Core.runStateful fuel (.initial prepared.core prepared.inputs.environment.values store) =
          .done value finalStore ↔ cost ≤ fuel) ∧
        ((∃ checkpoint, Core.runStateful fuel (.initial prepared.core prepared.inputs.environment.values store) =
          .outOfFuel checkpoint) ↔ fuel < cost)) ∧
      ∀ fuel, runComputationFunction? checkChild types owner declaration arguments fuel store =
        some (prepared.returnType, Core.runStateful fuel (.initial prepared.core prepared.inputs.environment.values store)) := by
  have accepted := (prepareComputationFunction?_iff childCorrect).mpr preparation
  have environmentTyped := safety_prepared_runtime_environment preparation.parameters argumentsTyped
  have sameIds : prepared.inputs.environment.ids = prepared.inputs.toTypeInputs.context.ids := by
    simpa only [LocalInputs.toTypeInputs_context] using prepared.inputs.sameIds
  have execution := ComputationReturnTreeElaborates.runtime_typed_execution (F := F)
    (ChildElab := ChildElab) (ChildEval := ChildEval) (ChildCost := ChildCost)
    childCoreType childMembership childWeakening childInserts childExecution childCostIff childPaths childSteps
    preparation.body sameIds (by simpa only [LocalInputs.toTypeInputs_context] using environmentTyped) storeTyped finite
  obtain ⟨finalWorld, finalStore, value, cost, extension, finalTyped, valueTyped, costed, paths, thresholds⟩ := execution
  refine ⟨accepted, finalWorld, finalStore, value, cost, extension, finalTyped, valueTyped, ?_, paths, thresholds, ?_⟩
  · simpa only [LocalInputs.toTypeInputs_names] using costed
  · intro fuel
    simp only [runComputationFunction?, accepted, bind, Option.bind_some, pure]

end Solcore.Frontend

/-!
## Consolidated module: `Solcore.Frontend.ComputationReturnTreeRuntimeWorldProperties`
-/

/-! Actual saved stores have uniquely determined worlds extending the supplied
world. Every further finite path retains a further extension of that same world. -/
set_option autoImplicit false
namespace Solcore.Frontend

theorem ComputationReturnTreeElaborates.runtime_checkpoint_world_extension
    {ChildElab : LocalNameTable → Resolved.Context → Syntax.Expr → Core.Expr → Core.Ty → Prop}
    (childCoreType : ∀ {table context source core type},
      ChildElab table context source core type → Core.HasType context.values core type)
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {inputs : LocalTypeInputs}
    {body : Syntax.Block} {core : Core.Expr} {type : Core.Ty}
    (elaboration : ComputationReturnTreeElaborates ChildElab types owner inputs body core type)
    {world : Core.StoreTyping} {environment : Core.Environment} {store : Core.Store}
    (environmentTyped : Core.RuntimeEnvironmentHasTypes world environment inputs.context.values)
    (storeTyped : Core.StoreHasTypes world store)
    {continuation : List Core.Frame} {resultType : Core.Ty}
    (continuationTyped : Core.ContinuationHasType world continuation type resultType)
    {spent : Nat} {checkpoint : Core.State}
    (exhausted : Core.runStateful spent ⟨.eval core environment,continuation,store⟩ = .outOfFuel checkpoint) :
    ∃ savedWorld, Core.WorldExtends world savedWorld ∧ Core.RuntimeStoreHasTypes savedWorld checkpoint.store ∧
      ∀ {steps next}, Core.Steps steps checkpoint next →
        ∃ future, Core.WorldExtends savedWorld future ∧ Core.RuntimeStoreHasTypes future next.store := by
  have safe := elaboration.runtime_checkpoint_safety childCoreType environmentTyped storeTyped continuationTyped
  have path := (Core.runStateful_outOfFuel_sound exhausted).1
  obtain ⟨savedWorld,extended,savedStored⟩ := path.preserve_store_world safe.1 storeTyped.toRuntime
  exact ⟨savedWorld,extended,savedStored,fun further => further.preserve_store_world (safe.2.2 exhausted).1 savedStored⟩

end Solcore.Frontend

/-!
## Consolidated module: `Solcore.Frontend.ComputationFunctionRuntimeCheckpointProperties`
-/

/-! Checkpoint safety of the literal prepared Core state uses only child Core
typing and one runtime world for actual arguments, store and typed caller frames.
The caller result type may differ from the prepared return type. No checker,
source cost, termination or optional-runner acceptance is inferred. -/

set_option autoImplicit false
namespace Solcore.Frontend

private theorem checkpoint_arguments_runtime_environment {world : Core.StoreTyping}
    (arguments : List TypedRuntimeArgument)
    (typed : ∀ argument ∈ arguments, Core.RuntimeValueHasType world argument.value argument.type) :
    Core.RuntimeEnvironmentHasTypes world (arguments.map (·.value)) (arguments.map (·.type)) := by
  revert typed
  induction arguments with
  | nil => intro _; exact .nil
  | cons argument arguments ih =>
      intro typed
      exact .cons (typed argument (by simp)) (ih (fun value member => typed value (by simp [member])))

private theorem checkpoint_prepared_runtime_environment {world : Core.StoreTyping}
    {types : TypeNameTable} {owner : Resolved.DeclarationId}
    {parameters : List Syntax.FunctionParameter} {arguments : List TypedRuntimeArgument}
    {inputs : LocalInputs} (bound : RuntimeParametersBind types owner parameters arguments inputs)
    (typed : ∀ argument ∈ arguments, Core.RuntimeValueHasType world argument.value argument.type) :
    Core.RuntimeEnvironmentHasTypes world inputs.environment.values inputs.context.values := by
  have reversed := checkpoint_arguments_runtime_environment arguments.reverse
    (fun argument member => typed argument (List.mem_reverse.mp member))
  simpa only [LocalInputs.environment, LocalInputs.context, Resolved.LocalScope.values,
    List.map_map, Function.comp_def, bound.argument_values, bound.argument_types] using reversed

/-- Preserve typing and exclude faults for the literal initial state, every
genuine checkpoint, and every additional fuel from that saved state. -/
theorem ComputationFunctionPrepares.runtime_checkpoint_safety
    {ChildElab : LocalNameTable → Resolved.Context → Syntax.Expr → Core.Expr → Core.Ty → Prop}
    (childCoreType : ∀ {table context source core type},
      ChildElab table context source core type → Core.HasType context.values core type)
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {declaration : Syntax.FunctionDecl}
    {arguments : List TypedRuntimeArgument} {prepared : PreparedRuntimeFunction}
    (preparation : ComputationFunctionPrepares ChildElab types owner declaration arguments prepared)
    {world : Core.StoreTyping} {store : Core.Store}
    (argumentsTyped : ∀ argument ∈ arguments, Core.RuntimeValueHasType world argument.value argument.type)
    (storeTyped : Core.StoreHasTypes world store)
    {continuation : List Core.Frame} {resultType : Core.Ty}
    (continuationTyped : Core.ContinuationHasType world continuation prepared.returnType resultType) :
    Core.StateHasType ⟨.eval prepared.core prepared.inputs.environment.values, continuation, store⟩ resultType ∧
      (∀ fuel error faultState, Core.runStateful fuel
        ⟨.eval prepared.core prepared.inputs.environment.values, continuation, store⟩ ≠ .fault error faultState) ∧
      ∀ {spent checkpoint}, Core.runStateful spent
        ⟨.eval prepared.core prepared.inputs.environment.values, continuation, store⟩ = .outOfFuel checkpoint →
        Core.StateHasType checkpoint resultType ∧
          ∀ additional error faultState,
            Core.runStateful additional checkpoint ≠ .fault error faultState := by
  have environmentTyped :=
    checkpoint_prepared_runtime_environment preparation.parameters argumentsTyped
  exact preparation.body.runtime_checkpoint_safety childCoreType
    (by simpa only [LocalInputs.toTypeInputs_context] using environmentTyped) storeTyped continuationTyped

/-- A genuine saved store has an existential extension of the supplied world;
every further path extends that same saved world and retains store typing. -/
theorem ComputationFunctionPrepares.runtime_checkpoint_world_extension
    {ChildElab : LocalNameTable → Resolved.Context → Syntax.Expr → Core.Expr → Core.Ty → Prop}
    (childCoreType : ∀ {table context source core type},
      ChildElab table context source core type → Core.HasType context.values core type)
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {declaration : Syntax.FunctionDecl}
    {arguments : List TypedRuntimeArgument} {prepared : PreparedRuntimeFunction}
    (preparation : ComputationFunctionPrepares ChildElab types owner declaration arguments prepared)
    {world : Core.StoreTyping} {store : Core.Store}
    (argumentsTyped : ∀ argument ∈ arguments, Core.RuntimeValueHasType world argument.value argument.type)
    (storeTyped : Core.StoreHasTypes world store)
    {continuation : List Core.Frame} {resultType : Core.Ty}
    (continuationTyped : Core.ContinuationHasType world continuation prepared.returnType resultType)
    {spent : Nat} {checkpoint : Core.State}
    (exhausted : Core.runStateful spent
      ⟨.eval prepared.core prepared.inputs.environment.values, continuation, store⟩ = .outOfFuel checkpoint) :
    ∃ savedWorld, Core.WorldExtends world savedWorld ∧ Core.RuntimeStoreHasTypes savedWorld checkpoint.store ∧
      ∀ {steps next}, Core.Steps steps checkpoint next →
        ∃ future, Core.WorldExtends savedWorld future ∧ Core.RuntimeStoreHasTypes future next.store := by
  have environmentTyped :=
    checkpoint_prepared_runtime_environment preparation.parameters argumentsTyped
  exact preparation.body.runtime_checkpoint_world_extension childCoreType
    (by simpa only [LocalInputs.toTypeInputs_context] using environmentTyped) storeTyped continuationTyped exhausted

end Solcore.Frontend
