import Solcore.Frontend.RuntimeValue
import Solcore.Resolved.FreshIdentity

/-!
Opt-in original source closure construction and unary call sequencing over mixed values.
Unmarked syntax does not establish canonical runtime staging: annotation meanings are
never inspected. These success rules do not close the supplied callbacks recursively
or classify failures, divergence, costs or effects of unsuccessful computations.
-/

set_option autoImplicit false

namespace Solcore.Frontend

/-- Unmarked unary syntax only; annotation meaning and canonical staging are not checked. -/
inductive SourceUnaryLambdaShape : Syntax.Expr → Syntax.Identifier → Syntax.Block → Prop where
  | inferred {span keyword parametersSpan parameterSpan : Syntax.SourceSpan}
      {name : Syntax.Identifier} {annotation : Option Syntax.TypeExpr} {body : Syntax.Block} :
      SourceUnaryLambdaShape
        ⟨span, .lambda keyword ⟨parametersSpan, [⟨parameterSpan, .inferred name⟩]⟩ annotation body⟩
        name body
  | typed {span keyword parametersSpan parameterSpan : Syntax.SourceSpan}
      {name : Syntax.Identifier} {parameterAnnotation : Syntax.TypeExpr}
      {annotation : Option Syntax.TypeExpr} {body : Syntax.Block} :
      SourceUnaryLambdaShape
        ⟨span, .lambda keyword
          ⟨parametersSpan, [⟨parameterSpan, .typed none name parameterAnnotation⟩]⟩ annotation body⟩
        name body

/-- Decode only the original direct unary shape, retaining the name/body verbatim.
Unsupported syntax is absent from this profile, not classified as a runtime fault. -/
def sourceUnaryLambdaShape? (source : Syntax.Expr) : Option (Syntax.Identifier × Syntax.Block) :=
  match source.value with
  | .lambda _ ⟨_, [parameter]⟩ _ body =>
      match parameter.value with
      | .inferred name => some (name, body)
      | .typed none name _ => some (name, body)
      | _ => none
  | _ => none

/-- Creation captures every original row without running the body or taking a heap
snapshot. Calls sequence actual stores through caller callee/argument evaluation and
then the saved source body. Fresh IDs depend on saved name rows only. -/
inductive SourceLambdaEvaluates
    (ChildEval : Resolved.DeclarationId → List (String × Resolved.LocalId) →
      List (Resolved.LocalId × RuntimeValue) → List RuntimeValue → Syntax.Expr →
      RuntimeValue → List RuntimeValue → Prop)
    (BodyEval : Resolved.DeclarationId → List (String × Resolved.LocalId) →
      List (Resolved.LocalId × RuntimeValue) → List RuntimeValue → Syntax.Block →
      RuntimeValue → List RuntimeValue → Prop)
    (owner : Resolved.DeclarationId) (names : List (String × Resolved.LocalId))
    (captured : List (Resolved.LocalId × RuntimeValue)) :
    List RuntimeValue → Syntax.Expr → RuntimeValue → List RuntimeValue → Prop where
  | creation {store : List RuntimeValue} {source : Syntax.Expr}
      {name : Syntax.Identifier} {body : Syntax.Block}
      (shape : SourceUnaryLambdaShape source name body) :
      SourceLambdaEvaluates ChildEval BodyEval owner names captured store source
        (.sourceClosure source owner names captured) store
  | call {initialStore calleeStore argumentStore finalStore : List RuntimeValue}
      {span argumentsSpan : Syntax.SourceSpan} {callee argument source : Syntax.Expr}
      {savedOwner : Resolved.DeclarationId} {savedNames : List (String × Resolved.LocalId)}
      {savedCaptured : List (Resolved.LocalId × RuntimeValue)}
      {name : Syntax.Identifier} {body : Syntax.Block} {argumentValue result : RuntimeValue}
      (shape : SourceUnaryLambdaShape source name body)
      (calleeEvaluation : ChildEval owner names captured initialStore callee
        (.sourceClosure source savedOwner savedNames savedCaptured) calleeStore)
      (argumentEvaluation : ChildEval owner names captured calleeStore argument argumentValue argumentStore)
      (bodyEvaluation : BodyEval savedOwner
        ((name.value, Resolved.freshLocalId savedOwner (savedNames.map Prod.snd)) :: savedNames)
        ((Resolved.freshLocalId savedOwner (savedNames.map Prod.snd), argumentValue) :: savedCaptured)
        argumentStore body result finalStore) :
      SourceLambdaEvaluates ChildEval BodyEval owner names captured initialStore
        ⟨span, .call callee ⟨argumentsSpan, [argument]⟩⟩ result finalStore

end Solcore.Frontend

/-!
## Consolidated module: `Solcore.Frontend.SourceLambdaEvaluationProperties`
-/

/-!
Exact independent shape/operational decomposition and conditional determinism.
No typing, staging, elaboration, row alignment or world assumptions are added.
-/

set_option autoImplicit false

namespace Solcore.Frontend

/-- Shape decoding is exactly the independent original-source judgment. -/
theorem sourceUnaryLambdaShape?_iff {source : Syntax.Expr} {name : Syntax.Identifier}
    {body : Syntax.Block} :
    sourceUnaryLambdaShape? source = some (name, body) ↔ SourceUnaryLambdaShape source name body := by
  constructor
  · intro accepted
    rcases source with ⟨span, source⟩
    cases source <;> simp only [sourceUnaryLambdaShape?, reduceCtorEq] at accepted
    rename_i keyword parameters annotation body
    rcases parameters with ⟨parametersSpan, parameters⟩
    cases parameters with
    | nil => cases accepted
    | cons parameter rest =>
        cases rest with
        | cons next rest => cases accepted
        | nil =>
            rcases parameter with ⟨parameterSpan, parameter⟩
            cases parameter with
            | inferred inferredName =>
                cases Option.some.inj accepted
                exact .inferred
            | typed marker typedName parameterAnnotation =>
                cases marker with
                | some marker => cases accepted
                | none =>
                    cases Option.some.inj accepted
                    exact .typed
            | error => cases accepted
  · intro shape
    cases shape <;> rfl

private theorem shape_unique {source : Syntax.Expr} {leftName rightName : Syntax.Identifier}
    {leftBody rightBody : Syntax.Block}
    (left : SourceUnaryLambdaShape source leftName leftBody)
    (right : SourceUnaryLambdaShape source rightName rightBody) :
    leftName = rightName ∧ leftBody = rightBody :=
  Prod.mk.inj (Option.some.inj
    ((sourceUnaryLambdaShape?_iff.mpr left).symm.trans (sourceUnaryLambdaShape?_iff.mpr right)))

variable {ChildEval : Resolved.DeclarationId → List (String × Resolved.LocalId) →
  List (Resolved.LocalId × RuntimeValue) → List RuntimeValue → Syntax.Expr →
  RuntimeValue → List RuntimeValue → Prop}
variable {BodyEval : Resolved.DeclarationId → List (String × Resolved.LocalId) →
  List (Resolved.LocalId × RuntimeValue) → List RuntimeValue → Syntax.Block →
  RuntimeValue → List RuntimeValue → Prop}

/-- A supported original lambda creates precisely its full captured datum and keeps
the store unchanged, irrespective of the supplied expression/body relations. -/
theorem SourceLambdaEvaluates.creation_iff
    {owner : Resolved.DeclarationId} {names : List (String × Resolved.LocalId)}
    {captured : List (Resolved.LocalId × RuntimeValue)} {initialStore finalStore : List RuntimeValue}
    {source : Syntax.Expr} {name : Syntax.Identifier} {body : Syntax.Block} {value : RuntimeValue}
    (shape : SourceUnaryLambdaShape source name body) :
    SourceLambdaEvaluates ChildEval BodyEval owner names captured initialStore source value finalStore ↔
      value = .sourceClosure source owner names captured ∧ finalStore = initialStore := by
  constructor
  · intro evaluated
    cases shape <;> cases evaluated <;> exact ⟨rfl, rfl⟩
  · rintro ⟨rfl, rfl⟩
    exact .creation shape

/-- Original unary calls expose both caller-side intermediate stores and the exact
saved lexical scope used for the original body with its one fresh argument row. -/
theorem SourceLambdaEvaluates.call_iff
    {owner : Resolved.DeclarationId} {names : List (String × Resolved.LocalId)}
    {captured : List (Resolved.LocalId × RuntimeValue)} {initialStore finalStore : List RuntimeValue}
    {span argumentsSpan : Syntax.SourceSpan} {callee argument : Syntax.Expr} {result : RuntimeValue} :
    SourceLambdaEvaluates ChildEval BodyEval owner names captured initialStore
      ⟨span, .call callee ⟨argumentsSpan, [argument]⟩⟩ result finalStore ↔
      ∃ source savedOwner savedNames savedCaptured name body calleeStore argumentValue argumentStore,
        SourceUnaryLambdaShape source name body ∧
        ChildEval owner names captured initialStore callee
          (.sourceClosure source savedOwner savedNames savedCaptured) calleeStore ∧
        ChildEval owner names captured calleeStore argument argumentValue argumentStore ∧
        BodyEval savedOwner
          ((name.value, Resolved.freshLocalId savedOwner (savedNames.map Prod.snd)) :: savedNames)
          ((Resolved.freshLocalId savedOwner (savedNames.map Prod.snd), argumentValue) :: savedCaptured)
          argumentStore body result finalStore := by
  constructor
  · intro evaluated
    cases evaluated with
    | creation shape => cases shape
    | call shape calleeEvaluation argumentEvaluation bodyEvaluation =>
        exact ⟨_, _, _, _, _, _, _, _, _, shape, calleeEvaluation, argumentEvaluation, bodyEvaluation⟩
  · rintro ⟨_, _, _, _, _, _, _, _, _, shape, calleeEvaluation, argumentEvaluation, bodyEvaluation⟩
    exact .call shape calleeEvaluation argumentEvaluation bodyEvaluation

/-- Value/store determinism follows only when each fixed callback is deterministic.
This success-only law says nothing about failing or diverging effect prefixes. -/
theorem SourceLambdaEvaluates.deterministic
    (childDeterministic : ∀ {owner names captured initialStore source left leftStore right rightStore},
      ChildEval owner names captured initialStore source left leftStore →
      ChildEval owner names captured initialStore source right rightStore →
      left = right ∧ leftStore = rightStore)
    (bodyDeterministic : ∀ {owner names captured initialStore source left leftStore right rightStore},
      BodyEval owner names captured initialStore source left leftStore →
      BodyEval owner names captured initialStore source right rightStore →
      left = right ∧ leftStore = rightStore)
    {owner : Resolved.DeclarationId} {names : List (String × Resolved.LocalId)}
    {captured : List (Resolved.LocalId × RuntimeValue)} {initialStore : List RuntimeValue}
    {source : Syntax.Expr} {left right : RuntimeValue} {leftStore rightStore : List RuntimeValue}
    (first : SourceLambdaEvaluates ChildEval BodyEval owner names captured initialStore source left leftStore)
    (second : SourceLambdaEvaluates ChildEval BodyEval owner names captured initialStore source right rightStore) :
    left = right ∧ leftStore = rightStore := by
  cases first with
  | creation shape =>
      obtain ⟨value, store⟩ := (creation_iff shape).mp second
      exact ⟨value.symm, store.symm⟩
  | call shape calleeEvaluation argumentEvaluation bodyEvaluation =>
      obtain ⟨_, _, _, _, _, _, _, _, _, otherShape, otherCallee, otherArgument, otherBody⟩ :=
        call_iff.mp second
      obtain ⟨sameCallee, sameCalleeStore⟩ := childDeterministic calleeEvaluation otherCallee
      cases sameCallee
      cases sameCalleeStore
      obtain ⟨sameArgument, sameArgumentStore⟩ := childDeterministic argumentEvaluation otherArgument
      cases sameArgument
      cases sameArgumentStore
      obtain ⟨sameName, sameBody⟩ := shape_unique shape otherShape
      cases sameName
      cases sameBody
      exact bodyDeterministic bodyEvaluation otherBody

end Solcore.Frontend
