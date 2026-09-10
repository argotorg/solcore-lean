import Solcore.Frontend.SourceLambdaEvaluationProperties

/-! Deliberately small callback models isolate raw success from body availability
and from each independent determinism premise. They are not a closed evaluator. -/
set_option autoImplicit false
namespace Tests.SourceLambdaBoundaries
open Solcore Solcore.Frontend
private abbrev Names := List (String × Resolved.LocalId)
private abbrev Captures := List (Resolved.LocalId × RuntimeValue)
private abbrev Store := List RuntimeValue
private def owner : Resolved.DeclarationId :=
  ⟨⟨.main,⟨[⟨"RawLambdaBoundaries",by decide⟩],by decide⟩⟩,153⟩
private def span : Syntax.SourceSpan := ⟨⟨.main,"raw-lambda-boundaries.sol"⟩,0,37⟩
private def ref (name : String) : Syntax.Expr := ⟨span,.identifier ⟨span,name⟩⟩
private def body : Syntax.Block := ⟨span,[⟨span,.returnStmt (some (ref "x"))⟩]⟩
private def original : Syntax.Expr :=
  ⟨span,.lambda span ⟨span,[⟨span,.inferred ⟨span,"x"⟩⟩]⟩ none body⟩
private def invocation : Syntax.Expr := ⟨span,.call (ref "callee") ⟨span,[ref "argument"]⟩⟩
private def NoExpr (_ : Resolved.DeclarationId) (_ : Names) (_ : Captures)
    (_ : Store) (_ : Syntax.Expr) (_ : RuntimeValue) (_ : Store) : Prop := False
private def NoBody (_ : Resolved.DeclarationId) (_ : Names) (_ : Captures)
    (_ : Store) (_ : Syntax.Block) (_ : RuntimeValue) (_ : Store) : Prop := False

theorem creation_is_possible_when_both_callbacks_are_empty
    (source : Syntax.Expr) (name : Syntax.Identifier) (block : Syntax.Block)
    (shape : SourceUnaryLambdaShape source name block)
    (caller : Resolved.DeclarationId) (names : Names) (captured : Captures) (store : Store) :
    SourceLambdaEvaluates NoExpr NoBody caller names captured store source
      (.sourceClosure source caller names captured) store := .creation shape

theorem raw_creation_keeps_any_annotations_and_unevaluated_body
    (parameterAnnotation : Syntax.TypeExpr) (returnAnnotation : Option Syntax.TypeExpr)
    (block : Syntax.Block) (names : Names) (captured : Captures) (store : Store) :
    let source : Syntax.Expr :=
      ⟨span,.lambda span ⟨span,[⟨span,.typed none ⟨span,"x"⟩ parameterAnnotation⟩]⟩ returnAnnotation block⟩
    sourceUnaryLambdaShape? source = some (⟨span,"x"⟩,block) ∧
    SourceLambdaEvaluates NoExpr NoBody owner names captured store source
      (.sourceClosure source owner names captured) store := by
  exact ⟨sourceUnaryLambdaShape?_iff.mpr .typed,.creation .typed⟩

theorem absent_body_evidence_prevents_every_successful_unary_call
    (ChildEval : Resolved.DeclarationId → Names → Captures → Store → Syntax.Expr → RuntimeValue → Store → Prop)
    (caller : Resolved.DeclarationId) (names : Names) (captured : Captures)
    (initial finalStore : Store) (callee argument : Syntax.Expr) (value : RuntimeValue) :
    ¬ SourceLambdaEvaluates ChildEval NoBody caller names captured initial
      ⟨span,.call callee ⟨span,[argument]⟩⟩ value finalStore := by
  intro evaluated
  obtain ⟨_,_,_,_,_,_,_,_,_,_,_,_,impossible⟩ := SourceLambdaEvaluates.call_iff.mp evaluated
  exact impossible

/- The child fixture reads only these two literal identifiers; its argument
choice is explicitly controlled by a supplied set of Boolean outcomes. -/
private inductive ChoiceChild (allowed : Bool → Prop)
    (_caller : Resolved.DeclarationId) (_names : Names) (_captured : Captures) :
    Store → Syntax.Expr → RuntimeValue → Store → Prop where
  | callee {store : Store} : ChoiceChild allowed _ _ _ store (ref "callee")
      (.sourceClosure original owner [] []) store
  | argument {store : Store} {bit : Bool} : allowed bit →
      ChoiceChild allowed _ _ _ store (ref "argument") (.bool bit) store
private def fixedOutcome (source : Syntax.Expr) : Option RuntimeValue :=
  match source.value with
  | .identifier name =>
      if name.value = "callee" then some (.sourceClosure original owner [] [])
      else if name.value = "argument" then some (.bool false) else none
  | _ => none
private theorem fixedChild_outcome
    {caller : Resolved.DeclarationId} {names : Names} {captured : Captures}
    {initial finalStore : Store} {source : Syntax.Expr} {value : RuntimeValue}
    (evaluated : ChoiceChild (fun bit => bit = false) caller names captured initial source value finalStore) :
    fixedOutcome source = some value ∧ finalStore = initial := by
  cases evaluated with
  | callee => exact ⟨rfl,rfl⟩
  | argument bitFalse => cases bitFalse; exact ⟨rfl,rfl⟩
private theorem fixedChild_deterministic
    {caller : Resolved.DeclarationId} {names : Names} {captured : Captures}
    {initial : Store} {source : Syntax.Expr} {left right : RuntimeValue} {leftStore rightStore : Store}
    (first : ChoiceChild (fun bit => bit = false) caller names captured initial source left leftStore)
    (second : ChoiceChild (fun bit => bit = false) caller names captured initial source right rightStore) :
    left = right ∧ leftStore = rightStore := by
  have firstResult := fixedChild_outcome first
  have secondResult := fixedChild_outcome second
  exact ⟨Option.some.inj (firstResult.1.symm.trans secondResult.1),
    firstResult.2.trans secondResult.2.symm⟩

/- This body has an intentional nondeterministic outcome, not source truth. -/
private inductive ChoiceBody (_caller : Resolved.DeclarationId) (_names : Names) (_captured : Captures) :
    Store → Syntax.Block → RuntimeValue → Store → Prop where
  | bit {store : Store} (value : Bool) : ChoiceBody _ _ _ store body (.bool value) store

private theorem bodyChoice (store : Store) (bit : Bool) :
    SourceLambdaEvaluates (ChoiceChild (fun bit => bit = false)) ChoiceBody owner [] []
      store invocation (.bool bit) store :=
  .call .inferred .callee (.argument rfl) (.bit bit)

theorem deterministic_children_do_not_supply_body_determinism (store : Store) :
    (∀ {caller names captured initial source left leftStore right rightStore},
      ChoiceChild (fun bit => bit = false) caller names captured initial source left leftStore →
      ChoiceChild (fun bit => bit = false) caller names captured initial source right rightStore →
      left = right ∧ leftStore = rightStore) ∧
    SourceLambdaEvaluates (ChoiceChild (fun bit => bit = false)) ChoiceBody owner [] []
      store invocation (.bool false) store ∧
    SourceLambdaEvaluates (ChoiceChild (fun bit => bit = false)) ChoiceBody owner [] []
      store invocation (.bool true) store ∧
    (RuntimeValue.bool false ≠ .bool true) :=
  ⟨fixedChild_deterministic,bodyChoice store false,bodyChoice store true,by intro same; cases same⟩

/- A separate deterministic original return-x body reads the matching first
parameter name and value row, with arbitrary actual mixed value and suffix. -/
private inductive HeadBody (_caller : Resolved.DeclarationId) :
    Names → Captures → Store → Syntax.Block → RuntimeValue → Store → Prop where
  | returned {names : Names} {captured : Captures} {id : Resolved.LocalId}
      {value : RuntimeValue} {store : Store} :
      HeadBody _ (("x",id)::names) ((id,value)::captured) store body value store
private theorem headBody_deterministic
    {caller : Resolved.DeclarationId} {names : Names} {captured : Captures}
    {initial : Store} {source : Syntax.Block} {left right : RuntimeValue} {leftStore rightStore : Store}
    (first : HeadBody caller names captured initial source left leftStore)
    (second : HeadBody caller names captured initial source right rightStore) :
    left = right ∧ leftStore = rightStore := by
  cases first
  cases second
  exact ⟨rfl,rfl⟩
private theorem argumentChoice (store : Store) (bit : Bool) :
    SourceLambdaEvaluates (ChoiceChild (fun _ => True)) HeadBody owner [] []
      store invocation (.bool bit) store :=
  .call .inferred .callee (.argument True.intro) .returned

theorem deterministic_bodies_do_not_supply_child_determinism (store : Store) :
    (∀ {caller names captured initial source left leftStore right rightStore},
      HeadBody caller names captured initial source left leftStore →
      HeadBody caller names captured initial source right rightStore →
      left = right ∧ leftStore = rightStore) ∧
    SourceLambdaEvaluates (ChoiceChild (fun _ => True)) HeadBody owner [] []
      store invocation (.bool false) store ∧
    SourceLambdaEvaluates (ChoiceChild (fun _ => True)) HeadBody owner [] []
      store invocation (.bool true) store ∧
    (RuntimeValue.bool false ≠ .bool true) :=
  ⟨headBody_deterministic,argumentChoice store false,argumentChoice store true,by intro same; cases same⟩

theorem separate_callback_determinism_laws_recover_exact_call_results
    (store : Store) {value : RuntimeValue} {finalStore : Store}
    (evaluated : SourceLambdaEvaluates (ChoiceChild (fun bit => bit = false)) HeadBody
      owner [] [] store invocation value finalStore) : value = .bool false ∧ finalStore = store := by
  have exactCall : SourceLambdaEvaluates (ChoiceChild (fun bit => bit = false)) HeadBody
      owner [] [] store invocation (.bool false) store :=
    .call .inferred .callee (.argument rfl) .returned
  exact SourceLambdaEvaluates.deterministic
    (ChildEval := ChoiceChild (fun bit => bit = false)) (BodyEval := HeadBody)
    fixedChild_deterministic headBody_deterministic evaluated exactCall

end Tests.SourceLambdaBoundaries
