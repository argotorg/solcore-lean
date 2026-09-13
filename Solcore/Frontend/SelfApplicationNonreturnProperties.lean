import Solcore.Frontend.ClosedSourceEvaluatorCompletenessProperties

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
