import Solcore.Frontend.ClosedSource

/- Original fresh binding witnesses precede all bounded-search consequences.
Repeated shadowing retains arbitrary mixed values and the entire actual store. -/
set_option autoImplicit false
namespace Tests.DataBodyDepthShadowing
open Solcore Solcore.Frontend

private def reference (span : Syntax.SourceSpan) (name : Syntax.Identifier) : Syntax.Expr :=
  ⟨span,.identifier name⟩
private def statements (spans : Fin 3 → Syntax.SourceSpan) (name : Syntax.Identifier)
    (annotation : Option Syntax.TypeExpr) : Nat → List Syntax.Statement
  | 0 => [⟨spans 0,.returnStmt (some (reference (spans 2) name))⟩]
  | n + 1 => ⟨spans 1,.letDecl name annotation (some (reference (spans 2) name))⟩ ::
      statements spans name annotation n
private def source (bodySpan : Syntax.SourceSpan) (spans : Fin 3 → Syntax.SourceSpan)
    (name : Syntax.Identifier) (annotation : Option Syntax.TypeExpr) (n : Nat) : Syntax.Block :=
  ⟨bodySpan,statements spans name annotation n⟩

private theorem admitted_chain (bodySpan : Syntax.SourceSpan) (spans : Fin 3 → Syntax.SourceSpan)
    (name : Syntax.Identifier) (annotation : Option Syntax.TypeExpr) (n : Nat) :
    ClosedSourceDataBody (source bodySpan spans name annotation n) := by
  induction n with
  | zero => exact .expression .reference
  | succ n ih => exact .binding .reference ih

private theorem bound (bodySpan : Syntax.SourceSpan) (spans : Fin 3 → Syntax.SourceSpan)
    (name : Syntax.Identifier) (annotation : Option Syntax.TypeExpr) (n : Nat) :
    closedSourceDataBodyDepthBound (source bodySpan spans name annotation n) = n + 2 := by
  induction n with
  | zero => simp only [source,statements,closedSourceDataBodyDepthBound,reference,closedSourceDataDepthBound]
  | succ n ih =>
      change closedSourceDataBodyDepthBound
        ⟨bodySpan,⟨spans 1,.letDecl name annotation (some (reference (spans 2) name))⟩ ::
          statements spans name annotation n⟩ = _
      rw [closedSourceDataBodyDepthBound]
      change max (closedSourceDataDepthBound (reference (spans 2) name))
        (closedSourceDataBodyDepthBound (source bodySpan spans name annotation n)) + 1 = _
      rw [ih]
      simp only [reference,closedSourceDataDepthBound]
      omega

private theorem original (bodySpan : Syntax.SourceSpan) (spans : Fin 3 → Syntax.SourceSpan)
    (name : Syntax.Identifier) (annotation : Option Syntax.TypeExpr) (n : Nat)
    (owner : Resolved.DeclarationId) (names : LocalNameTable)
    (captured : Resolved.LocalScope RuntimeValue) (store : List RuntimeValue)
    (id : Resolved.LocalId) (value : RuntimeValue)
    (named : LocalNameTable.Lookup names name.value id)
    (found : Resolved.LocalScope.Lookup captured id value) :
    ClosedSourceBodyEvaluates owner names captured store
      (source bodySpan spans name annotation n) value store := by
  induction n generalizing names captured id with
  | zero => exact .expression (.reference named found)
  | succ n ih =>
      have initializer : ClosedSourceExpressionEvaluates owner names captured store
          (reference (spans 2) name) value store := .reference named found
      have tail := ih ((name.value,Resolved.freshLocalId owner (names.map Prod.snd))::names)
        ((Resolved.freshLocalId owner (names.map Prod.snd),value)::captured)
        (Resolved.freshLocalId owner (names.map Prod.snd)) .head .head
      cases annotation with
      | none => exact .inferred initializer tail
      | some annotation => exact .binding initializer tail

private theorem before (bodySpan : Syntax.SourceSpan) (spans : Fin 3 → Syntax.SourceSpan)
    (name : Syntax.Identifier) (annotation : Option Syntax.TypeExpr) (n budget : Nat)
    (owner : Resolved.DeclarationId) (names : LocalNameTable)
    (captured : Resolved.LocalScope RuntimeValue) (store : List RuntimeValue)
    (small : budget ≤ n + 1) :
    evaluateClosedSourceBody? budget owner names captured store
      (source bodySpan spans name annotation n) = none := by
  induction n generalizing budget names captured store with
  | zero =>
      cases budget with
      | zero => simp only [evaluateClosedSourceBody?]
      | succ budget =>
          have zero : budget = 0 := by omega
          subst budget
          simp only [source,statements,evaluateClosedSourceBody?,evaluateClosedSourceExpression?]
  | succ n ih =>
      cases budget with
      | zero => simp only [evaluateClosedSourceBody?]
      | succ budget =>
          cases child : evaluateClosedSourceExpression? budget owner names captured store
              (reference (spans 2) name) with
          | none => simp only [source,statements,evaluateClosedSourceBody?,child,bind,Option.bind_none]
          | some endpoint =>
              obtain ⟨value,middleStore⟩ := endpoint
              have tail := ih budget
                ((name.value,Resolved.freshLocalId owner (names.map Prod.snd))::names)
                ((Resolved.freshLocalId owner (names.map Prod.snd),value)::captured)
                middleStore (by omega)
              simpa only [source,statements,evaluateClosedSourceBody?,child,bind,Option.bind_some] using tail

/-- Every typed or inferred shadowing chain has the exact source-depth boundary,
without uniqueness, typing, foreign-owner exclusions or an empty store premise. -/
theorem arbitrary_fresh_shadowing_depth (bodySpan : Syntax.SourceSpan)
    (spans : Fin 3 → Syntax.SourceSpan) (name : Syntax.Identifier)
    (annotation : Option Syntax.TypeExpr) (n extra : Nat)
    (owner : Resolved.DeclarationId) (names : LocalNameTable)
    (captured : Resolved.LocalScope RuntimeValue) (store : List RuntimeValue)
    (id : Resolved.LocalId) (value : RuntimeValue)
    (named : LocalNameTable.Lookup names name.value id)
    (found : Resolved.LocalScope.Lookup captured id value) :
    let body := source bodySpan spans name annotation n
    ClosedSourceDataBody body ∧ closedSourceDataBodyDepthBound body = n + 2 ∧
    ClosedSourceBodyEvaluates owner names captured store body value store ∧
    evaluateClosedSourceBody? (n + 1) owner names captured store body = none ∧
    evaluateClosedSourceBody? (n + 2 + extra) owner names captured store body = some (value,store) ∧
    (∀ actual final, evaluateClosedSourceBody? (n + 2 + extra) owner names captured store body =
      some (actual,final) ↔ actual = value ∧ final = store) := by
  intro body
  have gate := admitted_chain bodySpan spans name annotation n
  have depth : closedSourceDataBodyDepthBound body = n + 2 :=
    bound bodySpan spans name annotation n
  have enough : closedSourceDataBodyDepthBound body ≤ n + 2 + extra := by omega
  have witnessed := original bodySpan spans name annotation n owner names captured store id value named found
  refine ⟨gate,depth,witnessed,before bodySpan spans name annotation n _ owner names captured store (Nat.le_refl _),
    gate.evaluates_at_depthBound witnessed enough,?_⟩
  intro actual final
  rw [gate.evaluate_at_depthBound_iff enough]
  exact ⟨fun evaluated => evaluated.deterministic witnessed,by rintro ⟨rfl,rfl⟩; exact witnessed⟩

end Tests.DataBodyDepthShadowing
