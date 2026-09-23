import Solcore.Frontend.ClosedSource

/- A conditional initializer saves every lexical row before a later payload let.
Independent caller and saved lookups drive nested argument and body conditionals. -/
set_option autoImplicit false
namespace Tests.ClosedSourceConditionalClosure
open Solcore Solcore.Frontend

private structure Ranges where
  span : Nat → Syntax.SourceSpan
  outer : Nat → Syntax.SourceSpan
  question : Nat → Syntax.SourceSpan
  colon : Nat → Syntax.SourceSpan
  guard : Nat → Syntax.SourceSpan
  annotation : Syntax.TypeExpr

private structure Lexical where
  owner : Resolved.DeclarationId
  names : LocalNameTable
  captured : Resolved.LocalScope RuntimeValue
  gate : Syntax.Identifier
  payload : Syntax.Identifier
  parameter : Syntax.Identifier
  gateId : Resolved.LocalId
  payloadId : Resolved.LocalId
  choice : Bool
  kept : RuntimeValue
  gateNamed : LocalNameTable.Lookup names gate.value gateId
  gateFound : Resolved.LocalScope.Lookup captured gateId (.bool choice)
  payloadNamed : LocalNameTable.Lookup names payload.value payloadId
  payloadFound : Resolved.LocalScope.Lookup captured payloadId kept
  parameterGate : parameter.value ≠ gate.value
  parameterPayload : parameter.value ≠ payload.value

private def ref (r : Ranges) (name : Syntax.Identifier) : Syntax.Expr :=
  ⟨r.span 0, .identifier name⟩
private def unit (r : Ranges) : Syntax.Expr := ⟨r.span 1, .tuple ⟨r.span 2, []⟩⟩
private def nest (r : Ranges) (gate : Syntax.Identifier) :
    Nat → Syntax.Expr → Syntax.Expr → Syntax.Expr
  | 0, left, _ => left
  | n + 1, left, right =>
      ⟨r.outer n, .conditional ⟨r.guard n, .identifier gate⟩ (r.question n)
        (nest r gate n left right) (r.colon n) (nest r gate n right left)⟩
private def picked (choice : Bool) : Nat → RuntimeValue → RuntimeValue → RuntimeValue
  | 0, left, _ => left
  | n + 1, left, right =>
      if choice then picked choice n left right else picked choice n right left

private theorem nest_original (r : Ranges) (owner : Resolved.DeclarationId)
    (names : LocalNameTable) (captured : Resolved.LocalScope RuntimeValue)
    (store : List RuntimeValue) (gate : Syntax.Identifier) (id : Resolved.LocalId)
    (choice : Bool) (named : LocalNameTable.Lookup names gate.value id)
    (found : Resolved.LocalScope.Lookup captured id (.bool choice))
    (n : Nat) (left right : Syntax.Expr) (lv rv : RuntimeValue)
    (le : ClosedSourceExpressionEvaluates owner names captured store left lv store)
    (re : ClosedSourceExpressionEvaluates owner names captured store right rv store) :
    ClosedSourceExpressionEvaluates owner names captured store
      (nest r gate n left right) (picked choice n lv rv) store := by
  induction n generalizing left right lv rv with
  | zero => exact le
  | succ n ih =>
      cases choice
      · exact .conditionalFalse (.reference named found) (ih right left rv lv re le)
      · exact .conditionalTrue (.reference named found) (ih left right lv rv le re)

private def body (r : Ranges) (l : Lexical) (n : Nat) (typed : Bool) : Syntax.Block :=
  ⟨r.span 3, [⟨r.span 4, .returnStmt (some (nest r l.gate n
    (if typed then ref r l.parameter else ref r l.payload)
    (if typed then ref r l.payload else ref r l.parameter)))⟩]⟩
private def source (r : Ranges) (l : Lexical) (n : Nat) (typed : Bool) : Syntax.Expr :=
  ⟨r.span 5, .lambda (r.span 6) ⟨r.span 7, [⟨r.span 8,
    if typed then .typed none l.parameter r.annotation else .inferred l.parameter⟩]⟩
    none (body r l n typed)⟩
private theorem shape (r : Ranges) (l : Lexical) (n : Nat) (typed : Bool) :
    SourceUnaryLambdaShape (source r l n typed) l.parameter (body r l n typed) := by
  cases typed
  · exact .inferred
  · exact .typed

private theorem fresh_ne {names : LocalNameTable} {name : String} {id : Resolved.LocalId}
    (owner : Resolved.DeclarationId) (named : LocalNameTable.Lookup names name id) :
    Resolved.freshLocalId owner (names.map Prod.snd) ≠ id := by
  intro same
  apply Resolved.freshLocalId_not_mem owner (names.map Prod.snd)
  rw [same]
  exact List.mem_map.mpr ⟨(name, id), named.mem, rfl⟩

private theorem saved_body (r : Ranges) (l : Lexical) (n : Nat) (typed : Bool)
    (argument : RuntimeValue) (store : List RuntimeValue) :
    ClosedSourceBodyEvaluates l.owner
      ((l.parameter.value, Resolved.freshLocalId l.owner (l.names.map Prod.snd)) :: l.names)
      ((Resolved.freshLocalId l.owner (l.names.map Prod.snd), argument) :: l.captured)
      store (body r l n typed)
      (picked l.choice n (if typed then argument else l.kept)
        (if typed then l.kept else argument)) store := by
  apply ClosedSourceBodyEvaluates.expression
  apply nest_original r l.owner _ _ store l.gate l.gateId l.choice
    (.tail l.parameterGate l.gateNamed) (.tail (fresh_ne l.owner l.gateNamed) l.gateFound)
  · cases typed
    · exact .reference (.tail l.parameterPayload l.payloadNamed)
        (.tail (fresh_ne l.owner l.payloadNamed) l.payloadFound)
    · exact .reference .head .head
  · cases typed
    · exact .reference .head .head
    · exact .reference (.tail l.parameterPayload l.payloadNamed)
        (.tail (fresh_ne l.owner l.payloadNamed) l.payloadFound)

private def closure (r : Ranges) (saved : Lexical) (n : Nat) (creation : Bool) : RuntimeValue :=
  .sourceClosure (source r saved n (!creation)) saved.owner saved.names saved.captured
private def producer (r : Ranges) (saved : Lexical) (n : Nat)
    (choose f : Syntax.Identifier) : Syntax.Block :=
  ⟨r.span 9, [⟨r.span 10, .letDecl f none (some
      ⟨r.span 11, .conditional (ref r choose) (r.span 12)
        (source r saved n false) (r.span 13) (source r saved n true)⟩)⟩,
    ⟨r.span 14, .letDecl saved.payload (some r.annotation) (some (unit r))⟩,
    ⟨r.span 15, .returnStmt (some (ref r f))⟩]⟩

variable (r : Ranges) (saved caller : Lexical) (n m : Nat) (store : List RuntimeValue)
  (creation : Bool) (choose f : Syntax.Identifier) (chooseId fId : Resolved.LocalId)
  (chooseNamed : LocalNameTable.Lookup saved.names choose.value chooseId)
  (chooseFound : Resolved.LocalScope.Lookup saved.captured chooseId (.bool creation))
  (different : saved.payload.value ≠ f.value)

include chooseNamed chooseFound different in
theorem original_pre_shadow_closure_is_returned :
    ClosedSourceBodyEvaluates saved.owner saved.names saved.captured store
      (producer r saved n choose f) (closure r saved n creation) store := by
  apply ClosedSourceBodyEvaluates.inferred (boundValue := closure r saved n creation)
    (middleStore := store)
  · cases creation
    · exact .conditionalFalse (.reference chooseNamed chooseFound) (.creation (shape r saved n true))
    · exact .conditionalTrue (.reference chooseNamed chooseFound) (.creation (shape r saved n false))
  · apply ClosedSourceBodyEvaluates.binding ClosedSourceExpressionEvaluates.unit
    apply ClosedSourceBodyEvaluates.expression
    apply ClosedSourceExpressionEvaluates.reference (.tail different .head)
    exact .tail (Resolved.freshLocalId_cons_fresh_ne saved.owner (saved.names.map Prod.snd)) .head

private def argument (r : Ranges) (caller : Lexical) (m : Nat) : Syntax.Expr :=
  nest r caller.gate m (ref r caller.payload) (unit r)
private def argumentValue (caller : Lexical) (m : Nat) : RuntimeValue :=
  picked caller.choice m caller.kept .unit
private def invocation (r : Ranges) (caller : Lexical) (n m : Nat)
    (f : Syntax.Identifier) : Syntax.Expr :=
  ⟨r.span 16, .call ⟨r.span 17, .conditional (ref r caller.gate) (r.span 18)
    (ref r f) (r.span 19) (source r caller n true)⟩
    ⟨r.span 20, [argument r caller m]⟩⟩
private def result (saved caller : Lexical) (n m : Nat) (creation : Bool) : RuntimeValue :=
  if caller.choice then
    picked saved.choice n (if !creation then argumentValue caller m else saved.kept)
      (if !creation then saved.kept else argumentValue caller m)
  else picked caller.choice n (argumentValue caller m) caller.kept

variable (fNamed : LocalNameTable.Lookup caller.names f.value fId)
  (fFound : Resolved.LocalScope.Lookup caller.captured fId (closure r saved n creation))

include fNamed fFound in
private theorem invocation_original :
    ClosedSourceExpressionEvaluates caller.owner caller.names caller.captured store
      (invocation r caller n m f) (result saved caller n m creation) store := by
  have arg := nest_original r caller.owner caller.names caller.captured store
    caller.gate caller.gateId caller.choice caller.gateNamed caller.gateFound m
    (ref r caller.payload) (unit r) caller.kept .unit
    (.reference caller.payloadNamed caller.payloadFound) .unit
  cases h : caller.choice
  · simp only [result, h, Bool.false_eq_true, ↓reduceIte]
    exact .call (shape r caller n true)
      (.conditionalFalse (.reference caller.gateNamed (h ▸ caller.gateFound))
        (.creation (shape r caller n true))) arg
      (by simpa only [argumentValue, h, ↓reduceIte] using
        saved_body r caller n true (argumentValue caller m) store)
  · simp only [result, h, ↓reduceIte]
    exact .call (shape r saved n (!creation))
      (.conditionalTrue (.reference caller.gateNamed (h ▸ caller.gateFound))
        (.reference fNamed fFound)) arg (saved_body r saved n (!creation) _ store)

include chooseNamed chooseFound different fNamed fFound in
theorem returned_closure_composes_with_different_caller :
    ClosedSourceBodyEvaluates saved.owner saved.names saved.captured store
        (producer r saved n choose f) (closure r saved n creation) store ∧
      ClosedSourceExpressionEvaluates caller.owner caller.names caller.captured store
        (invocation r caller n m f) (result saved caller n m creation) store := by
  exact ⟨original_pre_shadow_closure_is_returned r saved n store creation choose f chooseId
    chooseNamed chooseFound different,
    invocation_original r saved caller n m store creation f fId fNamed fFound⟩

include fNamed fFound in
theorem original_caller_composition_has_open_body_compatibility :
    SourceLambdaEvaluates ClosedSourceExpressionEvaluates
      (SourceComputationBodyEvaluates ClosedSourceExpressionEvaluates)
      caller.owner caller.names caller.captured store
      (invocation r caller n m f) (result saved caller n m creation) store := by
  exact closedSourceExpressionEvaluates_call_iff.mp
    (invocation_original r saved caller n m store creation f fId fNamed fFound)

include chooseNamed chooseFound different fNamed fFound in
theorem independent_derivations_are_found_at_all_larger_budgets :
    ∃ required, ∀ budget, required ≤ budget →
      evaluateClosedSourceBody? budget saved.owner saved.names saved.captured store
          (producer r saved n choose f) = some (closure r saved n creation, store) ∧
        evaluateClosedSourceExpression? budget caller.owner caller.names caller.captured store
          (invocation r caller n m f) = some (result saved caller n m creation, store) := by
  have witnesses := returned_closure_composes_with_different_caller r saved caller n m store
    creation choose f chooseId fId chooseNamed chooseFound different fNamed fFound
  obtain ⟨p, producerFound⟩ := evaluateClosedSourceBody?_eventually_complete witnesses.1
  obtain ⟨c, callFound⟩ := evaluateClosedSourceExpression?_eventually_complete witnesses.2
  exact ⟨max p c, fun budget large =>
    ⟨producerFound budget (by omega), callFound budget (by omega)⟩⟩

end Tests.ClosedSourceConditionalClosure
