import Solcore.Frontend.ClosedSourceOwnerReflectionProperties
import Solcore.Frontend.ClosedSourceOwnerBudgetProperties
import Solcore.Frontend.SelfApplicationCallNonreturnProperties
import Solcore.Frontend.ClosedSourceEvaluationProperties

/- Old failures and both independent original controls precede reflection.
An observed mapped endpoint is arbitrary, not assumed to be in the image. -/
set_option autoImplicit false
namespace Tests.OwnerReflectionBoundaries
open Solcore Solcore.Frontend
private abbrev V := RuntimeValue
private abbrev E := ClosedSourceExpressionEvaluates
private abbrev B := ClosedSourceBodyEvaluates
private def owner (n : Nat) : Resolved.DeclarationId :=
  ⟨⟨.main,⟨[⟨"OwnerReflectionBoundary",by decide⟩],by decide⟩⟩,n⟩
private def co := owner 13
private def so := owner 313
private def fo := owner 913
private def id (o : Resolved.DeclarationId) (n : Nat) : Resolved.LocalId := ⟨o,n⟩
private def span (n : Nat) : Syntax.SourceSpan := ⟨⟨.main,"owner-reflection-boundary.sol"⟩,n,n+1⟩
private def name (n : Nat) (text : String) : Syntax.Identifier := ⟨span n,text⟩
private def ref (n : Nat) (text : String) : Syntax.Expr := ⟨span n,.identifier (name (n+1) text)⟩
private def call (f x : Syntax.Expr) : Syntax.Expr := ⟨span 80,.call f ⟨span 81,[x]⟩⟩
private def returning (source : Syntax.Expr) : Syntax.Block := ⟨span 90,[⟨span 91,.returnStmt (some source)⟩]⟩
private def source (n : Nat) (text : String) (loop : Bool) : Syntax.Expr :=
  ⟨span n,.lambda (span (n+1)) ⟨span (n+2),[⟨span (n+3),.inferred (name (n+4) text)⟩]⟩ none
    (returning (if loop then call (ref (n+5) text) (ref (n+7) text) else ref (n+5) text))⟩
private def identity := source 100 "p" false
private def selfCall := call (source 120 "q" true) (source 140 "r" true)
private def nested : V := .sourceClosure identity so [("p",id fo 7),("p",id so 7)]
  [(id fo 7,.cellRef .word 701),(id fo 7,.hostFunction .storageRead)]
private def core : V := .coreClosure .unit .word (.var 99) [nested,.cellRef .word 702]
private def payload : V := .pair nested (.pair core (.cellRef .word 703))
private def names : LocalNameTable := [("f",id co 1),("g",id co 2),("x",id co 3),("p",id co 99),("x",id fo 3)]
private def captured : Resolved.LocalScope V :=
  [(id fo 1,.unit),(id co 1,.hostFunction .storageWrite),(id co 1,.bool true),
   (id co 2,core),(id co 3,payload),(id co 3,.unit),(id co 100,.bool false),(id fo 3,.unit)]
private def store : List V := [payload,.cellRef .word 900,core,.hostFunction .storageWrite]
private def saved : V := .sourceClosure identity co names captured
private def failures : List Syntax.Expr :=
  [call (ref 10 "f") (ref 12 "x"),call (ref 14 "g") (ref 16 "x"),
   ⟨span 20,.unary ⟨span 21,.logicalNot⟩ (ref 22 "x")⟩,
   ⟨span 30,.unary ⟨span 31,.bitNot⟩ (ref 32 "x")⟩,ref 40 "missing",selfCall]
private abbrev mn (mapping : Resolved.DeclarationId → Resolved.DeclarationId) :=
  LocalNameTable.mapIds (ownerLocalIdMap mapping) names
private abbrev mc (mapping : Resolved.DeclarationId → Resolved.DeclarationId) := mapRuntimeCapturedOwners mapping captured
private abbrev ms (mapping : Resolved.DeclarationId → Resolved.DeclarationId) := store.map (RuntimeValue.mapOwners mapping)
private def observed (mapping : Resolved.DeclarationId → Resolved.DeclarationId) : V :=
  .sourceClosure identity (mapping co) (mn mapping) (mc mapping)

private theorem old_inputs (n : Nat) :
    E co names captured store (ref 10 "f") (.hostFunction .storageWrite) store ∧
    E co names captured store (ref 14 "g") core store ∧
    E co names captured store (ref n "x") payload store := by
  refine ⟨.reference .head (.tail (by decide) .head),
    .reference (.tail (by decide) .head) (.tail (by decide) (.tail (by decide) (.tail (by decide) .head))),?_⟩
  exact .reference (.tail (by change "f" ≠ "x"; decide) (.tail (by change "g" ≠ "x"; decide) .head))
    (.tail (by decide) (.tail (by decide) (.tail (by decide) (.tail (by decide) .head))))
private theorem old_self (budget : Nat) :
    evaluateClosedSourceExpression? budget co names captured store selfCall = none :=
  directSelfApplication_none (left:=source 120 "q" true) (right:=source 140 "r" true)
    (leftName:=name 124 "q") .inferred (.returning rfl rfl)
    (rightName:=name 144 "r") .inferred (.returning rfl rfl) co names captured store (span 80) (span 81) budget
private theorem old_none (expression : Syntax.Expr) (member : expression ∈ failures) (budget : Nat) :
    evaluateClosedSourceExpression? budget co names captured store expression = none := by
  simp only [failures,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first
    | exact old_self budget
    | rcases budget with _ | (_ | n)
      all_goals simp [evaluateClosedSourceExpression?,ref,name,call,names,captured,
        LocalNameTable.lookup?,Resolved.LocalScope.lookup?,id,co,fo,owner,core,payload]
private theorem old_body_none (expression : Syntax.Expr) (member : expression ∈ failures) (budget : Nat) :
    evaluateClosedSourceBody? budget co names captured store (returning expression) = none := by
  cases budget with
  | zero => simp only [evaluateClosedSourceBody?]
  | succ n => simpa only [returning,evaluateClosedSourceBody?] using old_none expression member n
private theorem old_no_original (expression : Syntax.Expr) (member : expression ∈ failures) :
    (∀ value final, ¬ E co names captured store expression value final) ∧
    (∀ value final, ¬ B co names captured store (returning expression) value final) := by
  constructor
  · intro value final original
    obtain ⟨budget,eventual⟩ := evaluateClosedSourceExpression?_eventually_complete original
    have ran := eventual budget (Nat.le_refl _)
    rw [old_none expression member budget] at ran
    cases ran
  · intro value final original
    obtain ⟨budget,eventual⟩ := evaluateClosedSourceBody?_eventually_complete original
    have ran := eventual budget (Nat.le_refl _)
    rw [old_body_none expression member budget] at ran
    cases ran

/-- Independent old absences and non-successes forbid every actual mapped endpoint, without a failure classifier. -/
theorem old_failures_reflect_no_mapped_success
    (mapping : Resolved.DeclarationId → Resolved.DeclarationId) (injective : Function.Injective mapping) :
    (∀ n, E co names captured store (ref n "x") payload store) ∧
    E co names captured store (ref 10 "f") (.hostFunction .storageWrite) store ∧
    E co names captured store (ref 14 "g") core store ∧
    ∀ expression ∈ failures,
      (∀ budget, evaluateClosedSourceExpression? budget co names captured store expression = none ∧
        evaluateClosedSourceExpression? budget (mapping co) (mn mapping) (mc mapping) (ms mapping) expression = none) ∧
      (∀ budget, evaluateClosedSourceBody? budget co names captured store (returning expression) = none ∧
        evaluateClosedSourceBody? budget (mapping co) (mn mapping) (mc mapping) (ms mapping) (returning expression) = none) ∧
      (∀ value final, ¬ E co names captured store expression value final) ∧
      (∀ value final, ¬ E (mapping co) (mn mapping) (mc mapping) (ms mapping) expression value final) ∧
      (∀ value final, ¬ B co names captured store (returning expression) value final) ∧
      (∀ value final, ¬ B (mapping co) (mn mapping) (mc mapping) (ms mapping) (returning expression) value final) := by
  have inputs := old_inputs
  refine ⟨fun n => (inputs n).2.2,(inputs 12).1,(inputs 16).2.1,?_⟩
  intro expression member
  have noneE := old_none expression member
  have noneB := old_body_none expression member
  have denied := old_no_original expression member
  refine ⟨?_,?_,denied.1,?_,denied.2,?_⟩
  · intro budget
    exact ⟨noneE budget,(evaluateClosedSourceExpression?_mapOwners_none_iff mapping injective
      budget co names captured store expression).mpr (noneE budget)⟩
  · intro budget
    exact ⟨noneB budget,(evaluateClosedSourceBody?_mapOwners_none_iff mapping injective
      budget co names captured store (returning expression)).mpr (noneB budget)⟩
  · intro value final actual
    obtain ⟨before,beforeStore,original,_,_⟩ := (ClosedSourceExpressionEvaluates.mapOwners_iff_exists mapping injective).mp actual
    exact denied.1 before beforeStore original
  · intro value final actual
    obtain ⟨before,beforeStore,original,_,_⟩ := (ClosedSourceBodyEvaluates.mapOwners_iff_exists mapping injective).mp actual
    exact denied.2 before beforeStore original

private theorem old_controls : E co names captured store identity saved store ∧
    E co names captured store (call identity identity) saved store ∧
    B co names captured store (returning identity) saved store :=
  ⟨.creation .inferred,.call .inferred (.creation .inferred) (.creation .inferred)
    (.expression (.reference .head .head)),.expression (.creation .inferred)⟩
private theorem mapped_controls (mapping : Resolved.DeclarationId → Resolved.DeclarationId) :
    E (mapping co) (mn mapping) (mc mapping) (ms mapping) identity (observed mapping) (ms mapping) ∧
    E (mapping co) (mn mapping) (mc mapping) (ms mapping) (call identity identity) (observed mapping) (ms mapping) ∧
    B (mapping co) (mn mapping) (mc mapping) (ms mapping) (returning identity) (observed mapping) (ms mapping) :=
  ⟨.creation .inferred,.call .inferred (.creation .inferred) (.creation .inferred)
    (.expression (.reference .head .head)),.expression (.creation .inferred)⟩
private theorem control_runs (o : Resolved.DeclarationId) (n : LocalNameTable)
    (e : Resolved.LocalScope V) (st : List V) :
    evaluateClosedSourceExpression? 1 o n e st identity = some (.sourceClosure identity o n e,st) ∧
    evaluateClosedSourceExpression? 3 o n e st (call identity identity) = some (.sourceClosure identity o n e,st) ∧
    evaluateClosedSourceBody? 2 o n e st (returning identity) = some (.sourceClosure identity o n e,st) := by
  simp [identity,source,returning,call,evaluateClosedSourceExpression?,evaluateClosedSourceBody?,
    sourceUnaryLambdaShape?,ref,name,LocalNameTable.lookup?,Resolved.LocalScope.lookup?]

/-- Independent mapped creation, identity and body successes permit reflection of arbitrary observed endpoints. -/
theorem actual_successes_have_complete_preimages
    (mapping : Resolved.DeclarationId → Resolved.DeclarationId) (injective : Function.Injective mapping) :
    store ≠ [] ∧
    E (mapping co) (mn mapping) (mc mapping) (ms mapping) identity (observed mapping) (ms mapping) ∧
    E (mapping co) (mn mapping) (mc mapping) (ms mapping) (call identity identity) (observed mapping) (ms mapping) ∧
    B (mapping co) (mn mapping) (mc mapping) (ms mapping) (returning identity) (observed mapping) (ms mapping) ∧
    (∀ actual actualStore, E (mapping co) (mn mapping) (mc mapping) (ms mapping) (call identity identity) actual actualStore →
      ∃ before beforeStore, E co names captured store (call identity identity) before beforeStore ∧
        actual=before.mapOwners mapping ∧ actualStore=beforeStore.map (RuntimeValue.mapOwners mapping) ∧ before=saved ∧ beforeStore=store) ∧
    (∀ actual actualStore, B (mapping co) (mn mapping) (mc mapping) (ms mapping) (returning identity) actual actualStore →
      ∃ before beforeStore, B co names captured store (returning identity) before beforeStore ∧
        actual=before.mapOwners mapping ∧ actualStore=beforeStore.map (RuntimeValue.mapOwners mapping) ∧ before=saved ∧ beforeStore=store) ∧
    (∀ budget actual actualStore, evaluateClosedSourceExpression? budget (mapping co) (mn mapping) (mc mapping)
      (ms mapping) (call identity identity)=some (actual,actualStore) →
      ∃ before beforeStore, evaluateClosedSourceExpression? budget co names captured store (call identity identity)=some (before,beforeStore) ∧
        actual=before.mapOwners mapping ∧ actualStore=beforeStore.map (RuntimeValue.mapOwners mapping) ∧ before=saved ∧ beforeStore=store) ∧
    (∀ budget actual actualStore, evaluateClosedSourceBody? budget (mapping co) (mn mapping) (mc mapping)
      (ms mapping) (returning identity)=some (actual,actualStore) →
      ∃ before beforeStore, evaluateClosedSourceBody? budget co names captured store (returning identity)=some (before,beforeStore) ∧
        actual=before.mapOwners mapping ∧ actualStore=beforeStore.map (RuntimeValue.mapOwners mapping) ∧ before=saved ∧ beforeStore=store) ∧
    (evaluateClosedSourceExpression? 1 co names captured store identity = some (saved,store) ∧
      evaluateClosedSourceExpression? 3 co names captured store (call identity identity) = some (saved,store) ∧
      evaluateClosedSourceBody? 2 co names captured store (returning identity) = some (saved,store)) ∧
    (evaluateClosedSourceExpression? 1 (mapping co) (mn mapping) (mc mapping) (ms mapping) identity = some (observed mapping,ms mapping) ∧
      evaluateClosedSourceExpression? 3 (mapping co) (mn mapping) (mc mapping) (ms mapping) (call identity identity) = some (observed mapping,ms mapping) ∧
      evaluateClosedSourceBody? 2 (mapping co) (mn mapping) (mc mapping) (ms mapping) (returning identity) = some (observed mapping,ms mapping)) := by
  have old := old_controls
  have independentlyMapped := mapped_controls mapping
  have oldRuns := control_runs co names captured store
  have mappedRuns := control_runs (mapping co) (mn mapping) (mc mapping) (ms mapping)
  refine ⟨by decide,independentlyMapped.1,independentlyMapped.2.1,independentlyMapped.2.2,?_,?_,?_,?_,oldRuns,mappedRuns⟩
  · intro actual actualStore successful
    obtain ⟨before,beforeStore,original,values,stores⟩ := (ClosedSourceExpressionEvaluates.mapOwners_iff_exists mapping injective).mp successful
    have exactEndpoint := original.deterministic old.2.1
    exact ⟨before,beforeStore,original,values,stores,exactEndpoint⟩
  · intro actual actualStore successful
    obtain ⟨before,beforeStore,original,values,stores⟩ := (ClosedSourceBodyEvaluates.mapOwners_iff_exists mapping injective).mp successful
    have exactEndpoint := original.deterministic old.2.2
    exact ⟨before,beforeStore,original,values,stores,exactEndpoint⟩
  · intro budget actual actualStore successful
    obtain ⟨before,beforeStore,ran,values,stores⟩ :=
      (evaluateClosedSourceExpression?_mapOwners_some_iff_exists mapping injective).mp successful
    have exactEndpoint := (evaluateClosedSourceExpression?_sound ran).deterministic old.2.1
    exact ⟨before,beforeStore,ran,values,stores,exactEndpoint⟩
  · intro budget actual actualStore successful
    obtain ⟨before,beforeStore,ran,values,stores⟩ :=
      (evaluateClosedSourceBody?_mapOwners_some_iff_exists mapping injective).mp successful
    have exactEndpoint := (evaluateClosedSourceBody?_sound ran).deterministic old.2.2
    exact ⟨before,beforeStore,ran,values,stores,exactEndpoint⟩

private def shift (o : Resolved.DeclarationId) : Resolved.DeclarationId := ⟨o.moduleId,o.declarationIndex+1⟩
private theorem shift_injective : Function.Injective shift := by
  intro left right same
  have modules := congrArg Resolved.DeclarationId.moduleId same
  have indices := congrArg Resolved.DeclarationId.declarationIndex same
  cases left; cases right
  simp only [shift] at modules indices
  cases modules
  have equal := Nat.add_right_cancel indices
  cases equal
  rfl

/-- A non-surjective shift has independent mapped successes but no mapped self-application endpoint. -/
theorem nonsurjective_success_and_nonreturn_controls :
    Function.Injective shift ∧ ¬ Function.Surjective shift ∧
    E (shift co) (mn shift) (mc shift) (ms shift) (call identity identity) (observed shift) (ms shift) ∧
    (∃ before beforeStore, E co names captured store (call identity identity) before beforeStore ∧
      observed shift=before.mapOwners shift ∧ ms shift=beforeStore.map (RuntimeValue.mapOwners shift) ∧ before=saved ∧ beforeStore=store) ∧
    (∀ value final, ¬ E (shift co) (mn shift) (mc shift) (ms shift) selfCall value final) := by
  have actual := (mapped_controls shift).2.1
  have noOnto : ¬ Function.Surjective shift := by
    intro onto
    obtain ⟨before,equal⟩ := onto (owner 0)
    have impossible := congrArg Resolved.DeclarationId.declarationIndex equal
    change before.declarationIndex+1=0 at impossible
    omega
  have reflected := actual_successes_have_complete_preimages shift shift_injective
  have denied := old_failures_reflect_no_mapped_success shift shift_injective
  exact ⟨shift_injective,noOnto,actual,reflected.2.2.2.2.1 _ _ actual,
    (denied.2.2.2 selfCall (by simp [failures])).2.2.2.1⟩

end Tests.OwnerReflectionBoundaries
