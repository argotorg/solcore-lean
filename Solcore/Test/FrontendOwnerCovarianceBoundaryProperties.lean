import Solcore.Frontend.SelfApplicationCallNonreturnProperties
import Solcore.Frontend.ClosedSourceEvaluatorOwnerProperties

/- Independent old evaluator failures precede owner covariance. None does not
classify failure, and inert host/Core payloads are not dispatched by these calls. -/
set_option autoImplicit false
namespace Tests.OwnerCovarianceBoundaries
open Solcore Solcore.Frontend
private abbrev V := RuntimeValue
private abbrev E := ClosedSourceExpressionEvaluates
private def owner (n : Nat) : Resolved.DeclarationId :=
  ⟨⟨.main,⟨[⟨"OwnerOptionBoundary",by decide⟩],by decide⟩⟩,n⟩
private def co := owner 12
private def so := owner 312
private def fo := owner 912
private def id (o : Resolved.DeclarationId) (n : Nat) : Resolved.LocalId := ⟨o,n⟩
private def span (n : Nat) : Syntax.SourceSpan := ⟨⟨.main,"owner-option-boundary.sol"⟩,n,n+1⟩
private def name (n : Nat) (text : String) : Syntax.Identifier := ⟨span n,text⟩
private def ref (n : Nat) (text : String) : Syntax.Expr := ⟨span n,.identifier (name (n+1) text)⟩
private def unit : Syntax.Expr := ⟨span 1,.tuple ⟨span 2,[]⟩⟩
private def nested : V := .sourceClosure unit so [("x",id fo 3),("x",id so 8)]
  [(id fo 3,.cellRef .word 701),(id fo 3,.hostFunction .storageRead)]
private def core : V := .coreClosure .unit .word (.var 99) [nested,.cellRef .word 702]
private def payload : V := .pair nested (.pair core (.cellRef .word 703))
private def names : LocalNameTable :=
  [("f",id co 1),("g",id co 2),("x",id co 3),("q",id co 99),("hole",id co 404),
   ("x",id fo 3),("q",id fo 8),("f",id co 9)]
private def captured : Resolved.LocalScope V :=
  [(id fo 1,.unit),(id co 1,.hostFunction .storageWrite),(id co 1,.bool true),
   (id co 2,core),(id co 3,payload),(id co 3,.unit),(id co 99,.bool true),
   (id co 405,.bool false),(id co 406,.hostFunction .storageRead),(id fo 3,.unit)]
private def store : List V := [payload,.cellRef .word 900,core,.hostFunction .storageWrite]
private def call (f x : Syntax.Expr) : Syntax.Expr := ⟨span 80,.call f ⟨span 81,[x]⟩⟩
private def failures : List Syntax.Expr :=
  [ref 10 "missing",ref 12 "hole",call (ref 14 "f") (ref 16 "x"),call (ref 18 "g") (ref 20 "x"),
   ⟨span 30,.conditional (ref 31 "x") (span 32) unit (span 33) unit⟩,
   ⟨span 40,.unary ⟨span 41,.logicalNot⟩ (ref 42 "x")⟩,
   ⟨span 50,.unary ⟨span 51,.bitNot⟩ (ref 52 "x")⟩,
   ⟨span 60,.binary (ref 61 "x") ⟨span 62,.add⟩ unit⟩]
private def badBody (typed : Bool) : Syntax.Block :=
  ⟨span 90,[⟨span 91,.letDecl (name 92 "q") (if typed then some ⟨span 93,.tuple []⟩ else none)
    (some (ref 94 "x"))⟩,⟨span 95,.returnStmt
      (some ⟨span 96,.unary ⟨span 97,.logicalNot⟩ (ref 98 "q")⟩)⟩]⟩
private def selfBody (n : Nat) (text : String) : Syntax.Block :=
  ⟨span n,[⟨span (n+1),.returnStmt (some (call (ref (n+2) text) (ref (n+4) text)))⟩]⟩
private def source (n : Nat) (text : String) : Syntax.Expr :=
  ⟨span (n+6),.lambda (span (n+7))
    ⟨span (n+8),[⟨span (n+9),.inferred (name (n+10) text)⟩]⟩ none (selfBody n text)⟩

private theorem independent_inputs (a b c : Nat) :
    E co names captured store (ref a "f") (.hostFunction .storageWrite) store ∧
    E co names captured store (ref b "g") core store ∧
    E co names captured store (ref c "x") payload store ∧
    evaluateClosedSourceExpression? 1 co names captured store (ref a "f") = some (.hostFunction .storageWrite,store) ∧
    evaluateClosedSourceExpression? 1 co names captured store (ref b "g") = some (core,store) ∧
    evaluateClosedSourceExpression? 1 co names captured store (ref c "x") = some (payload,store) := by
  have host : E co names captured store (ref a "f") (.hostFunction .storageWrite) store :=
    .reference .head (.tail (by decide) .head)
  have closure : E co names captured store (ref b "g") core store :=
    .reference (.tail (by change "f" ≠ "g"; decide) .head) (.tail (by decide) (.tail (by decide) (.tail (by decide) .head)))
  have argument : E co names captured store (ref c "x") payload store :=
    .reference (.tail (by change "f" ≠ "x"; decide) (.tail (by change "g" ≠ "x"; decide) .head))
      (.tail (by decide) (.tail (by decide) (.tail (by decide) (.tail (by decide) .head))))
  refine ⟨host,closure,argument,?_,?_,?_⟩
  all_goals simp [evaluateClosedSourceExpression?,ref,name,names,captured,
    LocalNameTable.lookup?,Resolved.LocalScope.lookup?,id,co,fo,owner]

private theorem independent_shadow :
    let fresh := Resolved.freshLocalId co (names.map Prod.snd)
    fresh = id co 405 ∧ captured.lookup? fresh = some (.bool false) ∧
    E co (("q",fresh)::names) ((fresh,payload)::captured) store (ref 98 "q") payload store ∧
    evaluateClosedSourceExpression? 1 co (("q",fresh)::names) ((fresh,payload)::captured)
      store (ref 98 "q") = some (payload,store) := by
  intro fresh
  have freshExact : fresh = id co 405 := by decide
  refine ⟨freshExact,?_,.reference .head .head,?_⟩
  · rw [freshExact]; rfl
  · simp [evaluateClosedSourceExpression?,ref,name,LocalNameTable.lookup?,Resolved.LocalScope.lookup?]

private theorem independent_failures (expression : Syntax.Expr) (member : expression ∈ failures) (budget : Nat) :
    evaluateClosedSourceExpression? budget co names captured store expression = none := by
  simp only [failures,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    rcases budget with _ | (_ | n)
    all_goals simp [evaluateClosedSourceExpression?,ref,name,call,names,captured,
      LocalNameTable.lookup?,Resolved.LocalScope.lookup?,id,co,fo,owner,core,payload]

private theorem independent_bad_body (typed : Bool) (budget : Nat) :
    evaluateClosedSourceBody? budget co names captured store (badBody typed) = none := by
  rcases budget with _ | (_ | (_ | (_ | n)))
  all_goals simp [badBody,evaluateClosedSourceBody?,evaluateClosedSourceExpression?,ref,name,names,captured,
    LocalNameTable.lookup?,Resolved.LocalScope.lookup?,id,co,fo,owner,payload]

private theorem independent_low :
    evaluateClosedSourceExpression? 0 co names captured store (ref 16 "x") = none ∧
    evaluateClosedSourceExpression? 1 co names captured store ⟨span 15,.group (ref 16 "x")⟩ = none := by
  simp [evaluateClosedSourceExpression?]

private theorem independent_creation (n : Nat) (text : String) :
    E co names captured store (source n text) (.sourceClosure (source n text) co names captured) store ∧
    evaluateClosedSourceExpression? 1 co names captured store (source n text) =
      some (.sourceClosure (source n text) co names captured,store) := by
  refine ⟨.creation .inferred,?_⟩
  simp [source,evaluateClosedSourceExpression?,sourceUnaryLambdaShape?]

private theorem independent_self (budget : Nat) :
    evaluateClosedSourceExpression? budget co names captured store (call (source 100 "q") (source 120 "r")) = none := by
  exact directSelfApplication_none (left:=source 100 "q") (right:=source 120 "r")
    (leftName:=name 110 "q") .inferred (.returning rfl rfl)
    (rightName:=name 130 "r") .inferred (.returning rfl rfl)
    co names captured store (span 80) (span 81) budget

private abbrev run (budget : Nat) (expression : Syntax.Expr) :=
  evaluateClosedSourceExpression? budget co names captured store expression
private abbrev mappedRun (mapping : Resolved.DeclarationId → Resolved.DeclarationId)
    (budget : Nat) (expression : Syntax.Expr) :=
  evaluateClosedSourceExpression? budget (mapping co) (LocalNameTable.mapIds (ownerLocalIdMap mapping) names)
    (mapRuntimeCapturedOwners mapping captured) (store.map (RuntimeValue.mapOwners mapping)) expression

/-- Independent successful inputs coexist with distinct old failures; each absence then transports at the same budget. -/
theorem independent_failures_keep_the_same_budget
    (mapping : Resolved.DeclarationId → Resolved.DeclarationId) (injective : Function.Injective mapping) (budget : Nat) :
    store ≠ [] ∧
    E co names captured store (ref 14 "f") (.hostFunction .storageWrite) store ∧
    E co names captured store (ref 18 "g") core store ∧
    E co names captured store (ref 20 "x") payload store ∧
    E co names captured store (ref 16 "x") payload store ∧
    E co names captured store (ref 94 "x") payload store ∧
    run 1 (ref 14 "f") = some (.hostFunction .storageWrite,store) ∧
    run 1 (ref 18 "g") = some (core,store) ∧ run 1 (ref 20 "x") = some (payload,store) ∧
    run 1 (ref 16 "x") = some (payload,store) ∧ run 1 (ref 94 "x") = some (payload,store) ∧
    (∀ expression ∈ failures, run budget expression = none ∧ mappedRun mapping budget expression = none) ∧
    (∀ typed, evaluateClosedSourceBody? budget co names captured store (badBody typed) = none ∧
      evaluateClosedSourceBody? budget (mapping co) (LocalNameTable.mapIds (ownerLocalIdMap mapping) names)
        (mapRuntimeCapturedOwners mapping captured) (store.map (RuntimeValue.mapOwners mapping)) (badBody typed) = none) ∧
    run 0 (ref 16 "x") = none ∧ mappedRun mapping 0 (ref 16 "x") = none ∧
    run 1 ⟨span 15,.group (ref 16 "x")⟩ = none ∧ mappedRun mapping 1 ⟨span 15,.group (ref 16 "x")⟩ = none ∧
    (let fresh := Resolved.freshLocalId co (names.map Prod.snd);
      fresh = id co 405 ∧ captured.lookup? fresh = some (.bool false) ∧
      E co (("q",fresh)::names) ((fresh,payload)::captured) store (ref 98 "q") payload store ∧
      evaluateClosedSourceExpression? 1 co (("q",fresh)::names) ((fresh,payload)::captured)
        store (ref 98 "q") = some (payload,store)) := by
  have inputs := independent_inputs 14 18 20
  have hostArgument := independent_inputs 14 18 16
  have initializer := independent_inputs 14 18 94
  have shadow := independent_shadow
  have failed := fun expression member => independent_failures expression member budget
  have bodyFailed := fun typed => independent_bad_body typed budget
  have low := independent_low
  refine ⟨by decide,inputs.1,inputs.2.1,inputs.2.2.1,hostArgument.2.2.1,initializer.2.2.1,
    inputs.2.2.2.1,inputs.2.2.2.2.1,inputs.2.2.2.2.2,hostArgument.2.2.2.2.2,initializer.2.2.2.2.2,
    ?_,?_,low.1,?_,low.2,?_,shadow⟩
  · intro expression member
    refine ⟨failed expression member,?_⟩
    rw [mappedRun,evaluateClosedSourceExpression?_mapOwners mapping injective,failed expression member,Option.map_none]
  · intro typed
    refine ⟨bodyFailed typed,?_⟩
    rw [evaluateClosedSourceBody?_mapOwners mapping injective,bodyFailed typed,Option.map_none]
  · rw [mappedRun,evaluateClosedSourceExpression?_mapOwners mapping injective,low.1,Option.map_none]
  · rw [mappedRun,evaluateClosedSourceExpression?_mapOwners mapping injective,low.2,Option.map_none]

/-- Distinct self-callers have complete independent creation endpoints but no result at any depth, before and after mapping. -/
theorem self_application_and_complete_saved_fields
    (mapping : Resolved.DeclarationId → Resolved.DeclarationId) (injective : Function.Injective mapping) :
    (∀ n text,
      E co names captured store (source n text) (.sourceClosure (source n text) co names captured) store ∧
      run 1 (source n text) = some (.sourceClosure (source n text) co names captured,store) ∧
      mappedRun mapping 1 (source n text) =
        some (.sourceClosure (source n text) (mapping co) (LocalNameTable.mapIds (ownerLocalIdMap mapping) names)
          (mapRuntimeCapturedOwners mapping captured),store.map (RuntimeValue.mapOwners mapping))) ∧
    (∀ budget, run budget (call (source 100 "q") (source 120 "r")) = none ∧
      mappedRun mapping budget (call (source 100 "q") (source 120 "r")) = none) ∧
    (∀ value final, ¬ E co names captured store (call (source 100 "q") (source 120 "r")) value final) := by
  have creations := independent_creation
  have nonreturn := independent_self
  have noOriginal : ∀ value final, ¬ E co names captured store (call (source 100 "q") (source 120 "r")) value final :=
    fun value final => directSelfApplication_no_original (left:=source 100 "q") (right:=source 120 "r")
      (leftName:=name 110 "q") .inferred (.returning rfl rfl)
      (rightName:=name 130 "r") .inferred (.returning rfl rfl)
      co names captured store (span 80) (span 81) value final
  refine ⟨?_,?_,noOriginal⟩
  · intro n text
    refine ⟨(creations n text).1,(creations n text).2,?_⟩
    rw [mappedRun,evaluateClosedSourceExpression?_mapOwners mapping injective,(creations n text).2]
    simp only [Option.map_some,RuntimeValue.mapOwners_sourceClosure]
  · intro budget
    refine ⟨nonreturn budget,?_⟩
    rw [mappedRun,evaluateClosedSourceExpression?_mapOwners mapping injective,nonreturn budget,Option.map_none]

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

/-- A concrete non-surjective injection is admitted; no inverse owner map is supplied. -/
theorem nonsurjective_injection_is_admitted :
    Function.Injective shift ∧ ¬ Function.Surjective shift ∧
    (∀ budget, run budget (call (source 100 "q") (source 120 "r")) = none ∧
      mappedRun shift budget (call (source 100 "q") (source 120 "r")) = none) := by
  have notOnto : ¬ Function.Surjective shift := by
    intro onto
    obtain ⟨before,equal⟩ := onto (owner 0)
    have impossible := congrArg Resolved.DeclarationId.declarationIndex equal
    change before.declarationIndex+1=0 at impossible
    omega
  have transported := self_application_and_complete_saved_fields shift shift_injective
  exact ⟨shift_injective,notOnto,transported.2.1⟩

end Tests.OwnerCovarianceBoundaries
