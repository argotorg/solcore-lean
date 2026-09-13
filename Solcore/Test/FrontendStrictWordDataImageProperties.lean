import Solcore.Frontend.ClosedSourceDataExpressionProperties
import Solcore.Frontend.StrictWordBinaryProperties
import Solcore.Frontend.LocalExpressionCostExecutionProperties
import Solcore.Resolved.LocalScopeProperties

/- Fourteen independent original paths precede the two data-image conversions.
The left is grouped bitwise negation; mixed Core tails and stores stay opaque. -/
set_option autoImplicit false
namespace Tests.StrictWordDataImages
open Solcore Solcore.Frontend

private def reference (span : Syntax.SourceSpan) (name : Syntax.Identifier) : Syntax.Expr :=
  ⟨span,.identifier name⟩
private def left (spans : Fin 6 → Syntax.SourceSpan) (name : Syntax.Identifier) : Syntax.Expr :=
  ⟨spans 2,.group ⟨spans 3,.unary ⟨spans 4,.bitNot⟩ (reference (spans 5) name)⟩⟩
private def right (span : Syntax.SourceSpan) (name : Syntax.Identifier) : Syntax.Expr :=
  ⟨span,.group (reference name.span name)⟩
private def source (spans : Fin 6 → Syntax.SourceSpan) (rightSpan : Syntax.SourceSpan)
    (leftName rightName : Syntax.Identifier) (operator : Syntax.BinaryOp) : Syntax.Expr :=
  ⟨spans 0,.binary (left spans leftName) ⟨spans 1,operator⟩ (right rightSpan rightName)⟩
private def embedded (environment : Resolved.Environment) : Resolved.LocalScope RuntimeValue :=
  environment.map (fun row => (row.1,RuntimeValue.ofCore row.2))
private def outcomes (a b : Core.Word) : List (Syntax.BinaryOp × Core.Value) :=
  [(.add,.word (a.add b)),(.subtract,.word (a.sub b)),(.multiply,.word (a.mul b)),
   (.divide,.word (a.udiv b)),(.modulo,.word (a.umod b)),(.bitAnd,.word (a.bitAnd b)),
   (.bitOr,.word (a.bitOr b)),(.bitXor,.word (a.bitXor b)),
   (.greater,.bool (decide (a>b))),(.less,.bool (decide (a<b))),(.equal,.bool (a==b)),
   (.notEqual,.bool (!(a==b))),(.lessEqual,.bool (!(decide (a>b)))),
   (.greaterEqual,.bool (!(decide (a<b))))]
private theorem meaning {a b : Core.Word} {op : Syntax.BinaryOp} {value : Core.Value}
    (member : (op,value) ∈ outcomes a b) : StrictWordBinaryDenotes op a b value := by
  simp only [outcomes,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with h | h | h | h | h | h | h | h | h | h | h | h | h | h
  all_goals cases h; constructor
private def overhead : Syntax.BinaryOp → Nat
  | .notEqual | .lessEqual => 5
  | .less => 9
  | .greaterEqual => 11
  | _ => 3
private def resolved (op : Syntax.BinaryOp) (l r : Resolved.Expr) : Resolved.Expr :=
  match op with
  | .add => .binary .wordAdd l r
  | .subtract => .binary .wordSub l r
  | .multiply => .binary .wordMul l r
  | .divide => .binary .wordDiv l r
  | .modulo => .binary .wordMod l r
  | .bitAnd => .binary .wordAnd l r
  | .bitOr => .binary .wordOr l r
  | .bitXor => .binary .wordXor l r
  | .greater => .binary .wordGt l r
  | .equal => .binary .wordEq l r
  | .notEqual => .unary .boolNot (.binary .wordEq l r)
  | .lessEqual => .unary .boolNot (.binary .wordGt l r)
  | .less => .wordLt l r
  | .greaterEqual => .unary .boolNot (.wordLt l r)
  | .logicalAnd | .logicalOr => .unit
private def code (op : Syntax.BinaryOp) (l r : Core.Expr) : Core.Expr :=
  match op with
  | .add => .binary .wordAdd l r
  | .subtract => .binary .wordSub l r
  | .multiply => .binary .wordMul l r
  | .divide => .binary .wordDiv l r
  | .modulo => .binary .wordMod l r
  | .bitAnd => .binary .wordAnd l r
  | .bitOr => .binary .wordOr l r
  | .bitXor => .binary .wordXor l r
  | .greater => .binary .wordGt l r
  | .equal => .binary .wordEq l r
  | .notEqual => .unary .boolNot (.binary .wordEq l r)
  | .lessEqual => .unary .boolNot (.binary .wordGt l r)
  | .less => l.wordLt r
  | .greaterEqual => .unary .boolNot (l.wordLt r)
  | .logicalAnd | .logicalOr => .unit

private theorem mapped_lookup {environment : Resolved.Environment} {id : Resolved.LocalId}
    {value : Core.Value} (found : Resolved.LocalScope.Lookup environment id value) :
    Resolved.LocalScope.Lookup (embedded environment) id (RuntimeValue.ofCore value) := by
  induction found with
  | head => exact .head
  | tail different _ ih => exact .tail different ih
private theorem local_image {owner : Resolved.DeclarationId} {names : LocalNameTable}
    {environment : Resolved.Environment} {store : Core.Store} {original : Syntax.Expr}
    {expected : Core.Value} (gate : ClosedSourceDataExpression original)
    (path : LocalExpressionEvaluates names environment store original expected store) :
    ∀ actual final, ClosedSourceExpressionEvaluates owner names (embedded environment)
      (store.map RuntimeValue.ofCore) original actual final ↔
      actual = RuntimeValue.ofCore expected ∧ final = store.map RuntimeValue.ofCore := by
  intro actual final; constructor
  · intro closed
    obtain ⟨value,finalStore,same,finalSame,previous⟩ := gate.local_evaluates_iff.mp closed
    obtain ⟨rfl,rfl⟩ := previous.deterministic path
    exact ⟨same,finalSame⟩
  · rintro ⟨rfl,rfl⟩
    exact gate.local_evaluates_iff.mpr ⟨expected,store,rfl,rfl,path⟩
private theorem core_image {owner : Resolved.DeclarationId} {names : LocalNameTable}
    {environment : Resolved.Environment} {store : Core.Store} {original : Syntax.Expr}
    {expected : Core.Value} {resolved : Resolved.Expr} {core : Core.Expr}
    (gate : ClosedSourceDataExpression original)
    (resolution : ResolvesLocalExpression names original resolved)
    (lowering : Resolved.Lowers environment.ids resolved core)
    (path : Core.Evaluates environment.values store core expected store) :
    ∀ actual final, ClosedSourceExpressionEvaluates owner names (embedded environment)
      (store.map RuntimeValue.ofCore) original actual final ↔
      actual = RuntimeValue.ofCore expected ∧ final = store.map RuntimeValue.ofCore := by
  intro actual final; constructor
  · intro closed
    obtain ⟨value,finalStore,same,finalSame,previous⟩ :=
      (gate.core_evaluates_iff resolution lowering).mp closed
    obtain ⟨rfl,rfl⟩ := Core.evaluation_deterministic previous path
    exact ⟨same,finalSame⟩
  · rintro ⟨rfl,rfl⟩
    exact (gate.core_evaluates_iff resolution lowering).mpr ⟨expected,store,rfl,rfl,path⟩

/-- Original, costed and machine witnesses are built before both image iff directions.
Ordered lookups allow duplicate spellings/IDs and arbitrary opaque Core rows/stores. -/
theorem all_fourteen_original_and_all_actual_images
    (owner : Resolved.DeclarationId) (names : LocalNameTable)
    (environment : Resolved.Environment) (store : Core.Store)
    (spans : Fin 6 → Syntax.SourceSpan) (rightSpan : Syntax.SourceSpan)
    (leftName rightName : Syntax.Identifier) (leftId rightId : Resolved.LocalId)
    (a b : Core.Word)
    (leftNamed : LocalNameTable.Lookup names leftName.value leftId)
    (rightNamed : LocalNameTable.Lookup names rightName.value rightId)
    (leftFound : Resolved.LocalScope.Lookup environment leftId (.word a))
    (rightFound : Resolved.LocalScope.Lookup environment rightId (.word b)) :
    ∀ op value, (op,value) ∈ outcomes a.bitNot b →
      let src := source spans rightSpan leftName rightName op
      ClosedSourceDataExpression src ∧
      ClosedSourceExpressionEvaluates owner names (embedded environment)
        (store.map RuntimeValue.ofCore) src (RuntimeValue.ofCore value) (store.map RuntimeValue.ofCore) ∧
      LocalExpressionEvaluatesWithCost names environment store src value store (4+overhead op) ∧
      ∃ res core, ResolvesLocalExpression names src res ∧ Resolved.Lowers environment.ids res core ∧
        Core.Evaluates environment.values store core value store ∧
        (∀ continuation, Core.Steps (4+overhead op)
          ⟨.eval core environment.values,continuation,store⟩ ⟨.ret value,continuation,store⟩) ∧
        (∀ actual final, ClosedSourceExpressionEvaluates owner names (embedded environment)
          (store.map RuntimeValue.ofCore) src actual final ↔
          actual=RuntimeValue.ofCore value ∧ final=store.map RuntimeValue.ofCore) ∧
        (∀ actual final, ClosedSourceExpressionEvaluates owner names (embedded environment)
          (store.map RuntimeValue.ofCore) src actual final ↔
          actual=RuntimeValue.ofCore value ∧ final=store.map RuntimeValue.ofCore) := by
  intro op value member
  dsimp only
  have m := meaning member
  obtain ⟨li,leftIndex,_⟩ := leftFound.indexed
  obtain ⟨ri,rightIndex,_⟩ := rightFound.indexed
  have admitted : ClosedSourceDataExpression (source spans rightSpan leftName rightName op) :=
    .strictWordBinary (.group (.bitNot .reference)) (.group .reference)
      m.operator_is_strict.1 m.operator_is_strict.2
  have rawLeft : ClosedSourceExpressionEvaluates owner names (embedded environment)
      (store.map RuntimeValue.ofCore) (left spans leftName) (.word a.bitNot) (store.map RuntimeValue.ofCore) :=
    .group (.bitNot (.reference leftNamed (by simpa only [RuntimeValue.ofCore] using mapped_lookup leftFound)))
  have rawRight : ClosedSourceExpressionEvaluates owner names (embedded environment)
      (store.map RuntimeValue.ofCore) (right rightSpan rightName) (.word b) (store.map RuntimeValue.ofCore) :=
    .group (.reference rightNamed (by simpa only [RuntimeValue.ofCore] using mapped_lookup rightFound))
  have original : ClosedSourceExpressionEvaluates owner names (embedded environment)
      (store.map RuntimeValue.ofCore) (source spans rightSpan leftName rightName op)
      (RuntimeValue.ofCore value) (store.map RuntimeValue.ofCore) := .strictWordBinary rawLeft rawRight m
  have localLeft : LocalExpressionEvaluatesWithCost names environment store
      (left spans leftName) (.word a.bitNot) store 3 := .group (.bitNot (.identifier leftNamed leftFound))
  have localRight : LocalExpressionEvaluatesWithCost names environment store
      (right rightSpan rightName) (.word b) store 1 := .group (.identifier rightNamed rightFound)
  have costed : LocalExpressionEvaluatesWithCost names environment store
      (source spans rightSpan leftName rightName op) value store (4+overhead op) := by
    cases m with
    | add => exact .add localLeft localRight
    | subtract => exact .subtract localLeft localRight
    | multiply => exact .multiply localLeft localRight
    | divide => exact .divide localLeft localRight
    | modulo => exact .modulo localLeft localRight
    | bitAnd => exact .bitAnd localLeft localRight
    | bitOr => exact .bitOr localLeft localRight
    | bitXor => exact .bitXor localLeft localRight
    | greater => exact .greater localLeft localRight
    | less => exact .less localLeft localRight
    | equal => exact .equal localLeft localRight
    | notEqual => exact .notEqual localLeft localRight
    | lessEqual => exact .lessEqual localLeft localRight
    | greaterEqual => exact .greaterEqual localLeft localRight
  have resolution : ResolvesLocalExpression names (source spans rightSpan leftName rightName op)
      (resolved op (.unary .wordNot (.var leftId)) (.var rightId)) := by
    cases m <;> constructor
    all_goals first
    | exact .group (.bitNot (.identifier leftNamed))
    | exact .group (.identifier rightNamed)
  have lowering : Resolved.Lowers environment.ids
      (resolved op (.unary .wordNot (.var leftId)) (.var rightId))
      (code op (.unary .wordNot (.var li)) (.var ri)) := by
    cases m
    all_goals first
    | exact .binary (.unary (.var leftIndex)) (.var rightIndex)
    | exact .unary (.binary (.unary (.var leftIndex)) (.var rightIndex))
    | exact .wordLt (.unary (.var leftIndex)) (.var rightIndex)
    | exact .unary (.wordLt (.unary (.var leftIndex)) (.var rightIndex))
  have steps := costed.toSteps resolution lowering
  have corePath := Core.steps_from_initial_sound steps
  exact ⟨admitted,original,costed,_,_,resolution,lowering,corePath,
    costed.toStepsWithContinuation resolution lowering,
    local_image admitted costed.erase,core_image admitted resolution lowering corePath⟩

end Tests.StrictWordDataImages
