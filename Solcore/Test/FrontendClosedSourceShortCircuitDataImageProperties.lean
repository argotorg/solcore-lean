import Solcore.Frontend.ClosedSource
import Solcore.Frontend.LocalExpressionEvaluation
import Solcore.Resolved.LocalScope

set_option autoImplicit false
namespace Tests.ClosedSourceShortCircuitDataImages
open Solcore Solcore.Frontend

private def reference (span : Syntax.SourceSpan) (name : Syntax.Identifier) : Syntax.Expr :=
  ⟨span, .identifier name⟩
private def left (spans : Fin 6 → Syntax.SourceSpan) (name : Syntax.Identifier) : Syntax.Expr :=
  ⟨spans 2, .group ⟨spans 3, .unary ⟨spans 4, .logicalNot⟩ (reference (spans 5) name)⟩⟩
private def right (span : Syntax.SourceSpan) (name : Syntax.Identifier) : Syntax.Expr :=
  ⟨span, .group (reference name.span name)⟩
private def source (spans : Fin 6 → Syntax.SourceSpan) (rightSpan : Syntax.SourceSpan)
    (leftName rightName : Syntax.Identifier) (isOr : Bool) : Syntax.Expr :=
  ⟨spans 0, .binary (left spans leftName)
    ⟨spans 1, if isOr then .logicalOr else .logicalAnd⟩ (right rightSpan rightName)⟩
private def result (isOr input : Bool) (payload : Core.Value) : Core.Value :=
  if (!input) == isOr then .bool isOr else payload
private def resolved (isOr : Bool) (leftId rightId : Resolved.LocalId) : Resolved.Expr :=
  if isOr then .ifE (.unary .boolNot (.var leftId)) (.bool true) (.var rightId)
  else .ifE (.unary .boolNot (.var leftId)) (.var rightId) (.bool false)
private def code (isOr : Bool) (leftIndex rightIndex : Nat) : Core.Expr :=
  if isOr then .ifE (.unary .boolNot (.var leftIndex)) (.bool true) (.var rightIndex)
  else .ifE (.unary .boolNot (.var leftIndex)) (.var rightIndex) (.bool false)
private def embedded (environment : Resolved.Environment) : Resolved.LocalScope RuntimeValue :=
  environment.map (fun row => (row.1, RuntimeValue.ofCore row.2))

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
  intro actual final
  constructor
  · intro closed
    obtain ⟨value, finalStore, same, finalSame, previous⟩ := gate.local_evaluates_iff.mp closed
    obtain ⟨rfl, rfl⟩ := previous.deterministic path
    exact ⟨same, finalSame⟩
  · rintro ⟨rfl, rfl⟩
    exact gate.local_evaluates_iff.mpr ⟨expected, store, rfl, rfl, path⟩

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
  intro actual final
  constructor
  · intro closed
    obtain ⟨value, finalStore, same, finalSame, previous⟩ :=
      (gate.core_evaluates_iff resolution lowering).mp closed
    obtain ⟨rfl, rfl⟩ := Core.evaluation_deterministic previous path
    exact ⟨same, finalSame⟩
  · rintro ⟨rfl, rfl⟩
    exact (gate.core_evaluates_iff resolution lowering).mpr ⟨expected, store, rfl, rfl, path⟩

/-- Whole symbolic paths precede both actual-output images. No typing or unique-row premise. -/
theorem original_and_all_actual_images
    (owner : Resolved.DeclarationId) (names : LocalNameTable)
    (environment : Resolved.Environment) (store : Core.Store)
    (spans : Fin 6 → Syntax.SourceSpan) (rightSpan : Syntax.SourceSpan)
    (leftName rightName : Syntax.Identifier) (leftId rightId : Resolved.LocalId)
    (isOr input : Bool) (payload : Core.Value)
    (leftNamed : LocalNameTable.Lookup names leftName.value leftId)
    (rightNamed : LocalNameTable.Lookup names rightName.value rightId)
    (leftFound : Resolved.LocalScope.Lookup environment leftId (.bool input))
    (rightFound : Resolved.LocalScope.Lookup environment rightId payload) :
    let original := source spans rightSpan leftName rightName isOr
    let expected := result isOr input payload
    ClosedSourceDataExpression original ∧
    ClosedSourceExpressionEvaluates owner names (embedded environment)
      (store.map RuntimeValue.ofCore) original (RuntimeValue.ofCore expected)
      (store.map RuntimeValue.ofCore) ∧
    LocalExpressionEvaluates names environment store original expected store ∧
    ∃ resolved core,
      ResolvesLocalExpression names original resolved ∧
      Resolved.Lowers environment.ids resolved core ∧
      Core.Evaluates environment.values store core expected store ∧
      (∀ actual final, ClosedSourceExpressionEvaluates owner names (embedded environment)
        (store.map RuntimeValue.ofCore) original actual final ↔
        actual = RuntimeValue.ofCore expected ∧ final = store.map RuntimeValue.ofCore) ∧
      (∀ actual final, ClosedSourceExpressionEvaluates owner names (embedded environment)
        (store.map RuntimeValue.ofCore) original actual final ↔
        actual = RuntimeValue.ofCore expected ∧ final = store.map RuntimeValue.ofCore) := by
  dsimp only
  obtain ⟨li, leftIndex, leftAt⟩ := leftFound.indexed
  obtain ⟨ri, rightIndex, rightAt⟩ := rightFound.indexed
  have admitted : ClosedSourceDataExpression (source spans rightSpan leftName rightName isOr) := by
    cases isOr
    · exact .logicalAnd (.group (.logicalNot .reference)) (.group .reference)
    · exact .logicalOr (.group (.logicalNot .reference)) (.group .reference)
  have closedLeft : ClosedSourceExpressionEvaluates owner names (embedded environment)
      (store.map RuntimeValue.ofCore) (left spans leftName)
      (.bool (!input)) (store.map RuntimeValue.ofCore) :=
    .group (.logicalNot (.reference leftNamed
      (by simpa only [RuntimeValue.ofCore] using mapped_lookup leftFound)))
  have closedRight : ClosedSourceExpressionEvaluates owner names (embedded environment)
      (store.map RuntimeValue.ofCore) (right rightSpan rightName)
      (RuntimeValue.ofCore payload) (store.map RuntimeValue.ofCore) :=
    .group (.reference rightNamed (mapped_lookup rightFound))
  have original : ClosedSourceExpressionEvaluates owner names (embedded environment)
      (store.map RuntimeValue.ofCore) (source spans rightSpan leftName rightName isOr)
      (RuntimeValue.ofCore (result isOr input payload)) (store.map RuntimeValue.ofCore) := by
    cases isOr <;> cases input
    all_goals simp only [source, result, Bool.not_true, Bool.not_false,
      Bool.false_beq, Bool.true_beq,
      ↓reduceIte, RuntimeValue.ofCore]
    · exact .andTrue closedLeft closedRight
    · exact .andFalse closedLeft
    · exact .orTrue closedLeft
    · exact .orFalse closedLeft closedRight
  have localLeft : LocalExpressionEvaluates names environment store
      (left spans leftName) (.bool (!input)) store :=
    .group (.logicalNot (.identifier leftNamed leftFound))
  have localRight : LocalExpressionEvaluates names environment store
      (right rightSpan rightName) payload store := .group (.identifier rightNamed rightFound)
  have localPath : LocalExpressionEvaluates names environment store
      (source spans rightSpan leftName rightName isOr) (result isOr input payload) store := by
    cases isOr <;> cases input
    · exact .andTrue localLeft localRight
    · exact .andFalse localLeft
    · exact .orTrue localLeft
    · exact .orFalse localLeft localRight
  have resolution : ResolvesLocalExpression names
      (source spans rightSpan leftName rightName isOr) (resolved isOr leftId rightId) := by
    cases isOr
    · exact .logicalAnd (.group (.logicalNot (.identifier leftNamed))) (.group (.identifier rightNamed))
    · exact .logicalOr (.group (.logicalNot (.identifier leftNamed))) (.group (.identifier rightNamed))
  have lowering : Resolved.Lowers environment.ids (resolved isOr leftId rightId) (code isOr li ri) := by
    cases isOr
    · exact .ifE (.unary (.var leftIndex)) (.var rightIndex) .bool
    · exact .ifE (.unary (.var leftIndex)) .bool (.var rightIndex)
  have coreLeft : Core.Evaluates environment.values store
      (.unary .boolNot (.var li)) (.bool (!input)) store := .unary (.var leftAt) rfl
  have coreRight : Core.Evaluates environment.values store (.var ri) payload store := .var rightAt
  have corePath : Core.Evaluates environment.values store (code isOr li ri)
      (result isOr input payload) store := by
    cases isOr <;> cases input
    · exact .ifTrue coreLeft coreRight
    · exact .ifFalse coreLeft .bool
    · exact .ifTrue coreLeft .bool
    · exact .ifFalse coreLeft coreRight
  exact ⟨admitted, original, localPath, resolved isOr leftId rightId, code isOr li ri,
    resolution, lowering, corePath, local_image admitted localPath,
    core_image admitted resolution lowering corePath⟩

end Tests.ClosedSourceShortCircuitDataImages
