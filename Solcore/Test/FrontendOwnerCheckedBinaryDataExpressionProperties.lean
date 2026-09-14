import Solcore.Frontend.CheckedDataExpressionOwnerProperties

/- Two independently evaluated checked expressions consume the generic owner
image.  Duplicate and foreign rows are intentional; no row uniqueness or
runtime validity hypothesis is used. -/
set_option autoImplicit false
namespace Tests.ADR0316CheckedBinaryOwnerConsumerIndependent
open Solcore Solcore.Frontend

private def declaration (index : Nat) : Resolved.DeclarationId :=
  ⟨⟨.main, ⟨[⟨"CheckedBinaryOwner", by decide⟩], by decide⟩⟩, index⟩
private def oldOwner := declaration 316
private def foreignOwner := declaration 9316
private def localId (owner : Resolved.DeclarationId) (index : Nat) : Resolved.LocalId :=
  ⟨owner, index⟩
private def guardId := localId oldOwner 1
private def leftId := localId oldOwner 2
private def rightId := localId oldOwner 3
private def dormantId := localId foreignOwner 4
private def payloadId := localId foreignOwner 5
private def duplicateLeftId := leftId
private def noiseId := localId foreignOwner 99

private def shift (owner : Resolved.DeclarationId) : Resolved.DeclarationId :=
  { owner with declarationIndex := owner.declarationIndex + 3 }
private theorem shift_injective : Function.Injective shift := by
  intro left right same
  have modules := congrArg Resolved.DeclarationId.moduleId same
  have indices := congrArg Resolved.DeclarationId.declarationIndex same
  cases left; cases right
  simp only [shift, Resolved.DeclarationId.mk.injEq] at modules indices ⊢
  exact ⟨modules, by omega⟩
private theorem shift_not_surjective : ¬ Function.Surjective shift := by
  intro onto
  obtain ⟨before, same⟩ := onto (declaration 0)
  have impossible := congrArg Resolved.DeclarationId.declarationIndex same
  change before.declarationIndex + 3 = 0 at impossible
  omega

private def sourceId : Syntax.SourceId := ⟨.main, "adr0316-checked-binary-owner.sol"⟩
private def span (start stop : Nat) : Syntax.SourceSpan := ⟨sourceId, start, stop⟩
private def identifier (start stop : Nat) (name : String) : Syntax.Identifier :=
  ⟨span start stop, name⟩
private def reference (start stop : Nat) (name : String) : Syntax.Expr :=
  ⟨span start stop, .identifier (identifier start stop name)⟩
private def boolSource : Syntax.Expr :=
  ⟨span 0 17, .binary (reference 0 5 "guard") ⟨span 6 8, .logicalOr⟩
    (reference 9 16 "dormant")⟩
private def wordSource : Syntax.Expr :=
  ⟨span 20 32, .binary (reference 20 24 "left") ⟨span 25 26, .add⟩
    (reference 27 32 "right")⟩
private def illTypedSource : Syntax.Expr :=
  ⟨span 40 53, .binary (reference 40 45 "guard") ⟨span 46 48, .logicalOr⟩
    (reference 49 53 "left")⟩

private def names : LocalNameTable :=
  [("guard", guardId), ("left", leftId), ("right", rightId),
    ("dormant", dormantId), ("left", noiseId)]
private def forty : Core.Word := Core.Word.ofNatModulo 40
private def two : Core.Word := Core.Word.ofNatModulo 2
private def opaqueValue : Core.Value :=
  .closure .unit (.product .word .unit) (.pair (.var 0) .unit)
    [.cellRef .word 73, .hostFunction .storageWrite,
      .closure .unit .unit (.var 9) [.hostFunction .storageRead]]
private def environment : Resolved.Environment :=
  [(guardId, .bool true), (leftId, .word forty), (rightId, .word two),
    (dormantId, .bool false), (payloadId, opaqueValue),
    (duplicateLeftId, .unit), (noiseId, .hostFunction .storageRead)]
private def context : Resolved.Context :=
  [(guardId, .bool), (leftId, .word), (rightId, .word),
    (dormantId, .bool), (payloadId, .function .unit (.product .word .unit)),
    (duplicateLeftId, .unit), (noiseId, .unit)]
private def store : Core.Store :=
  [opaqueValue, .cellRef (.function .word .word) 800,
    .hostFunction .storageWrite,
    .pair (.hostFunction .storageRead) (.cellRef .bool 801)]
private def captured : Resolved.LocalScope RuntimeValue :=
  environment.map fun row => (row.1, RuntimeValue.ofCore row.2)
private def heap : List RuntimeValue := store.map RuntimeValue.ofCore
private def mappedNames := LocalNameTable.mapIds (ownerLocalIdMap shift) names
private def mappedEnvironment :=
  Resolved.LocalScope.mapIds (ownerLocalIdMap shift) environment
private def mappedContext :=
  Resolved.LocalScope.mapIds (ownerLocalIdMap shift) context
private def mappedCaptured : Resolved.LocalScope RuntimeValue :=
  mappedEnvironment.map fun row => (row.1, RuntimeValue.ofCore row.2)

private def boolCore : Core.Expr :=
  .ifE (.var 0) (.bool true) (.var 3)
private def wordCore : Core.Expr :=
  .binary .wordAdd (.var 1) (.var 2)
private def boolResolved : Resolved.Expr :=
  .ifE (.var guardId) (.bool true) (.var dormantId)
private def wordResolved : Resolved.Expr :=
  .binary .wordAdd (.var leftId) (.var rightId)
private def sum : Core.Value := .word (forty.add two)

private theorem aligned : environment.ids = context.ids := by rfl
private theorem boolGate : ClosedSourceDataExpression boolSource :=
  .logicalOr .reference .reference
private theorem wordGate : ClosedSourceDataExpression wordSource :=
  .strictWordBinary .reference .reference (by decide) (by decide)
private theorem illTypedGate : ClosedSourceDataExpression illTypedSource :=
  .logicalOr .reference .reference
private theorem boolResolution :
    ResolvesLocalExpression names boolSource boolResolved :=
  .logicalOr (.identifier .head)
    (.identifier (.tail (by decide) (.tail (by decide) (.tail (by decide) .head))))
private theorem wordResolution :
    ResolvesLocalExpression names wordSource wordResolved :=
  .add (.identifier (.tail (by decide) .head))
    (.identifier (.tail (by decide) (.tail (by decide) .head)))
private theorem boolLowering : Resolved.Lowers context.ids boolResolved boolCore :=
  .ifE (.var .head) .bool
    (.var (.tail (by decide) (.tail (by decide) (.tail (by decide) .head))))
private theorem wordLowering : Resolved.Lowers context.ids wordResolved wordCore :=
  .binary (.var (.tail (by decide) .head))
    (.var (.tail (by decide) (.tail (by decide) .head)))
private theorem boolTyping : Resolved.HasType context boolResolved .bool :=
  .ifE (.var .head) .bool
    (.var (.tail (by decide) (.tail (by decide) (.tail (by decide) .head))))
private theorem wordTyping : Resolved.HasType context wordResolved .word :=
  .binary (.var (.tail (by decide) .head))
    (.var (.tail (by decide) (.tail (by decide) .head)))
private theorem boolAccepted :
    elaborateLocalExpression? names context boolSource = some (boolCore, .bool) :=
  elaborateLocalExpression?_complete boolResolution boolLowering boolTyping
private theorem wordAccepted :
    elaborateLocalExpression? names context wordSource = some (wordCore, .word) :=
  elaborateLocalExpression?_complete wordResolution wordLowering wordTyping
private theorem illTypedRejected :
    elaborateLocalExpression? names context illTypedSource = none := by
  simp [elaborateLocalExpression?, resolveLocalExpression?, LocalNameTable.lookup?,
    names, context, illTypedSource, reference, identifier, Resolved.Expr.lower?,
    Resolved.LocalScope.ids, Resolved.LocalScope.values, Resolved.LocalScope.index?,
    guardId, leftId, rightId, dormantId, payloadId, duplicateLeftId, noiseId,
    localId, oldOwner, foreignOwner, declaration]
  intro type inferred
  cases Core.infer_sound inferred with
  | ifE _ thenBranch elseBranch =>
      cases elseBranch with
      | var found => cases found <;> cases thenBranch

private theorem oldBoolRaw :
    ClosedSourceExpressionEvaluates oldOwner names captured heap boolSource
      (.bool true) heap := by
  simp only [captured, environment, List.map_cons, List.map_nil, RuntimeValue.ofCore]
  exact .orTrue (.reference .head .head)
private theorem mappedBoolRaw :
    ClosedSourceExpressionEvaluates (shift oldOwner) mappedNames mappedCaptured heap boolSource
      (.bool true) heap := by
  simp only [mappedCaptured, mappedEnvironment, Resolved.LocalScope.mapIds,
    environment, List.map_cons, List.map_nil, RuntimeValue.ofCore]
  exact .orTrue (.reference .head .head)
private theorem oldWordRaw :
    ClosedSourceExpressionEvaluates oldOwner names captured heap wordSource
      (RuntimeValue.ofCore sum) heap := by
  simp only [captured, environment, List.map_cons, List.map_nil, RuntimeValue.ofCore]
  exact .strictWordBinary
    (.reference (.tail (by decide) .head) (.tail (by decide) .head))
    (.reference (.tail (by decide) (.tail (by decide) .head))
      (.tail (by decide) (.tail (by decide) .head))) .add
private theorem mappedWordRaw :
    ClosedSourceExpressionEvaluates (shift oldOwner) mappedNames mappedCaptured heap wordSource
      (RuntimeValue.ofCore sum) heap := by
  simp only [mappedCaptured, mappedEnvironment, Resolved.LocalScope.mapIds,
    environment, List.map_cons, List.map_nil, RuntimeValue.ofCore]
  exact .strictWordBinary
    (.reference (.tail (by decide) .head) (.tail (by decide) .head))
    (.reference (.tail (by decide) (.tail (by decide) .head))
      (.tail (by decide) (.tail (by decide) .head))) .add

private theorem boolCoreRun :
    Core.Evaluates environment.values store boolCore (.bool true) store := by
  exact .ifTrue (.var rfl) .bool
private theorem wordCoreRun :
    Core.Evaluates environment.values store wordCore sum store := by
  exact .binary (.var rfl) (.var rfl) rfl

private def MappedRaw (source : Syntax.Expr) (actual : RuntimeValue)
    (finalStore : List RuntimeValue) : Prop :=
  ClosedSourceExpressionEvaluates (shift oldOwner) mappedNames mappedCaptured heap
    source actual finalStore
private def CoreImage (core : Core.Expr) (actual : RuntimeValue)
    (actualFinal : List RuntimeValue) : Prop :=
  ∃ value finalStore,
    actual = RuntimeValue.ofCore value ∧
    actualFinal = finalStore.map RuntimeValue.ofCore ∧
    Core.Evaluates environment.values store core value finalStore

/-- The concrete fixture exposes the nonsurjective map, duplicate and foreign
rows, mixed opaque store, exact checker alignment, and an admitted rejection. -/
theorem fixture_controls :
    Function.Injective shift ∧ ¬ Function.Surjective shift ∧ store ≠ [] ∧
    environment.ids = context.ids ∧
    environment.ids[1]? = some leftId ∧ environment.ids[5]? = some leftId ∧
    environment.ids[3]? = some dormantId ∧ environment.ids[4]? = some payloadId ∧
    names[1]? = some ("left", leftId) ∧ names[4]? = some ("left", noiseId) ∧
    elaborateLocalExpression? names context boolSource = some (boolCore, .bool) ∧
    elaborateLocalExpression? names context wordSource = some (wordCore, .word) ∧
    ClosedSourceDataExpression illTypedSource ∧
    elaborateLocalExpression? names context illTypedSource = none := by
  exact ⟨shift_injective, shift_not_surjective, by decide, aligned, rfl, rfl, rfl, rfl,
    rfl, rfl, boolAccepted, wordAccepted, illTypedGate, illTypedRejected⟩

/-- Both binary forms have separately constructed old/mapped raw and Core
endpoints. The generic checked owner theorem then classifies arbitrary mapped
endpoints and supplies the mapped checker and ID equalities for both forms. -/
theorem both_checked_binary_owner_images
    {boolActual wordActual : RuntimeValue}
    {boolFinal wordFinal : List RuntimeValue} :
    ClosedSourceExpressionEvaluates oldOwner names captured heap boolSource (.bool true) heap ∧
    MappedRaw boolSource (.bool true) heap ∧
    Core.Evaluates environment.values store boolCore (.bool true) store ∧
    ClosedSourceExpressionEvaluates oldOwner names captured heap wordSource
      (RuntimeValue.ofCore sum) heap ∧
    MappedRaw wordSource (RuntimeValue.ofCore sum) heap ∧
    Core.Evaluates environment.values store wordCore sum store ∧
    elaborateLocalExpression? mappedNames mappedContext boolSource = some (boolCore, .bool) ∧
    mappedEnvironment.ids = mappedContext.ids ∧
    elaborateLocalExpression? mappedNames mappedContext wordSource = some (wordCore, .word) ∧
    mappedEnvironment.ids = mappedContext.ids ∧
    (MappedRaw boolSource boolActual boolFinal ↔ CoreImage boolCore boolActual boolFinal) ∧
    (MappedRaw wordSource wordActual wordFinal ↔ CoreImage wordCore wordActual wordFinal) := by
  have oldBool := oldBoolRaw
  have newBool := mappedBoolRaw
  have coreBool := boolCoreRun
  have oldWord := oldWordRaw
  have newWord := mappedWordRaw
  have coreWord := wordCoreRun
  obtain ⟨boolCheck, boolIds, _, _, _, _, _, boolImage⟩ :=
    boolGate.mapOwners_checked_core_evaluates_iff shift shift_injective
      (owner := oldOwner) (names := names) (context := context)
      (environment := environment) (initialStore := store)
      (actualValue := boolActual) (actualFinal := boolFinal) boolAccepted aligned
  obtain ⟨wordCheck, wordIds, _, _, _, _, _, wordImage⟩ :=
    wordGate.mapOwners_checked_core_evaluates_iff shift shift_injective
      (owner := oldOwner) (names := names) (context := context)
      (environment := environment) (initialStore := store)
      (actualValue := wordActual) (actualFinal := wordFinal) wordAccepted aligned
  exact ⟨oldBool, newBool, coreBool, oldWord, newWord, coreWord,
    boolCheck, boolIds, wordCheck, wordIds, boolImage, wordImage⟩

end Tests.ADR0316CheckedBinaryOwnerConsumerIndependent
