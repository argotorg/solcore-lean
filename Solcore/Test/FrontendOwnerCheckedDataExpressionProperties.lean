import Solcore.Frontend.CheckedDataExpressionOwnerProperties

/- Bool and Word instances build old, mapped, checked, and Core paths before
the common checked-data owner theorem is consumed. -/
set_option autoImplicit false
namespace Tests.ADR0316CheckedDataOwnerConsumer
open Solcore Solcore.Frontend

private def declaration (index : Nat) : Resolved.DeclarationId :=
  ⟨⟨.main, ⟨[⟨"CheckedDataOwner", by decide⟩], by decide⟩⟩, index⟩
private def oldOwner := declaration 16
private def foreignOwner := declaration 116
private def lid (owner : Resolved.DeclarationId) (index : Nat) : Resolved.LocalId :=
  ⟨owner, index⟩
private def flagId := lid oldOwner 1
private def wordId := lid oldOwner 2
private def noiseId := lid foreignOwner 3
private def payloadId := lid foreignOwner 4
private def shadowFlagId := lid foreignOwner 1

private def shift (owner : Resolved.DeclarationId) : Resolved.DeclarationId :=
  {owner with declarationIndex := owner.declarationIndex + 7}
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
  simp [shift, declaration] at impossible

private def sourceId : Syntax.SourceId := ⟨.main, "checked-data-owner.sol"⟩
private def span (start stop : Nat) : Syntax.SourceSpan := ⟨sourceId, start, stop⟩
private def ident (start stop : Nat) (name : String) : Syntax.Identifier :=
  ⟨span start stop, name⟩
private def reference (start stop : Nat) (name : String) : Syntax.Expr :=
  ⟨span start stop, .identifier (ident start stop name)⟩
private def flagRef := reference 1 5 "flag"
private def wordRef := reference 7 11 "word"
private def boolSource : Syntax.Expr :=
  ⟨span 0 5, .unary ⟨span 0 1, .logicalNot⟩ flagRef⟩
private def wordSource : Syntax.Expr :=
  ⟨span 6 11, .unary ⟨span 6 7, .bitNot⟩ wordRef⟩
private def boolResolved : Resolved.Expr := .unary .boolNot (.var flagId)
private def wordResolved : Resolved.Expr := .unary .wordNot (.var wordId)
private def boolCore : Core.Expr := .unary .boolNot (.var 1)
private def wordCore : Core.Expr := .unary .wordNot (.var 2)

private def names : LocalNameTable :=
  [("flag", flagId), ("word", wordId), ("flag", shadowFlagId), ("word", noiseId)]
private def context : Resolved.Context :=
  [(noiseId, .unit), (flagId, .bool), (wordId, .word),
    (payloadId, .function .unit .unit), (flagId, .bool)]
private def word : Core.Word := Core.Word.ofNatModulo 42
private def payload : Core.Value :=
  .closure .unit .unit (.var 8)
    [.cellRef .word 19, .hostFunction .storageWrite]
private def environment : Resolved.Environment :=
  [(noiseId, .hostFunction .storageRead), (flagId, .bool true),
    (wordId, .word word), (payloadId, payload), (flagId, .bool false)]
private def store : Core.Store :=
  [payload, .cellRef (.function .word .word) 23, .hostFunction .storageWrite]
private def captured : List (Resolved.LocalId × RuntimeValue) :=
  environment.map (fun row => (row.1, RuntimeValue.ofCore row.2))
private def heap : List RuntimeValue := store.map RuntimeValue.ofCore
private def mappedNames := LocalNameTable.mapIds (ownerLocalIdMap shift) names
private def mappedContext := Resolved.LocalScope.mapIds (ownerLocalIdMap shift) context
private def mappedEnvironment := Resolved.LocalScope.mapIds (ownerLocalIdMap shift) environment

private theorem sameIds : environment.ids = context.ids := by rfl
private theorem boolGate : ClosedSourceDataExpression boolSource :=
  .logicalNot .reference
private theorem wordGate : ClosedSourceDataExpression wordSource :=
  .bitNot .reference
private theorem boolResolution : ResolvesLocalExpression names boolSource boolResolved :=
  .logicalNot (.identifier .head)
private theorem wordResolution : ResolvesLocalExpression names wordSource wordResolved :=
  .bitNot (.identifier (.tail (by decide) .head))
private theorem boolLowering : Resolved.Lowers context.ids boolResolved boolCore :=
  .unary (.var (.tail (by decide) .head))
private theorem wordLowering : Resolved.Lowers context.ids wordResolved wordCore :=
  .unary (.var (.tail (by decide) (.tail (by decide) .head)))
private theorem boolTyping : Resolved.HasType context boolResolved .bool :=
  .unary (.var (.tail (by decide) .head))
private theorem wordTyping : Resolved.HasType context wordResolved .word :=
  .unary (.var (.tail (by decide) (.tail (by decide) .head)))
private theorem boolAccepted :
    elaborateLocalExpression? names context boolSource = some (boolCore, .bool) :=
  elaborateLocalExpression?_complete boolResolution boolLowering boolTyping
private theorem wordAccepted :
    elaborateLocalExpression? names context wordSource = some (wordCore, .word) :=
  elaborateLocalExpression?_complete wordResolution wordLowering wordTyping

private theorem embedLookup {scope : Resolved.Environment} {id : Resolved.LocalId}
    {value : Core.Value} (found : Resolved.LocalScope.Lookup scope id value) :
    Resolved.LocalScope.Lookup
      (scope.map (fun row => (row.1, RuntimeValue.ofCore row.2))) id
      (RuntimeValue.ofCore value) := by
  induction found with
  | head => exact .head
  | tail different _ ih => exact .tail different ih
private theorem flagFound :
    Resolved.LocalScope.Lookup environment flagId (.bool true) :=
  .tail (by decide) .head
private theorem wordFound :
    Resolved.LocalScope.Lookup environment wordId (.word word) :=
  .tail (by decide) (.tail (by decide) .head)
private theorem flagNamed : LocalNameTable.Lookup names "flag" flagId := .head
private theorem wordNamed : LocalNameTable.Lookup names "word" wordId :=
  .tail (by decide) .head

private theorem boolRaw : ClosedSourceExpressionEvaluates oldOwner names captured heap
    boolSource (.bool false) heap := by
  have child : ClosedSourceExpressionEvaluates oldOwner names captured heap
      flagRef (.bool true) heap := by
    simpa [captured, flagRef, reference, ident, RuntimeValue.ofCore] using
      ClosedSourceExpressionEvaluates.reference flagNamed (embedLookup flagFound)
  simpa [boolSource] using ClosedSourceExpressionEvaluates.logicalNot child
private theorem wordRaw : ClosedSourceExpressionEvaluates oldOwner names captured heap
    wordSource (.word word.bitNot) heap := by
  have child : ClosedSourceExpressionEvaluates oldOwner names captured heap
      wordRef (.word word) heap := by
    simpa [captured, wordRef, reference, ident, RuntimeValue.ofCore] using
      ClosedSourceExpressionEvaluates.reference wordNamed (embedLookup wordFound)
  simpa [wordSource] using ClosedSourceExpressionEvaluates.bitNot child
private theorem mappedBoolRaw : ClosedSourceExpressionEvaluates (shift oldOwner) mappedNames
    (mappedEnvironment.map (fun row => (row.1, RuntimeValue.ofCore row.2))) heap
    boolSource (.bool false) heap := by
  simpa only [mappedNames, mappedEnvironment, captured, heap,
    mapRuntimeCapturedOwners_ofCore, mapRuntimeStoreOwners_ofCore,
    RuntimeValue.mapOwners] using boolRaw.mapOwners shift shift_injective
private theorem mappedWordRaw : ClosedSourceExpressionEvaluates (shift oldOwner) mappedNames
    (mappedEnvironment.map (fun row => (row.1, RuntimeValue.ofCore row.2))) heap
    wordSource (.word word.bitNot) heap := by
  simpa only [mappedNames, mappedEnvironment, captured, heap,
    mapRuntimeCapturedOwners_ofCore, mapRuntimeStoreOwners_ofCore,
    RuntimeValue.mapOwners] using wordRaw.mapOwners shift shift_injective
private theorem boolCoreRun :
    Core.Evaluates environment.values store boolCore (.bool false) store :=
  .unary (.var rfl) rfl
private theorem wordCoreRun :
    Core.Evaluates environment.values store wordCore (.word word.bitNot) store :=
  .unary (.var rfl) rfl

/-- The checked Bool instance retains mapped checking and both lowering stages,
then classifies every arbitrary mapped raw endpoint by the old Core run. -/
theorem checked_bool_owner_image {actualValue : RuntimeValue}
    {actualFinal : List RuntimeValue} :
    ClosedSourceExpressionEvaluates oldOwner names captured heap boolSource
        (.bool false) heap ∧
    ClosedSourceExpressionEvaluates (shift oldOwner) mappedNames
        (mappedEnvironment.map (fun row => (row.1, RuntimeValue.ofCore row.2))) heap
        boolSource (.bool false) heap ∧
    Core.Evaluates environment.values store boolCore (.bool false) store ∧
    elaborateLocalExpression? mappedNames mappedContext boolSource = some (boolCore, .bool) ∧
    mappedEnvironment.ids = mappedContext.ids ∧
    ∃ resolved,
      ResolvesLocalExpression names boolSource resolved ∧
      Resolved.Lowers environment.ids resolved boolCore ∧
      ResolvesLocalExpression mappedNames boolSource
        (resolved.renameIds (ownerLocalIdMap shift)) ∧
      Resolved.Lowers mappedEnvironment.ids
        (resolved.renameIds (ownerLocalIdMap shift)) boolCore ∧
      (ClosedSourceExpressionEvaluates (shift oldOwner) mappedNames
        (mappedEnvironment.map (fun row => (row.1, RuntimeValue.ofCore row.2))) heap
        boolSource actualValue actualFinal ↔
      ∃ value finalStore,
        actualValue = RuntimeValue.ofCore value ∧
        actualFinal = finalStore.map RuntimeValue.ofCore ∧
        Core.Evaluates environment.values store boolCore value finalStore) := by
  have bridge := boolGate.mapOwners_checked_core_evaluates_iff shift shift_injective
    (owner := oldOwner) (environment := environment) (initialStore := store)
    (actualValue := actualValue) (actualFinal := actualFinal) boolAccepted sameIds
  exact ⟨boolRaw, mappedBoolRaw, boolCoreRun, by
    simpa only [mappedNames, mappedContext, mappedEnvironment, heap] using bridge⟩

/-- The same public theorem instantiates independently at Word bitwise negation;
the known old, mapped and Core endpoints are constructed without that bridge. -/
theorem checked_word_owner_image {actualValue : RuntimeValue}
    {actualFinal : List RuntimeValue} :
    ClosedSourceExpressionEvaluates oldOwner names captured heap wordSource
        (.word word.bitNot) heap ∧
    ClosedSourceExpressionEvaluates (shift oldOwner) mappedNames
        (mappedEnvironment.map (fun row => (row.1, RuntimeValue.ofCore row.2))) heap
        wordSource (.word word.bitNot) heap ∧
    Core.Evaluates environment.values store wordCore (.word word.bitNot) store ∧
    elaborateLocalExpression? mappedNames mappedContext wordSource = some (wordCore, .word) ∧
    mappedEnvironment.ids = mappedContext.ids ∧
    ∃ resolved,
      ResolvesLocalExpression names wordSource resolved ∧
      Resolved.Lowers environment.ids resolved wordCore ∧
      ResolvesLocalExpression mappedNames wordSource
        (resolved.renameIds (ownerLocalIdMap shift)) ∧
      Resolved.Lowers mappedEnvironment.ids
        (resolved.renameIds (ownerLocalIdMap shift)) wordCore ∧
      (ClosedSourceExpressionEvaluates (shift oldOwner) mappedNames
        (mappedEnvironment.map (fun row => (row.1, RuntimeValue.ofCore row.2))) heap
        wordSource actualValue actualFinal ↔
      ∃ value finalStore,
        actualValue = RuntimeValue.ofCore value ∧
        actualFinal = finalStore.map RuntimeValue.ofCore ∧
        Core.Evaluates environment.values store wordCore value finalStore) := by
  have bridge := wordGate.mapOwners_checked_core_evaluates_iff shift shift_injective
    (owner := oldOwner) (environment := environment) (initialStore := store)
    (actualValue := actualValue) (actualFinal := actualFinal) wordAccepted sameIds
  exact ⟨wordRaw, mappedWordRaw, wordCoreRun, by
    simpa only [mappedNames, mappedContext, mappedEnvironment, heap] using bridge⟩

private def swappedEnvironment : Resolved.Environment :=
  [(wordId, .word word), (noiseId, .hostFunction .storageRead),
    (flagId, .bool true), (payloadId, payload), (flagId, .bool false)]
private def swappedCaptured : List (Resolved.LocalId × RuntimeValue) :=
  swappedEnvironment.map (fun row => (row.1, RuntimeValue.ofCore row.2))
private theorem swappedWordRaw : ClosedSourceExpressionEvaluates oldOwner names swappedCaptured
    heap wordSource (.word word.bitNot) heap := by
  have found : Resolved.LocalScope.Lookup swappedEnvironment wordId (.word word) := .head
  have child : ClosedSourceExpressionEvaluates oldOwner names swappedCaptured heap
      wordRef (.word word) heap := by
    simpa [swappedCaptured, wordRef, reference, ident, RuntimeValue.ofCore] using
      ClosedSourceExpressionEvaluates.reference wordNamed (embedLookup found)
  simpa [wordSource] using ClosedSourceExpressionEvaluates.bitNot child
private def wrongTyped : Syntax.Expr :=
  ⟨span 12 17, .unary ⟨span 12 13, .bitNot⟩ flagRef⟩
private def outsideGate : Syntax.Expr :=
  ⟨span 18 24, .call flagRef ⟨span 22 24, []⟩⟩

/-- Admission and exact ID alignment remain independent premises: a structurally
admitted but ill-typed unary is rejected, while a misaligned raw run may exist. -/
theorem checked_owner_boundaries :
    ¬ Function.Surjective shift ∧ store ≠ [] ∧
    names[2]? = some ("flag", shadowFlagId) ∧
    environment.ids[4]? = some flagId ∧
    ClosedSourceDataExpression wrongTyped ∧
    elaborateLocalExpression? names context wrongTyped = none ∧
    swappedEnvironment.ids ≠ context.ids ∧
    ClosedSourceExpressionEvaluates oldOwner names swappedCaptured heap
      wordSource (.word word.bitNot) heap ∧
    ¬ ClosedSourceDataExpression outsideGate := by
  refine ⟨shift_not_surjective, by decide, rfl, rfl, .bitNot .reference, ?_, ?_,
    swappedWordRaw, ?_⟩
  · simp [elaborateLocalExpression?, resolveLocalExpression?, LocalNameTable.lookup?,
      names, context, wrongTyped, flagRef, reference, ident, Resolved.Expr.lower?,
      Resolved.LocalScope.ids, Resolved.LocalScope.values, Resolved.LocalScope.index?,
      flagId, wordId, noiseId, payloadId, shadowFlagId, lid, oldOwner, foreignOwner,
      declaration]
    intro type inferred
    cases Core.infer_sound inferred with
    | unary operand => cases operand with | var found => cases found
  · decide
  · intro admitted
    cases admitted

end Tests.ADR0316CheckedDataOwnerConsumer
