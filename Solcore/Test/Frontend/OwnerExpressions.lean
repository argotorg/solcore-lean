import Solcore.Frontend.Fragments.Internal.LambdaDepth
import Solcore.Frontend.Fragments.Internal.ClosedSource
import Solcore.Core.Internal.WordComparisons
import Solcore.Frontend.Fragments.Internal.LocalExpressions
import Solcore.Frontend.Fragments.Internal.Foundations
import Solcore.Resolved.LocalScope
import Solcore.Frontend.Fragments.Internal.Expected
import Solcore.Core.Correspondence
import Solcore.Syntax.Parser.Internal.TermBasics
import Solcore.Frontend.Fragments.Internal.LocalFunctionApplication

/-!
# Owner expression tests

Owners of checked expressions and core bodies: covariance, reflection and expected data lambdas.
-/

section
-- leanmerge: from Solcore.Test.FrontendOwnerCheckedBinaryDataExpressionProperties
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
end

section
-- leanmerge: from Solcore.Test.FrontendOwnerCheckedDataExpressionProperties
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
end

section
-- leanmerge: from Solcore.Test.FrontendOwnerCoreBodyProperties
/- Independent checker, exact-ID, Core, and old/mapped raw paths precede the bridge.
The fixture retains spans, typed/inferred freshness, ordered match misses, a foreign
owner, duplicate spelling, an opaque embedded closure, and a nonempty Core store. -/
set_option autoImplicit false
namespace Tests.ADR0314OwnerCoreBodyConsumerIndependent
open Solcore Solcore.Frontend

private def declaration (index : Nat) : Resolved.DeclarationId :=
  ⟨⟨.main, ⟨[⟨"OwnerCoreBody", by decide⟩], by decide⟩⟩, index⟩
private def localId (declarationIndex binderIndex : Nat) : Resolved.LocalId :=
  ⟨declaration declarationIndex, binderIndex⟩
private def owner := declaration 4
private def foreign := declaration 9
private def shift (id : Resolved.DeclarationId) : Resolved.DeclarationId :=
  { id with declarationIndex := id.declarationIndex + 5 }
private theorem shift_injective : Function.Injective shift := by
  intro left right same
  have modules := congrArg Resolved.DeclarationId.moduleId same
  have indices := Nat.add_right_cancel (congrArg Resolved.DeclarationId.declarationIndex same)
  cases left; cases right; cases modules; cases indices; rfl
private theorem shift_not_surjective : ¬ Function.Surjective shift := by
  intro onto
  obtain ⟨preimage, same⟩ := onto (declaration 0)
  have impossible := congrArg Resolved.DeclarationId.declarationIndex same
  change preimage.declarationIndex + 5 = 0 at impossible
  omega

private def sourceId : Syntax.SourceId := ⟨.main, "owner-core-body.sol"⟩
private def span (offset : Nat) : Syntax.SourceSpan := ⟨sourceId, offset, offset + 3⟩
private def ident (offset : Nat) (name : String) : Syntax.Identifier := ⟨span offset, name⟩
private def ref (offset : Nat) (name : String) : Syntax.Expr :=
  ⟨span offset, .identifier (ident offset name)⟩
private def annotation : Syntax.TypeExpr :=
  ⟨span 11, .named ⟨span 12, ⟨⟨⟨span 13, "Word"⟩, []⟩⟩⟩ none⟩
private def returned (offset : Nat) (name : String) : Syntax.Block :=
  ⟨span offset, [⟨span (offset + 1), .returnStmt (some (ref (offset + 2) name))⟩]⟩
private def pattern (offset : Nat) (digits : String) : Syntax.Pattern :=
  ⟨span offset, .literal ⟨span (offset + 1), .decimal digits⟩⟩
private def wildcard : Syntax.Pattern := ⟨span 72, .wildcard (span 73)⟩
private def arm (offset : Nat) (tag : Syntax.Pattern) (name : String) : Syntax.MatchCase :=
  ⟨span offset, ⟨tag, returned (offset + 2) name⟩⟩
private def cases : List Syntax.MatchCase :=
  [arm 40 (pattern 41 "1") "seed", arm 50 (pattern 51 "2") "inferred",
    arm 60 wildcard "typed"]
private def body : Syntax.Block := ⟨span 0,
  [⟨span 10, .letDecl (ident 14 "typed") (some annotation) (some (ref 15 "seed"))⟩,
   ⟨span 20, .letDecl (ident 21 "inferred") none (some (ref 22 "typed"))⟩,
   ⟨span 30, .matchWith ⟨span 31, ⟨ref 32 "tag", []⟩⟩ ⟨span 33, ⟨cases, none⟩⟩⟩]⟩

private def inputs : LocalTypeInputs :=
  ⟨[⟨"seed", localId 4 7, .word⟩, ⟨"tag", localId 9 31, .word⟩,
    ⟨"seed", localId 4 2, .bool⟩], by decide⟩
private def types : TypeNameTable := [(["Word"], .word)]
private def mappedInputs : LocalTypeInputs :=
  inputs.mapIds (ownerLocalIdMap shift) (ownerLocalIdMap_injective shift shift_injective)
private def first := Core.Word.ofNatModulo 1
private def selected := Core.Word.ofNatModulo 2
private def payload : Core.Value :=
  .closure .bool .word (.var 1) [.cellRef .word 1, .hostFunction .callerAddress]
private def environment : Resolved.Environment :=
  [(localId 4 7, payload), (localId 9 31, .word selected), (localId 4 2, .bool false)]
private def mappedEnvironment : Resolved.Environment :=
  Resolved.LocalScope.mapIds (ownerLocalIdMap shift) environment
private def store : Core.Store :=
  [.word (Core.Word.ofNatModulo 77), .cellRef .word 0, .hostFunction .storageRead]

private def matchCore : Core.Expr := .letE (.var 3)
  (.ifE (.binary .wordEq (.var 0) (.word first)) (.var 3)
    (.ifE (.binary .wordEq (.var 0) (.word selected)) (.var 1) (.var 2)))
private def core : Core.Expr := .letE (.var 0) (.letE (.var 0) matchCore)

private theorem old_ids : environment.ids = inputs.context.ids := by rfl

private theorem first_meaning : WordMatchPatternClassifies (pattern 41 "1") (some first) :=
  .literal ⟨⟨span 42, .decimal "1"⟩, rfl,
    .decimal (by decide) (.cons (.decimal (digit := 1) (by decide) rfl) .nil)⟩
private theorem selected_meaning : WordMatchPatternClassifies (pattern 51 "2") (some selected) :=
  .literal ⟨⟨span 52, .decimal "2"⟩, rfl,
    .decimal (by decide) (.cons (.decimal (digit := 2) (by decide) rfl) .nil)⟩
private theorem selected_choice :
    RuntimeWordMatchChooses (RuntimeValue.ofCore (.word selected)) cases none
      (returned 52 "inferred") 2 := by
  have choice : RuntimeWordMatchChooses (.word selected)
      [arm 40 (pattern 41 "1") "seed", arm 50 (pattern 51 "2") "inferred",
        arm 60 wildcard "typed"] none (returned 52 "inferred") 2 :=
    RuntimeWordMatchChooses.miss (word := selected) (literal := first)
      (first := arm 40 (pattern 41 "1") "seed")
      (rest := [arm 50 (pattern 51 "2") "inferred", arm 60 wildcard "typed"])
      first_meaning (by decide)
      (RuntimeWordMatchChooses.hit (word := selected)
        (first := arm 50 (pattern 51 "2") "inferred")
        (rest := [arm 60 wildcard "typed"]) selected_meaning)
  simpa only [cases, RuntimeValue.ofCore] using choice

private abbrev ChildGraph (names : LocalNameTable) (context : Resolved.Context)
    (source : Syntax.Expr) (expression : Core.Expr) (type : Core.Ty) : Prop :=
  elaborateLocalExpression? names context source = some (expression, type)

private theorem old_elaboration :
    ComputationReturnTreeElaborates ChildGraph types owner inputs body core .word := by
  unfold body core
  apply ComputationReturnTreeElaborates.binding (initializerCore := .var 0)
  · exact .named .head
  · exact elaborateLocalExpression?_complete (.identifier .head) (.var .head) (.var .head)
  apply ComputationReturnTreeElaborates.inferred (initializerCore := .var 0)
  · exact elaborateLocalExpression?_complete (.identifier .head) (.var .head) (.var .head)
  apply ComputationReturnTreeElaborates.wordMatch
      (entries := [(arm 40 (pattern 41 "1") "seed", some first, .var 2),
        (arm 50 (pattern 51 "2") "inferred", some selected, .var 0),
        (arm 60 wildcard "typed", none, .var 1)])
      (defaultEntry := none)
  · exact elaborateLocalExpression?_complete
      (.identifier (.tail (by decide) (.tail (by decide) (.tail (by decide) .head))))
      (.var (.tail (by decide) (.tail (by decide) (.tail (by decide) .head))))
      (.var (.tail (by decide) (.tail (by decide) (.tail (by decide) .head))))
  · simp [cases]
  · intro entry member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl
    · exact first_meaning
    · exact selected_meaning
    · exact .wildcard rfl
  · exact .inl rfl
  · intro entry member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl
    · exact .expression (elaborateLocalExpression?_complete
        (.identifier (.tail (by decide) (.tail (by decide) .head)))
        (.var (.tail (by decide) (.tail (by decide) .head)))
        (.var (.tail (by decide) (.tail (by decide) .head))))
    · exact .expression (elaborateLocalExpression?_complete
        (.identifier .head) (.var .head) (.var .head))
    · exact .expression (elaborateLocalExpression?_complete
        (.identifier (.tail (by decide) .head))
        (.var (.tail (by decide) .head)) (.var (.tail (by decide) .head)))
  · rfl
  · intro entry member; cases member
  · simp [Core.Expr.weakenAt]

private theorem old_accepted :
    elaborateComputationReturnTree? elaborateLocalExpression? types owner inputs body =
      some (core, .word) :=
  (elaborateComputationReturnTree?_iff (ChildElab := ChildGraph) Iff.rfl).mpr old_elaboration

private theorem mapped_accepted :
    elaborateComputationReturnTree? elaborateLocalExpression? types (shift owner) mappedInputs body =
      some (core, .word) := by
  exact (elaborateComputationReturnTree?_mapOwner shift shift_injective elaborateLocalExpression?
    (elaborateLocalExpression?_mapIds (ownerLocalIdMap shift)
      (ownerLocalIdMap_injective shift shift_injective)) types owner inputs body).trans old_accepted
private theorem mapped_ids : mappedEnvironment.ids = mappedInputs.context.ids := by rfl

private theorem old_raw :
    ClosedSourceBodyEvaluates owner inputs.names
      (environment.map (fun row => (row.1, RuntimeValue.ofCore row.2)))
      (store.map RuntimeValue.ofCore) body (RuntimeValue.ofCore payload)
      (store.map RuntimeValue.ofCore) := by
  apply ClosedSourceBodyEvaluates.binding
  · exact .reference .head .head
  apply ClosedSourceBodyEvaluates.inferred
  · exact .reference .head .head
  apply ClosedSourceBodyEvaluates.wordMatch
  · exact .reference (.tail (by decide) (.tail (by decide) (.tail (by decide) .head)))
      (.tail (by decide) (.tail (by decide) (.tail (by decide) .head)))
  · exact selected_choice
  · exact .expression (.reference .head .head)

private theorem mapped_raw :
    ClosedSourceBodyEvaluates (shift owner)
      mappedInputs.names (mappedEnvironment.map (fun row => (row.1, RuntimeValue.ofCore row.2)))
      (store.map RuntimeValue.ofCore) body (RuntimeValue.ofCore payload)
      (store.map RuntimeValue.ofCore) := by
  apply ClosedSourceBodyEvaluates.binding
  · exact .reference .head .head
  apply ClosedSourceBodyEvaluates.inferred
  · exact .reference .head .head
  apply ClosedSourceBodyEvaluates.wordMatch
  · exact .reference (.tail (by decide) (.tail (by decide) (.tail (by decide) .head)))
      (.tail (by decide) (.tail (by decide) (.tail (by decide) .head)))
  · exact selected_choice
  · exact .expression (.reference .head .head)

private theorem data_body : ClosedSourceDataBody body := by
  apply ClosedSourceDataBody.binding .reference
  apply ClosedSourceDataBody.binding .reference
  apply ClosedSourceDataBody.wordMatch .reference
  · intro candidate member
    simp only [cases, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl <;> exact .expression .reference
  · intro fallback member; cases member

private theorem core_path :
    Core.Evaluates environment.values store core payload store := by
  apply Core.Evaluates.letE (.var rfl)
  apply Core.Evaluates.letE (.var rfl)
  apply Core.Evaluates.letE (.var rfl)
  apply Core.Evaluates.ifFalse
  · exact Core.Evaluates.wordEq_ne (by decide) (.var rfl) .word
  apply Core.Evaluates.ifTrue
  · exact Core.Evaluates.wordEq_eq rfl (.var rfl) .word
  · exact .var rfl

/-- The complete old and renamed paths are concrete evidence before the bridge is consumed. -/
theorem typed_inferred_ordered_match_complete_boundary
    (actualValue : RuntimeValue) (actualFinal : List RuntimeValue) :
    ¬ Function.Surjective shift ∧
    body.span = span 0 ∧ body.value.map (fun statement => statement.span) = [span 10, span 20, span 30] ∧
    Resolved.freshLocalId owner inputs.ids = localId 4 8 ∧
    Resolved.freshLocalId owner ((localId 4 8) :: inputs.ids) = localId 4 9 ∧
    elaborateComputationReturnTree? elaborateLocalExpression? types owner inputs body = some (core, .word) ∧
    environment.ids = inputs.context.ids ∧
    elaborateComputationReturnTree? elaborateLocalExpression? types (shift owner) mappedInputs body = some (core, .word) ∧
    mappedEnvironment.ids = mappedInputs.context.ids ∧
    ClosedSourceBodyEvaluates owner inputs.names
      (environment.map (fun row => (row.1, RuntimeValue.ofCore row.2)))
      (store.map RuntimeValue.ofCore) body (RuntimeValue.ofCore payload) (store.map RuntimeValue.ofCore) ∧
    ClosedSourceBodyEvaluates (shift owner)
      mappedInputs.names (mappedEnvironment.map (fun row => (row.1, RuntimeValue.ofCore row.2)))
      (store.map RuntimeValue.ofCore) body (RuntimeValue.ofCore payload) (store.map RuntimeValue.ofCore) ∧
    Core.Evaluates environment.values store core payload store ∧
    (ClosedSourceBodyEvaluates (shift owner)
      mappedInputs.names (mappedEnvironment.map (fun row => (row.1, RuntimeValue.ofCore row.2)))
      (store.map RuntimeValue.ofCore) body actualValue actualFinal ↔
      ∃ value finalStore, actualValue = RuntimeValue.ofCore value ∧
        actualFinal = finalStore.map RuntimeValue.ofCore ∧
        Core.Evaluates environment.values store core value finalStore) := by
  have bridge := data_body.mapOwners_core_evaluates_iff shift shift_injective
    (initialStore := store) (actualValue := actualValue) (actualFinal := actualFinal)
    old_accepted old_ids
  exact ⟨shift_not_surjective, rfl, rfl, rfl, rfl, old_accepted, old_ids, mapped_accepted,
    mapped_ids, old_raw, mapped_raw, core_path, bridge.2.2⟩

private def single : Syntax.Block := returned 80 "seed"
private def swapped : Resolved.Environment :=
  [(localId 9 31, .word selected), (localId 4 7, payload), (localId 4 2, .bool false)]
private def nonimage : RuntimeValue :=
  .sourceClosure (ref 90 "seed") owner inputs.names
    [(localId 4 7, RuntimeValue.ofCore (.cellRef .word 1))]
private def mixed : List (Resolved.LocalId × RuntimeValue) :=
  [(localId 4 7, nonimage), (localId 9 31, .word selected), (localId 4 2, .bool false)]

/-- Raw success supplies no checker, alignment, or Core-image premise; `none` is only an option result. -/
theorem raw_success_does_not_recover_missing_boundary_premises :
    elaborateComputationReturnTree? elaborateLocalExpression? [] owner inputs body = none ∧
    elaborateComputationReturnTree? elaborateLocalExpression? [] (shift owner) mappedInputs body = none ∧
    ClosedSourceBodyEvaluates owner inputs.names
      (environment.map (fun row => (row.1, RuntimeValue.ofCore row.2)))
      (store.map RuntimeValue.ofCore) body (RuntimeValue.ofCore payload) (store.map RuntimeValue.ofCore) ∧
    ClosedSourceBodyEvaluates (shift owner) mappedInputs.names
      (mappedEnvironment.map (fun row => (row.1, RuntimeValue.ofCore row.2)))
      (store.map RuntimeValue.ofCore) body (RuntimeValue.ofCore payload) (store.map RuntimeValue.ofCore) ∧
    swapped.ids ≠ inputs.context.ids ∧
    elaborateComputationReturnTree? elaborateLocalExpression? types owner inputs single = some (.var 0, .word) ∧
    ClosedSourceBodyEvaluates owner inputs.names
      (swapped.map (fun row => (row.1, RuntimeValue.ofCore row.2)))
      (store.map RuntimeValue.ofCore) single (RuntimeValue.ofCore payload) (store.map RuntimeValue.ofCore) ∧
    Core.Evaluates swapped.values store (.var 0) (.word selected) store ∧ payload ≠ .word selected ∧
    ClosedSourceBodyEvaluates owner inputs.names mixed (store.map RuntimeValue.ofCore)
      single nonimage (store.map RuntimeValue.ofCore) ∧
    ¬ ∃ value, nonimage = RuntimeValue.ofCore value := by
  have rejected : elaborateComputationReturnTree? elaborateLocalExpression? [] owner inputs body = none := by
    simp [body, annotation, elaborateComputationReturnTree?, interpretStructuralType?,
      TypeNameTable.lookup?]
  have mappedRejected : elaborateComputationReturnTree? elaborateLocalExpression? []
      (shift owner) mappedInputs body = none := by
    exact (elaborateComputationReturnTree?_mapOwner shift shift_injective elaborateLocalExpression?
      (elaborateLocalExpression?_mapIds (ownerLocalIdMap shift)
        (ownerLocalIdMap_injective shift shift_injective)) [] owner inputs body).trans rejected
  have checked : elaborateComputationReturnTree? elaborateLocalExpression? types owner inputs single =
      some (.var 0, .word) := by
    simpa only [single, returned, elaborateComputationReturnTree?] using
      (elaborateLocalExpression?_complete (.identifier .head) (.var .head) (.var .head) :
        elaborateLocalExpression? inputs.names inputs.context (ref 82 "seed") = some (.var 0, .word))
  have misalignedRaw : ClosedSourceBodyEvaluates owner inputs.names
      (swapped.map (fun row => (row.1, RuntimeValue.ofCore row.2))) (store.map RuntimeValue.ofCore)
      single (RuntimeValue.ofCore payload) (store.map RuntimeValue.ofCore) :=
    .expression (.reference .head (.tail (by decide) .head))
  have sourceRaw : ClosedSourceBodyEvaluates owner inputs.names mixed (store.map RuntimeValue.ofCore)
      single nonimage (store.map RuntimeValue.ofCore) := .expression (.reference .head .head)
  have payloadDifferent : payload ≠ Core.Value.word selected := by intro same; cases same
  refine ⟨rejected, mappedRejected, old_raw, mapped_raw, ?_, checked, misalignedRaw,
    .var rfl, payloadDifferent, sourceRaw, ?_⟩
  · change [localId 9 31, localId 4 7, localId 4 2] ≠ [localId 4 7, localId 9 31, localId 4 2]
    decide
  · rintro ⟨value, same⟩
    have projected := congrArg RuntimeValue.toCore? same
    simp only [nonimage, RuntimeValue.toCore?, RuntimeValue.toCore?_ofCore, reduceCtorEq] at projected


end Tests.ADR0314OwnerCoreBodyConsumerIndependent
end

section
-- leanmerge: from Solcore.Test.FrontendOwnerCoreExpressionProperties
/- The concrete old local/Core and mapped raw paths are built before the new
owner/Core image theorem is consumed. No runtime validity premise is added. -/
set_option autoImplicit false
namespace Tests.OwnerCoreExpressionConsumer
open Solcore Solcore.Frontend

private def sourceText : String :=
  "guard || dormant ? (payload, left + right) : (fallback, payload)"
private def sourceFile : Syntax.SourceFile :=
  ⟨⟨.main,"adr0314-owner-core-expression.sol"⟩,sourceText⟩
private def span (startByte endByte : Nat) : Syntax.SourceSpan :=
  ⟨sourceFile.id,startByte,endByte⟩
private def ident (startByte endByte : Nat) (text : String) : Syntax.Identifier :=
  ⟨span startByte endByte,text⟩
private def ref (startByte endByte : Nat) (text : String) : Syntax.Expr :=
  ⟨span startByte endByte,.identifier (ident startByte endByte text)⟩

private def guard := ref 0 5 "guard"
private def dormant := ref 9 16 "dormant"
private def condition : Syntax.Expr :=
  ⟨span 0 16,.binary guard ⟨span 6 8,.logicalOr⟩ dormant⟩
private def payloadRef := ref 20 27 "payload"
private def leftRef := ref 29 33 "left"
private def rightRef := ref 36 41 "right"
private def addition : Syntax.Expr :=
  ⟨span 29 41,.binary leftRef ⟨span 34 35,.add⟩ rightRef⟩
private def chosen : Syntax.Expr :=
  ⟨span 19 42,.tuple ⟨span 20 41,[payloadRef,addition]⟩⟩
private def fallbackRef := ref 46 54 "fallback"
private def secondPayloadRef := ref 56 63 "payload"
private def skipped : Syntax.Expr :=
  ⟨span 45 64,.tuple ⟨span 46 63,[fallbackRef,secondPayloadRef]⟩⟩
private def source : Syntax.Expr :=
  ⟨Syntax.SourceSpan.fullFile sourceFile,
    .conditional condition (span 17 18) chosen (span 43 44) skipped⟩
private def sourceSpans : List Syntax.SourceSpan :=
  [source.span,span 0 16,span 0 5,span 6 8,span 9 16,span 17 18,
   span 19 42,span 20 41,span 20 27,span 29 41,span 29 33,span 34 35,
   span 36 41,span 43 44,span 45 64,span 46 63,span 46 54,span 56 63]

private def owner (index : Nat) : Resolved.DeclarationId :=
  ⟨⟨.main,⟨[⟨"OwnerCoreExpression",by decide⟩],by decide⟩⟩,index⟩
private def oldOwner := owner 314
private def foreignOwner := owner 9314
private def lid (own : Resolved.DeclarationId) (index : Nat) : Resolved.LocalId :=
  ⟨own,index⟩
private def guardId := lid oldOwner 1
private def payloadId := lid oldOwner 2
private def leftId := lid oldOwner 3
private def rightId := lid oldOwner 4
private def dormantId := lid foreignOwner 5
private def fallbackId := lid oldOwner 6
private def noiseId := lid foreignOwner 99
private def foreignPayloadId := lid foreignOwner 2

private def names : LocalNameTable :=
  [("guard",guardId),("payload",payloadId),("left",leftId),("right",rightId),
   ("dormant",dormantId),("fallback",fallbackId),("payload",foreignPayloadId),
   ("guard",noiseId)]
private def leftWord : Core.Word := Core.Word.ofNatModulo 40
private def rightWord : Core.Word := Core.Word.ofNatModulo 2
private def payload : Core.Value :=
  .closure .unit (.product .word .unit) (.pair (.var 0) .unit)
    [.cellRef .word 73,.hostFunction .storageWrite,
     .closure .unit .unit (.var 9) [.hostFunction .storageRead]]
private def environment : Resolved.Environment :=
  [(noiseId,.hostFunction .storageRead),(guardId,.bool true),(payloadId,payload),
   (leftId,.word leftWord),(rightId,.word rightWord),(dormantId,.bool false),
   (fallbackId,.cellRef .word 44),(payloadId,.unit)]
private def initialStore : Core.Store :=
  [payload,.cellRef (.function .word .word) 800,.hostFunction .storageWrite,
   .pair (.hostFunction .storageRead) (.cellRef .bool 801)]
private def result : Core.Value :=
  .pair payload (.word (leftWord.add rightWord))

private def resolved : Resolved.Expr :=
  .ifE (.ifE (.var guardId) (.bool true) (.var dormantId))
    (.pair (.var payloadId) (.binary .wordAdd (.var leftId) (.var rightId)))
    (.pair (.var fallbackId) (.var payloadId))
private def core : Core.Expr :=
  .ifE (.ifE (.var 1) (.bool true) (.var 5))
    (.pair (.var 2) (.binary .wordAdd (.var 3) (.var 4)))
    (.pair (.var 6) (.var 2))

private def shift (declaration : Resolved.DeclarationId) : Resolved.DeclarationId :=
  ⟨declaration.moduleId,declaration.declarationIndex+1⟩
private theorem shift_injective : Function.Injective shift := by
  intro left right equal
  have modules := congrArg Resolved.DeclarationId.moduleId equal
  have indices := congrArg Resolved.DeclarationId.declarationIndex equal
  cases left; cases right
  simp only [shift] at modules indices
  cases modules
  cases Nat.add_right_cancel indices
  rfl
private theorem shift_not_surjective : ¬ Function.Surjective shift := by
  intro surjective
  obtain ⟨before,equal⟩ := surjective (owner 0)
  have impossible := congrArg Resolved.DeclarationId.declarationIndex equal
  change before.declarationIndex+1=0 at impossible
  omega

private theorem nameLookup {text id}
    (found : names.lookup? text = some id) : LocalNameTable.Lookup names text id :=
  LocalNameTable.lookup?_iff.mp found
private theorem indexLookup {id index}
    (found : Resolved.LocalScope.index? environment.ids id = some index) :
    Resolved.LocalScope.IndexOf environment.ids id index :=
  Resolved.LocalScope.index?_iff.mp found

private theorem guardNamed : LocalNameTable.Lookup names "guard" guardId :=
  nameLookup (by decide)
private theorem payloadNamed : LocalNameTable.Lookup names "payload" payloadId :=
  nameLookup (by decide)
private theorem leftNamed : LocalNameTable.Lookup names "left" leftId :=
  nameLookup (by decide)
private theorem rightNamed : LocalNameTable.Lookup names "right" rightId :=
  nameLookup (by decide)
private theorem guardFound :
    Resolved.LocalScope.Lookup environment guardId (.bool true) :=
  .tail (by decide) .head
private theorem payloadFound :
    Resolved.LocalScope.Lookup environment payloadId payload :=
  .tail (by decide) (.tail (by decide) .head)
private theorem leftFound :
    Resolved.LocalScope.Lookup environment leftId (.word leftWord) :=
  .tail (by decide) (.tail (by decide) (.tail (by decide) .head))
private theorem rightFound :
    Resolved.LocalScope.Lookup environment rightId (.word rightWord) :=
  .tail (by decide) (.tail (by decide) (.tail (by decide) (.tail (by decide) .head)))

private theorem gate : ClosedSourceDataExpression source := by
  exact .conditional (.logicalOr .reference .reference)
    (.pair .reference (.strictWordBinary .reference .reference (by decide) (by decide)))
    (.pair .reference .reference)
private theorem resolution : ResolvesLocalExpression names source resolved := by
  refine .conditional (.logicalOr ?_ ?_) (.pair ?_ (.add ?_ ?_)) (.pair ?_ ?_)
  all_goals exact .identifier (nameLookup (by decide))
private theorem lowering : Resolved.Lowers environment.ids resolved core := by
  refine .ifE (.ifE ?_ .bool ?_) (.pair ?_ (.binary ?_ ?_)) (.pair ?_ ?_)
  all_goals exact .var (indexLookup (by decide))

private theorem oldLocal :
    LocalExpressionEvaluates names environment initialStore source result initialStore := by
  exact .ifTrue (.orTrue (.identifier guardNamed guardFound))
    (.pair (.identifier payloadNamed payloadFound)
      (.add (.identifier leftNamed leftFound) (.identifier rightNamed rightFound)))
private theorem oldRaw :
    ClosedSourceExpressionEvaluates oldOwner names
      (environment.map (fun row => (row.1,RuntimeValue.ofCore row.2)))
      (initialStore.map RuntimeValue.ofCore) source (RuntimeValue.ofCore result)
      (initialStore.map RuntimeValue.ofCore) := by
  exact (gate.local_evaluates_iff (owner:=oldOwner)).mpr
    ⟨result,initialStore,rfl,rfl,oldLocal⟩
private theorem coreLookup {index value}
    (found : environment.values[index]? = some value) :
    Core.Evaluates environment.values initialStore (.var index) value initialStore :=
  .var found
private theorem oldCore :
    Core.Evaluates environment.values initialStore core result initialStore := by
  exact .ifTrue (.ifTrue
      (coreLookup (index:=1) (value:=.bool true) rfl) .bool)
    (.pair (coreLookup (index:=2) (value:=payload) rfl)
      (.binary
        (coreLookup (index:=3) (value:=.word leftWord) rfl)
        (coreLookup (index:=4) (value:=.word rightWord) rfl) rfl))

private theorem mappedRaw :
    ClosedSourceExpressionEvaluates (shift oldOwner)
      (LocalNameTable.mapIds (ownerLocalIdMap shift) names)
      ((Resolved.LocalScope.mapIds (ownerLocalIdMap shift) environment).map
        (fun row => (row.1,RuntimeValue.ofCore row.2)))
      (initialStore.map RuntimeValue.ofCore) source (RuntimeValue.ofCore result)
      (initialStore.map RuntimeValue.ofCore) := by
  have renamed := oldRaw.mapOwners shift shift_injective
  simpa only [mapRuntimeCapturedOwners_ofCore,mapRuntimeStoreOwners_ofCore,
    RuntimeValue.mapOwners_ofCore] using renamed

/-- The fixture keeps exact source ranges, a nonempty mixed Core store, repeated
rows, a foreign owner, and an injective but genuinely non-surjective shift. -/
theorem fixture_controls :
    Function.Injective shift ∧ ¬ Function.Surjective shift ∧
    initialStore ≠ [] ∧ source.span = Syntax.SourceSpan.fullFile sourceFile ∧
    sourceSpans.all (fun item => item.isValidFor sourceFile) = true ∧
    environment.ids[0]? = some noiseId ∧ environment.ids[2]? = some payloadId ∧
    environment.ids[7]? = some payloadId ∧ names[1]? = some ("payload",payloadId) ∧
    names[6]? = some ("payload",foreignPayloadId) := by
  refine ⟨shift_injective,shift_not_surjective,by decide,rfl,by decide,?_⟩
  decide

/-- All original premises and the known mapped raw endpoint are independent
constructions; in particular the unselected `dormant` child is still resolved. -/
theorem independent_paths :
    ClosedSourceDataExpression source ∧
    ResolvesLocalExpression names source resolved ∧
    Resolved.Lowers environment.ids resolved core ∧
    LocalExpressionEvaluates names environment initialStore source result initialStore ∧
    ClosedSourceExpressionEvaluates oldOwner names
      (environment.map (fun row => (row.1,RuntimeValue.ofCore row.2)))
      (initialStore.map RuntimeValue.ofCore) source (RuntimeValue.ofCore result)
      (initialStore.map RuntimeValue.ofCore) ∧
    Core.Evaluates environment.values initialStore core result initialStore ∧
    ClosedSourceExpressionEvaluates (shift oldOwner)
      (LocalNameTable.mapIds (ownerLocalIdMap shift) names)
      ((Resolved.LocalScope.mapIds (ownerLocalIdMap shift) environment).map
        (fun row => (row.1,RuntimeValue.ofCore row.2)))
      (initialStore.map RuntimeValue.ofCore) source (RuntimeValue.ofCore result)
      (initialStore.map RuntimeValue.ofCore) :=
  ⟨gate,resolution,lowering,oldLocal,oldRaw,oldCore,mappedRaw⟩

/-- Every arbitrary actual mapped endpoint is exactly in the old Core image,
while the independently built mapped endpoint witnesses that the boundary is live. -/
theorem arbitrary_mapped_endpoint_iff {actualValue : RuntimeValue}
    {actualFinal : List RuntimeValue} :
    ClosedSourceExpressionEvaluates (shift oldOwner)
      (LocalNameTable.mapIds (ownerLocalIdMap shift) names)
      ((Resolved.LocalScope.mapIds (ownerLocalIdMap shift) environment).map
        (fun row => (row.1,RuntimeValue.ofCore row.2)))
      (initialStore.map RuntimeValue.ofCore) source (RuntimeValue.ofCore result)
      (initialStore.map RuntimeValue.ofCore) ∧
    ResolvesLocalExpression (LocalNameTable.mapIds (ownerLocalIdMap shift) names) source
      (resolved.renameIds (ownerLocalIdMap shift)) ∧
    Resolved.Lowers
      (Resolved.LocalScope.ids (Resolved.LocalScope.mapIds (ownerLocalIdMap shift) environment))
      (resolved.renameIds (ownerLocalIdMap shift)) core ∧
    (ClosedSourceExpressionEvaluates (shift oldOwner)
      (LocalNameTable.mapIds (ownerLocalIdMap shift) names)
      ((Resolved.LocalScope.mapIds (ownerLocalIdMap shift) environment).map
        (fun row => (row.1,RuntimeValue.ofCore row.2)))
      (initialStore.map RuntimeValue.ofCore) source actualValue actualFinal ↔
      ∃ value finalStore, actualValue=RuntimeValue.ofCore value ∧
        actualFinal=finalStore.map RuntimeValue.ofCore ∧
        Core.Evaluates environment.values initialStore core value finalStore) := by
  obtain ⟨data,resolves,lowers,_local,_oldRaw,_core,mapped⟩ := independent_paths
  have transported := data.mapOwners_core_evaluates_iff shift shift_injective
    (owner:=oldOwner) (names:=names) (environment:=environment)
    (initialStore:=initialStore) (actualValue:=actualValue) (actualFinal:=actualFinal)
    resolves lowers
  exact ⟨mapped,transported.1,transported.2.1,transported.2.2⟩


end Tests.OwnerCoreExpressionConsumer
end

section
-- leanmerge: from Solcore.Test.FrontendOwnerCovarianceBoundaryProperties
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
end

section
-- leanmerge: from Solcore.Test.FrontendOwnerCovarianceSymbolicProperties
/- Independent original constructors and direct depth equations precede covariance.
Ordered rows, arbitrary opaque values and whole stores are never projected away.
The selected literal count is not an evaluator budget or a runtime cost. -/
set_option autoImplicit false
namespace Tests.OwnerCovarianceSymbolic
open Solcore Solcore.Frontend
private abbrev E := ClosedSourceExpressionEvaluates
private abbrev B := ClosedSourceBodyEvaluates
private def ref (s : Syntax.SourceSpan) (name : Syntax.Identifier) : Syntax.Expr := ⟨s,.identifier name⟩
private def result (value : RuntimeValue) (word : Core.Word) : RuntimeValue :=
  .pair value (.pair (.word (word.add word)) (.bool false))
private def nested (s ts os : Syntax.SourceSpan) (x w b : Syntax.Identifier) (bad : Syntax.Expr) : Syntax.Expr :=
  ⟨s,.tuple ⟨ts,[ref s x,⟨s,.binary (ref s w) ⟨os,.add⟩ (ref s w)⟩,
    ⟨s,.binary (ref s b) ⟨os,.logicalAnd⟩ bad⟩]⟩⟩
private theorem reference_run {s name owner names captured store id value}
    (n : Nat) (named : LocalNameTable.Lookup names name.value id) (found : Resolved.LocalScope.Lookup captured id value) :
    evaluateClosedSourceExpression? (n+1) owner names captured store (ref s name) = some (value,store) := by
  simp only [ref,evaluateClosedSourceExpression?,LocalNameTable.lookup?_iff.mpr named,
    Resolved.LocalScope.lookup?_iff.mpr found,bind,Option.bind_some,pure]
private theorem nested_original {s ts os x w b bad owner names captured store xid wid bid value word}
    (xn : LocalNameTable.Lookup names x.value xid) (xf : Resolved.LocalScope.Lookup captured xid value)
    (wn : LocalNameTable.Lookup names w.value wid) (wf : Resolved.LocalScope.Lookup captured wid (.word word))
    (bn : LocalNameTable.Lookup names b.value bid) (bf : Resolved.LocalScope.Lookup captured bid (.bool false)) :
    E owner names captured store (nested s ts os x w b bad) (result value word) store := by
  have addition : E owner names captured store ⟨s,.binary (ref s w) ⟨os,.add⟩ (ref s w)⟩
      (.word (word.add word)) store := by
    simpa only [RuntimeValue.ofCore] using
      (ClosedSourceExpressionEvaluates.strictWordBinary (span:=s) (operatorSpan:=os)
        (left:=ref s w) (right:=ref s w) (.reference wn wf) (.reference wn wf) .add)
  exact .many (.reference xn xf) (.pair addition (.andFalse (.reference bn bf)))
private theorem nested_run {s ts os x w b bad owner names captured store xid wid bid value word}
    (n : Nat) (xn : LocalNameTable.Lookup names x.value xid) (xf : Resolved.LocalScope.Lookup captured xid value)
    (wn : LocalNameTable.Lookup names w.value wid) (wf : Resolved.LocalScope.Lookup captured wid (.word word))
    (bn : LocalNameTable.Lookup names b.value bid) (bf : Resolved.LocalScope.Lookup captured bid (.bool false)) :
    evaluateClosedSourceExpression? (n+4) owner names captured store (nested s ts os x w b bad) =
      some (result value word,store) := by
  simp only [nested,evaluateClosedSourceExpression?,ref,LocalNameTable.lookup?_iff.mpr xn,
    LocalNameTable.lookup?_iff.mpr wn,LocalNameTable.lookup?_iff.mpr bn,
    Resolved.LocalScope.lookup?_iff.mpr xf,Resolved.LocalScope.lookup?_iff.mpr wf,
    Resolved.LocalScope.lookup?_iff.mpr bf,bind,Option.bind_some,evaluateStrictWordBinary?,
    RuntimeValue.ofCore,Bool.false_eq_true,↓reduceIte,pure,result]

/-- A right-associated tuple returns an opaque value, an actual Word sum and a
short-circuit Boolean at the same depth after every injective owner relabeling. -/
theorem nested_word_and_skipped_child_covary
    (s ts os : Syntax.SourceSpan) (x w b : Syntax.Identifier) (bad : Syntax.Expr)
    (owner : Resolved.DeclarationId) (names : LocalNameTable) (captured : Resolved.LocalScope RuntimeValue)
    (store : List RuntimeValue) (xid wid bid : Resolved.LocalId) (value : RuntimeValue) (word : Core.Word)
    (xn : LocalNameTable.Lookup names x.value xid) (xf : Resolved.LocalScope.Lookup captured xid value)
    (wn : LocalNameTable.Lookup names w.value wid) (wf : Resolved.LocalScope.Lookup captured wid (.word word))
    (bn : LocalNameTable.Lookup names b.value bid) (bf : Resolved.LocalScope.Lookup captured bid (.bool false))
    (mapping : Resolved.DeclarationId → Resolved.DeclarationId) (injective : Function.Injective mapping) :
    E owner names captured store (nested s ts os x w b bad) (result value word) store ∧
    evaluateClosedSourceExpression? 3 owner names captured store (nested s ts os x w b bad) = none ∧
    (∀ extra, evaluateClosedSourceExpression? (extra+4) owner names captured store (nested s ts os x w b bad) =
      some (result value word,store)) ∧
    (∀ extra, evaluateClosedSourceExpression? (extra+4) (mapping owner)
      (LocalNameTable.mapIds (ownerLocalIdMap mapping) names) (mapRuntimeCapturedOwners mapping captured)
      (store.map (RuntimeValue.mapOwners mapping)) (nested s ts os x w b bad) =
      some (result (value.mapOwners mapping) word,store.map (RuntimeValue.mapOwners mapping))) ∧
    (∀ budget, evaluateClosedSourceExpression? budget (mapping owner)
      (LocalNameTable.mapIds (ownerLocalIdMap mapping) names) (mapRuntimeCapturedOwners mapping captured)
      (store.map (RuntimeValue.mapOwners mapping)) (nested s ts os x w b bad) =
      (evaluateClosedSourceExpression? budget owner names captured store (nested s ts os x w b bad)).map
        (fun ep => (ep.1.mapOwners mapping,ep.2.map (RuntimeValue.mapOwners mapping)))) := by
  have original : E owner names captured store (nested s ts os x w b bad) (result value word) store :=
    nested_original xn xf wn wf bn bf
  have direct := fun extra => nested_run (s:=s) (ts:=ts) (os:=os) (bad:=bad) (owner:=owner) (store:=store)
    extra xn xf wn wf bn bf
  have low : evaluateClosedSourceExpression? 3 owner names captured store (nested s ts os x w b bad) = none := by
    simp only [nested,evaluateClosedSourceExpression?,ref,LocalNameTable.lookup?_iff.mpr xn,
      Resolved.LocalScope.lookup?_iff.mpr xf,bind,Option.bind_some,Option.bind_none,pure]
  have covariance := fun budget => evaluateClosedSourceExpression?_mapOwners mapping injective
    budget owner names captured store (nested s ts os x w b bad)
  refine ⟨original,low,direct,?_,covariance⟩
  intro extra
  simpa only [direct extra,Option.map_some,result,RuntimeValue.mapOwners] using covariance (extra+4)

private def one : Core.Word := ⟨1,by decide⟩
private def literal (s : Syntax.SourceSpan) (text : String) : Syntax.CoreLiteral := ⟨s,.decimal text⟩
private def returning (s : Syntax.SourceSpan) (x : Syntax.Identifier) : Syntax.Block :=
  ⟨s,[⟨s,.returnStmt (some (ref s x))⟩]⟩
private def arm (s : Syntax.SourceSpan) (text : String) (body : Syntax.Block) : Syntax.MatchCase :=
  ⟨s,⟨⟨s,.literal (literal s text)⟩,body⟩⟩
private def arms (s : Syntax.SourceSpan) (x : Syntax.Identifier) (bad : Syntax.Block) : Nat → List Syntax.MatchCase
  | 0 => [arm s "1" (returning s x),arm s "1" bad]
  | n+1 => arm s "0" bad :: arms s x bad n
private def matching (s : Syntax.SourceSpan) (x : Syntax.Identifier) (bad : Syntax.Block) (n : Nat) : Syntax.Block :=
  ⟨s,[⟨s,.matchWith ⟨s,⟨⟨s,.literal (literal s "1")⟩,[]⟩⟩ ⟨s,⟨arms s x bad n,some bad⟩⟩⟩]⟩
private theorem one_meaning (s : Syntax.SourceSpan) : WordLiteralDenotes (literal s "1") one :=
  .decimal (by decide) (.cons (.decimal (digit:=1) (by decide) rfl) .nil)
private theorem zero_meaning (s : Syntax.SourceSpan) : WordLiteralDenotes (literal s "0") Core.Word.zero :=
  .decimal (by decide) (.cons (.decimal (digit:=0) (by decide) rfl) .nil)
private theorem original_choice (s : Syntax.SourceSpan) (x : Syntax.Identifier) (bad : Syntax.Block) (n : Nat) :
    RuntimeWordMatchChooses (.word one) (arms s x bad n) (some bad) (returning s x) (n+1) := by
  induction n with
  | zero => exact .hit (.literal ⟨literal s "1",rfl,one_meaning s⟩)
  | succ n ih => exact .miss (.literal ⟨literal s "0",rfl,zero_meaning s⟩) (by decide) ih
private theorem matching_run {s x bad n owner names captured store id value}
    (extra : Nat) (named : LocalNameTable.Lookup names x.value id) (found : Resolved.LocalScope.Lookup captured id value) :
    evaluateClosedSourceBody? (extra+3) owner names captured store (matching s x bad n) = some (value,store) := by
  simp only [matching,evaluateClosedSourceBody?,evaluateClosedSourceExpression?,
    interpretWordLiteral?_iff.mpr (one_meaning s),chooseRuntimeWordMatch?_iff.mpr (original_choice s x bad n),
    bind,Option.bind_some,pure,returning,evaluateClosedSourceBody?]
  exact reference_run extra named found

/-- Arbitrarily many ordered literal misses still select the first hit and the
whole opaque result at depth three; relabeling keeps that exact budget and store. -/
theorem ordered_match_keeps_selected_endpoint_and_budget
    (s : Syntax.SourceSpan) (x : Syntax.Identifier) (bad : Syntax.Block) (n : Nat)
    (owner : Resolved.DeclarationId) (names : LocalNameTable) (captured : Resolved.LocalScope RuntimeValue)
    (store : List RuntimeValue) (id : Resolved.LocalId) (value : RuntimeValue)
    (named : LocalNameTable.Lookup names x.value id) (found : Resolved.LocalScope.Lookup captured id value)
    (mapping : Resolved.DeclarationId → Resolved.DeclarationId) (injective : Function.Injective mapping) :
    RuntimeWordMatchChooses (.word one) (arms s x bad n) (some bad) (returning s x) (n+1) ∧
    B owner names captured store (matching s x bad n) value store ∧
    evaluateClosedSourceBody? 2 owner names captured store (matching s x bad n) = none ∧
    (∀ extra, evaluateClosedSourceBody? (extra+3) owner names captured store (matching s x bad n) = some (value,store)) ∧
    (∀ extra, evaluateClosedSourceBody? (extra+3) (mapping owner)
      (LocalNameTable.mapIds (ownerLocalIdMap mapping) names) (mapRuntimeCapturedOwners mapping captured)
      (store.map (RuntimeValue.mapOwners mapping)) (matching s x bad n) =
      some (value.mapOwners mapping,store.map (RuntimeValue.mapOwners mapping))) ∧
    (∀ budget, evaluateClosedSourceBody? budget (mapping owner)
      (LocalNameTable.mapIds (ownerLocalIdMap mapping) names) (mapRuntimeCapturedOwners mapping captured)
      (store.map (RuntimeValue.mapOwners mapping)) (matching s x bad n) =
      (evaluateClosedSourceBody? budget owner names captured store (matching s x bad n)).map
        (fun ep => (ep.1.mapOwners mapping,ep.2.map (RuntimeValue.mapOwners mapping)))) := by
  have choice := original_choice s x bad n
  have original : B owner names captured store (matching s x bad n) value store :=
    .wordMatch (.wordLiteral (one_meaning s)) choice (.expression (.reference named found))
  have direct := fun extra => matching_run (s:=s) (bad:=bad) (n:=n) (owner:=owner) (store:=store) extra named found
  have low : evaluateClosedSourceBody? 2 owner names captured store (matching s x bad n) = none := by
    simp only [matching,evaluateClosedSourceBody?,evaluateClosedSourceExpression?,
      interpretWordLiteral?_iff.mpr (one_meaning s),chooseRuntimeWordMatch?_iff.mpr choice,
      bind,Option.bind_some,pure,returning,evaluateClosedSourceBody?,evaluateClosedSourceExpression?]
  have covariance := fun budget => evaluateClosedSourceBody?_mapOwners mapping injective
    budget owner names captured store (matching s x bad n)
  exact ⟨choice,original,low,direct,fun extra => by
    simpa only [direct extra,Option.map_some] using covariance (extra+3),covariance⟩

private def owner (n : Nat) : Resolved.DeclarationId :=
  ⟨⟨.main,⟨[⟨"OwnerCovariance",by decide⟩],by decide⟩⟩,n⟩
private def lid (o n : Nat) : Resolved.LocalId := ⟨owner o,n⟩
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
private def span (n : Nat) : Syntax.SourceSpan := ⟨⟨.main,"owner-covariance.sol"⟩,n,n+1⟩
private def name (text : String) : Syntax.Identifier := ⟨span 0,text⟩
private def inertSource : Syntax.Expr := ref (span 10) (name "inert")
private def core (k : Nat) : RuntimeValue := .coreClosure .unit .word (.var 99)
  [.sourceClosure inertSource (owner (9+k)) [("q",lid (9+k) 7),("q",lid (2+k) 7)]
    [(lid (9+k) 7,.cellRef .word 700),(lid (9+k) 7,.unit)],.hostFunction .storageWrite]
private def payload (k : Nat) : RuntimeValue := .sourceClosure inertSource (owner (2+k))
  [("p",lid (2+k) 3),("p",lid (9+k) 3)]
  [(lid (2+k) 3,core k),(lid (2+k) 3,.bool false)]
private def store (k : Nat) : List RuntimeValue := [payload k,core k,.cellRef .word 900,.hostFunction .storageWrite]
private def names : LocalNameTable :=
  [("x",lid 2 0),("w",lid 2 1),("b",lid 2 2),("x",lid 9 0),("b",lid 2 9)]
private def rows : Resolved.LocalScope RuntimeValue :=
  [(lid 9 0,.unit),(lid 2 0,payload 0),(lid 2 0,.bool false),
    (lid 2 1,.word one),(lid 2 2,.bool false),(lid 2 2,.bool true)]
private theorem xn : LocalNameTable.Lookup names "x" (lid 2 0) := .head
private theorem wn : LocalNameTable.Lookup names "w" (lid 2 1) := .tail (by decide) .head
private theorem bn : LocalNameTable.Lookup names "b" (lid 2 2) := .tail (by decide) (.tail (by decide) .head)
private theorem xf : Resolved.LocalScope.Lookup rows (lid 2 0) (payload 0) := .tail (by decide) .head
private theorem wf : Resolved.LocalScope.Lookup rows (lid 2 1) (.word one) :=
  .tail (by decide) (.tail (by decide) (.tail (by decide) .head))
private theorem bf : Resolved.LocalScope.Lookup rows (lid 2 2) (.bool false) :=
  .tail (by decide) (.tail (by decide) (.tail (by decide) (.tail (by decide) .head)))
private theorem payload_mapped : (payload 0).mapOwners shift = payload 1 := by
  simp [payload,core,RuntimeValue.mapOwners,LocalNameTable.mapIds,ownerLocalIdMap,shift,lid,owner]
private theorem store_mapped : (store 0).map (RuntimeValue.mapOwners shift) = store 1 := by
  simp [store,payload,core,RuntimeValue.mapOwners,LocalNameTable.mapIds,ownerLocalIdMap,shift,lid,owner]

example : ¬ Function.Surjective shift ∧ store 0 ≠ [] ∧ owner 2 ≠ owner 9 := by
  refine ⟨?_,by decide,by decide⟩
  intro onto
  obtain ⟨before,equal⟩ := onto (owner 0)
  have impossible := congrArg Resolved.DeclarationId.declarationIndex equal
  change before.declarationIndex+1=0 at impossible
  omega

example (extra : Nat) :
    E (owner 2) names rows (store 0)
      (nested (span 1) (span 2) (span 3) (name "x") (name "w") (name "b") inertSource)
      (result (payload 0) one) (store 0) ∧
    evaluateClosedSourceExpression? (extra+4) (owner 3)
      (LocalNameTable.mapIds (ownerLocalIdMap shift) names) (mapRuntimeCapturedOwners shift rows) (store 1)
      (nested (span 1) (span 2) (span 3) (name "x") (name "w") (name "b") inertSource) =
      some (result (payload 1) one,store 1) := by
  have original : E (owner 2) names rows (store 0)
      (nested (span 1) (span 2) (span 3) (name "x") (name "w") (name "b") inertSource)
      (result (payload 0) one) (store 0) := nested_original xn xf wn wf bn bf
  have checked := nested_word_and_skipped_child_covary (span 1) (span 2) (span 3)
    (name "x") (name "w") (name "b") inertSource (owner 2) names rows (store 0)
    (lid 2 0) (lid 2 1) (lid 2 2) (payload 0) one xn xf wn wf bn bf shift shift_injective
  exact ⟨original,by simpa only [payload_mapped,store_mapped,shift,owner] using checked.2.2.2.1 extra⟩

example (n extra : Nat) :
    B (owner 2) names rows (store 0) (matching (span 4) (name "x") ⟨span 5,[]⟩ n) (payload 0) (store 0) ∧
    evaluateClosedSourceBody? (extra+3) (owner 3)
      (LocalNameTable.mapIds (ownerLocalIdMap shift) names) (mapRuntimeCapturedOwners shift rows) (store 1)
      (matching (span 4) (name "x") ⟨span 5,[]⟩ n) = some (payload 1,store 1) := by
  have original : B (owner 2) names rows (store 0) (matching (span 4) (name "x") ⟨span 5,[]⟩ n)
      (payload 0) (store 0) := .wordMatch (.wordLiteral (one_meaning _))
    (original_choice _ _ _ n) (.expression (.reference xn xf))
  have checked := ordered_match_keeps_selected_endpoint_and_budget (span 4) (name "x") ⟨span 5,[]⟩ n
    (owner 2) names rows (store 0) (lid 2 0) (payload 0) xn xf shift shift_injective
  exact ⟨original,by simpa only [payload_mapped,store_mapped,shift,owner] using checked.2.2.2.2.1 extra⟩

end Tests.OwnerCovarianceSymbolic
end

section
-- leanmerge: from Solcore.Test.FrontendOwnerExpectedDataLambdaCoreProperties
/- Old, renamed, and Core paths are concrete before either owner/data-lambda
bridge is consumed.  The fixture deliberately has no runtime typing premise. -/
set_option autoImplicit false
namespace Tests.ADR0315OwnerExpectedDataLambdaCoreConsumer
open Solcore Solcore.Frontend

private def declaration (index : Nat) : Resolved.DeclarationId :=
  ⟨⟨.main, ⟨[⟨"OwnerDataLambda", by decide⟩], by decide⟩⟩, index⟩
private def savedOwner := declaration 4
private def foreignOwner := declaration 9
private def callerOwner := declaration 12
private def localId (owner : Resolved.DeclarationId) (index : Nat) : Resolved.LocalId :=
  ⟨owner, index⟩
private def payloadId := localId savedOwner 7
private def noiseId := localId foreignOwner 31
private def shadowId := localId savedOwner 2
private def calleeId := localId callerOwner 40
private def argumentId := localId callerOwner 41
private def foreignCalleeId := localId foreignOwner 40

private def shift (owner : Resolved.DeclarationId) : Resolved.DeclarationId :=
  { owner with declarationIndex := owner.declarationIndex + 5 }
private theorem shift_injective : Function.Injective shift := by
  intro left right same
  have modules := congrArg Resolved.DeclarationId.moduleId same
  have indices := Nat.add_right_cancel (congrArg Resolved.DeclarationId.declarationIndex same)
  cases left; cases right; cases modules; cases indices; rfl
private theorem shift_not_surjective : ¬ Function.Surjective shift := by
  intro onto
  obtain ⟨before, same⟩ := onto (declaration 0)
  have impossible := congrArg Resolved.DeclarationId.declarationIndex same
  change before.declarationIndex + 5 = 0 at impossible
  omega

private def sourceId : Syntax.SourceId := ⟨.main, "owner-data-lambda.sol"⟩
private def span (offset : Nat) : Syntax.SourceSpan := ⟨sourceId, offset, offset + 2⟩
private def ident (offset : Nat) (name : String) : Syntax.Identifier := ⟨span offset, name⟩
private def ref (offset : Nat) (name : String) : Syntax.Expr :=
  ⟨span offset, .identifier (ident offset name)⟩
private def parameter := ident 5 "x"
private def body : Syntax.Block :=
  ⟨span 10, [⟨span 11, .returnStmt (some (ref 12 "x"))⟩]⟩
private def source : Syntax.Expr :=
  ⟨span 0, .lambda (span 1) ⟨span 2, [⟨span 3, .inferred parameter⟩]⟩ none body⟩
private def argument := ref 20 "payload"
private def directCall : Syntax.Expr :=
  ⟨span 21, .call source ⟨span 22, [argument]⟩⟩
private def callee := ref 30 "fn"
private def callerArgument := ref 31 "arg"
private def invocation : Syntax.Expr :=
  ⟨span 32, .call callee ⟨span 33, [callerArgument]⟩⟩

private def inputs : LocalTypeInputs :=
  ⟨[⟨"payload", payloadId, .unit⟩, ⟨"noise", noiseId, .word⟩,
    ⟨"payload", shadowId, .bool⟩], by decide⟩
private def payload : Core.Value :=
  .closure .bool .word (.var 1)
    [.cellRef .word 8, .hostFunction .callerAddress,
      .closure .unit .unit (.var 4) [.hostFunction .storageRead]]
private def environment : Resolved.Environment :=
  [(payloadId, payload), (noiseId, .word (Core.Word.ofNatModulo 99)),
    (shadowId, .bool false)]
private def store : Core.Store :=
  [.word (Core.Word.ofNatModulo 77), .cellRef .word 3,
    .hostFunction .storageWrite, payload]
private def captures : List (Resolved.LocalId × RuntimeValue) :=
  environment.map (fun row => (row.1, RuntimeValue.ofCore row.2))
private def heap : List RuntimeValue := store.map RuntimeValue.ofCore
private def mappedEnvironment : Resolved.Environment :=
  Resolved.LocalScope.mapIds (ownerLocalIdMap shift) environment
private def mappedInputs : LocalTypeInputs :=
  inputs.mapIds (ownerLocalIdMap shift) (ownerLocalIdMap_injective shift shift_injective)

private theorem shape : SourceUnaryLambdaShape source parameter body := .inferred
private theorem dataBody : ClosedSourceDataBody body := .expression .reference
private theorem checked :
    elaborateExpectedComputationLambda? elaborateLocalExpression? [] savedOwner inputs source
      (.function .unit .unit) = some (.lambda .unit .unit (.var 0)) :=
  (elaborateExpectedComputationLambda?_iff (fun {_ _ _ _ _} => Iff.rfl)).mpr
    (.lambda (.lambda .inferred .omitted) .unit .unit
      (.expression (elaborateLocalExpression?_complete
        (.identifier .head) (.var .head) (.var .head))))
private theorem mappedChecked :
    elaborateExpectedComputationLambda? elaborateLocalExpression? [] (shift savedOwner)
      mappedInputs source (.function .unit .unit) = some (.lambda .unit .unit (.var 0)) := by
  simpa only [mappedInputs] using
    (elaborateExpectedComputationLambda?_mapOwner shift shift_injective elaborateLocalExpression?
      (elaborateLocalExpression?_mapIds (ownerLocalIdMap shift)
        (ownerLocalIdMap_injective shift shift_injective)) [] savedOwner inputs source
      (.function .unit .unit)).trans checked
private theorem sameIds : environment.ids = inputs.context.ids := by rfl
private theorem argumentData : ClosedSourceDataExpression argument := .reference
private theorem argumentResolution :
    ResolvesLocalExpression inputs.names argument (.var payloadId) := .identifier .head
private theorem argumentLowering : Resolved.Lowers environment.ids (.var payloadId) (.var 0) :=
  .var .head

private theorem bodyRaw :
    ClosedSourceBodyEvaluates savedOwner
      ((parameter.value, Resolved.freshLocalId savedOwner inputs.ids) :: inputs.names)
      ((Resolved.freshLocalId savedOwner inputs.ids, RuntimeValue.ofCore payload) :: captures)
      heap body (RuntimeValue.ofCore payload) heap :=
  .expression (.reference .head .head)
private theorem directRaw :
    ClosedSourceExpressionEvaluates savedOwner inputs.names captures heap directCall
      (RuntimeValue.ofCore payload) heap :=
  .call shape (.creation shape) (.reference .head .head) bodyRaw
private theorem mappedDirectRaw :
    ClosedSourceExpressionEvaluates (shift savedOwner)
      (LocalNameTable.mapIds (ownerLocalIdMap shift) inputs.names)
      (mappedEnvironment.map (fun row => (row.1, RuntimeValue.ofCore row.2))) heap directCall
      (RuntimeValue.ofCore payload) heap := by
  simpa only [captures, heap, mappedEnvironment, mapRuntimeCapturedOwners_ofCore,
    mapRuntimeStoreOwners_ofCore, RuntimeValue.mapOwners_ofCore] using
      directRaw.mapOwners shift shift_injective
/-- Direct creation/application has concrete old, mapped, and Core endpoints,
then the bridge classifies every arbitrary mapped endpoint. -/
theorem direct_application_boundary {actualValue : RuntimeValue}
    {actualFinal : List RuntimeValue} :
    ¬ Function.Surjective shift ∧ store ≠ [] ∧
    environment.ids[0]? = some payloadId ∧ environment.ids[1]? = some noiseId ∧
    inputs.names[0]? = some ("payload", payloadId) ∧
    inputs.names[2]? = some ("payload", shadowId) ∧
    elaborateExpectedComputationLambda? elaborateLocalExpression? [] (shift savedOwner)
      mappedInputs source (.function .unit .unit) = some (.lambda .unit .unit (.var 0)) ∧
    mappedEnvironment.ids = mappedInputs.context.ids ∧
    ClosedSourceExpressionEvaluates savedOwner inputs.names captures heap directCall
      (RuntimeValue.ofCore payload) heap ∧
    ClosedSourceExpressionEvaluates (shift savedOwner)
      (LocalNameTable.mapIds (ownerLocalIdMap shift) inputs.names)
      (mappedEnvironment.map (fun row => (row.1, RuntimeValue.ofCore row.2))) heap directCall
      (RuntimeValue.ofCore payload) heap ∧
    ResolvesLocalExpression (LocalNameTable.mapIds (ownerLocalIdMap shift) inputs.names)
      argument (.var (ownerLocalIdMap shift payloadId)) ∧
    Resolved.Lowers mappedEnvironment.ids (.var (ownerLocalIdMap shift payloadId)) (.var 0) ∧
    Core.Evaluates environment.values store
      (.apply (.lambda .unit .unit (.var 0)) (.var 0)) payload store ∧
    (ClosedSourceExpressionEvaluates (shift savedOwner)
      (LocalNameTable.mapIds (ownerLocalIdMap shift) inputs.names)
      (mappedEnvironment.map (fun row => (row.1, RuntimeValue.ofCore row.2))) heap directCall
      actualValue actualFinal ↔
      ∃ value finalStore, actualValue = RuntimeValue.ofCore value ∧
        actualFinal = finalStore.map RuntimeValue.ofCore ∧
        Core.Evaluates environment.values store
          (.apply (.lambda .unit .unit (.var 0)) (.var 0)) value finalStore) := by
  have bridge := closedSourceExpectedDataLambda_application_mapOwners_core_iff
    shift shift_injective shape dataBody checked sameIds argumentData argumentResolution
    argumentLowering (initialStore := store) (callSpan := span 21)
    (argumentsSpan := span 22) (actualValue := actualValue) (actualFinal := actualFinal)
  exact ⟨shift_not_surjective, by decide, rfl, rfl, rfl, rfl, mappedChecked, rfl, directRaw,
    mappedDirectRaw, .identifier .head, .var .head, .apply .lambda (.var rfl) (.var rfl),
    (by simpa only [mappedEnvironment, heap, directCall] using bridge.2.2.2.2)⟩

private def saved : RuntimeValue := .sourceClosure source savedOwner inputs.names captures
private def callerNames : LocalNameTable :=
  [("fn", calleeId), ("arg", argumentId), ("fn", foreignCalleeId)]
private def callerCaptured : List (Resolved.LocalId × RuntimeValue) :=
  [(argumentId, RuntimeValue.ofCore payload), (calleeId, saved),
    (calleeId, .sourceClosure argument foreignOwner [] []),
    (foreignCalleeId, saved)]
private theorem calleeRaw : ClosedSourceExpressionEvaluates callerOwner callerNames callerCaptured
    heap callee saved heap := .reference .head (.tail (by decide) .head)
private theorem callerArgumentRaw : ClosedSourceExpressionEvaluates callerOwner callerNames
    callerCaptured heap callerArgument (RuntimeValue.ofCore payload) heap :=
  .reference (.tail (by decide) .head) .head
private theorem invocationRaw : ClosedSourceExpressionEvaluates callerOwner callerNames callerCaptured
    heap invocation (RuntimeValue.ofCore payload) heap :=
  .call shape calleeRaw callerArgumentRaw bodyRaw
private theorem mappedCalleeRaw :
    ClosedSourceExpressionEvaluates (shift callerOwner)
      (LocalNameTable.mapIds (ownerLocalIdMap shift) callerNames)
      (mapRuntimeCapturedOwners shift callerCaptured) heap callee
      (.sourceClosure source (shift savedOwner)
        (LocalNameTable.mapIds (ownerLocalIdMap shift) inputs.names)
        (mappedEnvironment.map (fun row => (row.1, RuntimeValue.ofCore row.2)))) heap := by
  simpa only [saved, captures, heap, mappedEnvironment, RuntimeValue.mapOwners_sourceClosure,
    mapRuntimeCapturedOwners_ofCore, mapRuntimeStoreOwners_ofCore] using
      calleeRaw.mapOwners shift shift_injective
private theorem mappedCallerArgumentRaw :
    ClosedSourceExpressionEvaluates (shift callerOwner)
      (LocalNameTable.mapIds (ownerLocalIdMap shift) callerNames)
      (mapRuntimeCapturedOwners shift callerCaptured) heap callerArgument
      (RuntimeValue.ofCore payload) heap := by
  simpa only [heap, mapRuntimeStoreOwners_ofCore, RuntimeValue.mapOwners_ofCore] using
    callerArgumentRaw.mapOwners shift shift_injective
private theorem mappedInvocationRaw :
    ClosedSourceExpressionEvaluates (shift callerOwner)
      (LocalNameTable.mapIds (ownerLocalIdMap shift) callerNames)
      (mapRuntimeCapturedOwners shift callerCaptured) heap invocation
      (RuntimeValue.ofCore payload) heap := by
  simpa only [heap, mapRuntimeStoreOwners_ofCore, RuntimeValue.mapOwners_ofCore] using
    invocationRaw.mapOwners shift shift_injective
private theorem invocationCore :
    Core.Evaluates (payload :: environment.values) store (.var 0) payload store := .var rfl

/-- A separately saved closure retains duplicate and foreign caller rows. Both
prefixes and both complete calls exist before arbitrary mapped endpoints use the bridge. -/
theorem saved_invocation_boundary {actualValue : RuntimeValue}
    {actualFinal : List RuntimeValue} :
    callerNames[2]? = some ("fn", foreignCalleeId) ∧
    callerCaptured[1]?.map Prod.fst = some calleeId ∧
    callerCaptured[2]?.map Prod.fst = some calleeId ∧
    ClosedSourceExpressionEvaluates callerOwner callerNames callerCaptured heap invocation
      (RuntimeValue.ofCore payload) heap ∧
    ClosedSourceExpressionEvaluates (shift callerOwner)
      (LocalNameTable.mapIds (ownerLocalIdMap shift) callerNames)
      (mapRuntimeCapturedOwners shift callerCaptured) heap callee
      (.sourceClosure source (shift savedOwner)
        (LocalNameTable.mapIds (ownerLocalIdMap shift) inputs.names)
        (mappedEnvironment.map (fun row => (row.1, RuntimeValue.ofCore row.2)))) heap ∧
    ClosedSourceExpressionEvaluates (shift callerOwner)
      (LocalNameTable.mapIds (ownerLocalIdMap shift) callerNames)
      (mapRuntimeCapturedOwners shift callerCaptured) heap callerArgument
      (RuntimeValue.ofCore payload) heap ∧
    ClosedSourceExpressionEvaluates (shift callerOwner)
      (LocalNameTable.mapIds (ownerLocalIdMap shift) callerNames)
      (mapRuntimeCapturedOwners shift callerCaptured) heap invocation
      (RuntimeValue.ofCore payload) heap ∧
    Core.Evaluates (payload :: environment.values) store (.var 0) payload store ∧
    (ClosedSourceExpressionEvaluates (shift callerOwner)
      (LocalNameTable.mapIds (ownerLocalIdMap shift) callerNames)
      (mapRuntimeCapturedOwners shift callerCaptured) heap invocation actualValue actualFinal ↔
      ∃ value finalStore, actualValue = RuntimeValue.ofCore value ∧
        actualFinal = finalStore.map RuntimeValue.ofCore ∧
        Core.Evaluates (payload :: environment.values) store (.var 0) value finalStore) := by
  have bridge := closedSourceExpectedDataLambda_invocation_mapOwners_core_iff
    shift shift_injective (initialStore := heap) (calleeStore := heap) shape dataBody checked sameIds
    (by simpa only [heap, mappedEnvironment, mapRuntimeStoreOwners_ofCore] using mappedCalleeRaw)
    (by simpa only [heap, mapRuntimeStoreOwners_ofCore] using mappedCallerArgumentRaw)
    (callSpan := span 32) (argumentsSpan := span 33) (bodyStore := store)
    (actualValue := actualValue) (actualFinal := actualFinal)
  have exactBridge :
      ClosedSourceExpressionEvaluates (shift callerOwner)
        (LocalNameTable.mapIds (ownerLocalIdMap shift) callerNames)
        (mapRuntimeCapturedOwners shift callerCaptured) heap invocation actualValue actualFinal ↔
      ∃ value finalStore, actualValue = RuntimeValue.ofCore value ∧
        actualFinal = finalStore.map RuntimeValue.ofCore ∧
        Core.Evaluates (payload :: environment.values) store (.var 0) value finalStore := by
    simpa only [heap, invocation, mapRuntimeStoreOwners_ofCore] using bridge.2.2
  exact ⟨rfl, rfl, rfl, invocationRaw, mappedCalleeRaw, mappedCallerArgumentRaw,
    mappedInvocationRaw, invocationCore, exactBridge⟩

private def swappedEnvironment : Resolved.Environment :=
  [(noiseId, .word (Core.Word.ofNatModulo 99)), (payloadId, payload),
    (shadowId, .bool false)]
private def swappedCaptures : List (Resolved.LocalId × RuntimeValue) :=
  swappedEnvironment.map (fun row => (row.1, RuntimeValue.ofCore row.2))
private theorem misalignedRaw :
    ClosedSourceExpressionEvaluates savedOwner inputs.names swappedCaptures heap directCall
      (RuntimeValue.ofCore payload) heap := by
  have created : ClosedSourceExpressionEvaluates savedOwner inputs.names swappedCaptures heap source
      (.sourceClosure source savedOwner inputs.names swappedCaptures) heap := .creation shape
  have evaluatedArgument : ClosedSourceExpressionEvaluates savedOwner inputs.names swappedCaptures
      heap argument (RuntimeValue.ofCore payload) heap :=
    .reference .head (.tail (by decide) .head)
  have evaluatedBody : ClosedSourceBodyEvaluates savedOwner
      ((parameter.value, Resolved.freshLocalId savedOwner inputs.ids) :: inputs.names)
      ((Resolved.freshLocalId savedOwner inputs.ids, RuntimeValue.ofCore payload) ::
        swappedCaptures) heap body (RuntimeValue.ofCore payload) heap :=
    .expression (.reference .head .head)
  exact .call shape created evaluatedArgument evaluatedBody
private def nonDataBody : Syntax.Block :=
  ⟨span 50, [⟨span 51, .returnStmt (some source)⟩]⟩
private def nonimage : RuntimeValue :=
  .sourceClosure source savedOwner
    ((parameter.value, Resolved.freshLocalId savedOwner inputs.ids) :: inputs.names)
    ((Resolved.freshLocalId savedOwner inputs.ids, RuntimeValue.ofCore payload) :: captures)
private theorem nonDataRaw : ClosedSourceBodyEvaluates savedOwner
    ((parameter.value, Resolved.freshLocalId savedOwner inputs.ids) :: inputs.names)
    ((Resolved.freshLocalId savedOwner inputs.ids, RuntimeValue.ofCore payload) :: captures)
    heap nonDataBody nonimage heap := .expression (.creation shape)

/-- Raw success alone cannot recover expected-function checking, ID alignment,
the data-body gate, or a Core-image result. -/
theorem missing_premises_remain_observable :
    elaborateExpectedComputationLambda? elaborateLocalExpression? [] savedOwner inputs source .unit = none ∧
    swappedEnvironment.ids ≠ inputs.context.ids ∧
    ClosedSourceExpressionEvaluates savedOwner inputs.names swappedCaptures heap directCall
      (RuntimeValue.ofCore payload) heap ∧
    ClosedSourceBodyEvaluates savedOwner
      ((parameter.value, Resolved.freshLocalId savedOwner inputs.ids) :: inputs.names)
      ((Resolved.freshLocalId savedOwner inputs.ids, RuntimeValue.ofCore payload) :: captures)
      heap nonDataBody nonimage heap ∧
    ¬ ClosedSourceDataBody nonDataBody ∧ ¬ ∃ value, nonimage = RuntimeValue.ofCore value := by
  refine ⟨rfl, ?_, misalignedRaw, nonDataRaw, ?_, ?_⟩
  · change [noiseId, payloadId, shadowId] ≠ [payloadId, noiseId, shadowId]
    decide
  · intro admitted
    cases admitted with
    | expression child => cases child
  · rintro ⟨value, same⟩
    have projected := congrArg RuntimeValue.toCore? same
    simp only [nonimage, RuntimeValue.toCore?, RuntimeValue.toCore?_ofCore, reduceCtorEq] at projected

end Tests.ADR0315OwnerExpectedDataLambdaCoreConsumer
end

section
-- leanmerge: from Solcore.Test.FrontendOwnerReflectionBoundaryProperties
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
end

section
-- leanmerge: from Solcore.Test.FrontendOwnerReflectionSymbolicProperties
/- Independent originals and exact runner recursion precede reflection. Arbitrary
mixed payloads, duplicate rows, annotations and stores require no runtime typing. -/
set_option autoImplicit false
namespace Tests.OwnerReflectionSymbolic
open Solcore Solcore.Frontend
private abbrev V := RuntimeValue
private abbrev E := ClosedSourceExpressionEvaluates
private abbrev B := ClosedSourceBodyEvaluates
private def ref (p : Syntax.Identifier) : Syntax.Expr := ⟨p.span,.identifier p⟩
private def groups (s : Syntax.SourceSpan) : Nat → Syntax.Expr → Syntax.Expr
  | 0,e => e
  | n+1,e => ⟨s,.group (groups s n e)⟩
private def block (p : Syntax.Identifier) (annotation : Option Syntax.TypeExpr) (n : Nat) : Syntax.Block :=
  ⟨p.span,[⟨p.span,.letDecl p annotation (some (ref p))⟩,
    ⟨p.span,.returnStmt (some (groups p.span n (ref p)))⟩]⟩
private def call (f x : Syntax.Identifier) : Syntax.Expr := ⟨f.span,.call (ref f) ⟨x.span,[ref x]⟩⟩
private theorem group_original {o ns cs st e v fin} (s : Syntax.SourceSpan) (n : Nat)
    (original : E o ns cs st e v fin) : E o ns cs st (groups s n e) v fin := by
  induction n with
  | zero => exact original
  | succ n ih => exact .group ih
private theorem group_run (n budget : Nat) (o ns cs st p id v)
    (named : LocalNameTable.Lookup ns p.value id) (found : Resolved.LocalScope.Lookup cs id v) :
    evaluateClosedSourceExpression? budget o ns cs st (groups p.span n (ref p)) =
      if n+1 ≤ budget then some (v,st) else none := by
  induction n generalizing budget with
  | zero => cases budget <;> simp [groups,ref,evaluateClosedSourceExpression?,
      LocalNameTable.lookup?_iff.mpr named,Resolved.LocalScope.lookup?_iff.mpr found]
  | succ n ih =>
    cases budget with
    | zero => simp [evaluateClosedSourceExpression?]
    | succ budget => simpa only [groups,evaluateClosedSourceExpression?,Nat.add_le_add_iff_right] using ih budget
private theorem body_original (o ns cs st p id v annotation n) :
    B o ((p.value,id)::ns) ((id,v)::cs) st (block p annotation n) v st := by
  have initial : E o ((p.value,id)::ns) ((id,v)::cs) st (ref p) v st := .reference .head .head
  have tail : B o ((p.value,Resolved.freshLocalId o (((p.value,id)::ns).map Prod.snd))::(p.value,id)::ns)
      ((Resolved.freshLocalId o (((p.value,id)::ns).map Prod.snd),v)::(id,v)::cs) st
      ⟨p.span,[⟨p.span,.returnStmt (some (groups p.span n (ref p)))⟩]⟩ v st :=
    .expression (group_original _ _ (.reference .head .head))
  cases annotation with
  | none => exact .inferred initial tail
  | some _ => exact .binding initial tail
private theorem body_run (n budget : Nat) (o ns cs st p id v annotation) :
    evaluateClosedSourceBody? budget o ((p.value,id)::ns) ((id,v)::cs) st (block p annotation n) =
      if n+3 ≤ budget then some (v,st) else none := by
  cases budget with
  | zero => simp [evaluateClosedSourceBody?]
  | succ budget =>
    cases budget with
    | zero => simp [block,ref,evaluateClosedSourceBody?,evaluateClosedSourceExpression?]
    | succ budget =>
      simp only [block,ref,evaluateClosedSourceBody?,evaluateClosedSourceExpression?,
        LocalNameTable.lookup?,Resolved.LocalScope.lookup?,↓reduceIte,bind,Option.bind_some,pure]
      have bound : n+3 ≤ budget+1+1 ↔ n+1≤budget := by omega
      simpa only [ref,bound] using
        group_run n budget o _ _ st p _ v LocalNameTable.Lookup.head Resolved.LocalScope.Lookup.head
private def Certificate (original : V → List V → Prop) (before after : Nat → Option (V × List V))
    (mapping : Resolved.DeclarationId → Resolved.DeclarationId) (v : V) (st : List V) (depth : Nat) : Prop :=
  ∃ recovered final, original recovered final ∧ recovered=v ∧ final=st ∧
    ∃ required, required=depth ∧ 0<required ∧ ∀ budget,
      before budget=(if required≤budget then some (recovered,final) else none) ∧
      after budget=(if required≤budget then some (recovered.mapOwners mapping,final.map (RuntimeValue.mapOwners mapping)) else none)
private theorem body_certificate (m : Resolved.DeclarationId → Resolved.DeclarationId) (inj : Function.Injective m)
    {o ns cs st source v h} (positive : 0<h) (old : B o ns cs st source v st)
    (mapped : B (m o) (LocalNameTable.mapIds (ownerLocalIdMap m) ns) (mapRuntimeCapturedOwners m cs)
      (st.map (RuntimeValue.mapOwners m)) source (v.mapOwners m) (st.map (RuntimeValue.mapOwners m)))
    (run : ∀ k, evaluateClosedSourceBody? k o ns cs st source=if h≤k then some (v,st) else none)
    (actual : evaluateClosedSourceBody? h (m o) (LocalNameTable.mapIds (ownerLocalIdMap m) ns)
      (mapRuntimeCapturedOwners m cs) (st.map (RuntimeValue.mapOwners m)) source=some (v.mapOwners m,st.map (RuntimeValue.mapOwners m))) :
    Certificate (B o ns cs st source) (fun k => evaluateClosedSourceBody? k o ns cs st source)
      (fun k => evaluateClosedSourceBody? k (m o) (LocalNameTable.mapIds (ownerLocalIdMap m) ns)
        (mapRuntimeCapturedOwners m cs) (st.map (RuntimeValue.mapOwners m)) source) m v st h := by
  obtain ⟨pre,out,original,_,_⟩ := (ClosedSourceBodyEvaluates.mapOwners_iff_exists m inj).mp mapped
  have explicitOriginal := (ClosedSourceBodyEvaluates.mapOwners_iff m inj).mp mapped
  have endpoints := original.deterministic old
  obtain ⟨finite,finiteStore,ran,_,_⟩ := (evaluateClosedSourceBody?_mapOwners_some_iff_exists m inj).mp actual
  have finiteOriginal := evaluateClosedSourceBody?_sound ran
  have finiteEndpoints := finiteOriginal.deterministic explicitOriginal
  obtain ⟨required,pos,cutoff⟩ := finiteOriginal.mapOwners_exact_depth_threshold m inj
  have low : evaluateClosedSourceBody? (h-1) (m o) (LocalNameTable.mapIds (ownerLocalIdMap m) ns)
      (mapRuntimeCapturedOwners m cs) (st.map (RuntimeValue.mapOwners m)) source=none :=
    (evaluateClosedSourceBody?_mapOwners_none_iff m inj _ _ _ _ _ _).mpr (by rw [run,if_neg (by omega)])
  have upper : required≤h := by
    by_cases yes : required≤h
    · exact yes
    · have eqn := (cutoff h).1
      rw [run,if_pos (Nat.le_refl _),if_neg yes] at eqn
      cases eqn
  have lower : h≤required := by
    by_cases yes : h≤required
    · exact yes
    · have eqn := (cutoff (h-1)).2
      rw [low,if_pos (by omega)] at eqn
      cases eqn
  refine ⟨pre,out,original,endpoints.1,endpoints.2,required,by omega,pos,?_⟩
  intro k
  simpa only [endpoints.1,endpoints.2,finiteEndpoints.1,finiteEndpoints.2] using cutoff k
private theorem expression_certificate (m : Resolved.DeclarationId → Resolved.DeclarationId) (inj : Function.Injective m)
    {o ns cs st source v h} (positive : 0<h) (old : E o ns cs st source v st)
    (mapped : E (m o) (LocalNameTable.mapIds (ownerLocalIdMap m) ns) (mapRuntimeCapturedOwners m cs)
      (st.map (RuntimeValue.mapOwners m)) source (v.mapOwners m) (st.map (RuntimeValue.mapOwners m)))
    (run : ∀ k, evaluateClosedSourceExpression? k o ns cs st source=if h≤k then some (v,st) else none)
    (actual : evaluateClosedSourceExpression? h (m o) (LocalNameTable.mapIds (ownerLocalIdMap m) ns)
      (mapRuntimeCapturedOwners m cs) (st.map (RuntimeValue.mapOwners m)) source=some (v.mapOwners m,st.map (RuntimeValue.mapOwners m))) :
    Certificate (E o ns cs st source) (fun k => evaluateClosedSourceExpression? k o ns cs st source)
      (fun k => evaluateClosedSourceExpression? k (m o) (LocalNameTable.mapIds (ownerLocalIdMap m) ns)
        (mapRuntimeCapturedOwners m cs) (st.map (RuntimeValue.mapOwners m)) source) m v st h := by
  obtain ⟨pre,out,original,_,_⟩ := (ClosedSourceExpressionEvaluates.mapOwners_iff_exists m inj).mp mapped
  have explicitOriginal := (ClosedSourceExpressionEvaluates.mapOwners_iff m inj).mp mapped
  have endpoints := original.deterministic old
  obtain ⟨finite,finiteStore,ran,_,_⟩ := (evaluateClosedSourceExpression?_mapOwners_some_iff_exists m inj).mp actual
  have finiteOriginal := evaluateClosedSourceExpression?_sound ran
  have finiteEndpoints := finiteOriginal.deterministic explicitOriginal
  obtain ⟨required,pos,cutoff⟩ := finiteOriginal.mapOwners_exact_depth_threshold m inj
  have low : evaluateClosedSourceExpression? (h-1) (m o) (LocalNameTable.mapIds (ownerLocalIdMap m) ns)
      (mapRuntimeCapturedOwners m cs) (st.map (RuntimeValue.mapOwners m)) source=none :=
    (evaluateClosedSourceExpression?_mapOwners_none_iff m inj _ _ _ _ _ _).mpr (by rw [run,if_neg (by omega)])
  have upper : required≤h := by
    by_cases yes : required≤h
    · exact yes
    · have eqn := (cutoff h).1
      rw [run,if_pos (Nat.le_refl _),if_neg yes] at eqn
      cases eqn
  have lower : h≤required := by
    by_cases yes : h≤required
    · exact yes
    · have eqn := (cutoff (h-1)).2
      rw [low,if_pos (by omega)] at eqn
      cases eqn
  refine ⟨pre,out,original,endpoints.1,endpoints.2,required,by omega,pos,?_⟩
  intro k
  simpa only [endpoints.1,endpoints.2,finiteEndpoints.1,finiteEndpoints.2] using cutoff k

theorem fresh_body_recovers_complete_preimage
    (m : Resolved.DeclarationId → Resolved.DeclarationId) (inj : Function.Injective m)
    (o ns cs st p id v annotation n) :
    Certificate (B o ((p.value,id)::ns) ((id,v)::cs) st (block p annotation n))
      (fun k => evaluateClosedSourceBody? k o ((p.value,id)::ns) ((id,v)::cs) st (block p annotation n))
      (fun k => evaluateClosedSourceBody? k (m o) (LocalNameTable.mapIds (ownerLocalIdMap m) ((p.value,id)::ns))
        (mapRuntimeCapturedOwners m ((id,v)::cs)) (st.map (RuntimeValue.mapOwners m)) (block p annotation n)) m v st (n+3) := by
  have old := body_original o ns cs st p id v annotation n
  have mapped := body_original (m o) (LocalNameTable.mapIds (ownerLocalIdMap m) ns)
    (mapRuntimeCapturedOwners m cs) (st.map (RuntimeValue.mapOwners m)) p (ownerLocalIdMap m id) (v.mapOwners m) annotation n
  have actual := body_run n (n+3) (m o) (LocalNameTable.mapIds (ownerLocalIdMap m) ns)
    (mapRuntimeCapturedOwners m cs) (st.map (RuntimeValue.mapOwners m)) p (ownerLocalIdMap m id) (v.mapOwners m) annotation
  apply body_certificate m inj (by omega) old
    (by simpa only [LocalNameTable.mapIds,mapRuntimeCapturedOwners,List.map_cons] using mapped)
    (fun k => body_run n k o ns cs st p id v annotation)
  simpa only [LocalNameTable.mapIds,mapRuntimeCapturedOwners,List.map_cons,if_pos (Nat.le_refl _)] using actual

private theorem call_original {o ns cs st source savedOwner savedNames savedCaptured p annotation n f x fi xi v}
    (shape : SourceUnaryLambdaShape source p (block p annotation n))
    (nf : LocalNameTable.Lookup ns f.value fi)
    (ff : Resolved.LocalScope.Lookup cs fi (.sourceClosure source savedOwner savedNames savedCaptured))
    (nx : LocalNameTable.Lookup ns x.value xi) (fx : Resolved.LocalScope.Lookup cs xi v) :
    E o ns cs st (call f x) v st :=
  .call shape (.reference nf ff) (.reference nx fx)
    (body_original savedOwner savedNames savedCaptured st p _ v annotation n)
private theorem call_run {o ns cs st source savedOwner savedNames savedCaptured p annotation n f x fi xi v}
    (shape : SourceUnaryLambdaShape source p (block p annotation n))
    (nf : LocalNameTable.Lookup ns f.value fi)
    (ff : Resolved.LocalScope.Lookup cs fi (.sourceClosure source savedOwner savedNames savedCaptured))
    (nx : LocalNameTable.Lookup ns x.value xi) (fx : Resolved.LocalScope.Lookup cs xi v) (budget : Nat) :
    evaluateClosedSourceExpression? budget o ns cs st (call f x)=if n+4≤budget then some (v,st) else none := by
  cases budget with
  | zero => simp [evaluateClosedSourceExpression?]
  | succ budget =>
    cases budget with
    | zero => simp [call,ref,evaluateClosedSourceExpression?]
    | succ budget =>
      simp only [call,ref,evaluateClosedSourceExpression?,LocalNameTable.lookup?_iff.mpr nf,
        LocalNameTable.lookup?_iff.mpr nx,Resolved.LocalScope.lookup?_iff.mpr ff,
        Resolved.LocalScope.lookup?_iff.mpr fx,bind,Option.bind_some,pure,sourceUnaryLambdaShape?_iff.mpr shape]
      have bound : n+4≤budget+1+1 ↔ n+3≤budget+1 := by omega
      simpa only [bound] using body_run n (budget+1) savedOwner savedNames savedCaptured st p _ v annotation

theorem saved_call_recovers_complete_preimage
    (m : Resolved.DeclarationId → Resolved.DeclarationId) (inj : Function.Injective m)
    {o ns cs st source savedOwner savedNames savedCaptured p annotation n f x fi xi v}
    (creationStore : List V) (shape : SourceUnaryLambdaShape source p (block p annotation n))
    (nf : LocalNameTable.Lookup ns f.value fi)
    (ff : Resolved.LocalScope.Lookup cs fi (.sourceClosure source savedOwner savedNames savedCaptured))
    (nx : LocalNameTable.Lookup ns x.value xi) (fx : Resolved.LocalScope.Lookup cs xi v) :
    E savedOwner savedNames savedCaptured creationStore source
      (.sourceClosure source savedOwner savedNames savedCaptured) creationStore ∧
    E (m savedOwner) (LocalNameTable.mapIds (ownerLocalIdMap m) savedNames) (mapRuntimeCapturedOwners m savedCaptured)
      (creationStore.map (RuntimeValue.mapOwners m)) source
      (.sourceClosure source (m savedOwner) (LocalNameTable.mapIds (ownerLocalIdMap m) savedNames)
        (mapRuntimeCapturedOwners m savedCaptured)) (creationStore.map (RuntimeValue.mapOwners m)) ∧
    Certificate (E o ns cs st (call f x)) (fun k => evaluateClosedSourceExpression? k o ns cs st (call f x))
      (fun k => evaluateClosedSourceExpression? k (m o) (LocalNameTable.mapIds (ownerLocalIdMap m) ns)
        (mapRuntimeCapturedOwners m cs) (st.map (RuntimeValue.mapOwners m)) (call f x)) m v st (n+4) := by
  have creation : E savedOwner savedNames savedCaptured creationStore source
      (.sourceClosure source savedOwner savedNames savedCaptured) creationStore := .creation shape
  have mappedCreation : E (m savedOwner) (LocalNameTable.mapIds (ownerLocalIdMap m) savedNames)
      (mapRuntimeCapturedOwners m savedCaptured) (creationStore.map (RuntimeValue.mapOwners m)) source
      (.sourceClosure source (m savedOwner) (LocalNameTable.mapIds (ownerLocalIdMap m) savedNames)
        (mapRuntimeCapturedOwners m savedCaptured)) (creationStore.map (RuntimeValue.mapOwners m)) := .creation shape
  have old : E o ns cs st (call f x) v st := call_original shape nf ff nx fx
  have nfm := (LocalNameTable.lookup_mapIds_iff (ownerLocalIdMap m) (ownerLocalIdMap_injective m inj)).mpr nf
  have nxm := (LocalNameTable.lookup_mapIds_iff (ownerLocalIdMap m) (ownerLocalIdMap_injective m inj)).mpr nx
  have ffm := mapRuntimeCapturedOwners_lookup m inj ff
  simp only [RuntimeValue.mapOwners_sourceClosure] at ffm
  have fxm := mapRuntimeCapturedOwners_lookup m inj fx
  have mapped : E (m o) (LocalNameTable.mapIds (ownerLocalIdMap m) ns) (mapRuntimeCapturedOwners m cs)
      (st.map (RuntimeValue.mapOwners m)) (call f x) (v.mapOwners m) (st.map (RuntimeValue.mapOwners m)) :=
    call_original shape nfm ffm nxm fxm
  have actual := call_run (o:=m o) (st:=st.map (RuntimeValue.mapOwners m)) shape nfm ffm nxm fxm (n+4)
  refine ⟨creation,mappedCreation,expression_certificate m inj (by omega) old mapped (call_run shape nf ff nx fx) ?_⟩
  simpa only [if_pos (Nat.le_refl _)] using actual

private def owner (i : Nat) : Resolved.DeclarationId :=
  ⟨⟨.main,⟨[⟨"Reflection",by decide⟩],by decide⟩⟩,i⟩
private def fixtureSavedNames : LocalNameTable := [("p",⟨owner 1,40⟩),("p",⟨owner 3,40⟩),("p",⟨owner 1,40⟩)]
private theorem mixed_saved_fixture (m : Resolved.DeclarationId → Resolved.DeclarationId) (inj : Function.Injective m)
    (s : Syntax.SourceSpan) (parameterAnnotation bindingAnnotation : Option Syntax.TypeExpr) (opaqueCore : Core.Value) (n : Nat) :
    ∃ required : Nat, required=n+4 ∧ 0<required ∧
      Resolved.freshLocalId (owner 1) (fixtureSavedNames.map Prod.snd)=⟨owner 1,41⟩ ∧
      Resolved.freshLocalId (owner 1) (⟨owner 1,41⟩::fixtureSavedNames.map Prod.snd)=⟨owner 1,42⟩ := by
  let p : Syntax.Identifier := ⟨s,"p"⟩
  let parameter : Syntax.LambdaParameter := ⟨s,match parameterAnnotation with
    | none => .inferred p | some ty => .typed none p ty⟩
  let source : Syntax.Expr := ⟨s,.lambda s ⟨s,[parameter]⟩ none (block p bindingAnnotation n)⟩
  have shape : SourceUnaryLambdaShape source p (block p bindingAnnotation n) := by
    cases parameterAnnotation <;> first | exact .inferred | exact .typed
  let savedNames := fixtureSavedNames
  let nested : V := .coreClosure .unit .word (.var 17)
    [.sourceClosure source (owner 3) [("p",⟨owner 2,9⟩)]
      [(⟨owner 2,9⟩,.cellRef .word 77),(⟨owner 2,9⟩,.ofCore opaqueCore)],.ofCore opaqueCore]
  let savedCaptured : Resolved.LocalScope V :=
    [(⟨owner 3,40⟩,nested),(⟨owner 1,41⟩,.cellRef .word 800),(⟨owner 1,42⟩,.bool false),
      (⟨owner 1,40⟩,nested),(⟨owner 1,40⟩,.unit)]
  let saved : V := .sourceClosure source (owner 1) savedNames savedCaptured
  let arg : V := .pair nested (.pair (.ofCore opaqueCore) (.cellRef .word 78))
  let names : LocalNameTable := [("f",⟨owner 2,1⟩),("x",⟨owner 2,2⟩),("f",⟨owner 3,1⟩),("x",⟨owner 2,2⟩)]
  let captured : Resolved.LocalScope V := [(⟨owner 3,1⟩,.unit),(⟨owner 2,1⟩,saved),(⟨owner 2,2⟩,arg),
    (⟨owner 2,1⟩,.bool false),(⟨owner 2,2⟩,.unit)]
  have fresh : Resolved.freshLocalId (owner 1) (savedNames.map Prod.snd)=⟨owner 1,41⟩ := by decide
  have next : Resolved.freshLocalId (owner 1) (⟨owner 1,41⟩::savedNames.map Prod.snd)=⟨owner 1,42⟩ := by decide
  have result := saved_call_recovers_complete_preimage m inj (o:=owner 2) (ns:=names) (cs:=captured)
    (st:=[arg,.ofCore opaqueCore,.cellRef .word 900]) (f:=⟨s,"f"⟩) (x:=⟨s,"x"⟩) [nested] shape
    LocalNameTable.Lookup.head (Resolved.LocalScope.Lookup.tail (by decide) .head)
    (LocalNameTable.Lookup.tail (by change "f" ≠ "x"; decide) .head)
    (Resolved.LocalScope.Lookup.tail (by decide) (.tail (by decide) .head))
  obtain ⟨_,_,_,_,_,_,_,required,same,positive,_⟩ := result
  exact ⟨required,same,positive,fresh,next⟩

end Tests.OwnerReflectionSymbolic
end

section
-- leanmerge: from Solcore.Test.FrontendParsedOwnerCheckedDataExpression
/- A parsed strict-Word instance exercises the checked owner image only after
both executable frontends and the Core machine have produced their endpoints. -/
set_option autoImplicit false
namespace Tests.ADR0316ParsedCheckedDataOwnerConsumer
open Solcore Solcore.Frontend

private def check (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)
private def proof {proposition : Prop} (_ : proposition) : IO Unit := pure ()

private def declaration (index : Nat) : Resolved.DeclarationId :=
  ⟨⟨.main, ⟨[⟨"ParsedCheckedOwner", by decide⟩], by decide⟩⟩, index⟩
private def owner := declaration 316
private def foreignOwner := declaration 916
private def localId (declaration : Resolved.DeclarationId) (index : Nat) :
    Resolved.LocalId := ⟨declaration, index⟩
private def noiseId := localId foreignOwner 90
private def leftId := localId owner 7
private def rightId := localId owner 31
private def payloadId := localId foreignOwner 91

private def shift (value : Resolved.DeclarationId) : Resolved.DeclarationId :=
  { value with declarationIndex := value.declarationIndex + 5 }
private theorem shift_injective : Function.Injective shift := by
  intro left right equal
  have modules := congrArg Resolved.DeclarationId.moduleId equal
  have indices := congrArg Resolved.DeclarationId.declarationIndex equal
  cases left; cases right
  simp only [shift, Resolved.DeclarationId.mk.injEq] at modules indices ⊢
  exact ⟨modules, by omega⟩
private theorem shift_not_surjective : ¬ Function.Surjective shift := by
  intro onto
  obtain ⟨before, equal⟩ := onto (declaration 0)
  have impossible := congrArg Resolved.DeclarationId.declarationIndex equal
  simp [shift, declaration] at impossible

private def names : LocalNameTable :=
  [("x", leftId), ("y", rightId), ("x", payloadId), ("y", noiseId)]
private def leftWord : Core.Word := Core.Word.ofNatModulo 42
private def rightWord : Core.Word := Core.Word.ofNatModulo 17
private def resultWord : Core.Word := leftWord.add rightWord
private def opaqueValue : Core.Value :=
  .closure .unit .word (.var 99)
    [.hostFunction .storageWrite, .cellRef (.function .word .unit) 700]
private def environment : Resolved.Environment :=
  [(noiseId, .hostFunction .storageRead), (leftId, .word leftWord),
    (rightId, .word rightWord), (payloadId, opaqueValue), (leftId, .word .maximum)]
private def context : Resolved.Context :=
  [(noiseId, .unit), (leftId, .word), (rightId, .word),
    (payloadId, .function .unit .word), (leftId, .word)]
private def store : Core.Store :=
  [opaqueValue, .cellRef (.function .word .word) 23, .hostFunction .storageWrite]
private def captured := environment.map (fun row => (row.1, RuntimeValue.ofCore row.2))
private def heap := store.map RuntimeValue.ofCore
private def mappedNames := LocalNameTable.mapIds (ownerLocalIdMap shift) names
private def mappedContext := Resolved.LocalScope.mapIds (ownerLocalIdMap shift) context
private def mappedEnvironment :=
  Resolved.LocalScope.mapIds (ownerLocalIdMap shift) environment

private def range (file : Syntax.SourceFile) (start stop : Nat) : Syntax.SourceSpan :=
  ⟨file.id, start, stop⟩
private def reference (file : Syntax.SourceFile) (start stop : Nat) (name : String) :
    Syntax.Expr := ⟨range file start stop, .identifier ⟨range file start stop, name⟩⟩
private def source (file : Syntax.SourceFile) : Syntax.Expr :=
  ⟨range file 0 7, .group
    ⟨range file 1 6, .binary (reference file 1 2 "x")
      ⟨range file 3 4, .add⟩ (reference file 5 6 "y")⟩⟩
private def resolved : Resolved.Expr :=
  .binary .wordAdd (.var leftId) (.var rightId)
private def core : Core.Expr := .binary .wordAdd (.var 1) (.var 2)

private theorem sameIds : environment.ids = context.ids := by rfl
private theorem xy_ne : "x" ≠ "y" := by decide
private theorem gate (file : Syntax.SourceFile) : ClosedSourceDataExpression (source file) :=
  .group (.strictWordBinary .reference .reference (by decide) (by decide))
private theorem resolution (file : Syntax.SourceFile) :
    ResolvesLocalExpression names (source file) resolved :=
  by
    simp only [source, reference]
    exact .group (.add (.identifier .head) (.identifier (.tail xy_ne .head)))
private theorem lowering : Resolved.Lowers context.ids resolved core :=
  .binary (.var (.tail (by decide) .head))
    (.var (.tail (by decide) (.tail (by decide) .head)))
private theorem typing : Resolved.HasType context resolved .word :=
  .binary (.var (.tail (by decide) .head))
    (.var (.tail (by decide) (.tail (by decide) .head)))
private theorem accepted (file : Syntax.SourceFile) :
    elaborateLocalExpression? names context (source file) = some (core, .word) :=
  elaborateLocalExpression?_complete (resolution file) lowering typing

private theorem embedLookup {scope : Resolved.Environment} {id : Resolved.LocalId}
    {value : Core.Value} (found : Resolved.LocalScope.Lookup scope id value) :
    Resolved.LocalScope.Lookup
      (scope.map (fun row => (row.1, RuntimeValue.ofCore row.2))) id
      (RuntimeValue.ofCore value) := by
  induction found with
  | head => exact .head
  | tail different _ ih => exact .tail different ih
private theorem leftFound :
    Resolved.LocalScope.Lookup environment leftId (.word leftWord) :=
  .tail (by decide) .head
private theorem rightFound :
    Resolved.LocalScope.Lookup environment rightId (.word rightWord) :=
  .tail (by decide) (.tail (by decide) .head)
private theorem oldRaw (file : Syntax.SourceFile) :
    ClosedSourceExpressionEvaluates owner names captured heap (source file)
      (RuntimeValue.ofCore (.word resultWord)) heap := by
  simp only [source, reference]
  apply ClosedSourceExpressionEvaluates.group
  apply ClosedSourceExpressionEvaluates.strictWordBinary
  · exact .reference .head (by
      simpa only [captured, RuntimeValue.ofCore] using embedLookup leftFound)
  · exact .reference (.tail xy_ne .head) (by
      simpa only [captured, RuntimeValue.ofCore] using embedLookup rightFound)
  · exact .add
private theorem mappedRaw (file : Syntax.SourceFile) :
    ClosedSourceExpressionEvaluates (shift owner) mappedNames
      (mappedEnvironment.map (fun row => (row.1, RuntimeValue.ofCore row.2))) heap
      (source file) (RuntimeValue.ofCore (.word resultWord)) heap := by
  simpa only [mappedNames, mappedEnvironment, captured, heap,
    mapRuntimeCapturedOwners_ofCore, mapRuntimeStoreOwners_ofCore,
    RuntimeValue.mapOwners_ofCore] using (oldRaw file).mapOwners shift shift_injective
private theorem coreRun :
    Core.Evaluates environment.values store core (.word resultWord) store := by
  exact .binary (.var rfl) (.var rfl) rfl

/-- The parsed fixture's static contract records the deliberately non-surjective
map and duplicate/foreign payload boundary before exposing the generic image. -/
theorem checked_word_add_owner_image (file : Syntax.SourceFile)
    {actualValue : RuntimeValue} {actualFinal : List RuntimeValue} :
    ¬ Function.Surjective shift ∧ store ≠ [] ∧
    names[2]? = some ("x", payloadId) ∧ environment.ids[4]? = some leftId ∧
    elaborateLocalExpression? mappedNames mappedContext (source file) =
      some (core, .word) ∧
    mappedEnvironment.ids = mappedContext.ids ∧
    ∃ checkedResolved,
      ResolvesLocalExpression names (source file) checkedResolved ∧
      Resolved.Lowers environment.ids checkedResolved core ∧
      ResolvesLocalExpression mappedNames (source file)
        (checkedResolved.renameIds (ownerLocalIdMap shift)) ∧
      Resolved.Lowers mappedEnvironment.ids
        (checkedResolved.renameIds (ownerLocalIdMap shift)) core ∧
      (ClosedSourceExpressionEvaluates (shift owner) mappedNames
        (mappedEnvironment.map (fun row => (row.1, RuntimeValue.ofCore row.2))) heap
        (source file) actualValue actualFinal ↔
      ∃ value finalStore,
        actualValue = RuntimeValue.ofCore value ∧
        actualFinal = finalStore.map RuntimeValue.ofCore ∧
        Core.Evaluates environment.values store core value finalStore) := by
  have bridge := (gate file).mapOwners_checked_core_evaluates_iff
    shift shift_injective (owner := owner) (environment := environment)
    (initialStore := store) (actualValue := actualValue) (actualFinal := actualFinal)
    (accepted file) sameIds
  exact ⟨shift_not_surjective, by simp [store], rfl, rfl, by
    simpa only [mappedNames, mappedContext, mappedEnvironment, heap] using bridge⟩

private def exercise : IO Unit := do
  let text := "(x + y)"
  let file : Syntax.SourceFile :=
    ⟨⟨.main, "adr0316-parsed-checked-owner.sol"⟩, text⟩
  let .ok lexed := Syntax.Lexer.lex file |
    throw (IO.userError "checked owner lexer")
  match Syntax.Parser.expression (Syntax.Parser.State.initial file lexed) with
  | .ok parsed next =>
    check (lexed.diagnostics.isEmpty && next.diagnostics.isEmpty && next.atEnd &&
      parsed.span == Syntax.SourceSpan.fullFile file) "diagnostics, EOF and full span"
    match parsedShape : parsed with
    | ⟨groupSpan, .group
        ⟨binarySpan, .binary
          ⟨leftSpan, .identifier ⟨leftNameSpan, "x"⟩⟩
          ⟨operatorSpan, .add⟩
          ⟨rightSpan, .identifier ⟨rightNameSpan, "y"⟩⟩⟩⟩ =>
      if exactSpans : groupSpan = range file 0 7 ∧ binarySpan = range file 1 6 ∧
          leftSpan = range file 1 2 ∧ leftNameSpan = range file 1 2 ∧
          operatorSpan = range file 3 4 ∧ rightSpan = range file 5 6 ∧
          rightNameSpan = range file 5 6 then
        have parsedEq : parsed = source file := by
          rcases exactSpans with ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
          exact parsedShape
        check (parsed == source file &&
          [groupSpan, binarySpan, leftSpan, leftNameSpan, operatorSpan,
            rightSpan, rightNameSpan].all (fun span => span.isValidFor file))
          "exact AST and every nested span"
        match oldCheck : elaborateLocalExpression? names context parsed with
        | none => throw (IO.userError "old checker rejected")
        | some (oldCore, oldType) =>
          check (oldCore == core && oldType == .word) "old checker exact Core/type"
          proof (show elaborateLocalExpression? names context parsed =
            some (core, .word) by rw [parsedEq]; exact accepted file)
          match mappedCheck : elaborateLocalExpression? mappedNames mappedContext parsed with
          | none => throw (IO.userError "mapped checker rejected")
          | some (mappedCore, mappedType) =>
            check (mappedCore == core && mappedType == .word)
              "mapped checker exact unchanged Core/type"
            have mappedAccepted : elaborateLocalExpression? mappedNames mappedContext parsed =
                some (core, .word) := by
              rw [parsedEq]
              exact (elaborateLocalExpression?_mapIds (ownerLocalIdMap shift)
                (ownerLocalIdMap_injective shift shift_injective) names context
                (source file)).trans (accepted file)
            proof mappedAccepted
            match oldResult : evaluateClosedSourceExpression? 3 owner names captured heap parsed with
            | none => throw (IO.userError "old raw evaluator rejected")
            | some (oldValue, oldFinal) =>
              have oldEvaluation := evaluateClosedSourceExpression?_sound oldResult
              have expectedOld : ClosedSourceExpressionEvaluates owner names captured heap parsed
                  (RuntimeValue.ofCore (.word resultWord)) heap := by
                rw [parsedEq]
                exact oldRaw file
              proof (oldEvaluation.deterministic expectedOld)
              check (oldValue.toCore? == some (.word resultWord) &&
                oldFinal.mapM RuntimeValue.toCore? == some store)
                "old raw exact whole Core image"
              match mappedResult : evaluateClosedSourceExpression? 3 (shift owner) mappedNames
                  (mappedEnvironment.map (fun row => (row.1, RuntimeValue.ofCore row.2)))
                  heap parsed with
              | none => throw (IO.userError "mapped raw evaluator rejected")
              | some (mappedValue, mappedFinal) =>
                have mappedEvaluation := evaluateClosedSourceExpression?_sound mappedResult
                have expectedMapped : ClosedSourceExpressionEvaluates (shift owner) mappedNames
                    (mappedEnvironment.map
                      (fun row => (row.1, RuntimeValue.ofCore row.2))) heap parsed
                    (RuntimeValue.ofCore (.word resultWord)) heap := by
                  rw [parsedEq]
                  exact mappedRaw file
                proof (mappedEvaluation.deterministic expectedMapped)
                check (mappedValue.toCore? == some (.word resultWord) &&
                  mappedFinal.mapM RuntimeValue.toCore? == some store)
                  "mapped raw exact whole Core image"
                match coreResult : Core.runStateful 5
                    (Core.State.initial core environment.values store) with
                | .done coreValue coreFinal =>
                  have coreEvaluation := Core.runStateful_evaluation_sound coreResult
                  proof (Core.evaluation_deterministic coreEvaluation coreRun)
                  check (coreValue == .word resultWord && coreFinal == store)
                    "Core exact value/store"
                  have bridge := checked_word_add_owner_image file
                    (actualValue := mappedValue) (actualFinal := mappedFinal)
                  proof bridge
                  proof (show mappedValue = RuntimeValue.ofCore (.word resultWord) ∧
                      mappedFinal = heap from by
                    obtain ⟨_, _, _, _, _, _, checkedResolved, originalResolution,
                      originalLowering, mappedResolution, mappedLowering, image⟩ := bridge
                    have mappedAtSource : ClosedSourceExpressionEvaluates (shift owner)
                        mappedNames (mappedEnvironment.map
                          (fun row => (row.1, RuntimeValue.ofCore row.2))) heap
                        (source file) mappedValue mappedFinal := by
                      simpa only [parsedEq] using mappedEvaluation
                    obtain ⟨endpointValue, endpointStore, valueImage, storeImage,
                      endpointEvaluation⟩ := image.mp mappedAtSource
                    have same := Core.evaluation_deterministic endpointEvaluation coreRun
                    rw [same.1] at valueImage
                    rw [same.2] at storeImage
                    exact ⟨valueImage, by simpa only [heap] using storeImage⟩)
                | .outOfFuel _ => throw (IO.userError "Core fuel unexpectedly exhausted")
                | .fault _ _ => throw (IO.userError "Core evaluator faulted")
      else throw (IO.userError "nested spans differ")
    | _ => throw (IO.userError "parsed AST differs")
  | _ => throw (IO.userError "checked owner parser")

end Tests.ADR0316ParsedCheckedDataOwnerConsumer

def Tests.adr0316ParsedCheckedDataOwnerTests : IO Unit := do
  ADR0316ParsedCheckedDataOwnerConsumer.exercise
  IO.println "ADR0316 parsed checked-data owner image GREEN"
end

section
-- leanmerge: from Solcore.Test.FrontendParsedOwnerCore
/- Actual parser, checker/lowering, raw evaluators and Core machine all run before
the ADR0314 bridges consume their complete mapped endpoints. -/
set_option autoImplicit false
namespace Tests.ADR0314ParsedOwnerCore
open Solcore Solcore.Frontend

private def check (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)
private def proof {p : Prop} (_ : p) : IO Unit := pure ()
private def owner (n : Nat) : Resolved.DeclarationId :=
  ⟨⟨.main,⟨[⟨"ADR0314ParsedOwnerCore",by decide⟩],by decide⟩⟩,n⟩
private def oldOwner := owner 314
private def foreignOwner := owner 914
private def lid (o : Resolved.DeclarationId) (n : Nat) : Resolved.LocalId := ⟨o,n⟩
private def shift (o : Resolved.DeclarationId) : Resolved.DeclarationId :=
  {o with declarationIndex:=o.declarationIndex+5}
private theorem shift_injective : Function.Injective shift := by
  intro a b same
  have hm := congrArg Resolved.DeclarationId.moduleId same
  have hi := congrArg Resolved.DeclarationId.declarationIndex same
  cases a; cases b
  simp only [shift,Resolved.DeclarationId.mk.injEq] at hm hi ⊢
  exact ⟨hm,by omega⟩
private theorem shift_not_surjective : ¬ Function.Surjective shift := by
  intro onto
  obtain ⟨a,same⟩ := onto (owner 0)
  have impossible := congrArg Resolved.DeclarationId.declarationIndex same
  simp [shift,owner] at impossible

private def expressionText := "x"
private def expressionFile : Syntax.SourceFile :=
  ⟨⟨.main,"adr0314-owner-core-expression.sol"⟩,expressionText⟩
private def bodyText :=
  "{let a:Unit=x;let b=a;match(tag){case 0{return b;}case _{return x;}}}"
private def bodyFile : Syntax.SourceFile :=
  ⟨⟨.main,"adr0314-owner-core-body.sol"⟩,bodyText⟩
private def span (file : Syntax.SourceFile) (start stop : Nat) : Syntax.SourceSpan :=
  ⟨file.id,start,stop⟩
private def identifier (file : Syntax.SourceFile) (start stop : Nat) (name : String) :
    Syntax.Identifier := ⟨span file start stop,name⟩
private def reference (file : Syntax.SourceFile) (start stop : Nat) (name : String) :
    Syntax.Expr := ⟨span file start stop,.identifier (identifier file start stop name)⟩
private def unitType (file : Syntax.SourceFile) (start stop : Nat) : Syntax.TypeExpr :=
  ⟨span file start stop,.named
    ⟨span file start stop,⟨⟨identifier file start stop "Unit",[]⟩⟩⟩ none⟩
private def returning (file : Syntax.SourceFile) (bs rs a b : Nat) (name : String) : Syntax.Block :=
  ⟨span file bs rs,[⟨span file a b,.returnStmt (some (reference file (b-2) (b-1) name))⟩]⟩
private def zeroCase : Syntax.MatchCase :=
  ⟨span bodyFile 33 50,⟨⟨span bodyFile 38 39,
    .literal ⟨span bodyFile 38 39,.decimal "0"⟩⟩,
    returning bodyFile 39 50 40 49 "b"⟩⟩
private def wildcardCase : Syntax.MatchCase :=
  ⟨span bodyFile 50 67,⟨⟨span bodyFile 55 56,.wildcard (span bodyFile 55 56)⟩,
    returning bodyFile 56 67 57 66 "x"⟩⟩
private def expectedExpression : Syntax.Expr := reference expressionFile 0 1 "x"
private def expectedBody : Syntax.Block :=
  ⟨span bodyFile 0 69,[
    ⟨span bodyFile 1 14,.letDecl (identifier bodyFile 5 6 "a")
      (some (unitType bodyFile 7 11)) (some (reference bodyFile 12 13 "x"))⟩,
    ⟨span bodyFile 14 22,.letDecl (identifier bodyFile 18 19 "b") none
      (some (reference bodyFile 20 21 "a"))⟩,
    ⟨span bodyFile 22 68,.matchWith
      ⟨span bodyFile 27 32,⟨reference bodyFile 28 31 "tag",[]⟩⟩
      ⟨span bodyFile 32 68,⟨[zeroCase,wildcardCase],none⟩⟩⟩]⟩
private def bodyRanges : List (Nat×Nat) :=
  [(0,69),(1,14),(5,6),(7,11),(7,11),(7,11),(12,13),(12,13),
   (14,22),(18,19),(20,21),(20,21),(22,68),(27,32),(28,31),(28,31),
   (32,68),(33,50),(38,39),(38,39),(39,50),(40,49),(47,48),(47,48),
   (50,67),(55,56),(55,56),(56,67),(57,66),(64,65),(64,65)]
private def bodySpans : List Syntax.SourceSpan := bodyRanges.map fun p => span bodyFile p.1 p.2

private structure ParsedExpression where
  source : Syntax.Expr
  gate : ClosedSourceDataExpression source
private structure ParsedBody where
  source : Syntax.Block
  gate : ClosedSourceDataBody source

private def parseExpression : IO ParsedExpression := do
  let .ok lexed := Syntax.Lexer.lex expressionFile | throw (IO.userError "expression lexer")
  match Syntax.Parser.expression (Syntax.Parser.State.initial expressionFile lexed) with
  | .ok source next =>
    check (lexed.diagnostics.isEmpty && next.diagnostics.isEmpty && next.atEnd &&
      next.file==expressionFile && source.span==Syntax.SourceSpan.fullFile expressionFile &&
      source==expectedExpression && source.span.isValidFor expressionFile)
      "whole handwritten expression AST/spans/EOF/diagnostics"
    match shape : source with
    | ⟨_,.identifier _⟩ => return ⟨source,by rw [shape]; exact .reference⟩
    | _ => throw (IO.userError "expression gate shape")
  | _ => throw (IO.userError "expression parser")

private def parseBody : IO ParsedBody := do
  let .ok lexed := Syntax.Lexer.lex bodyFile | throw (IO.userError "body lexer")
  match Syntax.Parser.block .require (Syntax.Parser.State.initial bodyFile lexed) with
  | .ok source next =>
    check (lexed.diagnostics.isEmpty && next.diagnostics.isEmpty && next.atEnd &&
      next.file==bodyFile && source.span==Syntax.SourceSpan.fullFile bodyFile &&
      source==expectedBody && bodySpans.all (fun s => s.isValidFor bodyFile))
      "whole handwritten body AST/all 31 spans/EOF/diagnostics"
    match shape : source with
    | ⟨_,[
        ⟨_,.letDecl _ (some _) (some ⟨_,.identifier _⟩)⟩,
        ⟨_,.letDecl _ none (some ⟨_,.identifier _⟩)⟩,
        ⟨_,.matchWith ⟨_,⟨⟨_,.identifier _⟩,[]⟩⟩
          ⟨_,⟨[
            ⟨_,⟨_,⟨_,[⟨_,.returnStmt (some ⟨_,.identifier _⟩)⟩]⟩⟩⟩,
            ⟨_,⟨_,⟨_,[⟨_,.returnStmt (some ⟨_,.identifier _⟩)⟩]⟩⟩⟩],none⟩⟩⟩]⟩ =>
      return ⟨source,by
        rw [shape]
        refine .binding .reference (.binding .reference (.wordMatch .reference ?_ ?_))
        · intro arm member
          simp only [List.mem_cons,List.not_mem_nil,or_false] at member
          rcases member with rfl | rfl <;> exact .expression .reference
        · simp⟩
    | _ => throw (IO.userError "body gate shape")
  | _ => throw (IO.userError "body parser")

private def inputs : LocalTypeInputs := ⟨[
  ⟨"x",lid oldOwner 7,.unit⟩,⟨"tag",lid foreignOwner 4,.word⟩],by decide⟩
private def types : TypeNameTable := [(["Unit"],.unit)]
private def zero : Core.Word := ⟨0,by decide⟩
private def one : Core.Word := ⟨1,by decide⟩
private def payload : Core.Value :=
  .closure .unit .word (.var 0) [.cellRef .unit 701,.hostFunction .storageWrite]
private def store : Core.Store :=
  [payload,.cellRef (.function .unit .word) 702,.hostFunction .storageRead]
private def environment (word : Core.Word) : Resolved.Environment :=
  [(lid oldOwner 7,payload),(lid foreignOwner 4,.word word)]
private def expressionEnvironment : Resolved.Environment :=
  environment zero ++ [(lid oldOwner 7,.unit),(lid foreignOwner 99,.hostFunction .storageWrite)]
private def up (e : Resolved.Environment) := e.map fun row => (row.1,RuntimeValue.ofCore row.2)

private def exerciseExpression (source : Syntax.Expr) (gate : ClosedSourceDataExpression source) : IO Unit := do
  let e := expressionEnvironment
  match resolvedRun : resolveLocalExpression? inputs.names source with
  | none => throw (IO.userError "actual old whole expression resolution")
  | some resolved =>
    let resolution := resolveLocalExpression?_sound resolvedRun
    match loweredRun : resolved.lower? e.ids with
    | none => throw (IO.userError "actual old whole expression lowering")
    | some core =>
      let lowered := Resolved.Expr.lower?_sound loweredRun
      let mapId := ownerLocalIdMap shift
      let mappedNames := LocalNameTable.mapIds mapId inputs.names
      let mappedEnvironment := Resolved.LocalScope.mapIds mapId e
      match mappedResolvedRun : resolveLocalExpression? mappedNames source with
      | none => throw (IO.userError "independent mapped whole expression resolution")
      | some mappedResolved =>
        match mappedLoweredRun : mappedResolved.lower? mappedEnvironment.ids with
        | none => throw (IO.userError "independent mapped whole expression lowering")
        | some mappedCore =>
          check (resolved==.var (lid oldOwner 7) && core==.var 0 &&
            mappedResolved==resolved.renameIds mapId && mappedCore==core)
            "complete old/mapped resolution and identical positional Core"
          match oldRun : evaluateClosedSourceExpression? 64 oldOwner inputs.names (up e)
              (store.map RuntimeValue.ofCore) source with
          | none => throw (IO.userError "actual old raw expression endpoint")
          | some (oldValue,oldFinal) =>
            let oldRaw := evaluateClosedSourceExpression?_sound oldRun
            match mappedRun : evaluateClosedSourceExpression? 64 (shift oldOwner) mappedNames
                (up mappedEnvironment) (store.map RuntimeValue.ofCore) source with
            | none => throw (IO.userError "actual owner-mapped raw expression endpoint")
            | some (mappedValue,mappedFinal) =>
              let mappedRaw := evaluateClosedSourceExpression?_sound mappedRun
              match coreRun : Core.runStateful 64 (.initial core e.values store) with
              | .done coreValue coreFinal =>
                let coreEval := Core.runStateful_evaluation_sound coreRun
                have oldImage := (gate.core_evaluates_iff resolution lowered).mp oldRaw
                have bridge := gate.mapOwners_core_evaluates_iff shift shift_injective
                  (actualValue:=mappedValue) (actualFinal:=mappedFinal) resolution lowered
                proof bridge.1; proof bridge.2.1
                have oldEndpoint : oldValue=RuntimeValue.ofCore coreValue ∧
                    oldFinal=coreFinal.map RuntimeValue.ofCore := by
                  obtain ⟨imageValue,imageStore,hv,hs,ev⟩ := oldImage
                  obtain ⟨sameValue,sameStore⟩ := Core.evaluation_deterministic ev coreEval
                  exact ⟨hv.trans (congrArg _ sameValue),hs.trans (congrArg _ sameStore)⟩
                have mappedEndpoint : mappedValue=RuntimeValue.ofCore coreValue ∧
                    mappedFinal=coreFinal.map RuntimeValue.ofCore := by
                  obtain ⟨imageValue,imageStore,hv,hs,ev⟩ := bridge.2.2.mp mappedRaw
                  obtain ⟨sameValue,sameStore⟩ := Core.evaluation_deterministic ev coreEval
                  exact ⟨hv.trans (congrArg _ sameValue),hs.trans (congrArg _ sameStore)⟩
                have mappedOfOld : mappedValue=oldValue.mapOwners shift := by
                  rw [oldEndpoint.1,mappedEndpoint.1,RuntimeValue.mapOwners_ofCore]
                have mappedStoreOfOld : mappedFinal=oldFinal.map (RuntimeValue.mapOwners shift) := by
                  rw [oldEndpoint.2,mappedEndpoint.2,mapRuntimeStoreOwners_ofCore]
                proof oldEndpoint; proof mappedEndpoint; proof mappedOfOld; proof mappedStoreOfOld
                check (oldValue.toCore?==some coreValue && mappedValue.toCore?==some coreValue &&
                  oldFinal.mapM RuntimeValue.toCore?==some coreFinal &&
                  mappedFinal.mapM RuntimeValue.toCore?==some coreFinal &&
                  coreFinal==store && mappedFinal.length==store.length)
                  "exact complete expression value and every final-store element"
              | _ => throw (IO.userError "actual Core expression evaluation")

private def exerciseBody (source : Syntax.Block) (gate : ClosedSourceDataBody source)
    (word : Core.Word) : IO Unit := do
  let e := environment word
  have sameIds : e.ids=inputs.context.ids := by rfl
  let mapId := ownerLocalIdMap shift
  let mappedInputs := inputs.mapIds mapId (ownerLocalIdMap_injective shift shift_injective)
  let mappedEnvironment := Resolved.LocalScope.mapIds mapId e
  match accepted : elaborateComputationReturnTree? elaborateLocalExpression? types oldOwner inputs source with
  | none => throw (IO.userError "actual old whole body checker")
  | some (core,type) =>
    match mappedAccepted : elaborateComputationReturnTree? elaborateLocalExpression? types
        (shift oldOwner) mappedInputs source with
    | none => throw (IO.userError "independent mapped whole body checker")
    | some (mappedCore,mappedType) =>
      check (type==.unit && mappedCore==core && mappedType==type &&
        Resolved.freshLocalId oldOwner inputs.ids==lid oldOwner 8 &&
        Resolved.freshLocalId oldOwner (lid oldOwner 8::inputs.ids)==lid oldOwner 9 &&
        Resolved.freshLocalId (shift oldOwner) mappedInputs.ids==lid (shift oldOwner) 8 &&
        Resolved.freshLocalId (shift oldOwner) (lid (shift oldOwner) 8::mappedInputs.ids)==
          lid (shift oldOwner) 9)
        "typed/inferred fresh bindings and complete old/mapped checker result"
      match oldRun : evaluateClosedSourceBody? 64 oldOwner inputs.names (up e)
          (store.map RuntimeValue.ofCore) source with
      | none => throw (IO.userError "actual old raw body endpoint")
      | some (oldValue,oldFinal) =>
        let oldRaw := evaluateClosedSourceBody?_sound oldRun
        match mappedRun : evaluateClosedSourceBody? 64 (shift oldOwner) mappedInputs.names
            (up mappedEnvironment) (store.map RuntimeValue.ofCore) source with
        | none => throw (IO.userError "actual owner-mapped raw body endpoint")
        | some (mappedValue,mappedFinal) =>
          let mappedRaw := evaluateClosedSourceBody?_sound mappedRun
          match coreRun : Core.runStateful 128 (.initial core e.values store) with
          | .done coreValue coreFinal =>
            let coreEval := Core.runStateful_evaluation_sound coreRun
            have oldImage := (gate.core_evaluates_iff accepted sameIds).mp oldRaw
            have bridge := gate.mapOwners_core_evaluates_iff shift shift_injective
              (environment:=e) (initialStore:=store) (actualValue:=mappedValue)
              (actualFinal:=mappedFinal) accepted sameIds
            proof bridge.1; proof bridge.2.1
            have oldEndpoint : oldValue=RuntimeValue.ofCore coreValue ∧
                oldFinal=coreFinal.map RuntimeValue.ofCore := by
              obtain ⟨imageValue,imageStore,hv,hs,ev⟩ := oldImage
              obtain ⟨sameValue,sameStore⟩ := Core.evaluation_deterministic ev coreEval
              exact ⟨hv.trans (congrArg _ sameValue),hs.trans (congrArg _ sameStore)⟩
            have mappedEndpoint : mappedValue=RuntimeValue.ofCore coreValue ∧
                mappedFinal=coreFinal.map RuntimeValue.ofCore := by
              obtain ⟨imageValue,imageStore,hv,hs,ev⟩ := bridge.2.2.mp mappedRaw
              obtain ⟨sameValue,sameStore⟩ := Core.evaluation_deterministic ev coreEval
              exact ⟨hv.trans (congrArg _ sameValue),hs.trans (congrArg _ sameStore)⟩
            have mappedOfOld : mappedValue=oldValue.mapOwners shift := by
              rw [oldEndpoint.1,mappedEndpoint.1,RuntimeValue.mapOwners_ofCore]
            have mappedStoreOfOld : mappedFinal=oldFinal.map (RuntimeValue.mapOwners shift) := by
              rw [oldEndpoint.2,mappedEndpoint.2,mapRuntimeStoreOwners_ofCore]
            proof oldEndpoint; proof mappedEndpoint; proof mappedOfOld; proof mappedStoreOfOld
            check (oldValue.toCore?==some coreValue && mappedValue.toCore?==some coreValue &&
              oldFinal.mapM RuntimeValue.toCore?==some coreFinal &&
              mappedFinal.mapM RuntimeValue.toCore?==some coreFinal &&
              coreValue==payload && coreFinal==store && mappedFinal.length==store.length)
              "exact complete ordered-match body value and every final-store element"
          | _ => throw (IO.userError "actual Core body evaluation")

end Tests.ADR0314ParsedOwnerCore

open Solcore Tests.ADR0314ParsedOwnerCore in
def Tests.adr0314ParsedOwnerCoreConsumer : IO Unit := do
  proof shift_not_surjective
  check (!store.isEmpty && store.length==3 && expressionEnvironment.length==4)
    "nonempty complete store and duplicate/foreign expression rows"
  let expression ← parseExpression
  let body ← parseBody
  exerciseExpression expression.source expression.gate
  for word in [zero,one] do exerciseBody body.source body.gate word
  IO.println "ADR0314 parsed old/mapped raw endpoints and owner/Core bridges GREEN"
end

section
-- leanmerge: from Solcore.Test.FrontendParsedOwnerCovariance
/- Independent parsed originals and direct old runs precede finite covariance.
Every tested budget then executes the mapped evaluator and retains full endpoints.
Annotations, nested code and cell locations are inert, not heap-validity claims. -/
set_option autoImplicit false
namespace Tests.ParsedOwnerCovariance
open Solcore Solcore.Frontend
private abbrev V := RuntimeValue
private abbrev E := ClosedSourceExpressionEvaluates
private abbrev B := ClosedSourceBodyEvaluates
private def check (b : Bool) (s : String) : IO Unit := unless b do throw (IO.userError s)
private def proof {p : Prop} (_ : p) : IO Unit := pure ()
private def owner (n : Nat) : Resolved.DeclarationId := ⟨⟨.main,⟨[⟨"ParsedOwner",by decide⟩],by decide⟩⟩,n⟩
private def so := owner 311
private def co := owner 711
private def fo := owner 911
private def lid (o : Resolved.DeclarationId) (i : Nat) : Resolved.LocalId := ⟨o,i⟩
private def shift (o : Resolved.DeclarationId) : Resolved.DeclarationId := {o with declarationIndex:=o.declarationIndex+5}
private theorem shift_injective : Function.Injective shift := by
  intro a b same
  have hm := congrArg Resolved.DeclarationId.moduleId same
  have hi := congrArg Resolved.DeclarationId.declarationIndex same
  cases a; cases b
  simp only [shift,Resolved.DeclarationId.mk.injEq] at hm hi ⊢
  exact ⟨hm,by omega⟩
private def sn : LocalNameTable := [("q",lid so 8),("foreign",lid fo 99),("q",lid so 99),("q",lid fo 8)]
private def se (v : V) : Resolved.LocalScope V :=
  [(lid fo 8,.unit),(lid so 8,v),(lid so 8,.bool false),(lid so 100,.cellRef .word 800),
   (lid so 101,.hostFunction .storageWrite),(lid so 102,.bool false),(lid fo 100,v)]
private def cn : LocalNameTable := [("f",lid co 1),("x",lid co 2),("x",lid fo 2),("f",lid co 99),("x",lid co 99)]
private def ce (saved av : V) : Resolved.LocalScope V :=
  [(lid fo 1,.unit),(lid co 1,saved),(lid co 1,.bool false),(lid fo 2,.unit),(lid co 2,av),(lid co 2,.unit)]
private def core : V := .ofCore (.closure .unit .word (.var 99) [.cellRef .word 701,.hostFunction .storageWrite])
private def mixed (source : Syntax.Expr) (caller saved foreign : Resolved.DeclarationId) : V :=
  .pair (.sourceClosure source saved [("q",lid saved 8),("q",lid foreign 8)]
    [(lid saved 8,.coreClosure .unit .word (.var 17)
      [.sourceClosure source foreign [("q",lid caller 8)] [(lid caller 8,.cellRef .word 702),(lid caller 8,.unit)],core]),
     (lid saved 8,.bool false)]) (.pair core (.cellRef .word 703))
private theorem mixed_fields (source : Syntax.Expr) :
    (mixed source co so fo).mapOwners shift = mixed source (shift co) (shift so) (shift fo) := by
  simp only [mixed,core,RuntimeValue.ofCore,List.attach_map_val,RuntimeValue.mapOwners_sourceClosure,
    RuntimeValue.mapOwners_coreClosure,RuntimeValue.mapOwners,mapRuntimeCapturedOwners,
    LocalNameTable.mapIds,ownerLocalIdMap,lid,List.map_cons,List.map_nil]
private def span (f : Syntax.SourceFile) (a b : Nat) : Syntax.SourceSpan := ⟨f.id,a,b⟩
private def ref (f : Syntax.SourceFile) (a b : Nat) (n : String) : Syntax.Expr := ⟨span f a b,.identifier ⟨span f a b,n⟩⟩
private def ty (f : Syntax.SourceFile) (a b : Nat) : Syntax.TypeExpr :=
  ⟨span f a b,.named ⟨span f a b,⟨⟨⟨span f a b,"Unit"⟩,[]⟩⟩⟩ none⟩
private def expectedLambda (typed : Bool) (f : Syntax.SourceFile) : Syntax.Expr :=
  let d := if typed then 5 else 0
  ⟨span f 0 (38+d),.lambda (span f 0 3)
    ⟨span f 3 (6+d),[if typed then ⟨span f 4 10,.typed none ⟨span f 4 5,"q"⟩ (ty f 6 10)⟩
      else ⟨span f 4 5,.inferred ⟨span f 4 5,"q"⟩⟩]⟩ none
    ⟨span f (6+d) (38+d),[⟨span f (7+d) (20+d),.letDecl ⟨span f (11+d) (12+d),"q"⟩
      (some (ty f (13+d) (17+d))) (some (ref f (18+d) (19+d) "q"))⟩,
      ⟨span f (20+d) (28+d),.letDecl ⟨span f (24+d) (25+d),"q"⟩ none (some (ref f (26+d) (27+d) "q"))⟩,
      ⟨span f (28+d) (37+d),.returnStmt (some (ref f (35+d) (36+d) "q"))⟩]⟩⟩
private def expectedCall (f : Syntax.SourceFile) : Syntax.Expr := ⟨span f 0 4,.call (ref f 0 1 "f") ⟨span f 1 4,[ref f 2 3 "x"]⟩⟩
private def expectedChoice (f : Syntax.SourceFile) : Syntax.Expr :=
  ⟨span f 0 6,.binary (ref f 0 1 "a") ⟨span f 2 4,.logicalOr⟩ (ref f 5 6 "f")⟩
private def typeSpans : Syntax.TypeExpr → List Syntax.SourceSpan
  | ⟨s,.named ⟨q,⟨⟨n,[]⟩⟩⟩ none⟩ => [s,q,n.span]
  | _ => []
private def parameterSpans : Syntax.LambdaParameter → List Syntax.SourceSpan
  | ⟨s,.inferred n⟩ => [s,n.span]
  | ⟨s,.typed none n t⟩ => [s,n.span]++typeSpans t
  | _ => []
private def spans : Syntax.Expr → List Syntax.SourceSpan
  | ⟨s,.identifier n⟩ => [s,n.span]
  | ⟨s,.call f ⟨a,[x]⟩⟩ => [s]++spans f++[a]++spans x
  | ⟨s,.binary l op r⟩ => [s]++spans l++[op.span]++spans r
  | ⟨s,.lambda k ⟨ps,[p]⟩ none ⟨b,[⟨l,.letDecl n (some t) (some i)⟩,
      ⟨l2,.letDecl n2 none (some i2)⟩,⟨r,.returnStmt (some e)⟩]⟩⟩ =>
    [s,k,ps]++parameterSpans p++[b,l,n.span]++typeSpans t++spans i++[l2,n2.span]++spans i2++[r]++spans e
  | _ => []
private def ranges (typed : Bool) : List (Nat × Nat) :=
  let d := if typed then 5 else 0
  [(0,38+d),(0,3),(3,6+d)]++(if typed then [(4,10),(4,5),(6,10),(6,10),(6,10)] else [(4,5),(4,5)])++
    ([(6,38),(7,20),(11,12),(13,17),(13,17),(13,17),(18,19),(18,19),(20,28),(24,25),
      (26,27),(26,27),(28,37),(35,36),(35,36)].map (fun (a,b) => (a+d,b+d)))
private def parsed (text : String) (ast : Syntax.SourceFile → Syntax.Expr) (expectedRanges : List (Nat × Nat)) : IO Syntax.Expr := do
  let file : Syntax.SourceFile := ⟨⟨.main,"parsed-owner-replay.sol"⟩,text⟩
  let .ok lexed := Syntax.Lexer.lex file | throw (IO.userError "owner lexer")
  match Syntax.Parser.expression (Syntax.Parser.State.initial file lexed) with
  | .ok actual next =>
    check (lexed.diagnostics.isEmpty && next.diagnostics.isEmpty && next.atEnd && next.file==file &&
      actual.span==Syntax.SourceSpan.fullFile file && actual==ast file) "whole handwritten AST / EOF / diagnostics"
    check ((spans actual).all (fun s => s.isValidFor file) &&
      (spans actual).map (fun s => (s.startByte,s.endByte))==expectedRanges) "all actual handwritten spans"
    return actual
  | _ => throw (IO.userError "owner parser")
private def sameOption (before after : Option (V × List V))
    (law : after = before.map (fun result => (result.1.mapOwners shift,result.2.map (RuntimeValue.mapOwners shift)))) : IO Unit := do
  match hb : before, ha : after with
  | none,none => proof law; proof ha
  | some (expected,expectedStore),some (actual,actualStore) =>
    proof (show actual=expected.mapOwners shift ∧ actualStore=expectedStore.map (RuntimeValue.mapOwners shift) from
      Prod.mk.inj (Option.some.inj (by simpa only [hb,ha,Option.map_some] using law)))
  | _,_ => throw (IO.userError "same budget changed complete Option shape")
private def expression {o n e st source v final} (original : E o n e st source v final) (depth : Nat) : IO Unit := do
  proof original
  for budget in [0,depth-1,depth,depth+3] do
    let before := evaluateClosedSourceExpression? budget o n e st source
    match ran : before with
    | none => check (budget<depth) "independent insufficient expression budget"
    | some (actual,out) =>
      proof (show actual=v ∧ out=final from (evaluateClosedSourceExpression?_sound ran).deterministic original)
      check (depth≤budget) "independent full expression endpoint"
    let law := evaluateClosedSourceExpression?_mapOwners shift shift_injective budget o n e st source
    proof law
    sameOption before (evaluateClosedSourceExpression? budget (shift o) (LocalNameTable.mapIds (ownerLocalIdMap shift) n)
      (mapRuntimeCapturedOwners shift e) (st.map (RuntimeValue.mapOwners shift)) source) law
private def body {o n e st source v final} (original : B o n e st source v final) (depth : Nat) : IO Unit := do
  proof original
  for budget in [0,depth-1,depth,depth+3] do
    let before := evaluateClosedSourceBody? budget o n e st source
    match ran : before with
    | none => check (budget<depth) "independent insufficient body budget"
    | some (actual,out) =>
      proof (show actual=v ∧ out=final from (evaluateClosedSourceBody?_sound ran).deterministic original)
      check (depth≤budget) "independent full body endpoint"
    let law := evaluateClosedSourceBody?_mapOwners shift shift_injective budget o n e st source
    proof law
    sameOption before (evaluateClosedSourceBody? budget (shift o) (LocalNameTable.mapIds (ownerLocalIdMap shift) n)
      (mapRuntimeCapturedOwners shift e) (st.map (RuntimeValue.mapOwners shift)) source) law
private def logical (source : Syntax.Expr) (saved : V) (st : List V) : IO Unit := do
  match hs : source with
  | ⟨_,.binary ⟨ls,.identifier left⟩ ⟨_,.logicalOr⟩ ⟨rs,.identifier right⟩⟩ =>
    if names : left.value="a" ∧ right.value="f" then
      let n : LocalNameTable := [("a",lid co 0),("f",lid co 1),("f",lid fo 1)]
      let e : Resolved.LocalScope V := [(lid co 0,.bool false),(lid fo 1,.unit),(lid co 1,saved),(lid co 1,.unit)]
      have selected : E co n e st source saved st := by
        rw [hs]; exact .orFalse (.reference (names.1 ▸ LocalNameTable.Lookup.head) .head)
          (.reference (names.2 ▸ LocalNameTable.Lookup.tail (by decide) .head) (.tail (by decide) (.tail (by decide) .head)))
      have skipped : E co [("a",lid co 0)] [(lid co 0,.bool true)] st source (.bool true) st := by
        rw [hs]; exact .orTrue (.reference (names.1 ▸ LocalNameTable.Lookup.head) .head)
      have missing : LocalNameTable.lookup? [("a",lid co 0)] right.value = none := by
        simp only [names.2,LocalNameTable.lookup?]; decide
      proof selected; proof skipped; proof missing
      expression selected 2; expression skipped 2
    else throw (IO.userError "actual a/f spellings")
  | _ => throw (IO.userError "actual logical choice AST")
private def application {source whole : Syntax.Expr} {parameter : Syntax.Identifier} {block : Syntax.Block}
    (shape : SourceUnaryLambdaShape source parameter block) (choice : Syntax.Expr) (av : V) (st : List V) : IO Unit := do
  let creationStore := [core,.unit]
  have creation : E so sn (se av) creationStore source (.sourceClosure source so sn (se av)) creationStore := .creation shape
  proof creation
  match created : evaluateClosedSourceExpression? 1 so sn (se av) creationStore source with
  | some (.sourceClosure actualSource actualOwner actualNames actualCaptured,creationFinal) =>
    have same := (evaluateClosedSourceExpression?_sound created).deterministic creation
    have fields := RuntimeValue.sourceClosure.inj same.1
    have actualShape : SourceUnaryLambdaShape actualSource parameter block := fields.1.symm ▸ shape
    proof fields; proof same.2
    check (actualOwner != co && actualOwner != fo && creationFinal.length != st.length) "separate saved owner / creation and invocation stores"
    have mappedFields : (.sourceClosure actualSource actualOwner actualNames actualCaptured : V).mapOwners shift =
        .sourceClosure actualSource (shift actualOwner) (LocalNameTable.mapIds (ownerLocalIdMap shift) actualNames)
          (mapRuntimeCapturedOwners shift actualCaptured) := RuntimeValue.mapOwners_sourceClosure shift _ _ _ _
    proof mappedFields
    match hw : whole with
    | ⟨cs,.call ⟨fs,.identifier f⟩ ⟨als,[⟨xs,.identifier x⟩]⟩⟩ =>
      if names : f.value="f" ∧ x.value="x" ∧ parameter.value="q" then
        let n := cn; let e := ce (.sourceClosure actualSource actualOwner actualNames actualCaptured) av
        have picked : E co n e st ⟨fs,.identifier f⟩ (.sourceClosure actualSource actualOwner actualNames actualCaptured) st :=
          .reference (names.1 ▸ LocalNameTable.Lookup.head) (.tail (by decide) .head)
        have argumentOriginal : E co n e st ⟨xs,.identifier x⟩ av st :=
          .reference (names.2.1 ▸ LocalNameTable.Lookup.tail (by decide) .head)
            (.tail (by decide) (.tail (by decide) (.tail (by decide) (.tail (by decide) .head))))
        let fresh := Resolved.freshLocalId actualOwner (actualNames.map Prod.snd)
        let bn := (parameter.value,fresh)::actualNames; let be := (fresh,av)::actualCaptured
        have freshExact : fresh=lid so 100 ∧
            Resolved.freshLocalId actualOwner (bn.map Prod.snd)=lid so 101 := by
          rcases fields with ⟨_,rfl,rfl,rfl⟩
          exact ⟨by decide,by change Resolved.freshLocalId so (lid so 100 :: sn.map Prod.snd)=lid so 101; decide⟩
        proof freshExact
        match hb : block with
        | ⟨bs,[⟨_,.letDecl bound (some _) (some ⟨is,.identifier initializer⟩)⟩,
            ⟨_,.letDecl bound2 none (some ⟨is2,.identifier initializer2⟩)⟩,⟨rs,.returnStmt (some ⟨ys,.identifier key⟩)⟩]⟩ =>
          if equal : initializer.value=parameter.value ∧ initializer2.value=bound.value ∧ key.value=bound2.value then
            have init : E actualOwner bn be st ⟨is,.identifier initializer⟩ av st := .reference (equal.1 ▸ LocalNameTable.Lookup.head) .head
            let fresh2 := Resolved.freshLocalId actualOwner (bn.map Prod.snd)
            let bn2 := (bound.value,fresh2)::bn; let be2 := (fresh2,av)::be
            have init2 : E actualOwner bn2 be2 st ⟨is2,.identifier initializer2⟩ av st :=
              .reference (equal.2.1 ▸ LocalNameTable.Lookup.head) .head
            have fresh3 : Resolved.freshLocalId actualOwner (bn2.map Prod.snd)=lid so 102 := by
              rcases fields with ⟨_,rfl,rfl,rfl⟩
              change Resolved.freshLocalId so (lid so 101 :: lid so 100 :: sn.map Prod.snd)=lid so 102
              decide
            proof fresh3
            have returned : B actualOwner ((bound2.value,Resolved.freshLocalId actualOwner (bn2.map Prod.snd))::bn2)
                ((Resolved.freshLocalId actualOwner (bn2.map Prod.snd),av)::be2) st
                ⟨bs,[⟨rs,.returnStmt (some ⟨ys,.identifier key⟩)⟩]⟩ av st :=
              .expression (.reference (equal.2.2 ▸ LocalNameTable.Lookup.head) .head)
            have originalBody : B actualOwner bn be st block av st := by rw [hb]; exact .binding init (.inferred init2 returned)
            have originalCall : E co n e st whole av st := by rw [hw]; exact .call actualShape picked argumentOriginal originalBody
            proof picked; proof argumentOriginal; proof init; proof init2; proof returned; proof originalBody; proof originalCall
            match cr : evaluateClosedSourceExpression? 1 co n e st ⟨fs,.identifier f⟩ with
            | some (calleeValue,calleeStore) =>
              have actualCallee := evaluateClosedSourceExpression?_sound cr
              have calleeEndpoint := actualCallee.deterministic picked
              proof calleeEndpoint
              match ar : evaluateClosedSourceExpression? 1 co n e calleeStore ⟨xs,.identifier x⟩ with
              | some (argumentValue,argumentStore) =>
                have actualArgument := evaluateClosedSourceExpression?_sound ar
                have alignedArgument : E co n e st ⟨xs,.identifier x⟩ argumentValue argumentStore := calleeEndpoint.2 ▸ actualArgument
                have argumentEndpoint := alignedArgument.deterministic argumentOriginal
                proof argumentEndpoint
                match ran : evaluateClosedSourceBody? 4 actualOwner bn ((fresh,argumentValue)::actualCaptured) argumentStore block with
                | some (actual,out) =>
                  have actualBody := evaluateClosedSourceBody?_sound ran
                  have alignedBody : B actualOwner bn be st block actual out := by
                    simpa only [argumentEndpoint.1,argumentEndpoint.2] using actualBody
                  have endpoint := alignedBody.deterministic originalBody
                  proof endpoint
                  have actualCall := ClosedSourceExpressionEvaluates.call (span:=cs) (argumentsSpan:=als) actualShape
                    (calleeEndpoint.1 ▸ actualCallee) actualArgument actualBody
                  proof actualCall
                  body actualBody 4
                  expression actualCall 5
                | none => throw (IO.userError "actual typed/inferred saved body")
              | none => throw (IO.userError "actual argument at actual callee store")
            | none => throw (IO.userError "actual caller saved callee")
            expression creation 1; expression picked 1; expression argumentOriginal 1
            logical choice (.sourceClosure actualSource actualOwner actualNames actualCaptured) st
          else throw (IO.userError "actual fresh shadowing spellings")
        | _ => throw (IO.userError "actual typed/inferred saved body shape")
      else throw (IO.userError "actual caller and parameter spellings")
    | _ => throw (IO.userError "actual f(x) shape")
  | _ => throw (IO.userError "actual returned creation closure")
private def savedCall (source whole choice : Syntax.Expr) (av : V) (st : List V) : IO Unit := do
  match hs : source with
  | ⟨_,.lambda _ ⟨_,[⟨_,.inferred p⟩]⟩ _ b⟩ =>
    have shape : SourceUnaryLambdaShape source p b := by rw [hs]; exact .inferred
    application (whole:=whole) shape choice av st
  | ⟨_,.lambda _ ⟨_,[⟨_,.typed none p _⟩]⟩ _ b⟩ =>
    have shape : SourceUnaryLambdaShape source p b := by rw [hs]; exact .typed
    application (whole:=whole) shape choice av st
  | _ => throw (IO.userError "actual unmarked unary lambda")
end Tests.ParsedOwnerCovariance
open Solcore Solcore.Frontend Tests.ParsedOwnerCovariance in
def Tests.frontendParsedOwnerCovarianceTests : IO Unit := do
  let inferred ← parsed "lam(q){let q:Unit=q;let q=q;return q;}" (expectedLambda false) (ranges false)
  let typed ← parsed "lam(q:Unit){let q:Unit=q;let q=q;return q;}" (expectedLambda true) (ranges true)
  let call ← parsed "f(x)" expectedCall [(0,4),(0,1),(0,1),(1,4),(2,3),(2,3)]
  let choice ← parsed "a || f" expectedChoice [(0,6),(0,1),(0,1),(2,4),(5,6),(5,6)]
  let mut count := 0
  for source in [inferred,typed] do
    let nested := mixed source co so fo
    have exactValue := mixed_fields source
    have exactStore : [nested,RuntimeValue.cellRef .word 900,core].map (RuntimeValue.mapOwners shift) =
        [mixed source (shift co) (shift so) (shift fo),.cellRef .word 900,core] := by
      simp only [List.map_cons,List.map_nil,nested,exactValue,core,RuntimeValue.ofCore,List.attach_map_val,
        RuntimeValue.mapOwners_coreClosure,RuntimeValue.mapOwners,List.map_cons,List.map_nil]
    proof exactValue; proof exactStore
    for av in [nested,RuntimeValue.pair (.cellRef .word 901) nested] do
      for st in [[nested,.cellRef .word 900,core],[core,nested,.cellRef .word 999,.hostFunction .storageRead]] do
        savedCall source call choice av st
        count := count+1
  check (count==8) "two actual lambda annotations / two nested arguments / two nonempty stores"
end

section
-- leanmerge: from Solcore.Test.FrontendParsedOwnerExpectedDataLambdaApplications
/- The parser must produce a literal call(lambda,args), not a grouped callee.
Old and mapped checkers/runners and Core execution precede bridge use. -/
set_option autoImplicit false
namespace Tests.ADR0315ParsedOwnerExpectedDataLambdaApplications
open Solcore Solcore.Frontend

private def check (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)
private def proof {proposition : Prop} (_ : proposition) : IO Unit := pure ()
private def owner : Resolved.DeclarationId :=
  ⟨⟨.main, ⟨[⟨"ParsedOwnerDataApplication", by decide⟩], by decide⟩⟩, 175⟩
private def sid (index : Nat) : Resolved.LocalId := ⟨owner, index⟩
private def foreignOwner : Resolved.DeclarationId := { owner with declarationIndex := 901 }
private def foreign (index : Nat) : Resolved.LocalId := ⟨foreignOwner, index⟩
private def shift (declaration : Resolved.DeclarationId) : Resolved.DeclarationId :=
  { declaration with declarationIndex := declaration.declarationIndex + 5 }
private theorem shift_injective : Function.Injective shift := by
  intro left right same
  have modules := congrArg Resolved.DeclarationId.moduleId same
  have indices := Nat.add_right_cancel (congrArg Resolved.DeclarationId.declarationIndex same)
  cases left; cases right; cases modules; cases indices; rfl
private theorem shift_not_surjective : ¬ Function.Surjective shift := by
  intro onto
  obtain ⟨before, same⟩ := onto { owner with declarationIndex := 0 }
  have impossible := congrArg Resolved.DeclarationId.declarationIndex same
  change before.declarationIndex + 5 = 0 at impossible
  omega

private def inputs : LocalTypeInputs :=
  ⟨[⟨"arg", sid 9, .unit⟩, ⟨"noise", foreign 700, .word⟩,
    ⟨"arg", foreign 701, .bool⟩], by decide⟩
private def environment (payload : Core.Value) : Resolved.Environment :=
  [(sid 9, payload), (foreign 700, .word (Core.Word.ofNatModulo 99)),
    (foreign 701, .bool false)]
private def up (environment : Resolved.Environment) :
    List (Resolved.LocalId × RuntimeValue) :=
  environment.map (fun row => (row.1, RuntimeValue.ofCore row.2))

private def parse (text : String) : IO Syntax.Expr := do
  let file : Syntax.SourceFile :=
    ⟨⟨.main, "parsed-owner-expected-data-application.sol"⟩, text⟩
  let .ok lexed := Syntax.Lexer.lex file | throw (IO.userError "lexer")
  match Syntax.Parser.expression (Syntax.Parser.State.initial file lexed) with
  | .ok source next =>
      check (lexed.diagnostics.isEmpty && next.diagnostics.isEmpty && next.atEnd &&
        source.span == Syntax.SourceSpan.fullFile file) "complete parse and source span"
      return source
  | _ => throw (IO.userError "expression parser")

private def text := "lam(x){return x;}(arg)"

private def exercise (payload : Core.Value) (store : Core.Store) : IO Unit := do
  let parsed ← parse text
  let environment := environment payload
  let mappedInputs := inputs.mapIds (ownerLocalIdMap shift)
    (ownerLocalIdMap_injective shift shift_injective)
  let mappedEnvironment := Resolved.LocalScope.mapIds (ownerLocalIdMap shift) environment
  have sameIds : environment.ids = inputs.context.ids := rfl
  have mappedSameIds : mappedEnvironment.ids = mappedInputs.context.ids := rfl
  match original : parsed with
  | ⟨callSpan, .call function ⟨argumentsSpan, [argument]⟩⟩ =>
    match functionShape : function, argumentShape : argument with
    | ⟨functionSpan, .lambda keywordSpan
        ⟨parametersSpan, [⟨parameterSpan, .inferred name⟩]⟩ none
        ⟨bodySpan, [⟨returnSpan,
          .returnStmt (some ⟨referenceSpan, .identifier returnedName⟩)⟩]⟩⟩,
      ⟨argumentSpan, .identifier argumentName⟩ =>
      let returned : Syntax.Expr := ⟨referenceSpan, .identifier returnedName⟩
      let body : Syntax.Block :=
        ⟨bodySpan, [⟨returnSpan, .returnStmt (some returned)⟩]⟩
      have sourceShape : SourceUnaryLambdaShape function name body := by
        rw [functionShape]
        exact .inferred
      have bodyGate : ClosedSourceDataBody body := .expression .reference
      have argumentGate : ClosedSourceDataExpression argument := by
        rw [argumentShape]
        exact .reference
      check (functionSpan.startByte == 0 && functionSpan.endByte == argumentsSpan.startByte &&
        callSpan.startByte == 0 && argumentSpan == argumentName.span &&
        keywordSpan.startByte == 0 && parametersSpan.contains parameterSpan &&
        bodySpan.contains returnSpan && name.value == "x" && returnedName.value == "x" &&
        argumentName.value == "arg")
        "ungrouped call(lambda,args), spellings, and retained spans"
      match checked : elaborateExpectedComputationLambda? elaborateLocalExpression? [] owner
          inputs function (.function .unit .unit) with
      | some (.lambda .unit .unit bodyCore) =>
        have mappedChecked : elaborateExpectedComputationLambda? elaborateLocalExpression?
            [] (shift owner) mappedInputs function (.function .unit .unit) =
            some (.lambda .unit .unit bodyCore) := by
          simpa only [mappedInputs] using
            (elaborateExpectedComputationLambda?_mapOwner shift shift_injective
              elaborateLocalExpression?
              (elaborateLocalExpression?_mapIds (ownerLocalIdMap shift)
                (ownerLocalIdMap_injective shift shift_injective)) [] owner inputs function
              (.function .unit .unit)).trans checked
        check (elaborateExpectedComputationLambda? elaborateLocalExpression? []
          (shift owner) mappedInputs function (.function .unit .unit) ==
            some (.lambda .unit .unit bodyCore) &&
          elaborateComputationReturnTree? elaborateLocalExpression? [] (shift owner)
            (mappedInputs.bindFresh (shift owner) name.value .unit) body ==
              some (bodyCore, .unit)) "actual mapped expected/body checkers"
        proof checked; proof mappedChecked; proof sameIds; proof mappedSameIds
        match resolved : resolveLocalExpression? inputs.names argument with
        | some resolvedArgument =>
          let argumentResolution := resolveLocalExpression?_sound resolved
          match lowered : resolvedArgument.lower? environment.ids with
          | some argumentCore =>
            let argumentLowering := Resolved.Expr.lower?_sound lowered
            check (resolveLocalExpression?
              (LocalNameTable.mapIds (ownerLocalIdMap shift) inputs.names) argument ==
                some (resolvedArgument.renameIds (ownerLocalIdMap shift)) &&
              (resolvedArgument.renameIds (ownerLocalIdMap shift)).lower?
                mappedEnvironment.ids == some argumentCore)
              "actual mapped argument resolution and lowering"
            match oldRun : evaluateClosedSourceExpression? 16 owner inputs.names
                (up environment) (store.map RuntimeValue.ofCore) parsed with
            | none => throw (IO.userError "old raw evaluator")
            | some (oldValue, oldFinal) =>
              let oldActual := evaluateClosedSourceExpression?_sound oldRun
              match mappedRun : evaluateClosedSourceExpression? 16 (shift owner)
                  (LocalNameTable.mapIds (ownerLocalIdMap shift) inputs.names)
                  (mappedEnvironment.map (fun row => (row.1, RuntimeValue.ofCore row.2)))
                  (store.map RuntimeValue.ofCore) parsed with
              | none => throw (IO.userError "mapped raw evaluator")
              | some (mappedValue, mappedFinal) =>
                let mappedActual := evaluateClosedSourceExpression?_sound mappedRun
                let core := Core.Expr.apply (.lambda .unit .unit bodyCore) argumentCore
                match coreRun : Core.runStateful 64 (.initial core environment.values store) with
                | .done coreValue coreFinal =>
                  let actualCore := Core.runStateful_evaluation_sound coreRun
                  have oldImage {value finalStore} :=
                    closedSourceExpectedDataLambda_application_core_iff sourceShape bodyGate checked
                      sameIds argumentGate argumentResolution argumentLowering
                      (callSpan := callSpan) (argumentsSpan := argumentsSpan)
                      (initialStore := store) (actualValue := value) (actualFinal := finalStore)
                  have oldForward := (oldImage (value := oldValue) (finalStore := oldFinal)).mp
                    (by simpa only [original, up] using oldActual)
                  have mappedStages {value finalStore} :=
                    closedSourceExpectedDataLambda_application_mapOwners_core_iff
                      shift shift_injective sourceShape bodyGate checked sameIds argumentGate
                      argumentResolution argumentLowering (callSpan := callSpan)
                      (argumentsSpan := argumentsSpan) (initialStore := store)
                      (actualValue := value) (actualFinal := finalStore)
                  let mappedImage :=
                    (mappedStages (value := mappedValue) (finalStore := mappedFinal)).2.2.2.2
                  have mappedForward := mappedImage.mp
                    (by simpa only [original] using mappedActual)
                  have endpoint : mappedValue = RuntimeValue.ofCore coreValue ∧
                      mappedFinal = coreFinal.map RuntimeValue.ofCore := by
                    obtain ⟨imageValue, imageStore, valueEq, storeEq, imageCore⟩ := mappedForward
                    obtain ⟨sameValue, sameStore⟩ :=
                      Core.evaluation_deterministic imageCore actualCore
                    exact ⟨valueEq.trans (congrArg RuntimeValue.ofCore sameValue),
                      storeEq.trans (congrArg (List.map RuntimeValue.ofCore) sameStore)⟩
                  proof oldForward; proof endpoint
                  proof (mappedImage.mpr
                    ⟨coreValue, coreFinal, endpoint.1, endpoint.2, actualCore⟩)
                  proof ((mappedStages (value := RuntimeValue.ofCore coreValue)
                    (finalStore := coreFinal.map RuntimeValue.ofCore)).2.2.2.2.mpr
                      ⟨coreValue, coreFinal, rfl, rfl, actualCore⟩)
                  check (mappedValue.toCore? == some coreValue &&
                    mappedFinal.mapM RuntimeValue.toCore? == some coreFinal &&
                    oldValue.toCore? == some coreValue &&
                    oldFinal.mapM RuntimeValue.toCore? == some coreFinal)
                    "old/mapped projections after both mapped iff directions"
                | _ => throw (IO.userError "Core runner")
          | none => throw (IO.userError "old argument lowering")
        | none => throw (IO.userError "old argument resolution")
      | _ => throw (IO.userError "old expected checker")
    | _, _ => throw (IO.userError "inferred lambda and reference argument")
  | _ => throw (IO.userError "actual ungrouped call(lambda,args) AST")

end Tests.ADR0315ParsedOwnerExpectedDataLambdaApplications

open Solcore Tests.ADR0315ParsedOwnerExpectedDataLambdaApplications in
def Tests.adr0315ParsedOwnerExpectedDataLambdaApplicationTests : IO Unit := do
  proof shift_not_surjective
  let payload := Core.Value.closure .unit .word (.var 99)
    [.hostFunction .storageWrite, .cellRef .unit 700,
      .closure .bool .unit (.var 5) [.hostFunction .callerAddress]]
  let store : Core.Store :=
    [.cellRef (.function .unit .word) 900, .hostFunction .storageRead, payload, .unit]
  check (!store.isEmpty && inputs.names[0]?.map Prod.fst == some "arg" &&
    inputs.names[2]?.map Prod.fst == some "arg") "nonempty store and duplicate/foreign rows"
  exercise payload store
  IO.println "ADR0315 parsed ungrouped owner-mapped data-lambda application GREEN"
end

section
-- leanmerge: from Solcore.Test.FrontendParsedOwnerExpectedDataLambdaInvocations
/- Parsed old/mapped creation, caller prefixes, complete raw calls and the Core
runner all execute before the owner-transported saved-lambda bridge is consumed. -/
set_option autoImplicit false
namespace Tests.ADR0315ParsedOwnerExpectedDataLambdaInvocations
open Solcore Solcore.Frontend
private def check (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)
private def proof {p : Prop} (_ : p) : IO Unit := pure ()
private def declaration (index : Nat) : Resolved.DeclarationId :=
  ⟨⟨.main,⟨[⟨"ParsedOwnerSavedLambda",by decide⟩],by decide⟩⟩,index⟩
private def savedOwner := declaration 15
private def callerOwner := declaration 25
private def foreignOwner := declaration 915
private def lid (owner : Resolved.DeclarationId) (index : Nat) : Resolved.LocalId :=
  ⟨owner,index⟩
private def sid (index : Nat) := lid savedOwner index
private def cid (index : Nat) := lid callerOwner index
private def fid (index : Nat) := lid foreignOwner index
private def shift (owner : Resolved.DeclarationId) : Resolved.DeclarationId :=
  {owner with declarationIndex:=owner.declarationIndex+5}
private theorem shift_injective : Function.Injective shift := by
  intro a b same
  have modules := congrArg Resolved.DeclarationId.moduleId same
  have indices := congrArg Resolved.DeclarationId.declarationIndex same
  cases a; cases b
  simp only [shift,Resolved.DeclarationId.mk.injEq] at modules indices ⊢
  exact ⟨modules,by omega⟩
private theorem shift_not_surjective : ¬ Function.Surjective shift := by
  intro onto
  obtain ⟨before,same⟩ := onto (declaration 0)
  have impossible := congrArg Resolved.DeclarationId.declarationIndex same
  simp [shift,declaration] at impossible

private def span (file : Syntax.SourceFile) (start stop : Nat) : Syntax.SourceSpan :=
  ⟨file.id,start,stop⟩
private def reference (file : Syntax.SourceFile) (start stop : Nat) (name : String) :
    Syntax.Expr := ⟨span file start stop,.identifier ⟨span file start stop,name⟩⟩
private def expectedLambda (file : Syntax.SourceFile) : Syntax.Expr :=
  ⟨span file 0 17,.lambda (span file 0 3)
    ⟨span file 3 6,[⟨span file 4 5,.inferred ⟨span file 4 5,"p"⟩⟩]⟩ none
    ⟨span file 6 17,[⟨span file 7 16,.returnStmt
      (some (reference file 14 15 "p"))⟩]⟩⟩
private def expectedCall (file : Syntax.SourceFile) : Syntax.Expr :=
  ⟨span file 0 4,.call (reference file 0 1 "f")
    ⟨span file 1 4,[reference file 2 3 "x"]⟩⟩
private def parseExact (filename text : String) (expected : Syntax.SourceFile → Syntax.Expr) :
    IO Syntax.Expr := do
  let file : Syntax.SourceFile := ⟨⟨.main,filename⟩,text⟩
  let .ok lexed := Syntax.Lexer.lex file | throw (IO.userError "lexer")
  match Syntax.Parser.expression (Syntax.Parser.State.initial file lexed) with
  | .ok source next =>
    check (lexed.diagnostics.isEmpty && next.diagnostics.isEmpty && next.atEnd &&
      next.file==file && source.span==Syntax.SourceSpan.fullFile file &&
      source==expected file) "complete parsed AST/spans/EOF/diagnostics"
    return source
  | _ => throw (IO.userError "expression parser")

private def inputs : LocalTypeInputs := ⟨[
  ⟨"payload",sid 7,.unit⟩,⟨"noise",fid 31,.word⟩,⟨"payload",sid 2,.bool⟩],by decide⟩
private def payload : Core.Value :=
  .closure .bool .word (.var 1)
    [.cellRef .word 8,.hostFunction .callerAddress,
      .closure .unit .unit (.var 4) [.hostFunction .storageRead]]
private def environment : Resolved.Environment :=
  [(sid 7,payload),(fid 31,.word (Core.Word.ofNatModulo 99)),(sid 2,.bool false)]
private def store : Core.Store :=
  [.word (Core.Word.ofNatModulo 77),.cellRef .word 3,
    .hostFunction .storageWrite,payload]
private def captures := environment.map fun row => (row.1,RuntimeValue.ofCore row.2)
private def heap := store.map RuntimeValue.ofCore
private def mapId := ownerLocalIdMap shift
private def mappedInputs : LocalTypeInputs :=
  inputs.mapIds mapId (ownerLocalIdMap_injective shift shift_injective)
private def mappedEnvironment : Resolved.Environment := Resolved.LocalScope.mapIds mapId environment
private def callerNames : LocalNameTable :=
  [("f",cid 40),("x",cid 41),("f",fid 40)]
private def callerRows (saved : RuntimeValue) : Resolved.LocalScope RuntimeValue :=
  [(cid 41,RuntimeValue.ofCore payload),(cid 40,saved),
    (cid 40,.sourceClosure (reference ⟨⟨.main,"noise.sol"⟩,"z"⟩ 0 1 "z") foreignOwner [] []),
    (fid 40,saved)]

private def exercise (source call : Syntax.Expr) : IO Unit := do
  match sourceShape : source with
  | ⟨_,.lambda _ ⟨_,[⟨_,.inferred parameter⟩]⟩ none body⟩ =>
    have shape : SourceUnaryLambdaShape source parameter body := by
      rw [sourceShape]; exact .inferred
    match bodyShape : body, callShape : call with
    | ⟨_,[⟨_,.returnStmt (some result@⟨_,.identifier bodyName⟩)⟩]⟩,
        ⟨callSpan,.call ⟨calleeSpan,.identifier calleeName⟩
          ⟨argumentsSpan,[⟨argumentSpan,.identifier argumentName⟩]⟩⟩ =>
      if namesEqual : bodyName.value=parameter.value ∧ calleeName.value="f" ∧
          argumentName.value="x" then
        have gate : ClosedSourceDataBody body := by rw [bodyShape]; exact .expression .reference
        have sameIds : environment.ids=inputs.context.ids := rfl
        let inner := inputs.bindFresh savedOwner parameter.value .unit
        let mappedInner := mappedInputs.bindFresh (shift savedOwner) parameter.value .unit
        let expectedCore : Core.Expr := .lambda .unit .unit (.var 0)
        match oldCheckedRun : elaborateExpectedComputationLambda? elaborateLocalExpression? []
            savedOwner inputs source (.function .unit .unit),
          mappedCheckedRun : elaborateExpectedComputationLambda? elaborateLocalExpression? []
            (shift savedOwner) mappedInputs source (.function .unit .unit) with
        | some oldCore,some mappedCore =>
          if coresEqual : oldCore=expectedCore ∧ mappedCore=expectedCore then
            have checked : elaborateExpectedComputationLambda? elaborateLocalExpression? []
                savedOwner inputs source (.function .unit .unit)=some expectedCore :=
              coresEqual.1 ▸ oldCheckedRun
            check (elaborateComputationReturnTree? elaborateLocalExpression? [] savedOwner inner
                body==some (.var 0,.unit) &&
              elaborateComputationReturnTree? elaborateLocalExpression? [] (shift savedOwner)
                mappedInner body==some (.var 0,.unit) &&
              Resolved.freshLocalId savedOwner inputs.ids==sid 8 &&
              Resolved.freshLocalId (shift savedOwner) mappedInputs.ids==lid (shift savedOwner) 8)
              "actual old/mapped body checkers and owner-only fresh ID"
            let callee : Syntax.Expr := ⟨calleeSpan,.identifier calleeName⟩
            let argument : Syntax.Expr := ⟨argumentSpan,.identifier argumentName⟩
            let saved := RuntimeValue.sourceClosure source savedOwner inputs.names captures
            let mappedSaved := RuntimeValue.sourceClosure source (shift savedOwner)
              (LocalNameTable.mapIds mapId inputs.names)
              (mappedEnvironment.map fun row => (row.1,RuntimeValue.ofCore row.2))
            let oldRows := callerRows saved
            let mappedNames := LocalNameTable.mapIds mapId callerNames
            let mappedRows := mapRuntimeCapturedOwners shift oldRows
            let mappedHeap := heap.map (RuntimeValue.mapOwners shift)
            have mappedHeapEq : mappedHeap=heap := by
              simp only [mappedHeap,heap,mapRuntimeStoreOwners_ofCore]
            have bodyRaw : ClosedSourceBodyEvaluates savedOwner
                ((parameter.value,Resolved.freshLocalId savedOwner inputs.ids)::inputs.names)
                ((Resolved.freshLocalId savedOwner inputs.ids,RuntimeValue.ofCore payload)::captures)
                heap body (RuntimeValue.ofCore payload) heap := by
              rw [bodyShape]; exact .expression (.reference (namesEqual.1 ▸ .head) .head)
            have creationRaw : ClosedSourceExpressionEvaluates savedOwner inputs.names captures
                heap source saved heap := .creation shape
            have mappedCreationRaw : ClosedSourceExpressionEvaluates (shift savedOwner)
                (LocalNameTable.mapIds mapId inputs.names)
                (mappedEnvironment.map fun row => (row.1,RuntimeValue.ofCore row.2)) mappedHeap
                source mappedSaved mappedHeap := .creation shape
            have calleeRaw : ClosedSourceExpressionEvaluates callerOwner callerNames oldRows heap
                callee saved heap := .reference (namesEqual.2.1 ▸ .head) (.tail (by decide) .head)
            have argumentRaw : ClosedSourceExpressionEvaluates callerOwner callerNames oldRows heap
                argument (RuntimeValue.ofCore payload) heap :=
              .reference (namesEqual.2.2 ▸ .tail (by decide) .head) .head
            have callRaw : ClosedSourceExpressionEvaluates callerOwner callerNames oldRows heap call
                (RuntimeValue.ofCore payload) heap := by
              rw [callShape]; exact .call shape calleeRaw argumentRaw bodyRaw
            have mappedCalleeRaw : ClosedSourceExpressionEvaluates (shift callerOwner) mappedNames
                mappedRows mappedHeap callee mappedSaved mappedHeap := by
              simpa only [mappedNames,mappedRows,mappedHeap,saved,mappedSaved,captures,mapId,
                mappedEnvironment,RuntimeValue.mapOwners_sourceClosure,
                mapRuntimeCapturedOwners_ofCore] using calleeRaw.mapOwners shift shift_injective
            have mappedArgumentRaw : ClosedSourceExpressionEvaluates (shift callerOwner)
                mappedNames mappedRows mappedHeap argument (RuntimeValue.ofCore payload)
                mappedHeap := by
              simpa only [mappedNames,mappedRows,mappedHeap,mapId,RuntimeValue.mapOwners_ofCore] using
                argumentRaw.mapOwners shift shift_injective
            have mappedCallRaw : ClosedSourceExpressionEvaluates (shift callerOwner) mappedNames
                mappedRows mappedHeap call (RuntimeValue.ofCore payload) mappedHeap := by
              simpa only [mappedNames,mappedRows,mappedHeap,mapId,RuntimeValue.mapOwners_ofCore] using
                callRaw.mapOwners shift shift_injective
            match oldCreationRun : evaluateClosedSourceExpression? 1 savedOwner inputs.names
                captures heap source with
            | some (oldCreated,oldCreationFinal) =>
              have oldCreationEq :=
                (evaluateClosedSourceExpression?_sound oldCreationRun).deterministic creationRaw
              proof oldCreationEq
              match mappedCreationRun : evaluateClosedSourceExpression? 1 (shift savedOwner)
                  (LocalNameTable.mapIds mapId inputs.names)
                  (mappedEnvironment.map fun row => (row.1,RuntimeValue.ofCore row.2))
                  mappedHeap source with
              | some (mappedCreated,mappedCreationFinal) =>
                have mappedCreationEq :=
                  (evaluateClosedSourceExpression?_sound mappedCreationRun).deterministic
                    mappedCreationRaw
                proof mappedCreationEq
                match oldCalleeRun : evaluateClosedSourceExpression? 1 callerOwner callerNames
                    oldRows heap callee,
                  oldArgumentRun : evaluateClosedSourceExpression? 1 callerOwner callerNames
                    oldRows heap argument,
                  mappedCalleeRun : evaluateClosedSourceExpression? 1 (shift callerOwner)
                    mappedNames mappedRows mappedHeap callee,
                  mappedArgumentRun : evaluateClosedSourceExpression? 1 (shift callerOwner)
                    mappedNames mappedRows mappedHeap argument with
                | some (oldFn,oldCalleeStore),some (oldArg,oldBodyStore),
                    some (mappedFn,mappedCalleeStore),some (mappedArg,mappedBodyStore) =>
                  have oldFnEq :=
                    (evaluateClosedSourceExpression?_sound oldCalleeRun).deterministic calleeRaw
                  have oldArgEq :=
                    (evaluateClosedSourceExpression?_sound oldArgumentRun).deterministic argumentRaw
                  have mappedFnEq :=
                    (evaluateClosedSourceExpression?_sound mappedCalleeRun).deterministic
                      mappedCalleeRaw
                  have mappedArgEq :=
                    (evaluateClosedSourceExpression?_sound mappedArgumentRun).deterministic
                      mappedArgumentRaw
                  proof oldFnEq; proof oldArgEq; proof mappedFnEq; proof mappedArgEq
                  have mappedFnEval := evaluateClosedSourceExpression?_sound mappedCalleeRun
                  have mappedArgEval := evaluateClosedSourceExpression?_sound mappedArgumentRun
                  match oldRun : evaluateClosedSourceExpression? 3 callerOwner callerNames oldRows
                      heap call with
                  | some (oldValue,oldFinal) =>
                    have oldActual := evaluateClosedSourceExpression?_sound oldRun
                    proof (oldActual.deterministic callRaw)
                    match mappedRun : evaluateClosedSourceExpression? 3 (shift callerOwner)
                        mappedNames mappedRows mappedHeap call with
                    | some (mappedValue,mappedFinal) =>
                      have mappedActual := evaluateClosedSourceExpression?_sound mappedRun
                      proof (mappedActual.deterministic mappedCallRaw)
                      let core : Core.Expr := .apply (.var 0) (.var 1)
                      let coreEnvironment : List Core.Value :=
                        [.closure .unit .unit (.var 0) environment.values,payload]
                      match tooSmall : Core.runStateful 5 (.initial core coreEnvironment store) with
                      | .outOfFuel _ =>
                        match coreRun : Core.runStateful 6 (.initial core coreEnvironment store) with
                        | .done coreValue coreFinal =>
                          have coreEval := Core.runStateful_evaluation_sound coreRun
                          have functionEval : Core.Evaluates coreEnvironment store (.var 0)
                              (.closure .unit .unit (.var 0) environment.values) store := .var rfl
                          have argumentEval : Core.Evaluates coreEnvironment store (.var 1)
                              payload store := .var rfl
                          have beta : Core.Evaluates (payload::environment.values) store (.var 0)
                              coreValue coreFinal := by
                            change Core.Evaluates coreEnvironment store (.apply (.var 0) (.var 1))
                              coreValue coreFinal at coreEval
                            cases coreEval with
                            | apply f a b =>
                              obtain ⟨hf,hs⟩ := Core.evaluation_deterministic f functionEval
                              cases hf; cases hs
                              obtain ⟨ha,hs⟩ := Core.evaluation_deterministic a argumentEval
                              cases ha; cases hs; exact b
                          check (coreValue==payload && coreFinal==store)
                            "actual Core endpoint at exact 5/6 transition boundary"
                          have bridge {value final} :=
                            closedSourceExpectedDataLambda_invocation_mapOwners_core_iff
                              shift shift_injective (callerOwner:=callerOwner)
                              (callerNames:=callerNames) (callerCaptured:=oldRows)
                              (callee:=callee) (argument:=argument) (argumentValue:=payload)
                              shape gate checked sameIds
                              (by simpa only [mappedNames,mappedRows,mappedFnEq.1,mappedFnEq.2,
                                  mapId,callee,mappedSaved,saved,oldRows,mappedHeap,
                                  mappedEnvironment]
                                using mappedFnEval)
                              (by simpa only [mappedNames,mappedRows,mappedArgEq.1,mappedArgEq.2,
                                  mappedHeapEq,mapId,argument,saved,oldRows,mappedHeap,heap,
                                  mapRuntimeStoreOwners_ofCore]
                                using mappedArgEval)
                              (initialStore:=heap) (calleeStore:=heap) (bodyStore:=store)
                              (callSpan:=callSpan) (argumentsSpan:=argumentsSpan)
                              (actualValue:=value) (actualFinal:=final)
                          have mappedForBridge : ClosedSourceExpressionEvaluates
                              (shift callerOwner) mappedNames mappedRows mappedHeap call
                              mappedValue mappedFinal := mappedActual
                          have forward := (bridge (value:=mappedValue) (final:=mappedFinal)).2.2.mp
                            (by simpa only [mappedNames,mappedRows,mappedHeap,callShape,mapId,
                                oldRows,saved]
                              using mappedForBridge)
                          have endpoint : mappedValue=RuntimeValue.ofCore coreValue ∧
                              mappedFinal=coreFinal.map RuntimeValue.ofCore := by
                            obtain ⟨iv,ist,valueEq,storeEq,imageCore⟩ := forward
                            obtain ⟨valueCoreEq,storeCoreEq⟩ :=
                              Core.evaluation_deterministic imageCore beta
                            exact ⟨valueEq.trans (congrArg RuntimeValue.ofCore valueCoreEq),
                              storeEq.trans (congrArg (List.map RuntimeValue.ofCore) storeCoreEq)⟩
                          proof endpoint
                          proof ((bridge (value:=mappedValue) (final:=mappedFinal)).2.2.mpr
                            ⟨coreValue,coreFinal,endpoint.1,endpoint.2,beta⟩)
                          proof ((bridge (value:=RuntimeValue.ofCore coreValue)
                            (final:=coreFinal.map RuntimeValue.ofCore)).2.2.mpr
                              ⟨coreValue,coreFinal,rfl,rfl,beta⟩)
                          check (mappedValue.toCore?==some coreValue &&
                            mappedFinal.mapM RuntimeValue.toCore?==some coreFinal)
                            "project only after both mapped bridge directions"
                          proof shift_not_surjective
                        | _ => throw (IO.userError "Core six-transition completion")
                      | _ => throw (IO.userError "Core five-transition exhaustion")
                    | none => throw (IO.userError "mapped complete call depth three")
                  | none => throw (IO.userError "old complete call depth three")
                | _,_,_,_ => throw (IO.userError "actual old/mapped caller prefixes")
              | none => throw (IO.userError "actual mapped source-closure creation")
            | none => throw (IO.userError "actual old source-closure creation")
          else throw (IO.userError "old/mapped checked Core mismatch")
        | _,_ => throw (IO.userError "actual old/mapped expected-lambda checkers")
      else throw (IO.userError "parsed identifier spellings")
    | _,_ => throw (IO.userError "parsed body and saved call shapes")
  | _ => throw (IO.userError "parsed inferred unary source")

end Tests.ADR0315ParsedOwnerExpectedDataLambdaInvocations

open Tests.ADR0315ParsedOwnerExpectedDataLambdaInvocations in
def Tests.adr0315ParsedOwnerExpectedDataLambdaInvocationTests : IO Unit := do
  let source ← parseExact "adr0315-saved-lambda.sol" "lam(p){return p;}" expectedLambda
  let call ← parseExact "adr0315-saved-call.sol" "f(x)" expectedCall
  exercise source call
  IO.println "ADR0315 parsed owner-mapped saved data-lambda/Core image GREEN"
end

section
-- leanmerge: from Solcore.Test.FrontendParsedOwnerReflection
/- Actual mapped endpoints precede reflection; independent originals and adjacent runs identify full preimages and a shared cutoff. -/
set_option autoImplicit false
namespace Tests.ParsedOwnerReflection
open Solcore Solcore.Frontend
private abbrev V := RuntimeValue
private abbrev E := ClosedSourceExpressionEvaluates
private abbrev B := ClosedSourceBodyEvaluates
private def check (b : Bool) (s : String) : IO Unit := unless b do throw (IO.userError s)
private def proof {p : Prop} (_ : p) : IO Unit := pure ()
private def owner (n : Nat) : Resolved.DeclarationId := ⟨⟨.main,⟨[⟨"ParsedOwner",by decide⟩],by decide⟩⟩,n⟩
private def so := owner 311
private def co := owner 711
private def fo := owner 911
private def lid (o : Resolved.DeclarationId) (i : Nat) : Resolved.LocalId := ⟨o,i⟩
private def shift (o : Resolved.DeclarationId) : Resolved.DeclarationId := {o with declarationIndex:=o.declarationIndex+5}
private theorem shift_injective : Function.Injective shift := by
  intro a b same
  have hm := congrArg Resolved.DeclarationId.moduleId same
  have hi := congrArg Resolved.DeclarationId.declarationIndex same
  cases a; cases b
  simp only [shift,Resolved.DeclarationId.mk.injEq] at hm hi ⊢
  exact ⟨hm,by omega⟩
private theorem shift_not_surjective : ¬ Function.Surjective shift := by
  intro onto
  obtain ⟨a,same⟩ := onto (owner 0)
  have impossible := congrArg Resolved.DeclarationId.declarationIndex same
  simp [shift,owner] at impossible
private def sn : LocalNameTable := [("q",lid so 8),("foreign",lid fo 99),("q",lid so 99),("q",lid fo 8)]
private def se (v : V) : Resolved.LocalScope V :=
  [(lid fo 8,.unit),(lid so 8,v),(lid so 8,.bool false),(lid so 100,.cellRef .word 800),
   (lid so 101,.hostFunction .storageWrite),(lid so 102,.bool false),(lid fo 100,v)]
private def cn : LocalNameTable := [("f",lid co 1),("x",lid co 2),("x",lid fo 2),("f",lid co 99),("x",lid co 99)]
private def ce (saved av : V) : Resolved.LocalScope V :=
  [(lid fo 1,.unit),(lid co 1,saved),(lid co 1,.bool false),(lid fo 2,.unit),(lid co 2,av),(lid co 2,.unit)]
private def core : V := .ofCore (.closure .unit .word (.var 99) [.cellRef .word 701,.hostFunction .storageWrite])
private def mixed (source : Syntax.Expr) (caller saved foreign : Resolved.DeclarationId) : V :=
  .pair (.sourceClosure source saved [("q",lid saved 8),("q",lid foreign 8)]
    [(lid saved 8,.coreClosure .unit .word (.var 17)
      [.sourceClosure source foreign [("q",lid caller 8)] [(lid caller 8,.cellRef .word 702),(lid caller 8,.unit)],core]),
     (lid saved 8,.bool false)]) (.pair core (.cellRef .word 703))
private theorem mixed_fields (source : Syntax.Expr) :
    (mixed source co so fo).mapOwners shift = mixed source (shift co) (shift so) (shift fo) := by
  simp only [mixed,core,RuntimeValue.ofCore,List.attach_map_val,RuntimeValue.mapOwners_sourceClosure,
    RuntimeValue.mapOwners_coreClosure,RuntimeValue.mapOwners,mapRuntimeCapturedOwners,
    LocalNameTable.mapIds,ownerLocalIdMap,lid,List.map_cons,List.map_nil]
private def span (f : Syntax.SourceFile) (a b : Nat) : Syntax.SourceSpan := ⟨f.id,a,b⟩
private def ref (f : Syntax.SourceFile) (a b : Nat) (n : String) : Syntax.Expr := ⟨span f a b,.identifier ⟨span f a b,n⟩⟩
private def ty (f : Syntax.SourceFile) (a b : Nat) : Syntax.TypeExpr :=
  ⟨span f a b,.named ⟨span f a b,⟨⟨⟨span f a b,"Unit"⟩,[]⟩⟩⟩ none⟩
private def expectedLambda (typed : Bool) (f : Syntax.SourceFile) : Syntax.Expr :=
  let d := if typed then 5 else 0
  ⟨span f 0 (38+d),.lambda (span f 0 3)
    ⟨span f 3 (6+d),[if typed then ⟨span f 4 10,.typed none ⟨span f 4 5,"q"⟩ (ty f 6 10)⟩
      else ⟨span f 4 5,.inferred ⟨span f 4 5,"q"⟩⟩]⟩ none
    ⟨span f (6+d) (38+d),[⟨span f (7+d) (20+d),.letDecl ⟨span f (11+d) (12+d),"q"⟩
      (some (ty f (13+d) (17+d))) (some (ref f (18+d) (19+d) "q"))⟩,
      ⟨span f (20+d) (28+d),.letDecl ⟨span f (24+d) (25+d),"q"⟩ none (some (ref f (26+d) (27+d) "q"))⟩,
      ⟨span f (28+d) (37+d),.returnStmt (some (ref f (35+d) (36+d) "q"))⟩]⟩⟩
private def expectedCall (f : Syntax.SourceFile) : Syntax.Expr := ⟨span f 0 4,.call (ref f 0 1 "f") ⟨span f 1 4,[ref f 2 3 "x"]⟩⟩
private def typeSpans : Syntax.TypeExpr → List Syntax.SourceSpan
  | ⟨s,.named ⟨q,⟨⟨n,[]⟩⟩⟩ none⟩ => [s,q,n.span]
  | _ => []
private def parameterSpans : Syntax.LambdaParameter → List Syntax.SourceSpan
  | ⟨s,.inferred n⟩ => [s,n.span]
  | ⟨s,.typed none n t⟩ => [s,n.span]++typeSpans t
  | _ => []
private def spans : Syntax.Expr → List Syntax.SourceSpan
  | ⟨s,.identifier n⟩ => [s,n.span]
  | ⟨s,.call f ⟨a,[x]⟩⟩ => [s]++spans f++[a]++spans x
  | ⟨s,.lambda k ⟨ps,[p]⟩ none ⟨b,[⟨l,.letDecl n (some t) (some i)⟩,
      ⟨l2,.letDecl n2 none (some i2)⟩,⟨r,.returnStmt (some e)⟩]⟩⟩ =>
    [s,k,ps]++parameterSpans p++[b,l,n.span]++typeSpans t++spans i++[l2,n2.span]++spans i2++[r]++spans e
  | _ => []
private def ranges (typed : Bool) : List (Nat × Nat) :=
  let d := if typed then 5 else 0
  [(0,38+d),(0,3),(3,6+d)]++(if typed then [(4,10),(4,5),(6,10),(6,10),(6,10)] else [(4,5),(4,5)])++
    ([(6,38),(7,20),(11,12),(13,17),(13,17),(13,17),(18,19),(18,19),(20,28),(24,25),
      (26,27),(26,27),(28,37),(35,36),(35,36)].map (fun (a,b) => (a+d,b+d)))
private def parsed (text : String) (ast : Syntax.SourceFile → Syntax.Expr) (expectedRanges : List (Nat × Nat)) : IO Syntax.Expr := do
  let file : Syntax.SourceFile := ⟨⟨.main,"parsed-owner-replay.sol"⟩,text⟩
  let .ok lexed := Syntax.Lexer.lex file | throw (IO.userError "owner lexer")
  match Syntax.Parser.expression (Syntax.Parser.State.initial file lexed) with
  | .ok actual next =>
    check (lexed.diagnostics.isEmpty && next.diagnostics.isEmpty && next.atEnd && next.file==file &&
      actual.span==Syntax.SourceSpan.fullFile file && actual==ast file) "whole handwritten AST / EOF / diagnostics"
    check ((spans actual).all (fun s => s.isValidFor file) &&
      (spans actual).map (fun s => (s.startByte,s.endByte))==expectedRanges) "all actual handwritten spans"
    return actual
  | _ => throw (IO.userError "owner parser")
private theorem pinCutoff {before after : Nat → Option (V × List V)} {value final mapped mappedStore depth}
    (low : before (depth-1)=none) (high : before depth=some (value,final))
    (cutoff : ∃ required : Nat, 0<required ∧ ∀ budget,
      (before budget=if required≤budget then some (value,final) else none) ∧
      (after budget=if required≤budget then some (mapped,mappedStore) else none)) :
    0<depth ∧ ∀ budget, (before budget=if depth≤budget then some (value,final) else none) ∧
      (after budget=if depth≤budget then some (mapped,mappedStore) else none) := by
  obtain ⟨required,positive,cutoff⟩ := cutoff
  have upper : required≤depth := by
    have impossible := (cutoff depth).1
    split at impossible
    · assumption
    · simp only [high,Option.some_ne_none] at impossible
  have lower : depth≤required := by
    have impossible := (cutoff (depth-1)).1
    split at impossible
    · simp only [low,reduceCtorEq] at impossible
    · omega
  have same : required=depth := Nat.le_antisymm upper lower
  simpa only [same] using And.intro positive cutoff
private def expression {o n e st source v final} (original : E o n e st source v final) (depth : Nat) : IO Unit := do
  let before := fun budget => evaluateClosedSourceExpression? budget o n e st source
  let after := fun budget => evaluateClosedSourceExpression? budget (shift o)
    (LocalNameTable.mapIds (ownerLocalIdMap shift) n) (mapRuntimeCapturedOwners shift e)
    (st.map (RuntimeValue.mapOwners shift)) source
  for budget in [0,depth-1,depth,depth+3] do
    match observed : after budget with
    | none =>
      match ran : before budget with
      | none =>
        check (budget<depth) "independent mapped/original expression insufficient budget"
        proof ((evaluateClosedSourceExpression?_mapOwners_none_iff shift shift_injective budget o n e st source).mp observed)
      | some _ => throw (IO.userError "independent expression Option mismatch")
    | some (actual,out) =>
      have mappedOriginal := evaluateClosedSourceExpression?_sound observed
      have recovered := (ClosedSourceExpressionEvaluates.mapOwners_iff_exists shift shift_injective).mp mappedOriginal
      have complete : actual=v.mapOwners shift ∧ out=final.map (RuntimeValue.mapOwners shift) := by
        obtain ⟨prior,priorStore,priorOriginal,values,stores⟩ := recovered
        have same := priorOriginal.deterministic original
        simpa only [same.1,same.2] using And.intro values stores
      have finite := (evaluateClosedSourceExpression?_mapOwners_some_iff_exists shift shift_injective).mp observed
      have finiteComplete : before budget=some (v,final) := by
        obtain ⟨prior,priorStore,priorRun,_,_⟩ := finite
        have same := (evaluateClosedSourceExpression?_sound priorRun).deterministic original
        simpa only [same.1,same.2] using priorRun
      proof mappedOriginal; proof complete; proof finiteComplete
      match ran : before budget with
      | some (prior,priorStore) =>
        proof (show prior=v ∧ priorStore=final from (evaluateClosedSourceExpression?_sound ran).deterministic original)
        check (depth≤budget) "independent expression full recovered endpoint"
      | none => throw (IO.userError "actual old expression must match recovered run")
  match low : before (depth-1), high : before depth with
  | none,some (actual,out) =>
    have same := (evaluateClosedSourceExpression?_sound high).deterministic original
    have exactHigh : before depth=some (v,final) := by simpa only [same.1,same.2] using high
    proof (pinCutoff low exactHigh (original.mapOwners_exact_depth_threshold shift shift_injective))
  | _,_ => throw (IO.userError "independent expression adjacent cutoff observations")
private def body {o n e st source v final} (original : B o n e st source v final) (depth : Nat) : IO Unit := do
  let before := fun budget => evaluateClosedSourceBody? budget o n e st source
  let after := fun budget => evaluateClosedSourceBody? budget (shift o)
    (LocalNameTable.mapIds (ownerLocalIdMap shift) n) (mapRuntimeCapturedOwners shift e)
    (st.map (RuntimeValue.mapOwners shift)) source
  for budget in [0,depth-1,depth,depth+3] do
    match observed : after budget with
    | none =>
      match ran : before budget with
      | none =>
        check (budget<depth) "independent mapped/original body insufficient budget"
        proof ((evaluateClosedSourceBody?_mapOwners_none_iff shift shift_injective budget o n e st source).mp observed)
      | some _ => throw (IO.userError "independent body Option mismatch")
    | some (actual,out) =>
      have mappedOriginal := evaluateClosedSourceBody?_sound observed
      have recovered := (ClosedSourceBodyEvaluates.mapOwners_iff_exists shift shift_injective).mp mappedOriginal
      have complete : actual=v.mapOwners shift ∧ out=final.map (RuntimeValue.mapOwners shift) := by
        obtain ⟨prior,priorStore,priorOriginal,values,stores⟩ := recovered
        have same := priorOriginal.deterministic original
        simpa only [same.1,same.2] using And.intro values stores
      have finite := (evaluateClosedSourceBody?_mapOwners_some_iff_exists shift shift_injective).mp observed
      have finiteComplete : before budget=some (v,final) := by
        obtain ⟨prior,priorStore,priorRun,_,_⟩ := finite
        have same := (evaluateClosedSourceBody?_sound priorRun).deterministic original
        simpa only [same.1,same.2] using priorRun
      proof mappedOriginal; proof complete; proof finiteComplete
      match ran : before budget with
      | some (prior,priorStore) =>
        proof (show prior=v ∧ priorStore=final from (evaluateClosedSourceBody?_sound ran).deterministic original)
        check (depth≤budget) "independent body full recovered endpoint"
      | none => throw (IO.userError "actual old body must match recovered run")
  match low : before (depth-1), high : before depth with
  | none,some (actual,out) =>
    have same := (evaluateClosedSourceBody?_sound high).deterministic original
    have exactHigh : before depth=some (v,final) := by simpa only [same.1,same.2] using high
    proof (pinCutoff low exactHigh (original.mapOwners_exact_depth_threshold shift shift_injective))
  | _,_ => throw (IO.userError "independent body adjacent cutoff observations")
private def application {source whole : Syntax.Expr} {parameter : Syntax.Identifier} {block : Syntax.Block}
    (shape : SourceUnaryLambdaShape source parameter block) (av : V) (st : List V) : IO Unit := do
  let creationStore := [core,.unit]
  have creation : E so sn (se av) creationStore source (.sourceClosure source so sn (se av)) creationStore := .creation shape
  proof creation
  match created : evaluateClosedSourceExpression? 1 so sn (se av) creationStore source with
  | some (.sourceClosure actualSource actualOwner actualNames actualCaptured,creationFinal) =>
    have same := (evaluateClosedSourceExpression?_sound created).deterministic creation
    have fields := RuntimeValue.sourceClosure.inj same.1
    have actualShape : SourceUnaryLambdaShape actualSource parameter block := fields.1.symm ▸ shape
    proof fields; proof same.2
    check (actualOwner != co && actualOwner != fo && creationFinal.length != st.length) "separate saved owner / creation and invocation stores"
    match hw : whole with
    | ⟨cs,.call ⟨fs,.identifier f⟩ ⟨als,[⟨xs,.identifier x⟩]⟩⟩ =>
      if names : f.value="f" ∧ x.value="x" ∧ parameter.value="q" then
        let n := cn; let e := ce (.sourceClosure actualSource actualOwner actualNames actualCaptured) av
        have picked : E co n e st ⟨fs,.identifier f⟩ (.sourceClosure actualSource actualOwner actualNames actualCaptured) st :=
          .reference (names.1 ▸ LocalNameTable.Lookup.head) (.tail (by decide) .head)
        have argumentOriginal : E co n e st ⟨xs,.identifier x⟩ av st :=
          .reference (names.2.1 ▸ LocalNameTable.Lookup.tail (by decide) .head)
            (.tail (by decide) (.tail (by decide) (.tail (by decide) (.tail (by decide) .head))))
        let fresh := Resolved.freshLocalId actualOwner (actualNames.map Prod.snd)
        let bn := (parameter.value,fresh)::actualNames; let be := (fresh,av)::actualCaptured
        have freshExact : fresh=lid so 100 ∧
            Resolved.freshLocalId actualOwner (bn.map Prod.snd)=lid so 101 := by
          rcases fields with ⟨_,rfl,rfl,rfl⟩
          exact ⟨by decide,by change Resolved.freshLocalId so (lid so 100 :: sn.map Prod.snd)=lid so 101; decide⟩
        proof freshExact
        match hb : block with
        | ⟨bs,[⟨_,.letDecl bound (some _) (some ⟨is,.identifier initializer⟩)⟩,
            ⟨_,.letDecl bound2 none (some ⟨is2,.identifier initializer2⟩)⟩,⟨rs,.returnStmt (some ⟨ys,.identifier key⟩)⟩]⟩ =>
          if equal : initializer.value=parameter.value ∧ initializer2.value=bound.value ∧ key.value=bound2.value then
            have init : E actualOwner bn be st ⟨is,.identifier initializer⟩ av st := .reference (equal.1 ▸ LocalNameTable.Lookup.head) .head
            let fresh2 := Resolved.freshLocalId actualOwner (bn.map Prod.snd)
            let bn2 := (bound.value,fresh2)::bn; let be2 := (fresh2,av)::be
            have init2 : E actualOwner bn2 be2 st ⟨is2,.identifier initializer2⟩ av st :=
              .reference (equal.2.1 ▸ LocalNameTable.Lookup.head) .head
            have fresh3 : Resolved.freshLocalId actualOwner (bn2.map Prod.snd)=lid so 102 := by
              rcases fields with ⟨_,rfl,rfl,rfl⟩
              change Resolved.freshLocalId so (lid so 101 :: lid so 100 :: sn.map Prod.snd)=lid so 102
              decide
            proof fresh3
            have returned : B actualOwner ((bound2.value,Resolved.freshLocalId actualOwner (bn2.map Prod.snd))::bn2)
                ((Resolved.freshLocalId actualOwner (bn2.map Prod.snd),av)::be2) st
                ⟨bs,[⟨rs,.returnStmt (some ⟨ys,.identifier key⟩)⟩]⟩ av st :=
              .expression (.reference (equal.2.2 ▸ LocalNameTable.Lookup.head) .head)
            have originalBody : B actualOwner bn be st block av st := by rw [hb]; exact .binding init (.inferred init2 returned)
            have originalCall : E co n e st whole av st := by rw [hw]; exact .call actualShape picked argumentOriginal originalBody
            proof picked; proof argumentOriginal; proof init; proof init2; proof returned; proof originalBody; proof originalCall
            expression originalCall 5; body originalBody 4
            match cr : evaluateClosedSourceExpression? 1 co n e st ⟨fs,.identifier f⟩ with
            | some (calleeValue,calleeStore) =>
              have actualCallee := evaluateClosedSourceExpression?_sound cr
              have calleeEndpoint := actualCallee.deterministic picked
              proof calleeEndpoint
              match ar : evaluateClosedSourceExpression? 1 co n e calleeStore ⟨xs,.identifier x⟩ with
              | some (argumentValue,argumentStore) =>
                have actualArgument := evaluateClosedSourceExpression?_sound ar
                have alignedArgument : E co n e st ⟨xs,.identifier x⟩ argumentValue argumentStore := calleeEndpoint.2 ▸ actualArgument
                have argumentEndpoint := alignedArgument.deterministic argumentOriginal
                proof argumentEndpoint
                match ran : evaluateClosedSourceBody? 4 actualOwner bn ((fresh,argumentValue)::actualCaptured) argumentStore block with
                | some (actual,out) =>
                  have actualBody := evaluateClosedSourceBody?_sound ran
                  have alignedBody : B actualOwner bn be st block actual out := by
                    simpa only [argumentEndpoint.1,argumentEndpoint.2] using actualBody
                  have endpoint := alignedBody.deterministic originalBody
                  proof endpoint
                  have actualCall := ClosedSourceExpressionEvaluates.call (span:=cs) (argumentsSpan:=als) actualShape
                    (calleeEndpoint.1 ▸ actualCallee) actualArgument actualBody
                  proof actualCall
                | none => throw (IO.userError "actual typed/inferred saved body")
              | none => throw (IO.userError "actual argument at actual callee store")
            | none => throw (IO.userError "actual caller saved callee")
            expression creation 1; expression picked 1; expression argumentOriginal 1
          else throw (IO.userError "actual fresh shadowing spellings")
        | _ => throw (IO.userError "actual typed/inferred saved body shape")
      else throw (IO.userError "actual caller and parameter spellings")
    | _ => throw (IO.userError "actual f(x) shape")
  | _ => throw (IO.userError "actual returned creation closure")
private def savedCall (source whole : Syntax.Expr) (av : V) (st : List V) : IO Unit := do
  match hs : source with
  | ⟨_,.lambda _ ⟨_,[⟨_,.inferred p⟩]⟩ _ b⟩ =>
    have shape : SourceUnaryLambdaShape source p b := by rw [hs]; exact .inferred
    application (whole:=whole) shape av st
  | ⟨_,.lambda _ ⟨_,[⟨_,.typed none p _⟩]⟩ _ b⟩ =>
    have shape : SourceUnaryLambdaShape source p b := by rw [hs]; exact .typed
    application (whole:=whole) shape av st
  | _ => throw (IO.userError "actual unmarked unary lambda")
end Tests.ParsedOwnerReflection
open Solcore Solcore.Frontend Tests.ParsedOwnerReflection in
def Tests.frontendParsedOwnerReflectionTests : IO Unit := do
  let inferred ← parsed "lam(q){let q:Unit=q;let q=q;return q;}" (expectedLambda false) (ranges false)
  let typed ← parsed "lam(q:Unit){let q:Unit=q;let q=q;return q;}" (expectedLambda true) (ranges true)
  let call ← parsed "f(x)" expectedCall [(0,4),(0,1),(0,1),(1,4),(2,3),(2,3)]
  let mut count := 0
  for source in [inferred,typed] do
    let nested := mixed source co so fo
    have exactValue := mixed_fields source
    have exactStore : [nested,RuntimeValue.cellRef .word 900,core].map (RuntimeValue.mapOwners shift) =
        [mixed source (shift co) (shift so) (shift fo),.cellRef .word 900,core] := by
      simp only [List.map_cons,List.map_nil,nested,exactValue,core,RuntimeValue.ofCore,List.attach_map_val,
        RuntimeValue.mapOwners_coreClosure,RuntimeValue.mapOwners,List.map_cons,List.map_nil]
    proof exactValue; proof exactStore
    for av in [nested,RuntimeValue.pair (.cellRef .word 901) nested] do
      for st in [[nested,.cellRef .word 900,core],[core,nested,.cellRef .word 999,.hostFunction .storageRead]] do
        savedCall source call av st
        count := count+1
  check (count==8) "two actual lambda annotations / two nested arguments / two nonempty stores"
end
