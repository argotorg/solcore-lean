import Solcore.Frontend.CheckedDataExpressionOwnerProperties
import Solcore.Frontend.ClosedSource
import Solcore.Core.Correspondence
import Solcore.Syntax.Parser.Term

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
