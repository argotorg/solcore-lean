import Solcore.Frontend.ClosedSource
import Solcore.Frontend.LocalExpressionEvaluation

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
