import Solcore.Frontend.ClosedSourceOwnerCoreBodyProperties
import Solcore.Core.DirectWordComparisons

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

set_option pp.universes true in #check @typed_inferred_ordered_match_complete_boundary
set_option pp.universes true in #check @raw_success_does_not_recover_missing_boundary_premises
#print axioms typed_inferred_ordered_match_complete_boundary
#print axioms raw_success_does_not_recover_missing_boundary_premises

end Tests.ADR0314OwnerCoreBodyConsumerIndependent
