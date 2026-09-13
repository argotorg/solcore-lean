import Solcore.Frontend.ExpectedDataLambdaApplicationProperties
import Solcore.Frontend.LocalExpressionTypingProperties
import Solcore.Frontend.LocalTypeInputsProperties
import Solcore.Resolved.LocalScopeProperties

set_option autoImplicit false
namespace Tests.ExpectedWordUnaryDataImages
open Solcore Solcore.Frontend

private def types : TypeNameTable := [(["Word"], .word)]
private def annotation (s : Syntax.SourceSpan) : Syntax.TypeExpr :=
  ⟨s, .named ⟨s, ⟨⟨⟨s, "Word"⟩, []⟩⟩⟩ none⟩
private def ref (s : Syntax.SourceSpan) (name : String) : Syntax.Expr :=
  ⟨s, .identifier ⟨s, name⟩⟩
private def body (spans : Nat → Syntax.SourceSpan) : Syntax.Block :=
  ⟨spans 5, [
    ⟨spans 6, .letDecl ⟨spans 7, "p"⟩ (some (annotation (spans 8)))
      (some ⟨spans 9, .unary ⟨spans 10, .bitNot⟩ (ref (spans 11) "p")⟩)⟩,
    ⟨spans 12, .returnStmt (some ⟨spans 13, .tuple ⟨spans 14,
      [ref (spans 15) "p", ref (spans 16) "q"]⟩⟩)⟩]⟩
private def source (spans : Nat → Syntax.SourceSpan) : Syntax.Expr :=
  ⟨spans 0, .lambda (spans 1) ⟨spans 2, [⟨spans 3, .inferred ⟨spans 4, "p"⟩⟩]⟩
    none (body spans)⟩
private def argument (spans : Nat → Syntax.SourceSpan) (name : Syntax.Identifier) : Syntax.Expr :=
  ⟨spans 20, .unary ⟨spans 21, .bitNot⟩ ⟨spans 22, .identifier name⟩⟩
private def call (spans : Nat → Syntax.SourceSpan) (callee arg : Syntax.Expr) : Syntax.Expr :=
  ⟨spans 23, .call callee ⟨spans 24, [arg]⟩⟩
private def parameterId (owner : Resolved.DeclarationId) (inputs : LocalTypeInputs) : Resolved.LocalId :=
  Resolved.freshLocalId owner inputs.ids
private def entry (owner : Resolved.DeclarationId) (inputs : LocalTypeInputs) : LocalTypeInputs :=
  inputs.bindFresh owner "p" .word
private def entryEnvironment (owner : Resolved.DeclarationId) (inputs : LocalTypeInputs)
    (environment : Resolved.Environment) (input : Core.Word) : Resolved.Environment :=
  (parameterId owner inputs, .word input) :: environment
private def embedded (environment : Resolved.Environment) : Resolved.LocalScope RuntimeValue :=
  environment.map (fun row => (row.1, RuntimeValue.ofCore row.2))
private def heap (store : Core.Store) : List RuntimeValue := store.map RuntimeValue.ofCore
private def bodyCore (payloadIndex : Nat) : Core.Expr :=
  .letE (.unary .wordNot (.var 0)) (.pair (.var 0) (.var (payloadIndex + 2)))
private def result (input : Core.Word) (payload : Core.Value) : Core.Value :=
  .pair (.word input.bitNot) payload

private structure Frame where
  spans : Nat → Syntax.SourceSpan
  owner : Resolved.DeclarationId
  inputs : LocalTypeInputs
  environment : Resolved.Environment
  payload : Core.Value
  payloadId : Resolved.LocalId
  payloadIndex : Nat
  aligned : environment.ids = inputs.context.ids
  named : LocalNameTable.Lookup inputs.names "q" payloadId
  typed : Resolved.LocalScope.Lookup inputs.context payloadId .unit
  found : Resolved.LocalScope.Lookup environment payloadId payload
  indexed : Resolved.LocalScope.IndexOf environment.ids payloadId payloadIndex
private def pid (f : Frame) := parameterId f.owner f.inputs
private def lid (f : Frame) := Resolved.freshLocalId f.owner (pid f :: f.inputs.ids)
private theorem saved_ids_nodup (f : Frame) : f.environment.ids.Nodup := by
  rw [f.aligned, LocalTypeInputs.context_ids]; exact f.inputs.ids_nodup
private theorem q_member (f : Frame) : f.payloadId ∈ f.inputs.ids := by
  rw [← LocalTypeInputs.context_ids]
  exact List.mem_map.mpr ⟨(f.payloadId, .unit), f.typed.mem, rfl⟩
private theorem fresh_ne {owner : Resolved.DeclarationId} {ids : List Resolved.LocalId}
    {id : Resolved.LocalId} (member : id ∈ ids) : Resolved.freshLocalId owner ids ≠ id := by
  intro same; exact Resolved.freshLocalId_not_mem owner ids (same.symm ▸ member)
private theorem two_rows (f : Frame) {α : Type} {e : Resolved.LocalScope α} {q : α}
    (found : Resolved.LocalScope.Lookup e f.payloadId q) (p l : α) :
    Resolved.LocalScope.Lookup ((lid f, l) :: (pid f, p) :: e) f.payloadId q :=
  .tail (fresh_ne (List.mem_cons_of_mem _ (q_member f))) (.tail (fresh_ne (q_member f)) found)
private theorem mapped_lookup {e : Resolved.Environment} {id : Resolved.LocalId} {v : Core.Value}
    (found : Resolved.LocalScope.Lookup e id v) :
    Resolved.LocalScope.Lookup (embedded e) id (RuntimeValue.ofCore v) := by
  induction found with
  | head => exact .head
  | tail different _ ih => exact .tail different ih
private theorem gate (spans : Nat → Syntax.SourceSpan) : ClosedSourceDataBody (body spans) :=
  .binding (.bitNot .reference) (.expression (.pair .reference .reference))
private theorem checked (f : Frame) :
    elaborateComputationReturnTree? elaborateLocalExpression? types f.owner (entry f.owner f.inputs) (body f.spans) =
      some (bodyCore f.payloadIndex, .product .word .unit) ∧
    elaborateExpectedComputationLambda? elaborateLocalExpression? types f.owner f.inputs
      (source f.spans) (.function .word (.product .word .unit)) =
      some (.lambda .word (.product .word .unit) (bodyCore f.payloadIndex)) := by
  have index : Resolved.LocalScope.IndexOf f.inputs.ids f.payloadId f.payloadIndex := by
    have indexed := f.indexed; rw [f.aligned, LocalTypeInputs.context_ids] at indexed; exact indexed
  have index2 : Resolved.LocalScope.IndexOf (lid f :: pid f :: f.inputs.ids) f.payloadId (f.payloadIndex + 2) :=
    .tail (fresh_ne (List.mem_cons_of_mem _ (q_member f))) (.tail (fresh_ne (q_member f)) index)
  have compiled : ComputationReturnTreeElaborates
      (fun n c e k t => elaborateLocalExpression? n c e = some (k, t))
      types f.owner (entry f.owner f.inputs) (body f.spans) (bodyCore f.payloadIndex) (.product .word .unit) := by
    refine ComputationReturnTreeElaborates.binding (by exact .named .head) ?_ ?_
    · exact elaborateLocalExpression?_complete (.bitNot (.identifier .head)) (.unary (.var .head)) (.unary (.var .head))
    · apply ComputationReturnTreeElaborates.expression
      refine elaborateLocalExpression?_complete (resolved := .pair (.var (lid f)) (.var f.payloadId)) ?_ ?_ ?_
      · exact .pair (.identifier .head) (.identifier (.tail (by change ("p" : String) ≠ "q"; decide) (.tail (by change ("p" : String) ≠ "q"; decide) f.named)))
      · exact .pair (.var .head) (.var (by simpa only [entry, LocalTypeInputs.context_ids,
        LocalTypeInputs.bindFresh_ids, pid, lid, parameterId] using index2))
      · exact .pair (.var .head) (.var (by simpa only [entry, LocalTypeInputs.bindFresh_context, pid,
        lid, parameterId, LocalTypeInputs.bindFresh_ids] using two_rows f f.typed Core.Ty.word Core.Ty.word))
  exact ⟨(elaborateComputationReturnTree?_iff (fun {_ _ _ _ _} => Iff.rfl)).mpr compiled,
    (elaborateExpectedComputationLambda?_iff (fun {_ _ _ _ _} => Iff.rfl)).mpr
      (.lambda (.lambda .inferred .omitted) .word (.product .word .unit) compiled)⟩
private theorem original_paths (f : Frame) (s : Core.Store) (w : Core.Word) :
    ClosedSourceBodyEvaluates f.owner (entry f.owner f.inputs).names
      (embedded (entryEnvironment f.owner f.inputs f.environment w)) (heap s) (body f.spans)
      (RuntimeValue.ofCore (result w f.payload)) (heap s) ∧
    ComputationReturnTreeEvaluates LocalExpressionEvaluates f.owner (entry f.owner f.inputs).names
      (entryEnvironment f.owner f.inputs f.environment w) s (body f.spans) (result w f.payload) s ∧
    Core.Evaluates (.word w :: f.environment.values) s (bodyCore f.payloadIndex) (result w f.payload) s := by
  have qrows := two_rows f f.found (Core.Value.word w) (.word w.bitNot)
  have qnames : LocalNameTable.Lookup (("p", lid f) :: ("p", pid f) :: f.inputs.names) "q" f.payloadId :=
    .tail (by decide) (.tail (by decide) f.named)
  refine ⟨?_, ?_, ?_⟩
  · simp only [body, entry, LocalTypeInputs.bindFresh_names, entryEnvironment,
      embedded, heap, List.map_cons, RuntimeValue.ofCore, result, ref, parameterId]
    exact .binding (.bitNot (.reference .head .head)) (.expression (.pair (.reference .head .head)
      (.reference (by simpa only [List.map_cons, Prod.snd, LocalTypeInputs.names_ids, pid, lid, parameterId] using qnames)
        (by simpa only [embedded, List.map_cons, Prod.snd, LocalTypeInputs.names_ids, RuntimeValue.ofCore, pid, lid, parameterId]
        using (mapped_lookup qrows)))))
  · simp only [body, entry, LocalTypeInputs.bindFresh_names, entryEnvironment, result, ref, parameterId]
    exact .binding (.bitNot (.identifier .head .head))
      (.expression (.pair (.identifier .head .head) (.identifier
        (by simpa only [List.map_cons, Prod.snd, LocalTypeInputs.names_ids, pid, lid, parameterId] using qnames)
        (by simpa only [List.map_cons, Prod.snd, LocalTypeInputs.names_ids, pid, lid, parameterId] using qrows))))
  · exact .letE (.unary (.var rfl) rfl) (.pair (.var rfl) (.var (by
      simpa only [List.getElem?_cons_succ] using (Resolved.LocalScope.lookup_iff_getElem? f.indexed).mp f.found)))
private theorem old_endpoint (f : Frame) (s : Core.Store) (w : Core.Word) {v : Core.Value} {t : Core.Store}
    (h : ComputationReturnTreeEvaluates LocalExpressionEvaluates f.owner (entry f.owner f.inputs).names
      (entryEnvironment f.owner f.inputs f.environment w) s (body f.spans) v t) : v = result w f.payload ∧ t = s := by
  cases h with
  | binding initializer tail =>
      obtain ⟨sameValue, sameStore⟩ := initializer.deterministic (.bitNot (.identifier .head .head))
      rw [sameValue, sameStore] at tail
      cases tail with
      | expression child =>
          exact child.deterministic (.pair (.identifier .head .head)
            (.identifier (.tail (by change ("p" : String) ≠ "q"; decide) (.tail (by change ("p" : String) ≠ "q"; decide) f.named)) (by
              simpa only [entry, LocalTypeInputs.bindFresh_names, LocalTypeInputs.names_ids, entryEnvironment,
                List.map_cons, Prod.snd, pid, lid, parameterId] using two_rows f f.found (Core.Value.word w) (.word w.bitNot))))
private theorem core_exact {P : RuntimeValue → List RuntimeValue → Prop} {e : List Core.Value}
    {s : Core.Store} {c : Core.Expr} {v : Core.Value} (original : Core.Evaluates e s c v s)
    (image : ∀ a t, P a t ↔ ∃ w u, a = RuntimeValue.ofCore w ∧ t = heap u ∧ Core.Evaluates e s c w u) :
    ∀ a t, P a t ↔ a = RuntimeValue.ofCore v ∧ t = heap s := by
  intro a t; constructor
  · intro h
    obtain ⟨w, u, same, finalSame, evaluated⟩ := (image a t).mp h
    obtain ⟨valueEq, storeEq⟩ := Core.evaluation_deterministic evaluated original
    exact ⟨same.trans (congrArg RuntimeValue.ofCore valueEq), finalSame.trans (congrArg heap storeEq)⟩
  · intro images; exact (image _ _).mpr ⟨v, s, images.1, images.2, original⟩

theorem body_original_and_all_actual_images
    (spans : Nat → Syntax.SourceSpan) (savedOwner : Resolved.DeclarationId)
    (inputs : LocalTypeInputs) (environment : Resolved.Environment) (store : Core.Store)
    (payloadId : Resolved.LocalId) (input : Core.Word) (payload : Core.Value)
    (sameSavedIds : Resolved.LocalScope.ids environment = Resolved.LocalScope.ids inputs.context)
    (payloadNamed : LocalNameTable.Lookup inputs.names "q" payloadId)
    (payloadTyped : Resolved.LocalScope.Lookup inputs.context payloadId .unit)
    (payloadFound : Resolved.LocalScope.Lookup environment payloadId payload) :
    ClosedSourceDataBody (body spans) ∧
    ClosedSourceBodyEvaluates savedOwner (entry savedOwner inputs).names
      (embedded (entryEnvironment savedOwner inputs environment input)) (heap store) (body spans)
      (RuntimeValue.ofCore (result input payload)) (heap store) ∧
    ComputationReturnTreeEvaluates LocalExpressionEvaluates savedOwner (entry savedOwner inputs).names
      (entryEnvironment savedOwner inputs environment input) store (body spans) (result input payload) store ∧
    ∃ payloadIndex,
      Resolved.LocalScope.IndexOf (Resolved.LocalScope.ids inputs.context) payloadId payloadIndex ∧
      elaborateComputationReturnTree? elaborateLocalExpression? types savedOwner
        (entry savedOwner inputs) (body spans) = some (bodyCore payloadIndex, .product .word .unit) ∧
      elaborateExpectedComputationLambda? elaborateLocalExpression? types savedOwner inputs
        (source spans) (.function .word (.product .word .unit)) =
          some (.lambda .word (.product .word .unit) (bodyCore payloadIndex)) ∧
      Core.Evaluates (.word input :: Resolved.LocalScope.values environment) store
        (bodyCore payloadIndex) (result input payload) store ∧
      (∀ (actual : RuntimeValue) (actualFinal : List RuntimeValue),
        ClosedSourceBodyEvaluates savedOwner (entry savedOwner inputs).names
          (embedded (entryEnvironment savedOwner inputs environment input)) (heap store) (body spans)
          actual actualFinal ↔
        actual = RuntimeValue.ofCore (result input payload) ∧ actualFinal = heap store) := by
  obtain ⟨qi, qAt, _⟩ := payloadTyped.indexed
  let f : Frame := ⟨spans, savedOwner, inputs, environment, payload, payloadId, qi, sameSavedIds,
    payloadNamed, payloadTyped, payloadFound, sameSavedIds.symm ▸ qAt⟩
  have paths := original_paths f store input
  have checks := checked f
  have admitted := gate spans
  have aligned : (entryEnvironment savedOwner inputs environment input).ids = (entry savedOwner inputs).context.ids := by
    simpa only [entryEnvironment, entry, LocalTypeInputs.bindFresh_context, Resolved.LocalScope.ids,
      List.map_cons, Prod.fst, parameterId] using congrArg (parameterId savedOwner inputs :: ·) sameSavedIds
  refine ⟨admitted, paths.1, paths.2.1, qi, qAt, checks.1, checks.2, paths.2.2, ?_⟩
  intro actual actualFinal; constructor
  · intro evaluated
    obtain ⟨v, final, same, _, old⟩ := admitted.local_evaluates_iff.mp evaluated
    have valueEq := (old_endpoint f store input old).1
    obtain ⟨w, final, _, sameStore, core⟩ := (admitted.core_evaluates_iff checks.1 aligned).mp evaluated
    have storeEq := (Core.evaluation_deterministic core paths.2.2).2
    exact ⟨same.trans (congrArg RuntimeValue.ofCore valueEq), sameStore.trans (congrArg heap storeEq)⟩
  · intro images
    have back := (admitted.local_evaluates_iff (owner := savedOwner)).mpr
      ⟨result input payload, store, images.1, images.2, paths.2.1⟩
    obtain ⟨v, final, same, sameStore, core⟩ := (admitted.core_evaluates_iff checks.1 aligned).mp back
    obtain ⟨valueEq, storeEq⟩ := Core.evaluation_deterministic core paths.2.2
    exact (admitted.core_evaluates_iff checks.1 aligned).mpr ⟨result input payload, store,
      same.trans (congrArg RuntimeValue.ofCore valueEq), sameStore.trans (congrArg heap storeEq), paths.2.2⟩

theorem calls_original_and_all_actual_images
    (spans : Nat → Syntax.SourceSpan) (savedOwner : Resolved.DeclarationId)
    (inputs : LocalTypeInputs) (environment : Resolved.Environment) (store : Core.Store)
    (payloadId argumentId : Resolved.LocalId) (input : Core.Word) (payload : Core.Value)
    (argumentName calleeName : Syntax.Identifier)
    (sameSavedIds : Resolved.LocalScope.ids environment = Resolved.LocalScope.ids inputs.context)
    (payloadNamed : LocalNameTable.Lookup inputs.names "q" payloadId)
    (payloadTyped : Resolved.LocalScope.Lookup inputs.context payloadId .unit)
    (payloadFound : Resolved.LocalScope.Lookup environment payloadId payload)
    (argumentNamed : LocalNameTable.Lookup inputs.names argumentName.value argumentId)
    (argumentFound : Resolved.LocalScope.Lookup environment argumentId (.word input))
    (callerOwner : Resolved.DeclarationId) (callerNames : LocalNameTable)
    (callerCaptured : Resolved.LocalScope RuntimeValue) (calleeId callerArgumentId : Resolved.LocalId)
    (calleeNamed : LocalNameTable.Lookup callerNames calleeName.value calleeId)
    (calleeFound : Resolved.LocalScope.Lookup callerCaptured calleeId
      (.sourceClosure (source spans) savedOwner inputs.names (embedded environment)))
    (callerArgumentNamed : LocalNameTable.Lookup callerNames argumentName.value callerArgumentId)
    (callerArgumentFound : Resolved.LocalScope.Lookup callerCaptured callerArgumentId (.word input)) :
    let direct := call spans (source spans) (argument spans argumentName)
    let invoked := call spans ⟨spans 25, .identifier calleeName⟩ (argument spans argumentName)
    let expected := result input.bitNot payload
    ClosedSourceDataBody (body spans) ∧ ClosedSourceDataExpression (argument spans argumentName) ∧
    ClosedSourceExpressionEvaluates savedOwner inputs.names (embedded environment) (heap store)
      direct (RuntimeValue.ofCore expected) (heap store) ∧
    ClosedSourceExpressionEvaluates callerOwner callerNames callerCaptured (heap store)
      invoked (RuntimeValue.ofCore expected) (heap store) ∧
    ∃ payloadIndex argumentIndex,
      Resolved.LocalScope.IndexOf (Resolved.LocalScope.ids inputs.context) payloadId payloadIndex ∧
      Resolved.LocalScope.IndexOf (Resolved.LocalScope.ids environment) argumentId argumentIndex ∧
      ResolvesLocalExpression inputs.names (argument spans argumentName)
        (.unary .wordNot (.var argumentId)) ∧
      Resolved.Lowers (Resolved.LocalScope.ids environment) (.unary .wordNot (.var argumentId))
        (.unary .wordNot (.var argumentIndex)) ∧
      elaborateExpectedComputationLambda? elaborateLocalExpression? types savedOwner inputs
        (source spans) (.function .word (.product .word .unit)) =
          some (.lambda .word (.product .word .unit) (bodyCore payloadIndex)) ∧
      LocalExpressionEvaluates inputs.names environment store (argument spans argumentName)
        (.word input.bitNot) store ∧
      Core.Evaluates (Resolved.LocalScope.values environment) store
        (.unary .wordNot (.var argumentIndex)) (.word input.bitNot) store ∧
      Core.Evaluates (.word input.bitNot :: Resolved.LocalScope.values environment) store
        (bodyCore payloadIndex) expected store ∧
      Core.Evaluates (Resolved.LocalScope.values environment) store
        (.apply (.lambda .word (.product .word .unit) (bodyCore payloadIndex))
          (.unary .wordNot (.var argumentIndex))) expected store ∧
      (∀ (actual : RuntimeValue) (actualFinal : List RuntimeValue),
        ClosedSourceExpressionEvaluates savedOwner inputs.names (embedded environment) (heap store)
          direct actual actualFinal ↔
        actual = RuntimeValue.ofCore expected ∧ actualFinal = heap store) ∧
      (∀ (actual : RuntimeValue) (actualFinal : List RuntimeValue),
        ClosedSourceExpressionEvaluates callerOwner callerNames callerCaptured (heap store)
          invoked actual actualFinal ↔
        actual = RuntimeValue.ofCore expected ∧ actualFinal = heap store) := by
  dsimp only
  obtain ⟨qi, qAt, _⟩ := payloadTyped.indexed
  obtain ⟨ai, argAt, argValue⟩ := argumentFound.indexed
  let f : Frame := ⟨spans, savedOwner, inputs, environment, payload, payloadId, qi, sameSavedIds,
    payloadNamed, payloadTyped, payloadFound, sameSavedIds.symm ▸ qAt⟩
  have paths := original_paths f store input.bitNot
  have checks := checked f
  have directArg : ClosedSourceExpressionEvaluates savedOwner inputs.names (embedded environment) (heap store)
      (argument spans argumentName) (.word input.bitNot) (heap store) := .bitNot (.reference argumentNamed
        (by simpa only [RuntimeValue.ofCore] using mapped_lookup argumentFound))
  have savedArg : ClosedSourceExpressionEvaluates callerOwner callerNames callerCaptured (heap store)
      (argument spans argumentName) (.word input.bitNot) (heap store) := .bitNot (.reference callerArgumentNamed callerArgumentFound)
  have savedCallee : ClosedSourceExpressionEvaluates callerOwner callerNames callerCaptured (heap store)
      ⟨spans 25, .identifier calleeName⟩ (.sourceClosure (source spans) savedOwner inputs.names (embedded environment))
      (heap store) := .reference calleeNamed calleeFound
  have actualBody : ClosedSourceBodyEvaluates savedOwner
      (("p", Resolved.freshLocalId savedOwner (inputs.names.map Prod.snd)) :: inputs.names)
      ((Resolved.freshLocalId savedOwner (inputs.names.map Prod.snd), .word input.bitNot) :: embedded environment)
      (heap store) (body spans) (RuntimeValue.ofCore (result input.bitNot payload)) (heap store) := by
    simpa only [f, entry, LocalTypeInputs.bindFresh_names, LocalTypeInputs.names_ids, entryEnvironment, embedded,
      List.map_cons, RuntimeValue.ofCore, parameterId] using paths.1
  have directOriginal := ClosedSourceExpressionEvaluates.call (span := spans 23) (argumentsSpan := spans 24)
    (callee := source spans) .inferred (.creation .inferred) directArg actualBody
  have savedOriginal := ClosedSourceExpressionEvaluates.call (span := spans 23) (argumentsSpan := spans 24)
    .inferred savedCallee savedArg actualBody
  have argCore : Core.Evaluates environment.values store (.unary .wordNot (.var ai)) (.word input.bitNot) store :=
    .unary (.var argValue) rfl
  have appCore : Core.Evaluates environment.values store
      (.apply (.lambda .word (.product .word .unit) (bodyCore qi)) (.unary .wordNot (.var ai)))
      (result input.bitNot payload) store := .apply .lambda argCore paths.2.2
  refine ⟨gate spans, .bitNot .reference, directOriginal, savedOriginal, qi, ai, qAt, argAt,
    .bitNot (.identifier argumentNamed), .unary (.var argAt), checks.2,
    .bitNot (.identifier argumentNamed argumentFound), argCore, paths.2.2, appCore, ?_, ?_⟩
  · exact core_exact appCore (fun a t => closedSourceExpectedDataLambda_application_core_iff
      (initialStore := store) (callSpan := spans 23) (argumentsSpan := spans 24) (actualValue := a) (actualFinal := t)
      .inferred (gate spans) checks.2 sameSavedIds (.bitNot .reference)
      (.bitNot (.identifier argumentNamed)) (.unary (.var argAt)))
  · exact core_exact paths.2.2 (fun a t => closedSourceExpectedDataLambda_invocation_core_iff
      (callSpan := spans 23) (argumentsSpan := spans 24) (actualValue := a) (actualFinal := t)
      .inferred (gate spans) checks.2 sameSavedIds savedCallee (by simpa only [RuntimeValue.ofCore, heap] using savedArg))

end Tests.ExpectedWordUnaryDataImages
