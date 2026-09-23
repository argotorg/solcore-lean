import Solcore.Frontend.Expected
import Solcore.Frontend.LocalExpressionTyping
/- Independent Bool short-circuit body and direct/saved call data images.
Saved IDs inherit LocalTypeInputs NoDup; duplicate spellings/foreign owners remain possible.
Caller rows below are arbitrary mixed lists, including duplicate IDs. Runtime q is untyped. -/
set_option autoImplicit false
namespace Tests.ExpectedBoolShortCircuitDataImages
open Solcore Solcore.Frontend
private def ref (s : Syntax.SourceSpan) (name : String) : Syntax.Expr := ⟨s, .identifier ⟨s, name⟩⟩
private def neg (s op : Syntax.SourceSpan) (e : Syntax.Expr) : Syntax.Expr := ⟨s, .unary ⟨op, .logicalNot⟩ e⟩
private def types : TypeNameTable := [(["Bool"], .bool)]
private def annotation (s : Syntax.SourceSpan) : Syntax.TypeExpr :=
  ⟨s, .named ⟨s, ⟨⟨⟨s, "Bool"⟩, []⟩⟩⟩ none⟩
private def initializer (useOr : Bool) (s : Nat → Syntax.SourceSpan) : Syntax.Expr :=
  ⟨s 23, .binary (ref (s 24) "p") ⟨s 25, if useOr then .logicalOr else .logicalAnd⟩
    (neg (s 9) (s 10) (ref (s 11) "p"))⟩
private def initCode (useOr : Bool) : Core.Expr :=
  if useOr then .ifE (.var 0) (.bool true) (.unary .boolNot (.var 0))
  else .ifE (.var 0) (.unary .boolNot (.var 0)) (.bool false)
private def body (useOr : Bool) (s : Nat → Syntax.SourceSpan) : Syntax.Block :=
  ⟨s 5, [⟨s 6, .letDecl ⟨s 7, "p"⟩ (some (annotation (s 8)))
    (some (initializer useOr s))⟩,
    ⟨s 12, .returnStmt (some ⟨s 13, .tuple ⟨s 14, [ref (s 15) "p", ref (s 16) "q"]⟩⟩)⟩]⟩
private def source (useOr : Bool) (s : Nat → Syntax.SourceSpan) : Syntax.Expr :=
  ⟨s 0, .lambda (s 1) ⟨s 2, [⟨s 3, .inferred ⟨s 4, "p"⟩⟩]⟩ none (body useOr s)⟩
private def argument (s : Nat → Syntax.SourceSpan) := neg (s 17) (s 18) (ref (s 19) "c")
private def call (s : Nat → Syntax.SourceSpan) (callee : Syntax.Expr) : Syntax.Expr :=
  ⟨s 20, .call callee ⟨s 21, [argument s]⟩⟩
private def embedded (e : Resolved.Environment) : Resolved.LocalScope RuntimeValue :=
  e.map (fun row => (row.1, RuntimeValue.ofCore row.2))
private def code (useOr : Bool) (qIndex : Nat) : Core.Expr :=
  .letE (initCode useOr) (.pair (.var 0) (.var (qIndex + 2)))
private def result (useOr : Bool) (q : Core.Value) : Core.Value := .pair (.bool useOr) q
private structure Frame where
  useOr : Bool
  spans : Nat → Syntax.SourceSpan
  owner : Resolved.DeclarationId
  inputs : LocalTypeInputs
  environment : Resolved.Environment
  q : Core.Value
  qId : Resolved.LocalId
  qIndex : Nat
  aligned : environment.ids = inputs.context.ids
  named : LocalNameTable.Lookup inputs.names "q" qId
  typed : Resolved.LocalScope.Lookup inputs.context qId .unit
  found : Resolved.LocalScope.Lookup environment qId q
  indexed : Resolved.LocalScope.IndexOf environment.ids qId qIndex
private def pid (f : Frame) := Resolved.freshLocalId f.owner f.inputs.ids
private def lid (f : Frame) := Resolved.freshLocalId f.owner (pid f :: f.inputs.ids)
private def entered (f : Frame) := f.inputs.bindFresh f.owner "p" .bool
private def entry (f : Frame) (b : Bool) : Resolved.Environment := (pid f, .bool b) :: f.environment
private def closure (f : Frame) := RuntimeValue.sourceClosure (source f.useOr f.spans) f.owner
  f.inputs.names (embedded f.environment)
private theorem q_member (f : Frame) : f.qId ∈ f.inputs.ids := by
  rw [← LocalTypeInputs.context_ids]
  exact List.mem_map.mpr ⟨(f.qId, .unit), f.typed.mem, rfl⟩
private theorem fresh_ne {owner : Resolved.DeclarationId} {ids : List Resolved.LocalId}
    {id : Resolved.LocalId} (member : id ∈ ids) : Resolved.freshLocalId owner ids ≠ id := by
  intro same
  exact Resolved.freshLocalId_not_mem owner ids (same.symm ▸ member)
private theorem two_rows (f : Frame) {α : Type} {e : Resolved.LocalScope α} {q : α}
    (found : Resolved.LocalScope.Lookup e f.qId q) (parameterValue localValue : α) :
    Resolved.LocalScope.Lookup ((lid f, localValue) :: (pid f, parameterValue) :: e) f.qId q :=
  .tail (fresh_ne (List.mem_cons_of_mem _ (q_member f))) (.tail (fresh_ne (q_member f)) found)
private theorem mapped_lookup {e : Resolved.Environment} {id : Resolved.LocalId} {v : Core.Value}
    (found : Resolved.LocalScope.Lookup e id v) :
    Resolved.LocalScope.Lookup (embedded e) id (RuntimeValue.ofCore v) := by
  induction found with
  | head => exact .head
  | tail different _ ih => exact .tail different ih
private theorem gate (useOr : Bool) (s : Nat → Syntax.SourceSpan) : ClosedSourceDataBody (body useOr s) := by
  cases useOr
  · exact .binding (.logicalAnd .reference (.logicalNot .reference)) (.expression (.pair .reference .reference))
  · exact .binding (.logicalOr .reference (.logicalNot .reference)) (.expression (.pair .reference .reference))
private theorem initializer_paths (f : Frame) (s : Core.Store) (b : Bool) :
    ClosedSourceExpressionEvaluates f.owner (entered f).names (embedded (entry f b))
      (s.map RuntimeValue.ofCore) (initializer f.useOr f.spans) (.bool f.useOr) (s.map RuntimeValue.ofCore) ∧
    LocalExpressionEvaluates (entered f).names (entry f b) s (initializer f.useOr f.spans) (.bool f.useOr) s ∧
    Core.Evaluates (.bool b :: f.environment.values) s (initCode f.useOr) (.bool f.useOr) s := by
  cases choice : f.useOr <;> cases b <;> simp only [initializer, initCode, Bool.false_eq_true, if_false, if_true,
    entry, embedded, List.map_cons, RuntimeValue.ofCore, entered, LocalTypeInputs.bindFresh_names, ref, neg]
  · exact ⟨.andFalse (.reference .head .head), .andFalse (.identifier .head .head), .ifFalse (.var rfl) .bool⟩
  · exact ⟨.andTrue (.reference .head .head) (.logicalNot (value := true) (.reference .head .head)),
      .andTrue (.identifier .head .head) (.logicalNot (value := true) (.identifier .head .head)), .ifTrue (.var rfl) (.unary (.var rfl) rfl)⟩
  · exact ⟨.orFalse (.reference .head .head) (.logicalNot (value := false) (.reference .head .head)),
      .orFalse (.identifier .head .head) (.logicalNot (value := false) (.identifier .head .head)), .ifFalse (.var rfl) (.unary (.var rfl) rfl)⟩
  · exact ⟨.orTrue (.reference .head .head), .orTrue (.identifier .head .head), .ifTrue (.var rfl) .bool⟩
private theorem checked (f : Frame) :
    elaborateComputationReturnTree? elaborateLocalExpression? types f.owner (entered f) (body f.useOr f.spans) =
      some (code f.useOr f.qIndex, .product .bool .unit) ∧
    elaborateExpectedComputationLambda? elaborateLocalExpression? types f.owner f.inputs
      (source f.useOr f.spans) (.function .bool (.product .bool .unit)) =
      some (.lambda .bool (.product .bool .unit) (code f.useOr f.qIndex)) := by
  have index : Resolved.LocalScope.IndexOf f.inputs.ids f.qId f.qIndex := by
    have aligned := f.indexed
    rw [f.aligned, LocalTypeInputs.context_ids] at aligned
    exact aligned
  have index2 : Resolved.LocalScope.IndexOf (lid f :: pid f :: f.inputs.ids) f.qId (f.qIndex + 2) :=
    .tail (fresh_ne (List.mem_cons_of_mem _ (q_member f))) (.tail (fresh_ne (q_member f)) index)
  have compiled : ComputationReturnTreeElaborates
      (fun n c e k t => elaborateLocalExpression? n c e = some (k, t))
      types f.owner (entered f) (body f.useOr f.spans) (code f.useOr f.qIndex) (.product .bool .unit) := by
    dsimp only [body, code]
    refine .binding (.named .head) ?_ (.expression ?_)
    · cases choice : f.useOr
      · exact elaborateLocalExpression?_complete (.logicalAnd (.identifier .head) (.logicalNot (.identifier .head)))
          (.ifE (.var .head) (.unary (.var .head)) .bool) (.ifE (.var .head) (.unary (.var .head)) .bool)
      · exact elaborateLocalExpression?_complete (.logicalOr (.identifier .head) (.logicalNot (.identifier .head)))
          (.ifE (.var .head) .bool (.unary (.var .head))) (.ifE (.var .head) .bool (.unary (.var .head)))
    · refine elaborateLocalExpression?_complete
        (.pair (.identifier .head) (.identifier
          (.tail (by change "p" ≠ "q"; decide) (.tail (by change "p" ≠ "q"; decide) f.named)))) ?_ ?_
      · exact .pair (.var .head) (.var (by
        simpa only [entered, LocalTypeInputs.context_ids, LocalTypeInputs.bindFresh_ids, pid, lid] using index2))
      · exact .pair (.var .head) (.var (by
        simpa only [entered, LocalTypeInputs.bindFresh_context, pid, lid, LocalTypeInputs.bindFresh_ids]
          using two_rows f f.typed Core.Ty.bool Core.Ty.bool))
  exact ⟨(elaborateComputationReturnTree?_iff (fun {_ _ _ _ _} => Iff.rfl)).mpr compiled,
    (elaborateExpectedComputationLambda?_iff (fun {_ _ _ _ _} => Iff.rfl)).mpr
      (.lambda (.lambda .inferred .omitted) .bool (.product .bool .unit) compiled)⟩
private theorem original_paths (f : Frame) (s : Core.Store) (b : Bool) :
    ClosedSourceBodyEvaluates f.owner (entered f).names (embedded (entry f b))
      (s.map RuntimeValue.ofCore) (body f.useOr f.spans) (RuntimeValue.ofCore (result f.useOr f.q)) (s.map RuntimeValue.ofCore) ∧
    ComputationReturnTreeEvaluates LocalExpressionEvaluates f.owner (entered f).names (entry f b)
      s (body f.useOr f.spans) (result f.useOr f.q) s ∧
    Core.Evaluates (.bool b :: f.environment.values) s (code f.useOr f.qIndex) (result f.useOr f.q) s := by
  have ip := initializer_paths f s b
  have qrows := two_rows f f.found (Core.Value.bool b) (.bool f.useOr)
  have qnames : LocalNameTable.Lookup
      (("p", lid f) :: ("p", pid f) :: f.inputs.names) "q" f.qId :=
    .tail (by decide) (.tail (by decide) f.named)
  refine ⟨?_, ?_, ?_⟩
  · simp only [body, entered, LocalTypeInputs.bindFresh_names, entry,
      embedded, List.map_cons, RuntimeValue.ofCore, result, ref, pid]
    refine .binding (by simpa only [entered, LocalTypeInputs.bindFresh_names, entry, embedded, List.map_cons, RuntimeValue.ofCore, pid] using ip.1)
      (.expression (.pair (.reference .head .head) (.reference (id := f.qId) ?_ ?_)))
    · simpa only [List.map_cons, Prod.snd, LocalTypeInputs.names_ids, pid, lid] using qnames
    · simpa only [embedded, List.map_cons, Prod.snd, LocalTypeInputs.names_ids,
        RuntimeValue.ofCore, pid, lid] using mapped_lookup qrows
  · simp only [body, entered, LocalTypeInputs.bindFresh_names, entry,
      result, ref, pid]
    refine .binding (by simpa only [entered, LocalTypeInputs.bindFresh_names, entry, pid] using ip.2.1)
      (.expression (.pair (.identifier .head .head) (.identifier (id := f.qId) ?_ ?_)))
    · simpa only [List.map_cons, Prod.snd, LocalTypeInputs.names_ids, pid, lid] using qnames
    · simpa only [List.map_cons, Prod.snd, LocalTypeInputs.names_ids, pid, lid] using qrows
  · exact .letE ip.2.2 (.pair (.var rfl)
      (.var (by simpa only [List.getElem?_cons_succ] using
        (Resolved.LocalScope.lookup_iff_getElem? f.indexed).mp f.found)))
private theorem old_endpoint (f : Frame) (s : Core.Store) (b : Bool) {v : Core.Value} {t : Core.Store}
    (h : ComputationReturnTreeEvaluates LocalExpressionEvaluates f.owner (entered f).names (entry f b)
      s (body f.useOr f.spans) v t) : v = result f.useOr f.q ∧ t = s := by
  cases h with
  | binding initializer tail =>
      obtain ⟨rfl, rfl⟩ := initializer.deterministic (initializer_paths f s b).2.1
      cases tail with
      | expression child =>
          apply child.deterministic
          exact .pair (.identifier .head .head) (.identifier
            (.tail (by change "p" ≠ "q"; decide) (.tail (by change "p" ≠ "q"; decide) f.named))
            (by simpa only [entered, LocalTypeInputs.bindFresh_names, LocalTypeInputs.names_ids,
              entry, List.map_cons, Prod.snd, pid, lid] using
              two_rows f f.found (Core.Value.bool b) (.bool f.useOr)))
private theorem core_exact {P : RuntimeValue → List RuntimeValue → Prop} {e : List Core.Value}
    {s : Core.Store} {c : Core.Expr} {v : Core.Value} (original : Core.Evaluates e s c v s)
    (image : ∀ a t, P a t ↔ ∃ w u, a = RuntimeValue.ofCore w ∧ t = u.map RuntimeValue.ofCore ∧
      Core.Evaluates e s c w u) :
    ∀ a t, P a t ↔ a = RuntimeValue.ofCore v ∧ t = s.map RuntimeValue.ofCore := by
  intro a t
  constructor
  · intro h
    obtain ⟨w, u, same, finalSame, evaluated⟩ := (image a t).mp h
    obtain ⟨rfl, rfl⟩ := Core.evaluation_deterministic evaluated original
    exact ⟨same, finalSame⟩
  · rintro ⟨rfl, rfl⟩
    exact (image _ _).mpr ⟨v, s, rfl, rfl, original⟩
theorem body_original_and_all_actual_images (f : Frame) (s : Core.Store) (b : Bool) :
    ClosedSourceDataBody (body f.useOr f.spans) ∧
    elaborateExpectedComputationLambda? elaborateLocalExpression? types f.owner f.inputs
      (source f.useOr f.spans) (.function .bool (.product .bool .unit)) =
      some (.lambda .bool (.product .bool .unit) (code f.useOr f.qIndex)) ∧
    ClosedSourceBodyEvaluates f.owner (entered f).names (embedded (entry f b))
      (s.map RuntimeValue.ofCore) (body f.useOr f.spans) (RuntimeValue.ofCore (result f.useOr f.q)) (s.map RuntimeValue.ofCore) ∧
    ComputationReturnTreeEvaluates LocalExpressionEvaluates f.owner (entered f).names (entry f b)
      s (body f.useOr f.spans) (result f.useOr f.q) s ∧
    Core.Evaluates (.bool b :: f.environment.values) s (code f.useOr f.qIndex) (result f.useOr f.q) s ∧
    (∀ a t, ClosedSourceBodyEvaluates f.owner (entered f).names (embedded (entry f b))
      (s.map RuntimeValue.ofCore) (body f.useOr f.spans) a t ↔
      a = RuntimeValue.ofCore (result f.useOr f.q) ∧ t = s.map RuntimeValue.ofCore) ∧
    (∀ a t, ClosedSourceBodyEvaluates f.owner (entered f).names (embedded (entry f b))
      (s.map RuntimeValue.ofCore) (body f.useOr f.spans) a t ↔
      a = RuntimeValue.ofCore (result f.useOr f.q) ∧ t = s.map RuntimeValue.ofCore) := by
  have paths := original_paths f s b
  have admitted := gate f.useOr f.spans
  have checks := checked f
  have aligned : (entry f b).ids = (entered f).context.ids := by
    simpa only [entry, entered, LocalTypeInputs.bindFresh_context, Resolved.LocalScope.ids, List.map_cons,
      Prod.fst, LocalTypeInputs.context_ids, pid] using congrArg (pid f :: ·) f.aligned
  refine ⟨admitted, checks.2, paths.1, paths.2.1, paths.2.2, ?_, ?_⟩
  · intro a t
    constructor
    · intro h
      obtain ⟨v, u, same, finalSame, old⟩ := admitted.local_evaluates_iff.mp h
      obtain ⟨rfl, rfl⟩ := old_endpoint f s b old
      exact ⟨same, finalSame⟩
    · rintro ⟨rfl, rfl⟩
      exact admitted.local_evaluates_iff.mpr ⟨result f.useOr f.q, s, rfl, rfl, paths.2.1⟩
  · exact core_exact paths.2.2 (fun _ _ => admitted.core_evaluates_iff checks.1 aligned)
theorem calls_original_and_all_actual_images (f : Frame) (s : Core.Store) (b : Bool)
    (directId : Resolved.LocalId) (directIndex : Nat)
    (directNamed : LocalNameTable.Lookup f.inputs.names "c" directId)
    (directFound : Resolved.LocalScope.Lookup f.environment directId (.bool b))
    (directIndexed : Resolved.LocalScope.IndexOf f.environment.ids directId directIndex)
    (callerOwner : Resolved.DeclarationId) (callerNames : LocalNameTable)
    (callerCaptured : Resolved.LocalScope RuntimeValue) (calleeId argumentId : Resolved.LocalId)
    (calleeNamed : LocalNameTable.Lookup callerNames "picked" calleeId)
    (calleeFound : Resolved.LocalScope.Lookup callerCaptured calleeId (closure f))
    (argumentNamed : LocalNameTable.Lookup callerNames "c" argumentId)
    (argumentFound : Resolved.LocalScope.Lookup callerCaptured argumentId (.bool b)) :
    ClosedSourceDataExpression (argument f.spans) ∧
    ResolvesLocalExpression f.inputs.names (argument f.spans) (.unary .boolNot (.var directId)) ∧
    Resolved.Lowers f.environment.ids (.unary .boolNot (.var directId)) (.unary .boolNot (.var directIndex)) ∧
    LocalExpressionEvaluates f.inputs.names f.environment s (argument f.spans) (.bool (!b)) s ∧
    ClosedSourceExpressionEvaluates f.owner f.inputs.names (embedded f.environment) (s.map RuntimeValue.ofCore)
      (call f.spans (source f.useOr f.spans)) (RuntimeValue.ofCore (result f.useOr f.q)) (s.map RuntimeValue.ofCore) ∧
    ClosedSourceExpressionEvaluates callerOwner callerNames callerCaptured (s.map RuntimeValue.ofCore)
      (call f.spans (ref (f.spans 22) "picked")) (RuntimeValue.ofCore (result f.useOr f.q)) (s.map RuntimeValue.ofCore) ∧
    Core.Evaluates f.environment.values s
      (.apply (.lambda .bool (.product .bool .unit) (code f.useOr f.qIndex)) (.unary .boolNot (.var directIndex)))
      (result f.useOr f.q) s ∧
    Core.Evaluates (.bool (!b) :: f.environment.values) s (code f.useOr f.qIndex) (result f.useOr f.q) s ∧
    (∀ a t, ClosedSourceExpressionEvaluates f.owner f.inputs.names (embedded f.environment)
      (s.map RuntimeValue.ofCore) (argument f.spans) a t ↔ a = RuntimeValue.ofCore (.bool (!b)) ∧ t = s.map RuntimeValue.ofCore) ∧
    (∀ a t, ClosedSourceExpressionEvaluates f.owner f.inputs.names (embedded f.environment)
      (s.map RuntimeValue.ofCore) (argument f.spans) a t ↔ a = RuntimeValue.ofCore (.bool (!b)) ∧ t = s.map RuntimeValue.ofCore) ∧
    (∀ a t, ClosedSourceExpressionEvaluates f.owner f.inputs.names (embedded f.environment)
      (s.map RuntimeValue.ofCore) (call f.spans (source f.useOr f.spans)) a t ↔
      a = RuntimeValue.ofCore (result f.useOr f.q) ∧ t = s.map RuntimeValue.ofCore) ∧
    (∀ a t, ClosedSourceExpressionEvaluates callerOwner callerNames callerCaptured (s.map RuntimeValue.ofCore)
      (call f.spans (ref (f.spans 22) "picked")) a t ↔
      a = RuntimeValue.ofCore (result f.useOr f.q) ∧ t = s.map RuntimeValue.ofCore) := by
  have bodyPaths := original_paths f s (!b)
  have localArgument : LocalExpressionEvaluates f.inputs.names f.environment s (argument f.spans) (.bool (!b)) s :=
    .logicalNot (.identifier directNamed directFound)
  have directArg : ClosedSourceExpressionEvaluates f.owner f.inputs.names (embedded f.environment)
      (s.map RuntimeValue.ofCore) (argument f.spans) (.bool (!b)) (s.map RuntimeValue.ofCore) :=
    .logicalNot (.reference directNamed (by simpa only [RuntimeValue.ofCore] using mapped_lookup directFound))
  have savedArg : ClosedSourceExpressionEvaluates callerOwner callerNames callerCaptured
      (s.map RuntimeValue.ofCore) (argument f.spans) (.bool (!b)) (s.map RuntimeValue.ofCore) :=
    .logicalNot (.reference argumentNamed argumentFound)
  have savedCallee : ClosedSourceExpressionEvaluates callerOwner callerNames callerCaptured
      (s.map RuntimeValue.ofCore) (ref (f.spans 22) "picked") (closure f) (s.map RuntimeValue.ofCore) :=
    .reference calleeNamed calleeFound
  have actualBody : ClosedSourceBodyEvaluates f.owner
      (("p", Resolved.freshLocalId f.owner (f.inputs.names.map Prod.snd)) :: f.inputs.names)
      ((Resolved.freshLocalId f.owner (f.inputs.names.map Prod.snd), .bool (!b)) :: embedded f.environment)
      (s.map RuntimeValue.ofCore) (body f.useOr f.spans) (RuntimeValue.ofCore (result f.useOr f.q)) (s.map RuntimeValue.ofCore) := by
    simpa only [entered, LocalTypeInputs.bindFresh_names, LocalTypeInputs.names_ids, entry, embedded,
      List.map_cons, RuntimeValue.ofCore, pid] using bodyPaths.1
  have directOriginal : ClosedSourceExpressionEvaluates f.owner f.inputs.names (embedded f.environment)
      (s.map RuntimeValue.ofCore) (call f.spans (source f.useOr f.spans))
      (RuntimeValue.ofCore (result f.useOr f.q)) (s.map RuntimeValue.ofCore) :=
    .call .inferred (.creation .inferred) directArg actualBody
  have savedOriginal : ClosedSourceExpressionEvaluates callerOwner callerNames callerCaptured
      (s.map RuntimeValue.ofCore) (call f.spans (ref (f.spans 22) "picked"))
      (RuntimeValue.ofCore (result f.useOr f.q)) (s.map RuntimeValue.ofCore) :=
    .call .inferred savedCallee savedArg actualBody
  have argumentCore : Core.Evaluates f.environment.values s (.unary .boolNot (.var directIndex)) (.bool (!b)) s :=
    .unary (.var ((Resolved.LocalScope.lookup_iff_getElem? directIndexed).mp directFound)) rfl
  have applicationCore : Core.Evaluates f.environment.values s
      (.apply (.lambda .bool (.product .bool .unit) (code f.useOr f.qIndex)) (.unary .boolNot (.var directIndex)))
      (result f.useOr f.q) s := .apply .lambda argumentCore bodyPaths.2.2
  have admitted := gate f.useOr f.spans
  have checks := checked f
  refine ⟨.logicalNot .reference, .logicalNot (.identifier directNamed), .unary (.var directIndexed),
    localArgument, directOriginal, savedOriginal, applicationCore, bodyPaths.2.2, ?_, ?_, ?_, ?_⟩
  · intro a t
    constructor
    · intro h
      obtain ⟨v,u,hv,hs,ev⟩ := (ClosedSourceDataExpression.local_evaluates_iff (.logicalNot .reference)).mp h
      obtain ⟨vv,ss⟩ := ev.deterministic localArgument
      exact ⟨by simpa only [vv, RuntimeValue.ofCore] using hv, by simpa only [ss] using hs⟩
    · rintro ⟨rfl,rfl⟩
      exact (ClosedSourceDataExpression.local_evaluates_iff (.logicalNot .reference)).mpr ⟨.bool (!b),s,rfl,rfl,localArgument⟩
  · exact core_exact argumentCore (fun _ _ => (ClosedSourceDataExpression.logicalNot (.reference (name := ⟨f.spans 19,"c"⟩))).core_evaluates_iff
      (.logicalNot (.identifier directNamed)) (.unary (.var directIndexed)))
  · exact core_exact applicationCore (fun a t =>
      closedSourceExpectedDataLambda_application_core_iff
        (initialStore := s) (callSpan := f.spans 20) (argumentsSpan := f.spans 21)
        (actualValue := a) (actualFinal := t) .inferred admitted checks.2 f.aligned
        (.logicalNot .reference) (.logicalNot (.identifier directNamed)) (.unary (.var directIndexed)))
  · exact core_exact bodyPaths.2.2 (fun a t =>
      closedSourceExpectedDataLambda_invocation_core_iff
        (callSpan := f.spans 20) (argumentsSpan := f.spans 21) (actualValue := a) (actualFinal := t)
        .inferred admitted checks.2 f.aligned savedCallee
        (by simpa only [RuntimeValue.ofCore] using savedArg))
end Tests.ExpectedBoolShortCircuitDataImages
