import Solcore.Frontend.Fragments.Internal.Expected
import Solcore.Frontend.Fragments.Internal.LocalExpressions
import Solcore.Frontend.Fragments.Internal.LocalFunctionApplication
import Solcore.Resolved.LocalScope
import Solcore.Frontend.Fragments.Internal.ClosedSource
import Solcore.Core.Fuel
import Solcore.Syntax.Parser.Internal.TermBasics
import Solcore.Test.Frontend.ClosedStrictWords
import Solcore.Frontend.Fragments.Internal.Foundations

/-!
# Expected data image tests

Data images of expected Bool and Word expressions in strict, unary and short-circuit form, and the parsed
bridges to them.
-/

section
-- leanmerge: from Solcore.Test.FrontendExpectedBoolShortCircuitDataImageProperties
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
end

section
-- leanmerge: from Solcore.Test.FrontendExpectedBoolStrictDataImageProperties
set_option autoImplicit false
namespace Tests.ExpectedBoolStrictDataImages
open Solcore Solcore.Frontend
def up (e : Resolved.Environment) := e.map (fun r => (r.1,RuntimeValue.ofCore r.2))
def heap (s : Core.Store) := s.map RuntimeValue.ofCore
def one := Core.Word.ofNatModulo 1
def two := Core.Word.ofNatModulo 2
def ref (s : Syntax.SourceSpan) (n : String) : Syntax.Expr := ⟨s,.identifier ⟨s,n⟩⟩
def lit (s : Syntax.SourceSpan) (n : String) : Syntax.Expr := ⟨s,.literal ⟨s,.decimal n⟩⟩
def initializer (s : Nat → Syntax.SourceSpan) : Syntax.Expr :=
  ⟨s 9,.binary (ref (s 10) "p") ⟨s 11,.add⟩ (lit (s 12) "1")⟩
def lessSource (s : Nat → Syntax.SourceSpan) : Syntax.Expr := ⟨s 18,.binary (ref (s 19) "p") ⟨s 20,.less⟩ (lit (s 21) "2")⟩
def leftSource (s : Nat → Syntax.SourceSpan) : Syntax.Expr := ⟨s 15,.unary ⟨s 16,.logicalNot⟩ ⟨s 17,.group (lessSource s)⟩⟩
def rightSource (s : Nat → Syntax.SourceSpan) : Syntax.Expr := ⟨s 23,.group ⟨s 24,.binary (ref (s 25) "p") ⟨s 26,.greaterEqual⟩ (lit (s 27) "2")⟩⟩
def returned (s : Nat → Syntax.SourceSpan) : Syntax.Expr := ⟨s 14,.binary (leftSource s) ⟨s 22,.logicalAnd⟩ (rightSource s)⟩
def annotation (s : Syntax.SourceSpan) : Syntax.TypeExpr := ⟨s,.named ⟨s,⟨⟨⟨s,"Word"⟩,[]⟩⟩⟩ none⟩
def body (s : Nat → Syntax.SourceSpan) : Syntax.Block :=
  ⟨s 5,[⟨s 6,.letDecl ⟨s 7,"p"⟩ (some (annotation (s 8))) (some (initializer s))⟩,
    ⟨s 13,.returnStmt (some (returned s))⟩]⟩
def source (s : Nat → Syntax.SourceSpan) : Syntax.Expr :=
  ⟨s 0,.lambda (s 1) ⟨s 2,[⟨s 3,.inferred ⟨s 4,"p"⟩⟩]⟩ none (body s)⟩
def argument (s : Nat → Syntax.SourceSpan) : Syntax.Expr :=
  ⟨s 28,.binary (ref (s 29) "c") ⟨s 30,.add⟩ (lit (s 31) "1")⟩
def call (s : Nat → Syntax.SourceSpan) (fn a : Syntax.Expr) : Syntax.Expr := ⟨s 32,.call fn ⟨s 33,[a]⟩⟩
def types : TypeNameTable := [(["Word"],.word)]
def predicate (w : Core.Word) := !(decide (w < two))
def result (w : Core.Word) : Core.Value := .bool (predicate (w.add one))
def tailCode : Core.Expr :=
  .ifE (.unary .boolNot ((Core.Expr.var 0).wordLt (.word two)))
    (.unary .boolNot ((Core.Expr.var 0).wordLt (.word two))) (.bool false)
def code : Core.Expr := .letE (.binary .wordAdd (.var 0) (.word one)) tailCode
def bodyCost (w : Core.Word) := 5 + (if predicate (w.add one) then 28 else 16) + 2
def entered (o : Resolved.DeclarationId) (t : LocalTypeInputs) := t.bindFresh o "p" .word
def entry (o : Resolved.DeclarationId) (t : LocalTypeInputs) (e : Resolved.Environment) (w : Core.Word) : Resolved.Environment :=
  (Resolved.freshLocalId o t.ids,.word w)::e
private theorem literalOne (s : Syntax.SourceSpan) : WordLiteralDenotes ⟨s,.decimal "1"⟩ one :=
  .decimal (by decide) (.cons (.decimal (digit:=1) (by decide) rfl) .nil)
private theorem literalTwo (s : Syntax.SourceSpan) : WordLiteralDenotes ⟨s,.decimal "2"⟩ two :=
  .decimal (by decide) (.cons (.decimal (digit:=2) (by decide) rfl) .nil)
theorem mapped {e : Resolved.Environment} {i : Resolved.LocalId} {v : Core.Value}
    (h : Resolved.LocalScope.Lookup e i v) : Resolved.LocalScope.Lookup (up e) i (RuntimeValue.ofCore v) := by
  induction h with | head => exact .head | tail ne _ ih => exact .tail ne ih
private theorem tail_paths (s : Nat → Syntax.SourceSpan) (o : Resolved.DeclarationId)
    (n : LocalNameTable) (e : Resolved.Environment) (st : Core.Store) (i : Resolved.LocalId) (w : Core.Word) :
    ClosedSourceExpressionEvaluates o (("p",i)::n) (up ((i,.word w)::e)) (heap st)
      (returned s) (RuntimeValue.ofCore (.bool (predicate w))) (heap st) ∧
    LocalExpressionEvaluatesWithCost (("p",i)::n) ((i,.word w)::e) st
      (returned s) (.bool (predicate w)) st (if predicate w then 28 else 16) := by
  have cl : ClosedSourceExpressionEvaluates o (("p",i)::n) (up ((i,.word w)::e)) (heap st)
      (ref (s 19) "p") (.word w) (heap st) := by simp only [up,List.map_cons,RuntimeValue.ofCore]; exact .reference .head .head
  have cr : ClosedSourceExpressionEvaluates o (("p",i)::n) (up ((i,.word w)::e)) (heap st)
      (ref (s 25) "p") (.word w) (heap st) := by simp only [up,List.map_cons,RuntimeValue.ofCore]; exact .reference .head .head
  have ll : LocalExpressionEvaluatesWithCost (("p",i)::n) ((i,.word w)::e) st (ref (s 19) "p") (.word w) st 1 := .identifier .head .head
  have lr : LocalExpressionEvaluatesWithCost (("p",i)::n) ((i,.word w)::e) st (ref (s 25) "p") (.word w) st 1 := .identifier .head .head
  have cmp : ClosedSourceExpressionEvaluates o (("p",i)::n) (up ((i,.word w)::e)) (heap st) (lessSource s) (RuntimeValue.ofCore (.bool (decide (w<two)))) (heap st) := .strictWordBinary cl (.wordLiteral (literalTwo _)) .less
  have left : ClosedSourceExpressionEvaluates o (("p",i)::n) (up ((i,.word w)::e)) (heap st) (leftSource s) (.bool (predicate w)) (heap st) :=
    .logicalNot (.group (by simpa only [RuntimeValue.ofCore] using cmp))
  have right : ClosedSourceExpressionEvaluates o (("p",i)::n) (up ((i,.word w)::e)) (heap st) (rightSource s) (.bool (predicate w)) (heap st) := by
    apply ClosedSourceExpressionEvaluates.group
    rw [← RuntimeValue.ofCore.eq_2 (predicate w)]
    exact .strictWordBinary cr (.wordLiteral (literalTwo _)) .greaterEqual
  have oldLeft : LocalExpressionEvaluatesWithCost (("p",i)::n) ((i,.word w)::e) st (leftSource s) (.bool (predicate w)) st 13 := .logicalNot (.group (.less ll (.wordLiteral (literalTwo _))))
  have oldRight : LocalExpressionEvaluatesWithCost (("p",i)::n) ((i,.word w)::e) st (rightSource s) (.bool (predicate w)) st 13 := .group (.greaterEqual lr (.wordLiteral (literalTwo _)))
  cases h : predicate w <;> simp only [Bool.false_eq_true,↓reduceIte,RuntimeValue.ofCore]
  · exact ⟨.andFalse (by simpa only [predicate,RuntimeValue.ofCore] using h ▸ left),.andFalse (h ▸ oldLeft)⟩
  · exact ⟨.andTrue (by simpa only [predicate,RuntimeValue.ofCore] using h ▸ left) (by simpa only [predicate,RuntimeValue.ofCore] using h ▸ right),.andTrue (h ▸ oldLeft) (h ▸ oldRight)⟩
private theorem return_checked (s : Nat → Syntax.SourceSpan) (t : LocalTypeInputs)
    (o : Resolved.DeclarationId) :
    elaborateLocalExpression? (entered o t).names (entered o t).context (returned s) = some (tailCode,.bool) := by
  exact elaborateLocalExpression?_complete
    (.logicalAnd (.logicalNot (.group (.less (.identifier .head) (.wordLiteral (literalTwo _)))))
      (.group (.greaterEqual (.identifier .head) (.wordLiteral (literalTwo _)))))
    (.ifE (.unary (.wordLt (.var .head) .word)) (.unary (.wordLt (.var .head) .word)) .bool)
    (.ifE (.unary (.wordLt (.var .head) .word)) (.unary (.wordLt (.var .head) .word)) .bool)
theorem core_exact {P : RuntimeValue → List RuntimeValue → Prop} {e s c v}
    (original : Core.Evaluates e s c v s)
    (image : ∀ a z, P a z ↔ ∃ x t, a=RuntimeValue.ofCore x ∧ z=heap t ∧ Core.Evaluates e s c x t) :
    ∀ a z, P a z ↔ a=RuntimeValue.ofCore v ∧ z=heap s := by
  intro a z; constructor
  · intro h; obtain ⟨x,t,hx,ht,old⟩ := (image a z).mp h
    obtain ⟨rfl,rfl⟩ := Core.evaluation_deterministic old original; exact ⟨hx,ht⟩
  · rintro ⟨rfl,rfl⟩; exact (image _ _).mpr ⟨v,s,rfl,rfl,original⟩
structure BodyEvidence (s : Nat → Syntax.SourceSpan) (o : Resolved.DeclarationId) (t : LocalTypeInputs)
    (e : Resolved.Environment) (st : Core.Store) (w : Core.Word) : Prop where
  admitted : ClosedSourceDataBody (body s)
  checked : elaborateComputationReturnTree? elaborateLocalExpression? types o (entered o t) (body s) = some (code,.bool)
  expected : elaborateExpectedComputationLambda? elaborateLocalExpression? types o t (source s) (.function .word .bool) = some (.lambda .word .bool code)
  original : ClosedSourceBodyEvaluates o (entered o t).names (up (entry o t e w)) (heap st) (body s) (RuntimeValue.ofCore (result w)) (heap st)
  old : ComputationReturnTreeEvaluates LocalExpressionEvaluates o (entered o t).names (entry o t e w) st (body s) (result w) st
  steps : ∀ k, Core.Steps (bodyCost w) ⟨.eval code (.word w::e.values),k,st⟩ ⟨.ret (result w),k,st⟩
  localImage : ∀ a z, ClosedSourceBodyEvaluates o (entered o t).names (up (entry o t e w)) (heap st) (body s) a z ↔ a=RuntimeValue.ofCore (result w) ∧ z=heap st
  coreImage : ∀ a z, ClosedSourceBodyEvaluates o (entered o t).names (up (entry o t e w)) (heap st) (body s) a z ↔ a=RuntimeValue.ofCore (result w) ∧ z=heap st
theorem body_evidence (s : Nat → Syntax.SourceSpan) (o : Resolved.DeclarationId) (t : LocalTypeInputs)
    (e : Resolved.Environment) (st : Core.Store) (w : Core.Word) (aligned : e.ids=t.context.ids) : BodyEvidence s o t e st w := by
  let t1 := entered o t
  let e1 := entry o t e w
  let t2 := entered o t1
  let e2 := entry o t1 e1 (w.add one)
  have a1 : e1.ids=t1.context.ids := by simpa only [e1,t1,entry,entered,Resolved.LocalScope.ids,LocalTypeInputs.bindFresh_context,List.map_cons] using congrArg (List.cons _) aligned
  have a2 : e2.ids=t2.context.ids := by simpa only [e2,t2,entry,entered,Resolved.LocalScope.ids,LocalTypeInputs.bindFresh_context,List.map_cons] using congrArg (List.cons _) a1
  have initOld : LocalExpressionEvaluatesWithCost t1.names e1 st (initializer s) (.word (w.add one)) st 5 := by
    simp only [t1,e1,entered,entry,LocalTypeInputs.bindFresh_names,initializer,ref,lit]
    refine .add (middleStore:=st) (leftValue:=w) (rightValue:=one) (leftCost:=1) (rightCost:=1) ?_ ?_
    · exact .identifier .head .head
    · exact .wordLiteral (literalOne _)
  have initRaw : ClosedSourceExpressionEvaluates o t1.names (up e1) (heap st) (initializer s) (.word (w.add one)) (heap st) := by
    rw [← RuntimeValue.ofCore.eq_3 (w.add one)]
    apply ClosedSourceExpressionEvaluates.strictWordBinary (leftWord:=w) (rightWord:=one) (meaning:=StrictWordBinaryDenotes.add)
    · simp only [t1,e1,entered,entry,LocalTypeInputs.bindFresh_names,up,List.map_cons,RuntimeValue.ofCore]; exact .reference .head .head
    · exact .wordLiteral (literalOne _)
  have tail := tail_paths s o t1.names e1 st (Resolved.freshLocalId o t1.ids) (w.add one)
  have initCheck : elaborateLocalExpression? t1.names t1.context (initializer s) = some (.binary .wordAdd (.var 0) (.word one),.word) :=
    elaborateLocalExpression?_complete (.add (.identifier .head) (.wordLiteral (literalOne _))) (.binary (.var .head) .word) (.binary (.var .head) .word)
  have tailCheck := return_checked s t1 o
  have tc : LocalExpressionEvaluatesWithCost t2.names e2 st (returned s) (result w) st (if predicate (w.add one) then 28 else 16) := by
    simpa only [t2,e2,entry,entered,LocalTypeInputs.bindFresh_names,LocalTypeInputs.names_ids,result] using tail.2
  have tr : ClosedSourceExpressionEvaluates o t2.names (up e2) (heap st) (returned s) (RuntimeValue.ofCore (result w)) (heap st) := by
    simpa only [t2,e2,entry,entered,LocalTypeInputs.bindFresh_names,LocalTypeInputs.names_ids,result] using tail.1
  have raw : ClosedSourceBodyEvaluates o t1.names (up e1) (heap st) (body s) (RuntimeValue.ofCore (result w)) (heap st) := by
    apply ClosedSourceBodyEvaluates.binding initRaw
    simpa only [t2,e2,entry,entered,LocalTypeInputs.bindFresh_names,LocalTypeInputs.names_ids,up,List.map_cons,RuntimeValue.ofCore] using ClosedSourceBodyEvaluates.expression (blockSpan:=s 5) (returnSpan:=s 13) tr
  have old : ComputationReturnTreeEvaluates LocalExpressionEvaluates o t1.names e1 st (body s) (result w) st := by
    apply ComputationReturnTreeEvaluates.binding initOld.erase
    simpa only [t2,e2,entry,entered,LocalTypeInputs.bindFresh_names,LocalTypeInputs.names_ids] using ComputationReturnTreeEvaluates.expression (owner:=o) (blockSpan:=s 5) (returnSpan:=s 13) tc.erase
  have paths : ∀ k, Core.Steps (bodyCost w) ⟨.eval code (.word w::e.values),k,st⟩ ⟨.ret (result w),k,st⟩ := by
    obtain ⟨ir,irs,il,_⟩ := elaborateLocalExpression?_sound initCheck
    obtain ⟨rr,rrs,rl,_⟩ := elaborateLocalExpression?_sound tailCheck
    intro k
    exact CostStepComposition.letE (initOld.toStepsWithContinuation irs (a1 ▸ il) _)
      (by simpa only [e1,e2,entry,Resolved.LocalScope.values,List.map_cons] using tc.toStepsWithContinuation rrs (a2 ▸ rl) k)
  have gate : ClosedSourceDataBody (body s) := .binding (.strictWordBinary .reference .literal (by decide) (by decide))
    (.expression (.logicalAnd (.logicalNot (.group (.strictWordBinary .reference .literal (by decide) (by decide)))) (.group (.strictWordBinary .reference .literal (by decide) (by decide)))))
  have compiled : ComputationReturnTreeElaborates (fun n c x k ty => elaborateLocalExpression? n c x = some (k,ty)) types o t1 (body s) code .bool :=
    .binding (.named .head) initCheck (.expression tailCheck)
  have checked := (elaborateComputationReturnTree?_iff (fun {_ _ _ _ _} => Iff.rfl)).mpr compiled
  refine ⟨gate,checked,(elaborateExpectedComputationLambda?_iff (fun {_ _ _ _ _} => Iff.rfl)).mpr (.lambda (.lambda .inferred .omitted) .word .bool compiled),raw,old,paths,?_,?_⟩
  · intro a z; constructor
    · intro h; obtain ⟨v,fs,hv,hs,localRun⟩ := gate.local_evaluates_iff.mp h
      exact (gate.local_evaluates_iff.mpr ⟨v,fs,hv,hs,localRun⟩).deterministic raw
    · rintro ⟨rfl,rfl⟩; exact gate.local_evaluates_iff.mpr ⟨result w,st,rfl,rfl,old⟩
  · exact core_exact (Core.steps_from_initial_sound (paths [])) (fun _ _ => by simpa only [t1,e1,entry,up,heap,Resolved.LocalScope.values,List.map_cons] using gate.core_evaluates_iff checked a1)
theorem argument_paths (s : Nat → Syntax.SourceSpan) (o : Resolved.DeclarationId) (n : LocalNameTable)
    (e : Resolved.Environment) (st : Core.Store) (w : Core.Word) (i : Resolved.LocalId) (index : Nat)
    (named : LocalNameTable.Lookup n "c" i) (found : Resolved.LocalScope.Lookup e i (.word w))
    (indexed : Resolved.LocalScope.IndexOf e.ids i index) :
    ClosedSourceDataExpression (argument s) ∧
    ResolvesLocalExpression n (argument s) (.binary .wordAdd (.var i) (.word one)) ∧
    Resolved.Lowers e.ids (.binary .wordAdd (.var i) (.word one)) (.binary .wordAdd (.var index) (.word one)) ∧
    LocalExpressionEvaluatesWithCost n e st (argument s) (.word (w.add one)) st 5 ∧
    ClosedSourceExpressionEvaluates o n (up e) (heap st) (argument s) (.word (w.add one)) (heap st) :=
  ⟨.strictWordBinary .reference .literal (by decide) (by decide),.add (.identifier named) (.wordLiteral (literalOne _)),
    .binary (.var indexed) .word,.add (.identifier named found) (.wordLiteral (literalOne _)),
    by rw [← RuntimeValue.ofCore.eq_3 (w.add one)]
       exact .strictWordBinary (.reference named (by simpa only [RuntimeValue.ofCore] using mapped found)) (.wordLiteral (literalOne _)) .add⟩
theorem calls_original_and_images (s : Nat → Syntax.SourceSpan) (o : Resolved.DeclarationId) (t : LocalTypeInputs)
    (e : Resolved.Environment) (st : Core.Store) (w : Core.Word) (aligned : e.ids=t.context.ids)
    (i : Resolved.LocalId) (index : Nat) (named : LocalNameTable.Lookup t.names "c" i)
    (found : Resolved.LocalScope.Lookup e i (.word w)) (indexed : Resolved.LocalScope.IndexOf e.ids i index)
    (caller : Resolved.DeclarationId) (names : LocalNameTable) (rows : Resolved.LocalScope RuntimeValue)
    (callee arg : Syntax.Expr) (actualClosure : RuntimeValue) (creationStore : List RuntimeValue)
    (created : ClosedSourceExpressionEvaluates o t.names (up e) (heap st) (source s) actualClosure creationStore)
    (fetched : ClosedSourceExpressionEvaluates caller names rows creationStore callee actualClosure creationStore)
    (passed : ClosedSourceExpressionEvaluates caller names rows creationStore arg (.word (w.add one)) (heap st)) :
    actualClosure = .sourceClosure (source s) o t.names (up e) ∧ creationStore=heap st ∧
    ClosedSourceExpressionEvaluates o t.names (up e) (heap st) (call s (source s) (argument s)) (RuntimeValue.ofCore (result (w.add one))) (heap st) ∧
    ClosedSourceExpressionEvaluates caller names rows creationStore (call s callee arg) (RuntimeValue.ofCore (result (w.add one))) (heap st) ∧
    (∀ a z, ClosedSourceExpressionEvaluates o t.names (up e) (heap st) (call s (source s) (argument s)) a z ↔ a=RuntimeValue.ofCore (result (w.add one)) ∧ z=heap st) ∧
    (∀ a z, ClosedSourceExpressionEvaluates caller names rows creationStore (call s callee arg) a z ↔ a=RuntimeValue.ofCore (result (w.add one)) ∧ z=heap st) := by
  have b := body_evidence s o t e st (w.add one) aligned
  have a := argument_paths s o t.names e st w i index named found indexed
  have made : ClosedSourceExpressionEvaluates o t.names (up e) (heap st) (source s) (.sourceClosure (source s) o t.names (up e)) (heap st) := .creation .inferred
  have same := created.deterministic made
  have calleeOriginal := same.1 ▸ fetched
  have beta : ClosedSourceBodyEvaluates o (("p",Resolved.freshLocalId o (t.names.map Prod.snd))::t.names)
      ((Resolved.freshLocalId o (t.names.map Prod.snd),.word (w.add one))::up e) (heap st) (body s) (RuntimeValue.ofCore (result (w.add one))) (heap st) := by
    simpa only [entered,entry,LocalTypeInputs.bindFresh_names,LocalTypeInputs.names_ids,up,List.map_cons,RuntimeValue.ofCore] using b.original
  have direct := ClosedSourceExpressionEvaluates.call (span:=s 32) (argumentsSpan:=s 33) .inferred made a.2.2.2.2 beta
  have saved := ClosedSourceExpressionEvaluates.call (span:=s 32) (argumentsSpan:=s 33) .inferred calleeOriginal passed beta
  have coreArg := a.2.2.2.1.toStepsWithContinuation a.2.1 a.2.2.1 []
  have coreBody := Core.steps_from_initial_sound (b.steps [])
  have coreCall := Core.Evaluates.apply (Core.Evaluates.lambda (parameterType:=.word) (resultType:=.bool)) (Core.steps_from_initial_sound coreArg) coreBody
  exact ⟨same.1,same.2,direct,saved,
    core_exact coreCall (fun _ _ => closedSourceExpectedDataLambda_application_core_iff .inferred b.admitted b.expected aligned a.1 a.2.1 a.2.2.1),
    core_exact coreBody (fun _ _ => closedSourceExpectedDataLambda_invocation_core_iff .inferred b.admitted b.expected aligned calleeOriginal (by simpa only [RuntimeValue.ofCore,heap] using passed))⟩
end Tests.ExpectedBoolStrictDataImages
end

section
-- leanmerge: from Solcore.Test.FrontendExpectedBoolUnaryDataImageProperties
/- Symbolic Bool body and direct/saved call data images.
Saved IDs inherit LocalTypeInputs NoDup; duplicate spellings/foreign owners remain possible.
Caller rows below are arbitrary mixed lists, including duplicate IDs. Runtime q is untyped. -/
set_option autoImplicit false
namespace Tests.ExpectedBoolUnaryDataImages
open Solcore Solcore.Frontend

private def ref (s : Syntax.SourceSpan) (name : String) : Syntax.Expr := ⟨s, .identifier ⟨s, name⟩⟩
private def neg (s op : Syntax.SourceSpan) (e : Syntax.Expr) : Syntax.Expr := ⟨s, .unary ⟨op, .logicalNot⟩ e⟩
private def types : TypeNameTable := [(["Bool"], .bool)]
private def annotation (s : Syntax.SourceSpan) : Syntax.TypeExpr :=
  ⟨s, .named ⟨s, ⟨⟨⟨s, "Bool"⟩, []⟩⟩⟩ none⟩
private def body (s : Nat → Syntax.SourceSpan) : Syntax.Block :=
  ⟨s 5, [⟨s 6, .letDecl ⟨s 7, "p"⟩ (some (annotation (s 8)))
    (some (neg (s 9) (s 10) (ref (s 11) "p")))⟩,
    ⟨s 12, .returnStmt (some ⟨s 13, .tuple ⟨s 14, [ref (s 15) "p", ref (s 16) "q"]⟩⟩)⟩]⟩
private def source (s : Nat → Syntax.SourceSpan) : Syntax.Expr :=
  ⟨s 0, .lambda (s 1) ⟨s 2, [⟨s 3, .inferred ⟨s 4, "p"⟩⟩]⟩ none (body s)⟩
private def argument (s : Nat → Syntax.SourceSpan) := neg (s 17) (s 18) (ref (s 19) "c")
private def call (s : Nat → Syntax.SourceSpan) (callee : Syntax.Expr) : Syntax.Expr :=
  ⟨s 20, .call callee ⟨s 21, [argument s]⟩⟩
private def embedded (e : Resolved.Environment) : Resolved.LocalScope RuntimeValue :=
  e.map (fun row => (row.1, RuntimeValue.ofCore row.2))
private def code (qIndex : Nat) : Core.Expr :=
  .letE (.unary .boolNot (.var 0)) (.pair (.var 0) (.var (qIndex + 2)))
private def result (b : Bool) (q : Core.Value) : Core.Value := .pair (.bool (!b)) q

private structure Frame where
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
private def closure (f : Frame) := RuntimeValue.sourceClosure (source f.spans) f.owner
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
private theorem gate (s : Nat → Syntax.SourceSpan) : ClosedSourceDataBody (body s) :=
  .binding (.logicalNot .reference) (.expression (.pair .reference .reference))

private theorem checked (f : Frame) :
    elaborateComputationReturnTree? elaborateLocalExpression? types f.owner (entered f) (body f.spans) =
      some (code f.qIndex, .product .bool .unit) ∧
    elaborateExpectedComputationLambda? elaborateLocalExpression? types f.owner f.inputs
      (source f.spans) (.function .bool (.product .bool .unit)) =
      some (.lambda .bool (.product .bool .unit) (code f.qIndex)) := by
  have index : Resolved.LocalScope.IndexOf f.inputs.ids f.qId f.qIndex := by
    have aligned := f.indexed
    rw [f.aligned, LocalTypeInputs.context_ids] at aligned
    exact aligned
  have index2 : Resolved.LocalScope.IndexOf (lid f :: pid f :: f.inputs.ids) f.qId (f.qIndex + 2) :=
    .tail (fresh_ne (List.mem_cons_of_mem _ (q_member f))) (.tail (fresh_ne (q_member f)) index)
  have compiled : ComputationReturnTreeElaborates
      (fun n c e k t => elaborateLocalExpression? n c e = some (k, t))
      types f.owner (entered f) (body f.spans) (code f.qIndex) (.product .bool .unit) := by
    dsimp only [body, code]
    refine .binding (.named .head) ?_ (.expression ?_)
    · refine elaborateLocalExpression?_complete (.logicalNot (.identifier .head)) ?_ ?_
      · exact .unary (.var .head)
      · exact .unary (.var .head)
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
      (s.map RuntimeValue.ofCore) (body f.spans) (RuntimeValue.ofCore (result b f.q)) (s.map RuntimeValue.ofCore) ∧
    ComputationReturnTreeEvaluates LocalExpressionEvaluates f.owner (entered f).names (entry f b)
      s (body f.spans) (result b f.q) s ∧
    Core.Evaluates (.bool b :: f.environment.values) s (code f.qIndex) (result b f.q) s := by
  have qrows := two_rows f f.found (Core.Value.bool b) (.bool (!b))
  have qnames : LocalNameTable.Lookup
      (("p", lid f) :: ("p", pid f) :: f.inputs.names) "q" f.qId :=
    .tail (by decide) (.tail (by decide) f.named)
  refine ⟨?_, ?_, ?_⟩
  · simp only [body, entered, LocalTypeInputs.bindFresh_names, entry,
      embedded, List.map_cons, RuntimeValue.ofCore, result, ref, neg, pid]
    refine .binding (.logicalNot (.reference .head .head))
      (.expression (.pair (.reference .head .head) (.reference (id := f.qId) ?_ ?_)))
    · simpa only [List.map_cons, Prod.snd, LocalTypeInputs.names_ids, pid, lid] using qnames
    · simpa only [embedded, List.map_cons, Prod.snd, LocalTypeInputs.names_ids,
        RuntimeValue.ofCore, pid, lid] using mapped_lookup qrows
  · simp only [body, entered, LocalTypeInputs.bindFresh_names, entry,
      result, ref, neg, pid]
    refine .binding (.logicalNot (.identifier .head .head))
      (.expression (.pair (.identifier .head .head) (.identifier (id := f.qId) ?_ ?_)))
    · simpa only [List.map_cons, Prod.snd, LocalTypeInputs.names_ids, pid, lid] using qnames
    · simpa only [List.map_cons, Prod.snd, LocalTypeInputs.names_ids, pid, lid] using qrows
  · exact .letE (.unary (.var rfl) rfl) (.pair (.var rfl)
      (.var (by simpa only [List.getElem?_cons_succ] using
        (Resolved.LocalScope.lookup_iff_getElem? f.indexed).mp f.found)))

private theorem old_endpoint (f : Frame) (s : Core.Store) (b : Bool) {v : Core.Value} {t : Core.Store}
    (h : ComputationReturnTreeEvaluates LocalExpressionEvaluates f.owner (entered f).names (entry f b)
      s (body f.spans) v t) : v = result b f.q ∧ t = s := by
  cases h with
  | binding initializer tail =>
      obtain ⟨rfl, rfl⟩ := initializer.deterministic (.logicalNot (.identifier .head .head))
      cases tail with
      | expression child =>
          apply child.deterministic
          exact .pair (.identifier .head .head) (.identifier
            (.tail (by change "p" ≠ "q"; decide) (.tail (by change "p" ≠ "q"; decide) f.named))
            (by simpa only [entered, LocalTypeInputs.bindFresh_names, LocalTypeInputs.names_ids,
              entry, List.map_cons, Prod.snd, pid, lid] using
              two_rows f f.found (Core.Value.bool b) (.bool (!b))))

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

/-- Independent paths first; the final two identical endpoint clauses use local and Core laws separately. -/
theorem body_original_and_all_actual_images (f : Frame) (s : Core.Store) (b : Bool) :
    ClosedSourceDataBody (body f.spans) ∧
    elaborateExpectedComputationLambda? elaborateLocalExpression? types f.owner f.inputs
      (source f.spans) (.function .bool (.product .bool .unit)) =
      some (.lambda .bool (.product .bool .unit) (code f.qIndex)) ∧
    ClosedSourceBodyEvaluates f.owner (entered f).names (embedded (entry f b))
      (s.map RuntimeValue.ofCore) (body f.spans) (RuntimeValue.ofCore (result b f.q)) (s.map RuntimeValue.ofCore) ∧
    ComputationReturnTreeEvaluates LocalExpressionEvaluates f.owner (entered f).names (entry f b)
      s (body f.spans) (result b f.q) s ∧
    Core.Evaluates (.bool b :: f.environment.values) s (code f.qIndex) (result b f.q) s ∧
    (∀ a t, ClosedSourceBodyEvaluates f.owner (entered f).names (embedded (entry f b))
      (s.map RuntimeValue.ofCore) (body f.spans) a t ↔
      a = RuntimeValue.ofCore (result b f.q) ∧ t = s.map RuntimeValue.ofCore) ∧
    (∀ a t, ClosedSourceBodyEvaluates f.owner (entered f).names (embedded (entry f b))
      (s.map RuntimeValue.ofCore) (body f.spans) a t ↔
      a = RuntimeValue.ofCore (result b f.q) ∧ t = s.map RuntimeValue.ofCore) := by
  have paths := original_paths f s b
  have admitted := gate f.spans
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
      exact admitted.local_evaluates_iff.mpr ⟨result b f.q, s, rfl, rfl, paths.2.1⟩
  · exact core_exact paths.2.2 (fun _ _ => admitted.core_evaluates_iff checks.1 aligned)

/-- Actual direct and saved calls keep separate caller rows but the identical saved-body endpoint. -/
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
      (call f.spans (source f.spans)) (RuntimeValue.ofCore (result (!b) f.q)) (s.map RuntimeValue.ofCore) ∧
    ClosedSourceExpressionEvaluates callerOwner callerNames callerCaptured (s.map RuntimeValue.ofCore)
      (call f.spans (ref (f.spans 22) "picked")) (RuntimeValue.ofCore (result (!b) f.q)) (s.map RuntimeValue.ofCore) ∧
    Core.Evaluates f.environment.values s
      (.apply (.lambda .bool (.product .bool .unit) (code f.qIndex)) (.unary .boolNot (.var directIndex)))
      (result (!b) f.q) s ∧
    Core.Evaluates (.bool (!b) :: f.environment.values) s (code f.qIndex) (result (!b) f.q) s ∧
    (∀ a t, ClosedSourceExpressionEvaluates f.owner f.inputs.names (embedded f.environment)
      (s.map RuntimeValue.ofCore) (call f.spans (source f.spans)) a t ↔
      a = RuntimeValue.ofCore (result (!b) f.q) ∧ t = s.map RuntimeValue.ofCore) ∧
    (∀ a t, ClosedSourceExpressionEvaluates callerOwner callerNames callerCaptured (s.map RuntimeValue.ofCore)
      (call f.spans (ref (f.spans 22) "picked")) a t ↔
      a = RuntimeValue.ofCore (result (!b) f.q) ∧ t = s.map RuntimeValue.ofCore) := by
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
      (s.map RuntimeValue.ofCore) (body f.spans) (RuntimeValue.ofCore (result (!b) f.q)) (s.map RuntimeValue.ofCore) := by
    simpa only [entered, LocalTypeInputs.bindFresh_names, LocalTypeInputs.names_ids, entry, embedded,
      List.map_cons, RuntimeValue.ofCore, pid] using bodyPaths.1
  have directOriginal : ClosedSourceExpressionEvaluates f.owner f.inputs.names (embedded f.environment)
      (s.map RuntimeValue.ofCore) (call f.spans (source f.spans))
      (RuntimeValue.ofCore (result (!b) f.q)) (s.map RuntimeValue.ofCore) :=
    .call .inferred (.creation .inferred) directArg actualBody
  have savedOriginal : ClosedSourceExpressionEvaluates callerOwner callerNames callerCaptured
      (s.map RuntimeValue.ofCore) (call f.spans (ref (f.spans 22) "picked"))
      (RuntimeValue.ofCore (result (!b) f.q)) (s.map RuntimeValue.ofCore) :=
    .call .inferred savedCallee savedArg actualBody
  have argumentCore : Core.Evaluates f.environment.values s (.unary .boolNot (.var directIndex)) (.bool (!b)) s :=
    .unary (.var ((Resolved.LocalScope.lookup_iff_getElem? directIndexed).mp directFound)) rfl
  have applicationCore : Core.Evaluates f.environment.values s
      (.apply (.lambda .bool (.product .bool .unit) (code f.qIndex)) (.unary .boolNot (.var directIndex)))
      (result (!b) f.q) s := .apply .lambda argumentCore bodyPaths.2.2
  have admitted := gate f.spans
  have checks := checked f
  refine ⟨.logicalNot .reference, .logicalNot (.identifier directNamed), .unary (.var directIndexed),
    localArgument, directOriginal, savedOriginal, applicationCore, bodyPaths.2.2, ?_, ?_⟩
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

end Tests.ExpectedBoolUnaryDataImages
end

section
-- leanmerge: from Solcore.Test.FrontendExpectedWordShortCircuitDataImageProperties
set_option autoImplicit false
namespace Tests.ExpectedWordShortCircuitDataImages
open Solcore Solcore.Frontend

private def up (e : Resolved.Environment) := e.map (fun r => (r.1, RuntimeValue.ofCore r.2))
private def heap (s : Core.Store) := s.map RuntimeValue.ofCore
private def ref (s : Syntax.SourceSpan) (n : String) : Syntax.Expr := ⟨s, .identifier ⟨s,n⟩⟩
private def guard (s : Nat → Syntax.SourceSpan) (o : Bool) : Syntax.Expr :=
  ⟨s 0, .group ⟨s 1, .binary (ref (s 2) "a") ⟨s 3, if o then .logicalOr else .logicalAnd⟩ (ref (s 4) "b")⟩⟩
private def expr (s : Nat → Syntax.SourceSpan) (o : Bool) : Syntax.Expr :=
  ⟨s 5, .conditional (guard s o) (s 6) (ref (s 7) "p") (s 8)
    ⟨s 9, .unary ⟨s 10,.bitNot⟩ (ref (s 11) "p")⟩⟩
private def body (s : Nat → Syntax.SourceSpan) (o : Bool) : Syntax.Block :=
  ⟨s 12,[⟨s 13,.returnStmt (some (expr s o))⟩]⟩
private def source (s : Nat → Syntax.SourceSpan) (o : Bool) : Syntax.Expr :=
  ⟨s 14,.lambda (s 15) ⟨s 16,[⟨s 17,.inferred ⟨s 18,"p"⟩⟩]⟩ none (body s o)⟩
private def call (s : Nat → Syntax.SourceSpan) (fn arg : Syntax.Expr) : Syntax.Expr :=
  ⟨s 19,.call fn ⟨s 20,[arg]⟩⟩
private def choose (o a b : Bool) : Bool := if o then a || b else a && b
private def result (o a b : Bool) (w : Core.Word) : Core.Value :=
  .word (if choose o a b then w else w.bitNot)
private def guardCore (o : Bool) (a b : Nat) : Core.Expr :=
  if o then .ifE (.var a) (.bool true) (.var b) else .ifE (.var a) (.var b) (.bool false)
private def code (o : Bool) (a b : Nat) : Core.Expr :=
  .ifE (guardCore o (a+1) (b+1)) (.var 0) (.unary .wordNot (.var 0))
private def entry (owner : Resolved.DeclarationId) (t : LocalTypeInputs) := t.bindFresh owner "p" .word
private def env (owner : Resolved.DeclarationId) (t : LocalTypeInputs) (e : Resolved.Environment) (w : Core.Word) : Resolved.Environment :=
  (Resolved.freshLocalId owner t.ids, Core.Value.word w) :: e
private theorem mapped {e : Resolved.Environment} {i : Resolved.LocalId} {v : Core.Value}
    (h : Resolved.LocalScope.Lookup e i v) : Resolved.LocalScope.Lookup (up e) i (RuntimeValue.ofCore v) := by
  induction h with | head => exact .head | tail ne _ ih => exact .tail ne ih
private theorem fresh_ne {o : Resolved.DeclarationId} {t : LocalTypeInputs} {i : Resolved.LocalId} {ty : Core.Ty}
    (h : Resolved.LocalScope.Lookup t.context i ty) : Resolved.freshLocalId o t.ids ≠ i := by
  intro eq; apply Resolved.freshLocalId_not_mem o t.ids
  rw [eq, ← LocalTypeInputs.context_ids]; exact List.mem_map.mpr ⟨(i,ty),h.mem,rfl⟩
private theorem gate (s : Nat → Syntax.SourceSpan) (o : Bool) : ClosedSourceDataExpression (expr s o) := by
  apply ClosedSourceDataExpression.conditional
  · apply ClosedSourceDataExpression.group; cases o
    · exact .logicalAnd .reference .reference
    · exact .logicalOr .reference .reference
  · exact .reference
  · exact .bitNot .reference

private structure Frame where
  spans : Nat → Syntax.SourceSpan
  owner : Resolved.DeclarationId
  inputs : LocalTypeInputs
  environment : Resolved.Environment
  isOr : Bool
  left : Bool
  right : Bool
  aid : Resolved.LocalId
  bid : Resolved.LocalId
  ai : Nat
  bi : Nat
  aligned : environment.ids = inputs.context.ids
  an : LocalNameTable.Lookup inputs.names "a" aid
  bn : LocalNameTable.Lookup inputs.names "b" bid
  aTyped : Resolved.LocalScope.Lookup inputs.context aid .bool
  bTyped : Resolved.LocalScope.Lookup inputs.context bid .bool
  av : Resolved.LocalScope.Lookup environment aid (.bool left)
  bv : Resolved.LocalScope.Lookup environment bid (.bool right)
  ax : Resolved.LocalScope.IndexOf inputs.context.ids aid ai
  bx : Resolved.LocalScope.IndexOf inputs.context.ids bid bi
private theorem facts (f : Frame) (s : Core.Store) (w : Core.Word) :
    elaborateComputationReturnTree? elaborateLocalExpression? [] f.owner (entry f.owner f.inputs)
      (body f.spans f.isOr) = some (code f.isOr f.ai f.bi,.word) ∧
    elaborateExpectedComputationLambda? elaborateLocalExpression? [] f.owner f.inputs
      (source f.spans f.isOr) (.function .word .word) = some (.lambda .word .word (code f.isOr f.ai f.bi)) ∧
    ClosedSourceBodyEvaluates f.owner (entry f.owner f.inputs).names (up (env f.owner f.inputs f.environment w))
      (heap s) (body f.spans f.isOr) (RuntimeValue.ofCore (result f.isOr f.left f.right w)) (heap s) ∧
    ComputationReturnTreeEvaluates LocalExpressionEvaluates f.owner (entry f.owner f.inputs).names
      (env f.owner f.inputs f.environment w) s (body f.spans f.isOr) (result f.isOr f.left f.right w) s ∧
    Core.Evaluates (.word w :: f.environment.values) s (code f.isOr f.ai f.bi) (result f.isOr f.left f.right w) s := by
  have an : LocalNameTable.Lookup (entry f.owner f.inputs).names "a" f.aid := .tail (by change ("p" : String) ≠ "a"; decide) f.an
  have bn : LocalNameTable.Lookup (entry f.owner f.inputs).names "b" f.bid := .tail (by change ("p" : String) ≠ "b"; decide) f.bn
  have aTyped : Resolved.LocalScope.Lookup (entry f.owner f.inputs).context f.aid .bool := .tail (fresh_ne f.aTyped) f.aTyped
  have bTyped : Resolved.LocalScope.Lookup (entry f.owner f.inputs).context f.bid .bool := .tail (fresh_ne f.bTyped) f.bTyped
  have av : Resolved.LocalScope.Lookup (env f.owner f.inputs f.environment w) f.aid (.bool f.left) := .tail (fresh_ne f.aTyped) f.av
  have bv : Resolved.LocalScope.Lookup (env f.owner f.inputs f.environment w) f.bid (.bool f.right) := .tail (fresh_ne f.bTyped) f.bv
  have ax : Resolved.LocalScope.IndexOf (entry f.owner f.inputs).context.ids f.aid (f.ai+1) := .tail (fresh_ne f.aTyped) f.ax
  have bx : Resolved.LocalScope.IndexOf (entry f.owner f.inputs).context.ids f.bid (f.bi+1) := .tail (fresh_ne f.bTyped) f.bx
  have checkExpr : elaborateLocalExpression? (entry f.owner f.inputs).names (entry f.owner f.inputs).context
      (expr f.spans f.isOr) = some (code f.isOr f.ai f.bi,.word) := by
    cases ho : f.isOr
    · exact elaborateLocalExpression?_complete (.conditional (.group (.logicalAnd (.identifier an) (.identifier bn)))
        (.identifier .head) (.bitNot (.identifier .head))) (.ifE (.ifE (.var ax) (.var bx) .bool) (.var .head) (.unary (.var .head)))
        (.ifE (.ifE (.var aTyped) (.var bTyped) .bool) (.var .head) (.unary (.var .head)))
    · exact elaborateLocalExpression?_complete (.conditional (.group (.logicalOr (.identifier an) (.identifier bn)))
        (.identifier .head) (.bitNot (.identifier .head))) (.ifE (.ifE (.var ax) .bool (.var bx)) (.var .head) (.unary (.var .head)))
        (.ifE (.ifE (.var aTyped) .bool (.var bTyped)) (.var .head) (.unary (.var .head)))
  have checked : ComputationReturnTreeElaborates (fun n t e c ty => elaborateLocalExpression? n t e = some (c,ty))
      [] f.owner (entry f.owner f.inputs) (body f.spans f.isOr) (code f.isOr f.ai f.bi) .word := .expression checkExpr
  have cg : ClosedSourceExpressionEvaluates f.owner (entry f.owner f.inputs).names
      (up (env f.owner f.inputs f.environment w)) (heap s) (guard f.spans f.isOr)
      (.bool (choose f.isOr f.left f.right)) (heap s) := by
    apply ClosedSourceExpressionEvaluates.group
    cases ho : f.isOr <;> cases ha : f.left
    · exact .andFalse (.reference an (by simpa only [ha,RuntimeValue.ofCore] using mapped av))
    · exact .andTrue (.reference an (by simpa only [ha,RuntimeValue.ofCore] using mapped av)) (.reference bn (by simpa [RuntimeValue.ofCore,choose] using mapped bv))
    · exact .orFalse (.reference an (by simpa only [ha,RuntimeValue.ofCore] using mapped av)) (.reference bn (by simpa [RuntimeValue.ofCore,choose] using mapped bv))
    · exact .orTrue (.reference an (by simpa only [ha,RuntimeValue.ofCore] using mapped av))
  have lg : LocalExpressionEvaluates (entry f.owner f.inputs).names (env f.owner f.inputs f.environment w)
      s (guard f.spans f.isOr) (.bool (choose f.isOr f.left f.right)) s := by
    apply LocalExpressionEvaluates.group
    cases ho : f.isOr <;> cases ha : f.left
    · exact .andFalse (.identifier an (ha ▸ av))
    · exact .andTrue (.identifier an (ha ▸ av)) (.identifier bn bv)
    · exact .orFalse (.identifier an (ha ▸ av)) (.identifier bn bv)
    · exact .orTrue (.identifier an (ha ▸ av))
  have ac : f.environment.values[f.ai]? = some (.bool f.left) :=
    (Resolved.LocalScope.lookup_iff_getElem? (f.aligned.symm ▸ f.ax)).mp f.av
  have bc : f.environment.values[f.bi]? = some (.bool f.right) :=
    (Resolved.LocalScope.lookup_iff_getElem? (f.aligned.symm ▸ f.bx)).mp f.bv
  have kg : Core.Evaluates (.word w :: f.environment.values) s (guardCore f.isOr (f.ai+1) (f.bi+1))
      (.bool (choose f.isOr f.left f.right)) s := by
    cases ho : f.isOr <;> cases ha : f.left
    · exact .ifFalse (.var (by simpa only [List.getElem?_cons_succ,ha] using ac)) .bool
    · exact .ifTrue (.var (by simpa only [List.getElem?_cons_succ,ha] using ac)) (.var bc)
    · exact .ifFalse (.var (by simpa only [List.getElem?_cons_succ,ha] using ac)) (.var bc)
    · exact .ifTrue (.var (by simpa only [List.getElem?_cons_succ,ha] using ac)) .bool
  have ce : ClosedSourceExpressionEvaluates f.owner (entry f.owner f.inputs).names
      (up (env f.owner f.inputs f.environment w)) (heap s) (expr f.spans f.isOr)
      (RuntimeValue.ofCore (result f.isOr f.left f.right w)) (heap s) := by
    cases hc : choose f.isOr f.left f.right <;> simp only [result,hc,Bool.false_eq_true,↓reduceIte,RuntimeValue.ofCore,up,env,List.map_cons]
    · exact .conditionalFalse (by simpa only [hc,up,env,List.map_cons,RuntimeValue.ofCore] using cg) (.bitNot (.reference .head .head))
    · exact .conditionalTrue (by simpa only [hc,up,env,List.map_cons,RuntimeValue.ofCore] using cg) (.reference .head .head)
  have le : LocalExpressionEvaluates (entry f.owner f.inputs).names (env f.owner f.inputs f.environment w)
      s (expr f.spans f.isOr) (result f.isOr f.left f.right w) s := by
    cases hc : choose f.isOr f.left f.right <;> simp only [result,hc,Bool.false_eq_true,↓reduceIte]
    · exact .ifFalse (hc ▸ lg) (.bitNot (.identifier .head .head))
    · exact .ifTrue (hc ▸ lg) (.identifier .head .head)
  have ke : Core.Evaluates (.word w :: f.environment.values) s (code f.isOr f.ai f.bi)
      (result f.isOr f.left f.right w) s := by
    cases hc : choose f.isOr f.left f.right <;> simp only [result,hc,Bool.false_eq_true,↓reduceIte]
    · exact .ifFalse (hc ▸ kg) (.unary (.var rfl) rfl)
    · exact .ifTrue (hc ▸ kg) (.var rfl)
  have expressionImages := (gate f.spans f.isOr).local_evaluates_iff (owner:=f.owner)
    (names:=(entry f.owner f.inputs).names) (environment:=env f.owner f.inputs f.environment w)
    (initialStore:=s) (actualValue:=RuntimeValue.ofCore (result f.isOr f.left f.right w)) (actualFinal:=heap s)
  obtain ⟨lv,ls,lvEq,lsEq,localRun⟩ := expressionImages.mp ce
  obtain ⟨lve,lse⟩ := localRun.deterministic le
  have independentReverse := expressionImages.mpr ⟨_,s,lvEq.trans (congrArg RuntimeValue.ofCore lve),
    lsEq.trans (congrArg heap lse),le⟩
  have ⟨resolved,resolution,lowering,_⟩ := elaborateLocalExpression?_iff.mp checkExpr
  have same : (env f.owner f.inputs f.environment w).ids = (entry f.owner f.inputs).context.ids := by
    simpa only [env,entry,LocalTypeInputs.bindFresh_context,Resolved.LocalScope.ids,List.map_cons] using congrArg (List.cons _) f.aligned
  have coreImage := (gate f.spans f.isOr).core_evaluates_iff resolution (same ▸ lowering) (owner:=f.owner)
    (initialStore:=s) (actualValue:=RuntimeValue.ofCore (result f.isOr f.left f.right w)) (actualFinal:=heap s)
  obtain ⟨kv,ks,kvEq,ksEq,coreRun⟩ := coreImage.mp independentReverse
  have originalCore : Core.Evaluates (env f.owner f.inputs f.environment w).values s
      (code f.isOr f.ai f.bi) (result f.isOr f.left f.right w) s := by
    simpa only [env,Resolved.LocalScope.values,List.map_cons] using ke
  obtain ⟨kve,kse⟩ := Core.evaluation_deterministic coreRun originalCore
  have rebuilt := coreImage.mpr ⟨_,s,kvEq.trans (congrArg RuntimeValue.ofCore kve),
    ksEq.trans (congrArg heap kse),originalCore⟩
  exact ⟨(elaborateComputationReturnTree?_iff (fun {_ _ _ _ _} => Iff.rfl)).mpr checked,
    (elaborateExpectedComputationLambda?_iff (fun {_ _ _ _ _} => Iff.rfl)).mpr
      (.lambda (.lambda .inferred .omitted) .word .word checked), .expression rebuilt, .expression le, ke⟩
private theorem exactImage {P : RuntimeValue → List RuntimeValue → Prop} {e s c v}
    (old : Core.Evaluates e s c v s)
    (image : ∀ a z, P a z ↔ ∃ x t, a=RuntimeValue.ofCore x ∧ z=heap t ∧ Core.Evaluates e s c x t) :
    ∀ a z, P a z ↔ a=RuntimeValue.ofCore v ∧ z=heap s := by
  intro a z; constructor
  · intro actual; obtain ⟨x,t,hx,ht,run⟩ := (image a z).mp actual
    obtain ⟨rfl,rfl⟩ := Core.evaluation_deterministic run old; exact ⟨hx,ht⟩
  · rintro ⟨rfl,rfl⟩; exact (image _ _).mpr ⟨v,s,rfl,rfl,old⟩

theorem body_original_and_all_actual_images
    (spans : Nat → Syntax.SourceSpan) (owner : Resolved.DeclarationId) (inputs : LocalTypeInputs)
    (environment : Resolved.Environment) (store : Core.Store) (isOr left right : Bool) (word : Core.Word)
    (aid bid : Resolved.LocalId) (aligned : environment.ids=inputs.context.ids)
    (an : LocalNameTable.Lookup inputs.names "a" aid) (bn : LocalNameTable.Lookup inputs.names "b" bid)
    (aTyped : Resolved.LocalScope.Lookup inputs.context aid .bool) (bTyped : Resolved.LocalScope.Lookup inputs.context bid .bool)
    (av : Resolved.LocalScope.Lookup environment aid (.bool left)) (bv : Resolved.LocalScope.Lookup environment bid (.bool right)) :
    ∃ ai bi, ClosedSourceDataBody (body spans isOr) ∧
      elaborateExpectedComputationLambda? elaborateLocalExpression? [] owner inputs (source spans isOr)
        (.function .word .word) = some (.lambda .word .word (code isOr ai bi)) ∧
      ClosedSourceBodyEvaluates owner (entry owner inputs).names (up (env owner inputs environment word))
        (heap store) (body spans isOr) (RuntimeValue.ofCore (result isOr left right word)) (heap store) ∧
      ComputationReturnTreeEvaluates LocalExpressionEvaluates owner (entry owner inputs).names
        (env owner inputs environment word) store (body spans isOr) (result isOr left right word) store ∧
      Core.Evaluates (.word word :: environment.values) store (code isOr ai bi) (result isOr left right word) store ∧
      (∀ actual final, ClosedSourceBodyEvaluates owner (entry owner inputs).names (up (env owner inputs environment word))
        (heap store) (body spans isOr) actual final ↔ actual=RuntimeValue.ofCore (result isOr left right word) ∧ final=heap store) := by
  obtain ⟨ai,ax,_⟩ := aTyped.indexed; obtain ⟨bi,bx,_⟩ := bTyped.indexed
  let f : Frame := ⟨spans,owner,inputs,environment,isOr,left,right,aid,bid,ai,bi,aligned,an,bn,aTyped,bTyped,av,bv,ax,bx⟩
  have h := facts f store word
  have g : ClosedSourceDataBody (body spans isOr) := .expression (gate spans isOr)
  have same : (env owner inputs environment word).ids=(entry owner inputs).context.ids := by
    simpa only [env,entry,LocalTypeInputs.bindFresh_context,Resolved.LocalScope.ids,List.map_cons] using congrArg (List.cons _) aligned
  have localBack := g.local_evaluates_iff.mpr ⟨_,store,rfl,rfl,h.2.2.2.1⟩
  have localBoth := g.local_evaluates_iff.mpr (g.local_evaluates_iff.mp localBack)
  refine ⟨ai,bi,g,h.2.1,localBoth,h.2.2.2.1,h.2.2.2.2,?_⟩
  exact exactImage (by simpa only [env,Resolved.LocalScope.values,List.map_cons] using h.2.2.2.2)
    (fun _ _ => g.core_evaluates_iff h.1 same)

theorem calls_original_and_all_actual_images
    (spans : Nat → Syntax.SourceSpan) (owner : Resolved.DeclarationId) (inputs : LocalTypeInputs)
    (environment : Resolved.Environment) (store : Core.Store) (isOr left right : Bool) (word : Core.Word)
    (aid bid wid : Resolved.LocalId) (aligned : environment.ids=inputs.context.ids)
    (an : LocalNameTable.Lookup inputs.names "a" aid) (bn : LocalNameTable.Lookup inputs.names "b" bid)
    (aTyped : Resolved.LocalScope.Lookup inputs.context aid .bool) (bTyped : Resolved.LocalScope.Lookup inputs.context bid .bool)
    (av : Resolved.LocalScope.Lookup environment aid (.bool left)) (bv : Resolved.LocalScope.Lookup environment bid (.bool right))
    (wn : LocalNameTable.Lookup inputs.names "w" wid) (wv : Resolved.LocalScope.Lookup environment wid (.word word))
    (caller : Resolved.DeclarationId) (callerNames : LocalNameTable) (callerRows : Resolved.LocalScope RuntimeValue)
    (callee : Syntax.Expr) (actualClosure : RuntimeValue) (creationStore : List RuntimeValue)
    (created : ClosedSourceExpressionEvaluates owner inputs.names (up environment) (heap store)
      (source spans isOr) actualClosure creationStore)
    (fetched : ClosedSourceExpressionEvaluates caller callerNames callerRows creationStore callee actualClosure creationStore)
    (argument : Syntax.Expr) (argumentOld : ClosedSourceExpressionEvaluates caller callerNames callerRows creationStore
      argument (.word word) (heap store)) :
    actualClosure = .sourceClosure (source spans isOr) owner inputs.names (up environment) ∧ creationStore=heap store ∧
    ∃ ai bi wi, Core.Evaluates environment.values store
      (.apply (.lambda .word .word (code isOr ai bi)) (.var wi)) (result isOr left right word) store ∧
      ClosedSourceExpressionEvaluates owner inputs.names (up environment) (heap store)
        (call spans (source spans isOr) (ref (spans 21) "w")) (RuntimeValue.ofCore (result isOr left right word)) (heap store) ∧
      ClosedSourceExpressionEvaluates caller callerNames callerRows creationStore (call spans callee argument)
        (RuntimeValue.ofCore (result isOr left right word)) (heap store) ∧
      (∀ a z, ClosedSourceExpressionEvaluates owner inputs.names (up environment) (heap store)
        (call spans (source spans isOr) (ref (spans 21) "w")) a z ↔ a=RuntimeValue.ofCore (result isOr left right word) ∧ z=heap store) ∧
      (∀ a z, ClosedSourceExpressionEvaluates caller callerNames callerRows creationStore (call spans callee argument) a z ↔
        a=RuntimeValue.ofCore (result isOr left right word) ∧ z=heap store) := by
  obtain ⟨ai,ax,_⟩ := aTyped.indexed; obtain ⟨bi,bx,_⟩ := bTyped.indexed; obtain ⟨wi,wx,wget⟩ := wv.indexed
  let f : Frame := ⟨spans,owner,inputs,environment,isOr,left,right,aid,bid,ai,bi,aligned,an,bn,aTyped,bTyped,av,bv,ax,bx⟩
  have h := facts f store word
  have made : ClosedSourceExpressionEvaluates owner inputs.names (up environment) (heap store)
      (source spans isOr) (.sourceClosure (source spans isOr) owner inputs.names (up environment)) (heap store) := .creation .inferred
  have equal := created.deterministic made
  have originalArg : ClosedSourceExpressionEvaluates owner inputs.names (up environment) (heap store)
      (ref (spans 21) "w") (.word word) (heap store) := .reference wn (by simpa only [RuntimeValue.ofCore] using mapped wv)
  have beta : ClosedSourceBodyEvaluates owner (("p",Resolved.freshLocalId owner (inputs.names.map Prod.snd))::inputs.names)
      ((Resolved.freshLocalId owner (inputs.names.map Prod.snd),.word word)::up environment)
      (heap store) (body spans isOr) (RuntimeValue.ofCore (result isOr left right word)) (heap store) := by
    simpa only [f,entry,env,LocalTypeInputs.bindFresh_names,LocalTypeInputs.names_ids,up,List.map_cons,RuntimeValue.ofCore] using h.2.2.1
  have savedCallee : ClosedSourceExpressionEvaluates caller callerNames callerRows creationStore callee
      (.sourceClosure (source spans isOr) owner inputs.names (up environment)) creationStore := equal.1 ▸ fetched
  have directOld := ClosedSourceExpressionEvaluates.call (span:=spans 19) (argumentsSpan:=spans 20) .inferred made originalArg beta
  have savedOld := ClosedSourceExpressionEvaluates.call (span:=spans 19) (argumentsSpan:=spans 20) .inferred savedCallee argumentOld beta
  have core : Core.Evaluates environment.values store (.apply (.lambda .word .word (code isOr ai bi)) (.var wi))
      (result isOr left right word) store := .apply .lambda (.var wget) h.2.2.2.2
  refine ⟨equal.1,equal.2,ai,bi,wi,core,directOld,savedOld,?_,?_⟩
  · exact exactImage core (fun _ _ => closedSourceExpectedDataLambda_application_core_iff .inferred
      (.expression (gate spans isOr)) h.2.1 aligned .reference (.identifier wn) (.var wx))
  · exact exactImage h.2.2.2.2 (fun _ _ => closedSourceExpectedDataLambda_invocation_core_iff .inferred
      (.expression (gate spans isOr)) h.2.1 aligned savedCallee (by simpa only [RuntimeValue.ofCore,heap] using argumentOld))
end Tests.ExpectedWordShortCircuitDataImages
end

section
-- leanmerge: from Solcore.Test.FrontendExpectedWordStrictDataImageProperties
set_option autoImplicit false
namespace Tests.ExpectedWordStrictDataImages
open Solcore Solcore.Frontend
private def up (e : Resolved.Environment) := e.map (fun r => (r.1,RuntimeValue.ofCore r.2))
private def heap (s : Core.Store) := s.map RuntimeValue.ofCore
private def one : Core.Word := Core.Word.ofNatModulo 1
private def two : Core.Word := Core.Word.ofNatModulo 2
private def ref (s : Nat → Syntax.SourceSpan) (i : Nat) (n : String) : Syntax.Expr :=
  ⟨s i,.identifier ⟨s (i+1),n⟩⟩
private def lit (s : Nat → Syntax.SourceSpan) (i : Nat) (n : String) : Syntax.Expr :=
  ⟨s i,.literal ⟨s (i+1),.decimal n⟩⟩
private def init (s : Nat → Syntax.SourceSpan) : Syntax.Expr :=
  ⟨s 4,.binary (ref s 0 "p") ⟨s 5,.add⟩ (lit s 2 "1")⟩
private def returned (s : Nat → Syntax.SourceSpan) : Syntax.Expr :=
  ⟨s 23,.conditional ⟨s 12,.group ⟨s 10,.binary (ref s 6 "p") ⟨s 11,.less⟩ (lit s 8 "2")⟩⟩
    (s 24) ⟨s 17,.binary (ref s 13 "p") ⟨s 18,.multiply⟩ (lit s 15 "2")⟩
    (s 25) ⟨s 21,.unary ⟨s 22,.bitNot⟩ (ref s 19 "p")⟩⟩
private def annotation (s : Nat → Syntax.SourceSpan) : Syntax.TypeExpr :=
  ⟨s 26,.named ⟨s 27,⟨⟨⟨s 28,"Word"⟩,[]⟩⟩⟩ none⟩
private def body (s : Nat → Syntax.SourceSpan) : Syntax.Block :=
  ⟨s 29,[⟨s 30,.letDecl ⟨s 31,"p"⟩ (some (annotation s)) (some (init s))⟩,
    ⟨s 32,.returnStmt (some (returned s))⟩]⟩
private def source (s : Nat → Syntax.SourceSpan) : Syntax.Expr :=
  ⟨s 33,.lambda (s 34) ⟨s 35,[⟨s 36,.inferred ⟨s 37,"p"⟩⟩]⟩ none (body s)⟩
private def call (s : Nat → Syntax.SourceSpan) (fn arg : Syntax.Expr) : Syntax.Expr := ⟨s 38,.call fn ⟨s 39,[arg]⟩⟩
private def argument (s : Nat → Syntax.SourceSpan) : Syntax.Expr :=
  ⟨s 44,.binary (ref s 40 "c") ⟨s 45,.add⟩ (lit s 42 "1")⟩
private def decision (w : Core.Word) := decide (w.add one < two)
private def value (w : Core.Word) : Core.Value := .word (if decision w then (w.add one).mul two else (w.add one).bitNot)
private def retCore : Core.Expr := .ifE ((Core.Expr.var 0).wordLt (.word two))
  (.binary .wordMul (.var 0) (.word two)) (.unary .wordNot (.var 0))
private def core : Core.Expr := .letE (.binary .wordAdd (.var 0) (.word one)) retCore
private def cost (w : Core.Word) : Nat := 5 + (11 + (if decision w then 5 else 3) + 2) + 2
private def entry (o : Resolved.DeclarationId) (t : LocalTypeInputs) := t.bindFresh o "p" .word
private def env (o : Resolved.DeclarationId) (t : LocalTypeInputs) (e : Resolved.Environment) (w : Core.Word) : Resolved.Environment :=
  (Resolved.freshLocalId o t.ids,.word w)::e
private theorem literalOne (s : Syntax.SourceSpan) : WordLiteralDenotes ⟨s,.decimal "1"⟩ one := interpretWordLiteral?_iff.mp (by rfl)
private theorem literalTwo (s : Syntax.SourceSpan) : WordLiteralDenotes ⟨s,.decimal "2"⟩ two := interpretWordLiteral?_iff.mp (by rfl)
private theorem mapped {e : Resolved.Environment} {i : Resolved.LocalId} {v : Core.Value}
    (h : Resolved.LocalScope.Lookup e i v) : Resolved.LocalScope.Lookup (up e) i (RuntimeValue.ofCore v) := by
  induction h with | head => exact .head | tail ne _ ih => exact .tail ne ih
private theorem gate (s : Nat → Syntax.SourceSpan) : ClosedSourceDataBody (body s) := by
  refine .binding (.strictWordBinary .reference .literal (by decide) (by decide)) (.expression ?_)
  exact .conditional (.group (.strictWordBinary .reference .literal (by decide) (by decide)))
    (.strictWordBinary .reference .literal (by decide) (by decide)) (.bitNot .reference)
private theorem facts (s : Nat → Syntax.SourceSpan) (o : Resolved.DeclarationId) (t : LocalTypeInputs)
    (e : Resolved.Environment) (st : Core.Store) (w : Core.Word) (same : e.ids=t.context.ids) :
    elaborateComputationReturnTree? elaborateLocalExpression? [(["Word"],.word)] o (entry o t) (body s) = some (core,.word) ∧
    elaborateExpectedComputationLambda? elaborateLocalExpression? [(["Word"],.word)] o t (source s)
      (.function .word .word) = some (.lambda .word .word core) ∧
    ClosedSourceBodyEvaluates o (entry o t).names (up (env o t e w)) (heap st) (body s) (RuntimeValue.ofCore (value w)) (heap st) ∧
    ComputationReturnTreeEvaluates LocalExpressionEvaluates o (entry o t).names (env o t e w) st (body s) (value w) st ∧
    (∀ k, Core.Steps (cost w) ⟨.eval core (.word w::e.values),k,st⟩ ⟨.ret (value w),k,st⟩) := by
  let ti := entry o t
  let ei := env o t e w
  let tr := entry o ti
  let er := env o ti ei (w.add one)
  have si : ei.ids=ti.context.ids := by
    simpa only [ei,ti,env,entry,LocalTypeInputs.bindFresh_context,Resolved.LocalScope.ids,List.map_cons] using congrArg (List.cons _) same
  have sr : er.ids=tr.context.ids := by
    simpa only [er,tr,env,entry,LocalTypeInputs.bindFresh_context,Resolved.LocalScope.ids,List.map_cons] using congrArg (List.cons _) si
  have ic : elaborateLocalExpression? ti.names ti.context (init s) = some (.binary .wordAdd (.var 0) (.word one),.word) :=
    elaborateLocalExpression?_complete (.add (.identifier .head) (.wordLiteral (literalOne _))) (.binary (.var .head) .word) (.binary (.var .head) .word)
  have rc : elaborateLocalExpression? tr.names tr.context (returned s) = some (retCore,.word) :=
    elaborateLocalExpression?_complete
      (.conditional (.group (.less (.identifier .head) (.wordLiteral (literalTwo _))))
        (.multiply (.identifier .head) (.wordLiteral (literalTwo _))) (.bitNot (.identifier .head)))
      (.ifE (.wordLt (.var .head) .word) (.binary (.var .head) .word) (.unary (.var .head)))
      (.ifE (.wordLt (.var .head) .word) (.binary (.var .head) .word) (.unary (.var .head)))
  have il : LocalExpressionEvaluatesWithCost ti.names ei st (init s) (.word (w.add one)) st 5 := by
    simp only [ti,ei,entry,env,LocalTypeInputs.bindFresh_names,init,ref,lit]
    apply LocalExpressionEvaluatesWithCost.add (leftValue:=w) (rightValue:=one) (leftCost:=1) (rightCost:=1)
    · exact .identifier .head .head
    · exact .wordLiteral (literalOne _)
  have ig : ClosedSourceExpressionEvaluates o ti.names (up ei) (heap st) (init s) (.word (w.add one)) (heap st) := by
    simp only [ti,ei,entry,env,LocalTypeInputs.bindFresh_names,up,List.map_cons,RuntimeValue.ofCore,init,ref,lit]
    simpa only [RuntimeValue.ofCore] using ClosedSourceExpressionEvaluates.strictWordBinary
      (leftWord:=w) (rightWord:=one) (span:=s 4) (operatorSpan:=s 5)
      (.reference (span:=s 0) (name:=⟨s 1,"p"⟩) .head .head)
      (.wordLiteral (span:=s 2) (literalOne (s 3))) StrictWordBinaryDenotes.add
  have rl : LocalExpressionEvaluatesWithCost tr.names er st (returned s) (value w) st
      (11+(if decision w then 5 else 3)+2) := by
    have cmp : LocalExpressionEvaluatesWithCost tr.names er st
        ⟨s 12,.group ⟨s 10,.binary (ref s 6 "p") ⟨s 11,.less⟩ (lit s 8 "2")⟩⟩ (.bool (decision w)) st 11 := by
      simp only [decision,tr,er,entry,env,LocalTypeInputs.bindFresh_names,ref,lit]
      apply LocalExpressionEvaluatesWithCost.group
      apply LocalExpressionEvaluatesWithCost.less (leftValue:=w.add one) (rightValue:=two) (leftCost:=1) (rightCost:=1)
      · exact .identifier .head .head
      · exact .wordLiteral (literalTwo _)
    cases h : decision w <;> simp only [value,h,Bool.false_eq_true,↓reduceIte]
    · exact .ifFalse (h ▸ cmp) (.bitNot (.identifier .head .head))
    · apply LocalExpressionEvaluatesWithCost.ifTrue (h ▸ cmp)
      simp only [tr,er,entry,env,LocalTypeInputs.bindFresh_names,ref,lit]
      apply LocalExpressionEvaluatesWithCost.multiply (leftValue:=w.add one) (rightValue:=two) (leftCost:=1) (rightCost:=1)
      · exact .identifier .head .head
      · exact .wordLiteral (literalTwo _)
  have rg : ClosedSourceExpressionEvaluates o tr.names (up er) (heap st) (returned s)
      (RuntimeValue.ofCore (value w)) (heap st) := by
    have cmp : ClosedSourceExpressionEvaluates o tr.names (up er) (heap st)
        ⟨s 12,.group ⟨s 10,.binary (ref s 6 "p") ⟨s 11,.less⟩ (lit s 8 "2")⟩⟩ (.bool (decision w)) (heap st) :=
      by
        simp only [tr,er,entry,env,LocalTypeInputs.bindFresh_names,up,List.map_cons,RuntimeValue.ofCore,ref,lit,decision]
        apply ClosedSourceExpressionEvaluates.group
        simpa only [RuntimeValue.ofCore] using ClosedSourceExpressionEvaluates.strictWordBinary
          (leftWord:=w.add one) (rightWord:=two) (span:=s 10) (operatorSpan:=s 11)
          (.reference (span:=s 6) (name:=⟨s 7,"p"⟩) .head .head)
          (.wordLiteral (span:=s 8) (literalTwo (s 9))) StrictWordBinaryDenotes.less
    cases h : decision w <;> simp only [value,h,Bool.false_eq_true,↓reduceIte,RuntimeValue.ofCore]
    · apply ClosedSourceExpressionEvaluates.conditionalFalse (h ▸ cmp)
      simp only [tr,er,entry,env,LocalTypeInputs.bindFresh_names,up,List.map_cons,RuntimeValue.ofCore]
      exact .bitNot (.reference .head .head)
    · apply ClosedSourceExpressionEvaluates.conditionalTrue (h ▸ cmp)
      simp only [tr,er,entry,env,LocalTypeInputs.bindFresh_names,up,List.map_cons,RuntimeValue.ofCore,ref,lit]
      simpa only [RuntimeValue.ofCore] using ClosedSourceExpressionEvaluates.strictWordBinary
        (leftWord:=w.add one) (rightWord:=two) (span:=s 17) (operatorSpan:=s 18)
        (.reference (span:=s 13) (name:=⟨s 14,"p"⟩) .head .head)
        (.wordLiteral (span:=s 15) (literalTwo (s 16))) StrictWordBinaryDenotes.multiply
  have cb : ClosedSourceBodyEvaluates o ti.names (up ei) (heap st) (body s) (RuntimeValue.ofCore (value w)) (heap st) := by
    apply ClosedSourceBodyEvaluates.binding ig
    simpa only [tr,er,entry,env,LocalTypeInputs.bindFresh_names,LocalTypeInputs.names_ids,up,List.map_cons,RuntimeValue.ofCore] using ClosedSourceBodyEvaluates.expression rg
  have lb : ComputationReturnTreeEvaluates LocalExpressionEvaluates o ti.names ei st (body s) (value w) st := by
    apply ComputationReturnTreeEvaluates.binding il.erase
    simpa only [tr,er,entry,env,LocalTypeInputs.bindFresh_names,LocalTypeInputs.names_ids] using ComputationReturnTreeEvaluates.expression rl.erase
  have bc : ComputationReturnTreeElaborates (fun n t s c ty => elaborateLocalExpression? n t s=some (c,ty)) [(["Word"],.word)] o ti (body s) core .word :=
    .binding (.named .head) ic (.expression rc)
  obtain ⟨ri,resi,lowi,_⟩ := elaborateLocalExpression?_iff.mp ic
  obtain ⟨rr,resr,lowr,_⟩ := elaborateLocalExpression?_iff.mp rc
  have kp (k) := CostStepComposition.letE (il.toStepsWithContinuation resi (si ▸ lowi) _)
    (rl.toStepsWithContinuation resr (sr ▸ lowr) k)
  exact ⟨(elaborateComputationReturnTree?_iff (fun {_ _ _ _ _} => Iff.rfl)).mpr bc,
    (elaborateExpectedComputationLambda?_iff (fun {_ _ _ _ _} => Iff.rfl)).mpr
      (.lambda (.lambda .inferred .omitted) .word .word bc),cb,lb,
    fun k => by simpa only [ei,er,env,Resolved.LocalScope.values,List.map_cons,cost,core] using kp k⟩
private theorem exactImage {P : RuntimeValue → List RuntimeValue → Prop} {e st c v}
    (old : Core.Evaluates e st c v st)
    (image : ∀ a z, P a z ↔ ∃ x t, a=RuntimeValue.ofCore x ∧ z=heap t ∧ Core.Evaluates e st c x t) :
    ∀ a z, P a z ↔ a=RuntimeValue.ofCore v ∧ z=heap st := by
  intro a z; constructor
  · intro actual; obtain ⟨x,t,hx,ht,run⟩ := (image a z).mp actual
    obtain ⟨rfl,rfl⟩ := Core.evaluation_deterministic run old; exact ⟨hx,ht⟩
  · rintro ⟨rfl,rfl⟩; exact (image _ _).mpr ⟨v,st,rfl,rfl,old⟩

theorem body_original_and_all_actual_images (s : Nat → Syntax.SourceSpan) (o : Resolved.DeclarationId)
    (t : LocalTypeInputs) (e : Resolved.Environment) (st : Core.Store) (w : Core.Word) (same : e.ids=t.context.ids) :
    ClosedSourceDataBody (body s) ∧
    elaborateExpectedComputationLambda? elaborateLocalExpression? [(["Word"],.word)] o t (source s)
      (.function .word .word) = some (.lambda .word .word core) ∧
    ClosedSourceBodyEvaluates o (entry o t).names (up (env o t e w)) (heap st) (body s) (RuntimeValue.ofCore (value w)) (heap st) ∧
    ComputationReturnTreeEvaluates LocalExpressionEvaluates o (entry o t).names (env o t e w) st (body s) (value w) st ∧
    (∀ k, Core.Steps (cost w) ⟨.eval core (.word w::e.values),k,st⟩ ⟨.ret (value w),k,st⟩) ∧
    (∀ a z, ClosedSourceBodyEvaluates o (entry o t).names (up (env o t e w)) (heap st) (body s) a z ↔
      a=RuntimeValue.ofCore (value w) ∧ z=heap st) := by
  have h := facts s o t e st w same
  have si : (env o t e w).ids=(entry o t).context.ids := by
    simpa only [env,entry,LocalTypeInputs.bindFresh_context,Resolved.LocalScope.ids,List.map_cons] using congrArg (List.cons _) same
  have original := h.2.2.1
  have localForward := (gate s).local_evaluates_iff.mp original
  have localReverse : ClosedSourceBodyEvaluates o (entry o t).names (up (env o t e w)) (heap st) (body s) (RuntimeValue.ofCore (value w)) (heap st) :=
    (gate s).local_evaluates_iff.mpr ⟨_,st,rfl,rfl,h.2.2.2.1⟩
  refine ⟨gate s,h.2.1,localReverse,h.2.2.2.1,h.2.2.2.2,?_⟩
  have coreOld : Core.Evaluates (env o t e w).values st core (value w) st := by
    simpa only [env,Resolved.LocalScope.values,List.map_cons] using Core.steps_from_initial_sound (h.2.2.2.2 [])
  intro a z
  have exactCore := exactImage coreOld (fun _ _ => (gate s).core_evaluates_iff h.1 si) a z
  constructor
  · intro actual
    have both := (gate s).local_evaluates_iff.mpr ((gate s).local_evaluates_iff.mp actual)
    exact exactCore.mp both
  · intro endpoint
    have actual := exactCore.mpr endpoint
    exact (gate s).local_evaluates_iff.mpr ((gate s).local_evaluates_iff.mp actual)

theorem calls_original_and_all_actual_images (s : Nat → Syntax.SourceSpan) (o : Resolved.DeclarationId)
    (t : LocalTypeInputs) (e : Resolved.Environment) (st : Core.Store) (c : Core.Word) (same : e.ids=t.context.ids)
    (id : Resolved.LocalId) (named : LocalNameTable.Lookup t.names "c" id)
    (found : Resolved.LocalScope.Lookup e id (.word c))
    (i : Nat) (ix : Resolved.LocalScope.IndexOf e.ids id i)
    (caller : Resolved.DeclarationId) (names : LocalNameTable) (rows : Resolved.LocalScope RuntimeValue)
    (callee arg : Syntax.Expr) (actualClosure : RuntimeValue) (creationStore : List RuntimeValue)
    (created : ClosedSourceExpressionEvaluates o t.names (up e) (heap st) (source s) actualClosure creationStore)
    (fetched : ClosedSourceExpressionEvaluates caller names rows creationStore callee actualClosure creationStore)
    (argumentOld : ClosedSourceExpressionEvaluates caller names rows creationStore arg (.word (c.add one)) (heap st)) :
    actualClosure=.sourceClosure (source s) o t.names (up e) ∧ creationStore=heap st ∧
    (∀ k, Core.Steps (1+5+cost (c.add one)+3)
      ⟨.eval (.apply (.lambda .word .word core) (.binary .wordAdd (.var i) (.word one))) e.values,k,st⟩
      ⟨.ret (value (c.add one)),k,st⟩) ∧
    ClosedSourceExpressionEvaluates o t.names (up e) (heap st) (call s (source s) (argument s)) (RuntimeValue.ofCore (value (c.add one))) (heap st) ∧
    ClosedSourceExpressionEvaluates caller names rows creationStore (call s callee arg) (RuntimeValue.ofCore (value (c.add one))) (heap st) ∧
    (∀ a z, ClosedSourceExpressionEvaluates o t.names (up e) (heap st) (call s (source s) (argument s)) a z ↔ a=RuntimeValue.ofCore (value (c.add one)) ∧ z=heap st) ∧
    (∀ a z, ClosedSourceExpressionEvaluates caller names rows creationStore (call s callee arg) a z ↔ a=RuntimeValue.ofCore (value (c.add one)) ∧ z=heap st) := by
  have h := facts s o t e st (c.add one) same
  have made : ClosedSourceExpressionEvaluates o t.names (up e) (heap st) (source s) (.sourceClosure (source s) o t.names (up e)) (heap st) := .creation .inferred
  have ceq := created.deterministic made
  have mapped : Resolved.LocalScope.Lookup (up e) id (.word c) := by simpa only [RuntimeValue.ofCore] using mapped found
  have aold : ClosedSourceExpressionEvaluates o t.names (up e) (heap st) (argument s) (.word (c.add one)) (heap st) := by
    simp only [argument,ref,lit]
    simpa only [RuntimeValue.ofCore] using ClosedSourceExpressionEvaluates.strictWordBinary
      (leftWord:=c) (rightWord:=one) (span:=s 44) (operatorSpan:=s 45)
      (.reference (span:=s 40) (name:=⟨s 41,"c"⟩) named mapped)
      (.wordLiteral (span:=s 42) (literalOne (s 43))) StrictWordBinaryDenotes.add
  have al : LocalExpressionEvaluatesWithCost t.names e st (argument s) (.word (c.add one)) st 5 :=
    .add (.identifier named found) (.wordLiteral (literalOne _))
  have res : ResolvesLocalExpression t.names (argument s) (.binary .wordAdd (.var id) (.word one)) := .add (.identifier named) (.wordLiteral (literalOne _))
  have low : Resolved.Lowers e.ids (.binary .wordAdd (.var id) (.word one)) (.binary .wordAdd (.var i) (.word one)) := .binary (.var ix) .word
  have beta : ClosedSourceBodyEvaluates o (("p",Resolved.freshLocalId o (t.names.map Prod.snd))::t.names)
      ((Resolved.freshLocalId o (t.names.map Prod.snd),.word (c.add one))::up e) (heap st) (body s) (RuntimeValue.ofCore (value (c.add one))) (heap st) := by
    simpa only [entry,env,LocalTypeInputs.bindFresh_names,LocalTypeInputs.names_ids,up,List.map_cons,RuntimeValue.ofCore] using h.2.2.1
  have sf : ClosedSourceExpressionEvaluates caller names rows creationStore callee (.sourceClosure (source s) o t.names (up e)) creationStore := ceq.1 ▸ fetched
  have direct := ClosedSourceExpressionEvaluates.call (span:=s 38) (argumentsSpan:=s 39) .inferred made aold beta
  have saved := ClosedSourceExpressionEvaluates.call (span:=s 38) (argumentsSpan:=s 39) .inferred sf argumentOld beta
  have path (k) := CostStepComposition.apply (continuation:=k) (parameterType:=.word) (resultType:=.word)
    (.cons .lambda .refl) (al.toStepsWithContinuation res low _) (h.2.2.2.2 [])
  refine ⟨ceq.1,ceq.2,path,direct,saved,?_,?_⟩
  · exact exactImage (Core.steps_from_initial_sound (path [])) (fun _ _ => closedSourceExpectedDataLambda_application_core_iff .inferred
      (gate s) h.2.1 same (.strictWordBinary .reference .literal (by decide) (by decide)) res low)
  · exact exactImage (Core.steps_from_initial_sound (h.2.2.2.2 [])) (fun _ _ => closedSourceExpectedDataLambda_invocation_core_iff .inferred
      (gate s) h.2.1 same sf (by simpa only [RuntimeValue.ofCore,heap] using argumentOld))
end Tests.ExpectedWordStrictDataImages
end

section
-- leanmerge: from Solcore.Test.FrontendExpectedWordUnaryDataImageProperties
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
end

section
-- leanmerge: from Solcore.Test.FrontendParsedExpectedBoolStrictDataBridge
set_option autoImplicit false
namespace Tests.ParsedExpectedBoolStrictDataBridge
open Solcore Solcore.Frontend Tests.ExpectedBoolStrictDataImages
private def check (ok : Bool) (message : String) : IO Unit := unless ok do throw (IO.userError message)
private def proof {p : Prop} (_ : p) : IO Unit := pure ()
private def owner : Resolved.DeclarationId := ⟨⟨.main,⟨[⟨"StrictBoolData",by decide⟩],by decide⟩⟩,301⟩
private def caller := {owner with declarationIndex:=9301}
private def sid (n : Nat) : Resolved.LocalId := ⟨owner,n⟩
private def cid (n : Nat) : Resolved.LocalId := ⟨caller,n⟩
private def fid : Resolved.LocalId := ⟨{owner with declarationIndex:=900},900⟩
private def inputs : LocalTypeInputs := ⟨[⟨"p",sid 7,.unit⟩,⟨"c",sid 31,.word⟩,⟨"p",fid,.unit⟩],by decide⟩
private def old : Core.Value := .closure .unit .word (.var 99) [.hostFunction .storageWrite,.cellRef .word 700]
private def env (w : Core.Word) : Resolved.Environment := [(sid 7,old),(sid 31,.word w),(fid,old)]
private def callerNames : LocalNameTable := [("picked",cid 7),("c",cid 31),("c",cid 31),("p",fid)]
private def callerRows (fn : RuntimeValue) (w : Core.Word) : Resolved.LocalScope RuntimeValue :=
  [(cid 7,fn),(cid 31,.word w),(cid 31,RuntimeValue.ofCore old),(fid,fn),(cid 7,.unit)]
private def directText := "lam(p){let p:Word=p + 1;return !(p < 2) && (p >= 2);}(c + 1)"
private def range (f : Syntax.SourceFile) (a b : Nat) : Syntax.SourceSpan := ⟨f.id,a,b⟩
private def ranges : List (Nat × Nat) :=
  [(0,53),(0,3),(3,6),(4,5),(4,5),(6,53),(7,24),(11,12),(13,17),(18,23),(18,19),(20,21),(22,23),
   (24,52),(31,51),(31,39),(31,32),(32,39),(33,38),(33,34),(35,36),(37,38),(40,42),(43,51),
   (44,50),(44,45),(46,48),(49,50),(54,59),(54,55),(56,57),(58,59),(0,60),(53,60)]
private def spans (f : Syntax.SourceFile) (i : Nat) : Syntax.SourceSpan :=
  let p := ranges[i]?.getD (0,0); range f p.1 p.2
private def savedSpans (f : Syntax.SourceFile) (i : Nat) : Syntax.SourceSpan :=
  let p := if i=28 then (7,12) else if i=29 then (7,8) else if i=30 then (9,10)
    else if i=31 then (11,12) else if i=32 then (0,13) else if i=33 then (6,13) else (0,0)
  range f p.1 p.2
private def exactTree (a b : Syntax.Expr) : Option (PLift (a=b)) :=
  match a,b with
  | ⟨s,.identifier n⟩,⟨t,.identifier m⟩ =>
    if h : (s,n)=(t,m) then some ⟨by rcases Prod.mk.inj h with ⟨rfl,rfl⟩; rfl⟩ else none
  | ⟨s,.literal n⟩,⟨t,.literal m⟩ =>
    if h : (s,n)=(t,m) then some ⟨by rcases Prod.mk.inj h with ⟨rfl,rfl⟩; rfl⟩ else none
  | ⟨s,.group x⟩,⟨t,.group y⟩ =>
    if h : s=t then match exactTree x y with
      | some ⟨e⟩ => some ⟨by cases h; cases e; rfl⟩ | none => none
    else none
  | ⟨s,.unary op x⟩,⟨t,.unary oq y⟩ =>
    if h : (s,op)=(t,oq) then match exactTree x y with
      | some ⟨e⟩ => some ⟨by rcases Prod.mk.inj h with ⟨rfl,rfl⟩; cases e; rfl⟩ | none => none
    else none
  | ⟨s,.binary x op y⟩,⟨t,.binary z oq w⟩ =>
    if h : (s,op)=(t,oq) then match exactTree x z,exactTree y w with
      | some ⟨e⟩,some ⟨f⟩ => some ⟨by rcases Prod.mk.inj h with ⟨rfl,rfl⟩; cases e; cases f; rfl⟩ | _,_ => none
    else none
  | ⟨s,.call x ⟨ps,[y]⟩⟩,⟨t,.call z ⟨pt,[w]⟩⟩ =>
    if h : (s,ps)=(t,pt) then match exactTree x z,exactTree y w with
      | some ⟨e⟩,some ⟨f⟩ => some ⟨by rcases Prod.mk.inj h with ⟨rfl,rfl⟩; cases e; cases f; rfl⟩ | _,_ => none
    else none
  | ⟨s,.lambda k ⟨ps,[⟨p,.inferred n⟩]⟩ none ⟨bs,[⟨ls,.letDecl name (some ⟨ann,.named qn none⟩) (some x)⟩,⟨rs,.returnStmt (some y)⟩]⟩⟩,
    ⟨t,.lambda j ⟨pt,[⟨q,.inferred m⟩]⟩ none ⟨bt,[⟨lt,.letDecl other (some ⟨annt,.named qm none⟩) (some z)⟩,⟨rt,.returnStmt (some w)⟩]⟩⟩ =>
    if h : [s,k,ps,p,bs,ls,ann,rs]=[t,j,pt,q,bt,lt,annt,rt] ∧ (n,name,qn)=(m,other,qm) then
      match exactTree x z,exactTree y w with
      | some ⟨e⟩,some ⟨f⟩ => some ⟨by
          simp only [List.cons.injEq,Prod.mk.injEq] at h
          rcases h with ⟨⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,_⟩,rfl,rfl,rfl⟩
          cases e; cases f; rfl⟩
      | _,_ => none
    else none
  | _,_ => none
termination_by sizeOf a
private def parsed (f : Syntax.SourceFile) (expected : Syntax.Expr) : IO {actual : Syntax.Expr // actual=expected} := do
  let .ok lexed := Syntax.Lexer.lex f | throw (IO.userError "lexer")
  match Syntax.Parser.expression (Syntax.Parser.State.initial f lexed) with
  | .ok actual next =>
    check (next.file==f && lexed.diagnostics.isEmpty && next.diagnostics.isEmpty && next.atEnd &&
      actual.span==Syntax.SourceSpan.fullFile f) "whole actual SourceFile/EOF/diagnostics"
    match exactTree actual expected with
    | some ⟨h⟩ => return ⟨actual,h⟩
    | none => throw (IO.userError "whole handwritten AST and every nested range")
  | _ => throw (IO.userError "parser")
private structure Trace (o : Resolved.DeclarationId) (n : LocalNameTable) (e : Resolved.LocalScope RuntimeValue)
    (st : List RuntimeValue) (src : Syntax.Expr) where
  value : RuntimeValue
  final : List RuntimeValue
  original : ClosedSourceExpressionEvaluates o n e st src value final
  storeEq : final=st
private def observe {o n e st src v} (d : Nat)
    (original : ClosedSourceExpressionEvaluates o n e st src v st) : IO (Trace o n e st src) := do
  proof original
  match run : evaluateClosedSourceExpression? d o n e st src with
  | none => throw (IO.userError "actual expression endpoint")
  | some (a,z) =>
    have same := (evaluateClosedSourceExpression?_sound run).deterministic original
    return ⟨a,z,by rw [same.1,same.2]; exact original,same.2⟩
private structure BodyTrace (o : Resolved.DeclarationId) (n : LocalNameTable) (e : Resolved.LocalScope RuntimeValue)
    (st : List RuntimeValue) (src : Syntax.Block) where
  value : RuntimeValue
  final : List RuntimeValue
  original : ClosedSourceBodyEvaluates o n e st src value final
private def observeBody {o n e st src v} (d : Nat)
    (original : ClosedSourceBodyEvaluates o n e st src v st) : IO (BodyTrace o n e st src) := do
  proof original
  match run : evaluateClosedSourceBody? d o n e st src with
  | none => throw (IO.userError "actual saved body endpoint")
  | some (a,z) =>
    have same := (evaluateClosedSourceBody?_sound run).deterministic original
    return ⟨a,z,by rw [same.1,same.2]; exact original⟩
private def runCore {e st c v k} (steps : Core.Steps k (.initial c e st) (.final v st)) : IO Unit := do
  proof steps
  for fuel in [0,k-1,k,k+3] do
    match run : Core.runStateful fuel (.initial c e st) with
    | .done a z =>
      have same := Core.evaluation_deterministic (Core.runStateful_evaluation_sound run) (Core.steps_from_initial_sound steps)
      proof same; proof (steps.runStateful_done_iff.mp (by simpa only [same.1,same.2] using run))
      check (a==v && z==st && fuel≥k) "all actual Core values/stores and exact cost"
    | .outOfFuel suspended => proof (steps.runStateful_outOfFuel_iff.mp ⟨suspended,run⟩); check (fuel<k) "Core exhaustion"
    | _ => throw (IO.userError "Core stuck")
private def runClosed {o n e st src v} (d : Nat)
    (original : ClosedSourceExpressionEvaluates o n e st src v st)
    (image : ∀ a z, ClosedSourceExpressionEvaluates o n e st src a z ↔ a=v ∧ z=st) : IO Unit := do
  proof original
  for depth in [0,d-1,d,d+3] do
    match run : evaluateClosedSourceExpression? depth o n e st src with
    | none => check (depth<d) "closed depth exhaustion"
    | some (a,z) =>
      have endpoints := (image a z).mp (evaluateClosedSourceExpression?_sound run)
      proof endpoints; proof ((image a z).mpr endpoints)
      check (depth≥d && reprStr a==reprStr v && reprStr z==reprStr st) "all actual closed endpoints"
private theorem exactOriginal {o n e st src v}
    (original : ClosedSourceExpressionEvaluates o n e st src v st) :
    ∀ a z, ClosedSourceExpressionEvaluates o n e st src a z ↔ a=v ∧ z=st := by
  intro a z; constructor
  · exact fun h => h.deterministic original
  · rintro ⟨rfl,rfl⟩; exact original
private theorem oneMeaning (s : Syntax.SourceSpan) : WordLiteralDenotes ⟨s,.decimal "1"⟩ one :=
  .decimal (by decide) (.cons (.decimal (digit:=1) (by decide) rfl) .nil)
private def exercise (w : Core.Word) (st : Core.Store) : IO Unit := do
  let f : Syntax.SourceFile := ⟨⟨.main,"strict-bool-direct.sol"⟩,directText⟩
  let s := spans f
  let ⟨actual,treeEq⟩ ← parsed f (call s (source s) (argument s))
  let g : Syntax.SourceFile := ⟨⟨.main,"strict-bool-saved.sol"⟩,"picked(c + 1)"⟩
  let q := savedSpans g
  let ⟨invoked,invokeEq⟩ ← parsed g (call q (ref (range g 0 6) "picked") (argument q))
  let fs := match actual.value with | .call fn _ => fn | _ => actual
  let actualArg := match actual.value with | .call _ ⟨_,[a]⟩ => a | _ => actual
  let actualBody := match fs.value with | .lambda _ _ _ b => b | _ => body s
  have fsEq : fs=source s := by simp only [fs,treeEq,call]
  have argEq : actualArg=argument s := by simp only [actualArg,treeEq,call]
  have bodyEq : actualBody=body s := by simp only [actualBody,fsEq,source]
  have shape : SourceUnaryLambdaShape fs ⟨s 4,"p"⟩ actualBody := by rw [fsEq,bodyEq]; exact .inferred
  let e := env w
  have aligned : e.ids=inputs.context.ids := rfl
  have b := body_evidence s owner inputs e st (w.add one) aligned
  have a := argument_paths s owner inputs.names e st w (sid 31) 1 (.tail (by decide) .head) (.tail (by decide) .head) (.tail (by decide) .head)
  have beta : ClosedSourceBodyEvaluates owner (("p",Resolved.freshLocalId owner (inputs.names.map Prod.snd))::inputs.names)
      ((Resolved.freshLocalId owner (inputs.names.map Prod.snd),.word (w.add one))::up e) (heap st) actualBody (RuntimeValue.ofCore (result (w.add one))) (heap st) := by
    simpa only [bodyEq,entered,entry,LocalTypeInputs.bindFresh_names,LocalTypeInputs.names_ids,up,List.map_cons,RuntimeValue.ofCore] using b.original
  have creation : ClosedSourceExpressionEvaluates owner inputs.names (up e) (heap st) fs (.sourceClosure fs owner inputs.names (up e)) (heap st) := .creation shape
  have argOriginal : ClosedSourceExpressionEvaluates owner inputs.names (up e) (heap st) actualArg (.word (w.add one)) (heap st) := argEq ▸ a.2.2.2.2
  have directOriginal : ClosedSourceExpressionEvaluates owner inputs.names (up e) (heap st) actual (RuntimeValue.ofCore (result (w.add one))) (heap st) := by
    have h := ClosedSourceExpressionEvaluates.call (span:=s 32) (argumentsSpan:=s 33) shape creation argOriginal beta
    simpa only [treeEq,fsEq,argEq,call] using h
  have argSteps := a.2.2.2.1.toStepsWithContinuation a.2.1 a.2.2.1
  have betaSteps := b.steps []
  have fullSteps : Core.Steps (1+5+bodyCost (w.add one)+3)
      (.initial (.apply (.lambda .word .bool code) (.binary .wordAdd (.var 1) (.word one))) e.values st)
      (.final (result (w.add one)) st) := CostStepComposition.apply (.cons .lambda .refl) (argSteps _) betaSteps
  proof creation; proof a.2.2.2.1.erase; proof b.old; proof beta; proof directOriginal; proof fullSteps
  check (bodyCost (w.add one)==if predicate ((w.add one).add one) then 35 else 23) "independent body cost"
  runCore fullSteps; runCore betaSteps; runCore (argSteps [])
  let directImage : ∀ v z, ClosedSourceExpressionEvaluates owner inputs.names (up e) (heap st) actual v z ↔
      v=RuntimeValue.ofCore (result (w.add one)) ∧ z=heap st := by
    intro v z; rw [treeEq]
    exact core_exact (Core.steps_from_initial_sound fullSteps)
      (fun _ _ => closedSourceExpectedDataLambda_application_core_iff .inferred b.admitted b.expected aligned a.1 a.2.1 a.2.2.1) v z
  runClosed 8 directOriginal directImage
  runClosed 1 creation (exactOriginal creation)
  let made ← observe 1 creation
  have madeEq := made.original.deterministic creation
  match madeShape : made.value with
  | .sourceClosure saved savedOwner savedNames savedRows =>
    have fields := RuntimeValue.sourceClosure.inj (show RuntimeValue.sourceClosure saved savedOwner savedNames savedRows =
        .sourceClosure fs owner inputs.names (up e) from by rw [← madeShape]; exact madeEq.1)
    check (saved==fs && savedOwner==owner && savedOwner != caller && savedNames==inputs.names &&
      reprStr savedRows==reprStr (up e)) "all actually returned saved closure fields"
    let rows := callerRows made.value w
    let callee := ref (range g 0 6) "picked"
    let passed := argument q
    have fetchedOriginal : ClosedSourceExpressionEvaluates caller callerNames rows made.final callee made.value made.final := .reference .head .head
    let fetched ← observe 1 fetchedOriginal
    have fetchedEq := fetched.original.deterministic fetchedOriginal
    have passedOriginal : ClosedSourceExpressionEvaluates caller callerNames rows fetched.final passed (.word (w.add one)) fetched.final := by
      rw [← RuntimeValue.ofCore.eq_3 (w.add one)]
      exact .strictWordBinary (.reference (.tail (by change "picked"≠"c"; decide) .head) (.tail (by decide) .head)) (.wordLiteral (oneMeaning _)) .add
    let argumentRun ← observe 2 passedOriginal
    have passedEq := argumentRun.original.deterministic passedOriginal
    have initialEq := passedEq.2.trans (fetchedEq.2.trans madeEq.2)
    have savedShape : SourceUnaryLambdaShape saved ⟨s 4,"p"⟩ actualBody := by rw [fields.1]; exact shape
    let fresh := Resolved.freshLocalId savedOwner (savedNames.map Prod.snd)
    have bodyOriginal : ClosedSourceBodyEvaluates savedOwner (("p",fresh)::savedNames)
        ((fresh,argumentRun.value)::savedRows) argumentRun.final actualBody (RuntimeValue.ofCore (result (w.add one))) argumentRun.final := by
      simpa only [fields.2.1,fields.2.2.1,fields.2.2.2,passedEq.1,initialEq,fresh] using beta
    proof bodyOriginal
    check (fresh==sid 32 && Resolved.freshLocalId savedOwner (fresh::savedNames.map Prod.snd)==sid 33) "both actual saved-owner fresh shadows"
    for depth in [0,6,7,10] do
      match br : evaluateClosedSourceBody? depth savedOwner (("p",fresh)::savedNames) ((fresh,argumentRun.value)::savedRows) argumentRun.final actualBody with
      | none => check (depth<7) "body depth exhaustion"
      | some (v,z) =>
        have actualBodyRun : ClosedSourceBodyEvaluates owner (entered owner inputs).names (up (entry owner inputs e (w.add one))) (heap st) (body s) v z := by
          simpa only [fields.2.1,fields.2.2.1,fields.2.2.2,passedEq.1,initialEq,fresh,bodyEq,entered,entry,LocalTypeInputs.bindFresh_names,LocalTypeInputs.names_ids,up,List.map_cons,RuntimeValue.ofCore] using evaluateClosedSourceBody?_sound br
        proof ((b.localImage v z).mp actualBodyRun); proof ((b.localImage v z).mpr ((b.localImage v z).mp actualBodyRun))
        proof ((b.coreImage v z).mp actualBodyRun); proof ((b.coreImage v z).mpr ((b.coreImage v z).mp actualBodyRun))
        check (depth≥7 && reprStr z==reprStr (heap st)) "actual body image endpoints"
    have fetchedActual : ClosedSourceExpressionEvaluates caller callerNames rows made.final callee (.sourceClosure fs owner inputs.names (up e)) fetched.final := by
      simpa only [fetchedEq.1,madeEq.1] using fetched.original
    have argumentActual : ClosedSourceExpressionEvaluates caller callerNames rows fetched.final passed (RuntimeValue.ofCore (.word (w.add one))) (heap st) := by
      simpa only [passedEq.1,initialEq,RuntimeValue.ofCore] using argumentRun.original
    let bodyRun ← observeBody 7 bodyOriginal
    have returnedEq := bodyRun.original.deterministic bodyOriginal
    have fetchedSaved : ClosedSourceExpressionEvaluates caller callerNames rows made.final callee
        (.sourceClosure saved savedOwner savedNames savedRows) fetched.final := by
      simpa only [fetchedEq.1,madeShape] using fetched.original
    have callActual : ClosedSourceExpressionEvaluates caller callerNames rows made.final invoked bodyRun.value bodyRun.final := by
      rw [invokeEq]; exact .call savedShape fetchedSaved argumentRun.original bodyRun.original
    proof callActual
    have original : ClosedSourceExpressionEvaluates caller callerNames rows made.final invoked (RuntimeValue.ofCore (result (w.add one))) (heap st) := by
      simpa only [returnedEq.1,returnedEq.2,initialEq] using callActual
    have originalSame : ClosedSourceExpressionEvaluates caller callerNames rows made.final invoked (RuntimeValue.ofCore (result (w.add one))) made.final := by simpa only [madeEq.2] using original
    runClosed 8 originalSame (fun v z => by
      rw [madeEq.2,invokeEq]
      exact core_exact (Core.steps_from_initial_sound betaSteps)
        (fun _ _ => closedSourceExpectedDataLambda_invocation_core_iff shape (bodyEq ▸ b.admitted) (by simpa only [fsEq] using b.expected) aligned
          (by simpa only [madeEq.2,callee,up] using fetchedActual) argumentActual) v z)
  | _ => throw (IO.userError "actual created source closure")
end Tests.ParsedExpectedBoolStrictDataBridge
open Tests.ParsedExpectedBoolStrictDataBridge in
def Tests.frontendParsedExpectedBoolStrictDataBridgeTests : IO Unit := do
  for w in [Solcore.Core.Word.zero,Solcore.Core.Word.ofNatModulo 1,Solcore.Core.Word.maximum,
      Solcore.Core.Word.ofNatModulo (2^256-2),Solcore.Core.Word.ofNatModulo (2^255)] do
    for st in [[],[old,.hostFunction .storageWrite,.cellRef .word 900,.unit]] do exercise w st
end

section
-- leanmerge: from Solcore.Test.FrontendParsedExpectedWordShortCircuitDataBridge
set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace Tests.ParsedExpectedWordShortCircuitDataBridge
open Solcore Solcore.Frontend
private def check (b : Bool) (s : String) : IO Unit := unless b do throw (IO.userError s)
private def proof {p : Prop} (_ : p) : IO Unit := pure ()
private def owner : Resolved.DeclarationId := ⟨⟨.main,⟨[⟨"ParsedWordShortCircuit",by decide⟩],by decide⟩⟩,299⟩
private def sid (n : Nat) : Resolved.LocalId := ⟨owner,n⟩
private def caller : Resolved.DeclarationId := {owner with declarationIndex:=991}
private def cid (n : Nat) : Resolved.LocalId := ⟨caller,n⟩
private def inputs : LocalTypeInputs := ⟨[⟨"a",sid 7,.bool⟩,⟨"b",sid 31,.bool⟩,⟨"w",sid 11,.word⟩,
  ⟨"p",sid 12,.word⟩,⟨"extra",cid 700,.unit⟩,⟨"p",cid 701,.word⟩],by decide⟩
private def up (e : Resolved.Environment) := e.map (fun r => (r.1,RuntimeValue.ofCore r.2))
private def heap (s : Core.Store) := s.map RuntimeValue.ofCore
private def environment (a b : Bool) (w : Core.Word) (q : Core.Value) : Resolved.Environment :=
  [(sid 7,.bool a),(sid 31,.bool b),(sid 11,.word w),(sid 12,q),(cid 700,.cellRef .word 900),(cid 701,q)]
private abbrev Child (n : LocalNameTable) (t : Resolved.Context) (s : Syntax.Expr) (c : Core.Expr) (v : Core.Ty) :=
  ∃ r, ResolvesLocalExpression n s r ∧ Resolved.Lowers t.ids r c ∧ Resolved.HasType t r v
private structure EC (t : LocalTypeInputs) (e : Resolved.Environment) (s : Core.Store) (src : Syntax.Expr) where
  core : Core.Expr
  type : Core.Ty
  value : Core.Value
  cost : Nat
  depth : Nat
  gate : ClosedSourceDataExpression src
  elaboration : Child t.names t.context src core type
  old : LocalExpressionEvaluatesWithCost t.names e s src value s cost
  closed : ClosedSourceExpressionEvaluates owner t.names (up e) (heap s) src (RuntimeValue.ofCore value) (heap s)
private theorem mapped {e : Resolved.Environment} {i : Resolved.LocalId} {v : Core.Value}
    (h : Resolved.LocalScope.Lookup e i v) : Resolved.LocalScope.Lookup (up e) i (RuntimeValue.ofCore v) := by
  induction h with | head => exact .head | tail ne _ ih => exact .tail ne ih
private theorem path {t e s src} (h : EC t e s src) (same : e.ids=t.context.ids) (k : List Core.Frame) :
    Core.Steps h.cost ⟨.eval h.core e.values,k,s⟩ ⟨.ret h.value,k,s⟩ := by
  obtain ⟨r,res,low,_⟩ := h.elaboration; exact h.old.toStepsWithContinuation res (same ▸ low) k
private def logical {t e s left right} (o : Bool) (ss os : Syntax.SourceSpan)
    (l : EC t e s left) (r : EC t e s right) :
    IO (EC t e s ⟨ss,.binary left ⟨os,if o then .logicalOr else .logicalAnd⟩ right⟩) := do
  if typed : l.type=.bool ∧ r.type=.bool then
    match lv : l.value, rv : r.value with
    | .bool a,.bool b =>
      let v := if o then a || b else a && b
      let k := if a==o then l.cost+3 else l.cost+r.cost+2
      let d := if a==o then l.depth+1 else max l.depth r.depth+1
      let c := if o then Core.Expr.ifE l.core (.bool true) r.core else .ifE l.core r.core (.bool false)
      have admitted : ClosedSourceDataExpression ⟨ss,.binary left ⟨os,if o then .logicalOr else .logicalAnd⟩ right⟩ := by
        cases o; exact .logicalAnd l.gate r.gate; exact .logicalOr l.gate r.gate
      have el : Child t.names t.context ⟨ss,.binary left ⟨os,if o then .logicalOr else .logicalAnd⟩ right⟩ c .bool := by
        obtain ⟨lr,la,ll,lt⟩ := l.elaboration; obtain ⟨rr,ra,rl,rt⟩ := r.elaboration
        cases o
        · exact ⟨.ifE lr rr (.bool false),.logicalAnd la ra,.ifE ll rl .bool,.ifE (typed.1 ▸ lt) (typed.2 ▸ rt) .bool⟩
        · exact ⟨.ifE lr (.bool true) rr,.logicalOr la ra,.ifE ll .bool rl,.ifE (typed.1 ▸ lt) .bool (typed.2 ▸ rt)⟩
      have old : LocalExpressionEvaluatesWithCost t.names e s
          ⟨ss,.binary left ⟨os,if o then .logicalOr else .logicalAnd⟩ right⟩ (.bool v) s k := by
        cases o <;> cases a
        · exact .andFalse (lv ▸ l.old)
        · exact .andTrue (lv ▸ l.old) (rv ▸ r.old)
        · exact .orFalse (lv ▸ l.old) (rv ▸ r.old)
        · exact .orTrue (lv ▸ l.old)
      have closed : ClosedSourceExpressionEvaluates owner t.names (up e) (heap s)
          ⟨ss,.binary left ⟨os,if o then .logicalOr else .logicalAnd⟩ right⟩ (.bool v) (heap s) := by
        cases o <;> cases a
        · exact .andFalse (by simpa only [lv,RuntimeValue.ofCore] using l.closed)
        · exact .andTrue (by simpa only [lv,RuntimeValue.ofCore] using l.closed) (by simpa [rv,RuntimeValue.ofCore,v] using r.closed)
        · exact .orFalse (by simpa only [lv,RuntimeValue.ofCore] using l.closed) (by simpa [rv,RuntimeValue.ofCore,v] using r.closed)
        · exact .orTrue (by simpa only [lv,RuntimeValue.ofCore] using l.closed)
      return ⟨c,.bool,.bool v,k,d,admitted,el,old,by simpa only [RuntimeValue.ofCore] using closed⟩
    | _,_ => throw (IO.userError "checked guard requires actual Bool children")
  else throw (IO.userError "whole guard Bool checking")
private def expr (t : LocalTypeInputs) (e : Resolved.Environment) (s : Core.Store) (src : Syntax.Expr) : IO (EC t e s src) := do
  match shape : src with
  | ⟨_,.identifier name⟩ =>
    match named : t.names.lookup? name.value with
    | some i => match typed : t.context.lookup? i, found : e.lookup? i, indexed : Resolved.LocalScope.index? t.context.ids i with
      | some ty,some v,some n => return ⟨.var n,ty,v,1,1,by rw [shape]; exact .reference,
          by rw [shape]; exact ⟨.var i,.identifier (LocalNameTable.lookup?_iff.mp named),.var (Resolved.LocalScope.index?_iff.mp indexed),.var (Resolved.LocalScope.lookup?_iff.mp typed)⟩,
          by rw [shape]; exact .identifier (LocalNameTable.lookup?_iff.mp named) (Resolved.LocalScope.lookup?_iff.mp found),
          by rw [shape]; exact .reference (LocalNameTable.lookup?_iff.mp named) (mapped (Resolved.LocalScope.lookup?_iff.mp found))⟩
      | _,_,_ => throw (IO.userError "independent original row")
    | none => throw (IO.userError "independent original name")
  | ⟨_,.group child⟩ =>
    let h ← expr t e s child
    return ⟨h.core,h.type,h.value,h.cost,h.depth+1,by rw [shape]; exact .group h.gate,
      by obtain ⟨r,a,b,c⟩ := h.elaboration; rw [shape]; exact ⟨r,.group a,b,c⟩,
      by rw [shape]; exact .group h.old,by rw [shape]; exact .group h.closed⟩
  | ⟨_,.unary ⟨_,.bitNot⟩ child⟩ =>
    let h ← expr t e s child
    if ht : h.type=.word then
      match hv : h.value with
      | .word w => return ⟨.unary .wordNot h.core,.word,.word w.bitNot,h.cost+2,h.depth+1,by rw [shape]; exact .bitNot h.gate,
          by obtain ⟨r,a,b,c⟩ := h.elaboration; rw [shape]; exact ⟨.unary .wordNot r,.bitNot a,.unary b,.unary (by simpa only [ht,Core.UnaryOp.operandType] using c)⟩,
          by rw [shape]; exact .bitNot (hv ▸ h.old),by rw [shape]; simpa only [RuntimeValue.ofCore] using ClosedSourceExpressionEvaluates.bitNot (by simpa only [hv,RuntimeValue.ofCore] using h.closed)⟩
      | _ => throw (IO.userError "independent Word operand")
    else throw (IO.userError "whole Word unary checking")
  | ⟨ss,.binary left ⟨os,op⟩ right⟩ =>
    let l ← expr t e s left; let r ← expr t e s right
    match hop : op with
    | .logicalAnd => let h ← logical false ss os l r; return (by simpa only [shape,hop,Bool.false_eq_true,↓reduceIte] using h)
    | .logicalOr => let h ← logical true ss os l r; return (by simpa only [shape,hop,Bool.false_eq_true,↓reduceIte] using h)
    | _ => throw (IO.userError "only short-circuit binary")
  | ⟨_,.conditional guard _ yes _ no⟩ =>
    let g ← expr t e s guard; let y ← expr t e s yes; let n ← expr t e s no
    if typed : g.type=.bool ∧ y.type=.word ∧ n.type=.word then
      match gv : g.value with
      | .bool b =>
        have el : Child t.names t.context src (.ifE g.core y.core n.core) .word := by
          obtain ⟨gr,ga,gl,gt⟩ := g.elaboration; obtain ⟨yr,ya,yl,yt⟩ := y.elaboration; obtain ⟨nr,na,nl,nt⟩ := n.elaboration
          rw [shape]; exact ⟨.ifE gr yr nr,.conditional ga ya na,.ifE gl yl nl,.ifE (typed.1 ▸ gt) (typed.2.1 ▸ yt) (typed.2.2 ▸ nt)⟩
        return ⟨.ifE g.core y.core n.core,.word,(if b then y.value else n.value),g.cost+(if b then y.cost else n.cost)+2,max g.depth (if b then y.depth else n.depth)+1,
          by rw [shape]; exact .conditional g.gate y.gate n.gate,el,
          by rw [shape]; cases b; exact .ifFalse (gv ▸ g.old) n.old; exact .ifTrue (gv ▸ g.old) y.old,
          by rw [shape]; cases b; exact .conditionalFalse (by simpa only [gv,RuntimeValue.ofCore] using g.closed) n.closed; exact .conditionalTrue (by simpa only [gv,RuntimeValue.ofCore] using g.closed) y.closed⟩
      | _ => throw (IO.userError "actual conditional Bool guard")
    else throw (IO.userError "both Word branches checked")
  | _ => throw (IO.userError "bounded original expression")
termination_by sizeOf src
private def exprImages {t e s src} (h : EC t e s src) (same : e.ids=t.context.ids) {v st}
    (actual : ClosedSourceExpressionEvaluates owner t.names (up e) (heap s) src v st) : IO Unit := do
  have eq : v=RuntimeValue.ofCore h.value ∧ st=heap s := by
    obtain ⟨r,res,low,_⟩ := h.elaboration
    have old := h.old.erase; have core := Core.steps_from_initial_sound (path h same [])
    have localBack : ClosedSourceExpressionEvaluates owner t.names (up e) (heap s) src (RuntimeValue.ofCore h.value) (heap s) := h.gate.local_evaluates_iff.mpr ⟨h.value,s,rfl,rfl,old⟩
    have both : ClosedSourceExpressionEvaluates owner t.names (up e) (heap s) src v st := h.gate.local_evaluates_iff.mpr (h.gate.local_evaluates_iff.mp actual)
    have ci := h.gate.core_evaluates_iff res (same ▸ low) (owner:=owner) (initialStore:=s) (actualValue:=v) (actualFinal:=st)
    obtain ⟨a,b,hv,hs,run⟩ := ci.mp both
    obtain ⟨ve,se⟩ := Core.evaluation_deterministic run core
    exact (ci.mpr ⟨h.value,s,hv.trans (congrArg RuntimeValue.ofCore ve),hs.trans (congrArg heap se),core⟩).deterministic localBack
  proof eq
  check (v.toCore?==some h.value && st.mapM RuntimeValue.toCore?==some s) "all actual expression images"
private def text (o : Bool) := if o then "(lam(p){return(a||b)?p:~p;})(w)" else "(lam(p){return(a&&b)?p:~p;})(w)"
private def file (s : String) : Syntax.SourceFile := ⟨⟨.main,"parsed-word-short-circuit.sol"⟩,s⟩
private def sp (a b : Nat) : Syntax.SourceSpan := ⟨(file "").id,a,b⟩
private def ref (a b : Nat) (n : String) : Syntax.Expr := ⟨sp a b,.identifier ⟨sp a b,n⟩⟩
private def expected (o : Bool) : Syntax.Expr :=
  let guard : Syntax.Expr := ⟨sp 14 20,.group ⟨sp 15 19,.binary (ref 15 16 "a") ⟨sp 16 18,if o then .logicalOr else .logicalAnd⟩ (ref 18 19 "b")⟩⟩
  let b : Syntax.Block := ⟨sp 7 27,[⟨sp 8 26,.returnStmt (some ⟨sp 14 25,.conditional guard (sp 20 21) (ref 21 22 "p") (sp 22 23)
    ⟨sp 23 25,.unary ⟨sp 23 24,.bitNot⟩ (ref 24 25 "p")⟩⟩)⟩]⟩
  let f : Syntax.Expr := ⟨sp 1 27,.lambda (sp 1 4) ⟨sp 4 7,[⟨sp 5 6,.inferred ⟨sp 5 6,"p"⟩⟩]⟩ none b⟩
  ⟨sp 0 31,.call ⟨sp 0 28,.group f⟩ ⟨sp 28 31,[ref 29 30 "w"]⟩⟩
private def savedExpected : Syntax.Expr := ⟨sp 0 9,.call (ref 0 6 "picked") ⟨sp 6 9,[ref 7 8 "w"]⟩⟩
private def parsed (s : String) (want : Syntax.Expr) : IO Syntax.Expr := do
  let f := file s
  let .ok lexed := Syntax.Lexer.lex f | throw (IO.userError "lexer")
  match Syntax.Parser.expression (Syntax.Parser.State.initial f lexed) with
  | .ok src next => check (next.file==f && lexed.diagnostics.isEmpty && next.diagnostics.isEmpty && next.atEnd && src.span==Syntax.SourceSpan.fullFile f && src==want) "exact original AST/full ranges/EOF/diagnostics"; return src
  | _ => throw (IO.userError "parser")
private def names : LocalNameTable := [("picked",cid 7),("w",cid 900),("a",cid 42),("p",sid 12),("picked",cid 7)]
private def rows (fn : RuntimeValue) (w : Core.Word) : Resolved.LocalScope RuntimeValue :=
  [(cid 900,.word w),(cid 7,fn),(cid 42,.bool false),(sid 12,fn),(cid 7,.unit),(cid 701,fn)]
private def coreRuns {e s c v k} (p : Core.Steps k (.initial c e s) (.final v s)) : IO Unit := do
  proof p
  for fuel in [0,k-1,k,k+3] do
    match run : Core.runStateful fuel (.initial c e s) with
    | .done value final => proof (Core.evaluation_deterministic (Core.runStateful_evaluation_sound run) (Core.steps_from_initial_sound p)); check (fuel≥k && value==v && final==s) "independent Core cost/endpoints"
    | .outOfFuel _ => check (fuel<k) "independent Core exhaustion"
    | .fault _ _ => throw (IO.userError "Core fault")
private def closedRuns {o n e s src v} (d : Nat) (old : ClosedSourceExpressionEvaluates o n e s src v s)
    (after : ∀ {a z}, ClosedSourceExpressionEvaluates o n e s src a z → IO Unit) : IO Unit := do
  proof old
  for fuel in [0,d-1,d,d+3] do
    match run : evaluateClosedSourceExpression? fuel o n e s src with
    | none => check (fuel<d) "independent closed depth exhaustion"
    | some _ => have actual := evaluateClosedSourceExpression?_sound run; proof (actual.deterministic old); after actual; check (fuel≥d) "independent closed depth/actual endpoints"
private def consume {p : Prop} {e s c v a z} (old : Core.Evaluates e s c v s)
    (image : p ↔ ∃ x t, a=RuntimeValue.ofCore x ∧ z=heap t ∧ Core.Evaluates e s c x t) (actual : p) : IO Unit := do
  have forward := image.mp actual; proof forward
  have eq : a=RuntimeValue.ofCore v ∧ z=heap s := by
    obtain ⟨x,t,hx,ht,run⟩ := forward; obtain ⟨rfl,rfl⟩ := Core.evaluation_deterministic run old; exact ⟨hx,ht⟩
  proof (image.mpr ⟨v,s,eq.1,eq.2,old⟩)
  check (a.toCore?==some v && z.mapM RuntimeValue.toCore?==some s) "full actual image with independent reverse witness"
private def exercise (o a b : Bool) (w : Core.Word) (q : Core.Value) (s : Core.Store) : IO Unit := do
  let src ← parsed (text o) (expected o); let picked ← parsed "picked(w)" savedExpected; let e := environment a b w q
  match original : src, savedShape : picked with
  | ⟨cs,.call ⟨gs,.group fs⟩ ⟨args,[arg]⟩⟩,⟨pcs,.call ⟨fnSpan,.identifier ⟨fnName,"picked"⟩⟩ ⟨pas,[⟨ws,.identifier ⟨wn,"w"⟩⟩]⟩⟩ =>
    match fsShape : fs with
    | ⟨_,.lambda _ ⟨_,[⟨_,.inferred p⟩]⟩ none body⟩ =>
      match bodyShape : body with
      | ⟨bs,[⟨rs,.returnStmt (some returned)⟩]⟩ =>
        have shape : SourceUnaryLambdaShape fs p body := by rw [fsShape]; exact .inferred
        let ac ← expr inputs e s arg
        let inner := inputs.bindFresh owner p.value .word
        let ie : Resolved.Environment := (Resolved.freshLocalId owner inputs.ids,ac.value)::e
        have same : e.ids=inputs.context.ids := rfl
        have same1 : ie.ids=inner.context.ids := by simpa only [ie,inner,LocalTypeInputs.bindFresh_context,Resolved.LocalScope.ids,List.map_cons] using congrArg (List.cons _) same
        let bc ← expr inner ie s returned
        if bt : bc.type=.word then
          have gate : ClosedSourceDataBody body := by rw [bodyShape]; exact .expression bc.gate
          have checkedBody : ComputationReturnTreeElaborates Child [] owner inner body bc.core .word := by rw [bodyShape]; exact .expression (bt ▸ bc.elaboration)
          have oldBody : ComputationReturnTreeEvaluates LocalExpressionEvaluates owner inner.names ie s body bc.value s := by rw [bodyShape]; exact .expression bc.old.erase
          have cb : ClosedSourceBodyEvaluates owner inner.names (up ie) (heap s) body (RuntimeValue.ofCore bc.value) (heap s) := by rw [bodyShape]; exact .expression bc.closed
          have beta : ClosedSourceBodyEvaluates owner ((p.value,Resolved.freshLocalId owner (inputs.names.map Prod.snd))::inputs.names)
              ((Resolved.freshLocalId owner (inputs.names.map Prod.snd),RuntimeValue.ofCore ac.value)::up e) (heap s) body (RuntimeValue.ofCore bc.value) (heap s) := by
            simpa only [ie,inner,LocalTypeInputs.bindFresh_names,LocalTypeInputs.names_ids,up,List.map_cons] using cb
          let saved := RuntimeValue.sourceClosure fs owner inputs.names (up e)
          have madeOld : ClosedSourceExpressionEvaluates owner inputs.names (up e) (heap s) ⟨gs,.group fs⟩ saved (heap s) := .group (.creation shape)
          have whole : ClosedSourceExpressionEvaluates owner inputs.names (up e) (heap s) src (RuntimeValue.ofCore bc.value) (heap s) := by rw [original]; exact .call shape madeOld ac.closed beta
          let direct : Syntax.Expr := ⟨cs,.call fs ⟨args,[arg]⟩⟩
          have directOld : ClosedSourceExpressionEvaluates owner inputs.names (up e) (heap s) direct (RuntimeValue.ofCore bc.value) (heap s) := .call shape (.creation shape) ac.closed beta
          have betaPath (k) : Core.Steps bc.cost ⟨.eval bc.core (ac.value::e.values),k,s⟩ ⟨.ret bc.value,k,s⟩ := by simpa only [ie,Resolved.LocalScope.values,List.map_cons] using path bc same1 k
          let core := Core.Expr.apply (.lambda .word .word bc.core) ac.core
          have full : Core.Steps (1+ac.cost+bc.cost+3) (.initial core e.values s) (.final bc.value s) := CostStepComposition.apply (.cons .lambda .refl) (path ac same _) (betaPath [])
          proof ac.old; proof bc.old; proof oldBody; proof cb; proof whole; proof directOld; proof full
          let d := max 2 (max ac.depth (bc.depth+1))+1
          check (decide (ac.value=.word w ∧ ac.core=.var 2 ∧ ac.cost=1 ∧ ac.depth=1 ∧ bc.depth=4 ∧ d=6 ∧
            bc.core=.ifE (if o then .ifE (.var 1) (.bool true) (.var 2) else .ifE (.var 1) (.var 2) (.bool false)) (.var 0) (.unary .wordNot (.var 0)) ∧
            bc.value=.word (if (if o then a||b else a&&b) then w else w.bitNot) ∧ bc.cost=(if (if o then a||b else a&&b) then 7 else 9) ∧
            p.value="p" ∧ Resolved.freshLocalId owner inputs.ids=sid 32)) "independent literal Word/guard/shadow/depth/cost"
          have declaration : ExpectedUnaryLambdaHeaderDeclares [] owner inputs fs (.function .word .word) ⟨inner,body,.word,.word⟩ := by rw [fsShape]; exact .lambda .inferred .omitted
          have checked := (elaborateExpectedComputationLambda?_iff elaborateLocalExpression?_iff).mpr (.lambda declaration .word .word checkedBody)
          have bodyChecked := (elaborateComputationReturnTree?_iff elaborateLocalExpression?_iff).mpr checkedBody
          have bodyImage {v z} : ClosedSourceBodyEvaluates owner inner.names (up ie) (heap s) body v z ↔
              ∃ x t, v=RuntimeValue.ofCore x ∧ z=heap t ∧ Core.Evaluates ie.values s bc.core x t := gate.core_evaluates_iff bodyChecked same1
          proof (gate.local_evaluates_iff.mp cb); proof (gate.local_evaluates_iff.mpr ⟨bc.value,s,rfl,rfl,oldBody⟩ : ClosedSourceBodyEvaluates owner inner.names (up ie) (heap s) body (RuntimeValue.ofCore bc.value) (heap s))
          for fuel in [0,bc.depth,bc.depth+1,bc.depth+4] do
            match brun : evaluateClosedSourceBody? fuel owner inner.names (up ie) (heap s) body with
            | none => check (fuel<bc.depth+1) "body adjacent exhaustion"
            | some _ => consume (Core.steps_from_initial_sound (path bc same1 [])) bodyImage (evaluateClosedSourceBody?_sound brun); check (fuel≥bc.depth+1) "body adjacent success"
          coreRuns full; coreRuns (betaPath []); coreRuns (path ac same [])
          closedRuns ac.depth ac.closed (exprImages ac same)
          closedRuns 2 madeOld (fun actual => proof (actual.deterministic madeOld))
          match made : evaluateClosedSourceExpression? 2 owner inputs.names (up e) (heap s) ⟨gs,.group fs⟩ with
          | none => throw (IO.userError "actual grouped creation")
          | some (actualClosure,creationStore) =>
            have madeEq := (evaluateClosedSourceExpression?_sound made).deterministic madeOld
            proof madeEq
            check ((match actualClosure with
              | .sourceClosure sf so sn se => sf==fs && so==owner && sn==inputs.names && se.mapM (fun r => (r.2.toCore?).map (r.1,·))==some e
              | _ => false) && creationStore.mapM RuntimeValue.toCore?==some s) "all actual saved closure fields and creation store"
            match arun : evaluateClosedSourceExpression? ac.depth owner inputs.names (up e) creationStore arg with
            | none => throw (IO.userError "actual argument after creation")
            | some (actualArg,argumentStore) =>
              have ae := evaluateClosedSourceExpression?_sound arun
              have ae0 : ClosedSourceExpressionEvaluates owner inputs.names (up e) (heap s) arg actualArg argumentStore := by simpa only [madeEq.2] using ae
              let argEq := ae0.deterministic ac.closed
              exprImages ac same ae0
              match brun : evaluateClosedSourceBody? (bc.depth+1) owner inner.names ((Resolved.freshLocalId owner inputs.ids,actualArg)::up e) argumentStore body with
              | none => throw (IO.userError "actual body after actual argument store")
              | some (v,z) => consume (a:=v) (z:=z) (Core.steps_from_initial_sound (path bc same1 [])) bodyImage (by simpa only [argEq.1,argEq.2,ie,up,List.map_cons] using evaluateClosedSourceBody?_sound brun)
              have fn := evaluateClosedSourceExpression?_sound made
              have argEv : ClosedSourceExpressionEvaluates owner inputs.names (up e) creationStore arg (RuntimeValue.ofCore ac.value) (heap s) := by simpa only [argEq.1,argEq.2] using ae
              have fnEval : ClosedSourceExpressionEvaluates owner inputs.names (up e) (heap s) ⟨gs,.group fs⟩ (.sourceClosure fs owner inputs.names (up e)) creationStore := by simpa only [madeEq.1,saved] using fn
              closedRuns d whole (fun {a z} actual => consume (a:=a) (z:=z) (Core.steps_from_initial_sound (betaPath [])) (closedSourceExpectedDataLambda_invocation_core_iff (callSpan:=cs) (argumentsSpan:=args) shape gate checked same fnEval argEv) (by simpa only [original] using actual))
              have directImage {v z} : ClosedSourceExpressionEvaluates owner inputs.names (up e) (heap s) direct v z ↔ ∃ x t, v=RuntimeValue.ofCore x ∧ z=heap t ∧ Core.Evaluates e.values s core x t := by
                obtain ⟨r,res,low,_⟩ := ac.elaboration; exact closedSourceExpectedDataLambda_application_core_iff shape gate checked same ac.gate res (same ▸ low)
              closedRuns d directOld (fun actual => consume (Core.steps_from_initial_sound full) directImage actual)
              let cr := rows actualClosure w
              have fetched : ClosedSourceExpressionEvaluates caller names cr creationStore ⟨fnSpan,.identifier ⟨fnName,"picked"⟩⟩ saved creationStore := by rw [← madeEq.1]; exact .reference .head (.tail (by decide) .head)
              if aw : ac.value=.word w then
                let savedCode := Core.Expr.apply (.var 0) (.var 1)
                let savedRows := [Core.Value.closure .word .word bc.core e.values,.word w]
                have savedPath : Core.Steps (1+1+bc.cost+3) (.initial savedCode savedRows s) (.final bc.value s) :=
                  CostStepComposition.apply (.cons (.var rfl) .refl) (.cons (.var rfl) .refl) (by simpa only [aw,Core.State.initial,Core.State.final] using betaPath [])
                coreRuns savedPath
                have argOld : ClosedSourceExpressionEvaluates caller names cr creationStore ⟨ws,.identifier ⟨wn,"w"⟩⟩ (RuntimeValue.ofCore ac.value) (heap s) := by rw [madeEq.2,aw]; simp only [RuntimeValue.ofCore]; exact .reference (.tail (by change ("picked" : String) ≠ "w"; decide) .head) .head
                have savedOld : ClosedSourceExpressionEvaluates caller names cr creationStore picked (RuntimeValue.ofCore bc.value) creationStore := by rw [savedShape]; simpa only [madeEq.2] using ClosedSourceExpressionEvaluates.call shape fetched argOld beta
                match frun : evaluateClosedSourceExpression? 1 caller names cr creationStore ⟨fnSpan,.identifier ⟨fnName,"picked"⟩⟩ with
                | none => throw (IO.userError "actual saved fetch")
                | some (actualFn,calleeStore) =>
                  have feq := (evaluateClosedSourceExpression?_sound frun).deterministic fetched
                  match sar : evaluateClosedSourceExpression? 1 caller names cr calleeStore ⟨ws,.identifier ⟨wn,"w"⟩⟩ with
                  | none => throw (IO.userError "actual saved argument")
                  | some (sa,sas) =>
                    have sae := evaluateClosedSourceExpression?_sound sar
                    have seq := (show ClosedSourceExpressionEvaluates caller names cr creationStore ⟨ws,.identifier ⟨wn,"w"⟩⟩ sa sas from by simpa only [feq.2] using sae).deterministic argOld
                    match sbr : evaluateClosedSourceBody? (bc.depth+1) owner inner.names ((Resolved.freshLocalId owner inputs.ids,sa)::up e) sas body with
                    | none => throw (IO.userError "actual saved body")
                    | some (sv,ss) => consume (a:=sv) (z:=ss) (Core.steps_from_initial_sound (path bc same1 [])) bodyImage (by simpa only [seq.1,seq.2,ie,up,List.map_cons] using evaluateClosedSourceBody?_sound sbr)
                    have sf : ClosedSourceExpressionEvaluates caller names cr creationStore ⟨fnSpan,.identifier ⟨fnName,"picked"⟩⟩ (.sourceClosure fs owner inputs.names (up e)) calleeStore := by simpa only [feq.1,saved] using evaluateClosedSourceExpression?_sound frun
                    have se : ClosedSourceExpressionEvaluates caller names cr calleeStore ⟨ws,.identifier ⟨wn,"w"⟩⟩ (RuntimeValue.ofCore ac.value) (heap s) := by simpa only [seq.1,seq.2] using sae
                    closedRuns d savedOld (fun {a z} actual => consume (a:=a) (z:=z) (Core.steps_from_initial_sound (betaPath []))
                      (closedSourceExpectedDataLambda_invocation_core_iff (callSpan:=pcs) (argumentsSpan:=pas) shape gate checked same sf se) (by simpa only [savedShape] using actual))
              else throw (IO.userError "argument Word image")
        else throw (IO.userError "whole Word return checking")
      | _ => throw (IO.userError "original single return body")
    | _ => throw (IO.userError "original inferred lambda")
  | _,_ => throw (IO.userError "original grouped/direct and saved calls")
end Tests.ParsedExpectedWordShortCircuitDataBridge
open Tests.ParsedExpectedWordShortCircuitDataBridge in
def Tests.frontendParsedExpectedWordShortCircuitDataBridgeTests : IO Unit := do
  let q := Solcore.Core.Value.closure .unit .word (.var 99) [.hostFunction .storageWrite,.cellRef .unit 700]
  for o in [false,true] do
    for a in [false,true] do
      for b in [false,true] do
        for w in [Solcore.Core.Word.ofNatModulo 0,Solcore.Core.Word.ofNatModulo 1,Solcore.Core.Word.ofNatModulo (2^256-1)] do
          for s in [[],[q,.cellRef .word 900,.hostFunction .storageWrite,.unit]] do exercise o a b w q s
end

section
-- leanmerge: from Solcore.Test.FrontendParsedExpectedWordStrictDataBridge
/- Saved typed identities are unique, but their opaque Core payloads need not
inhabit the declared types. Raw caller rows deliberately retain duplicate IDs.
Depth checks below are finite fixture checks, separate from independent costs. -/
set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace Tests.ParsedExpectedWordStrictDataBridge
open Solcore Solcore.Frontend
private def check (b : Bool) (m : String) : IO Unit := unless b do throw (IO.userError m)
private def proof {p : Prop} (_ : p) : IO Unit := pure ()
private def up (e : Resolved.Environment) := e.map (fun r => (r.1,RuntimeValue.ofCore r.2))
private def heap (s : Core.Store) := s.map RuntimeValue.ofCore
private def one : Core.Word := Core.Word.ofNatModulo 1
private def two : Core.Word := Core.Word.ofNatModulo 2
private def ref (s : Nat → Syntax.SourceSpan) (i : Nat) (n : String) : Syntax.Expr :=
  ⟨s i,.identifier ⟨s (i+1),n⟩⟩
private def lit (s : Nat → Syntax.SourceSpan) (i : Nat) (n : String) : Syntax.Expr :=
  ⟨s i,.literal ⟨s (i+1),.decimal n⟩⟩
private def init (s : Nat → Syntax.SourceSpan) : Syntax.Expr :=
  ⟨s 4,.binary (ref s 0 "p") ⟨s 5,.add⟩ (lit s 2 "1")⟩
private def returned (s : Nat → Syntax.SourceSpan) : Syntax.Expr :=
  ⟨s 23,.conditional ⟨s 12,.group ⟨s 10,.binary (ref s 6 "p") ⟨s 11,.less⟩ (lit s 8 "2")⟩⟩
    (s 24) ⟨s 17,.binary (ref s 13 "p") ⟨s 18,.multiply⟩ (lit s 15 "2")⟩
    (s 25) ⟨s 21,.unary ⟨s 22,.bitNot⟩ (ref s 19 "p")⟩⟩
private def annotation (s : Nat → Syntax.SourceSpan) : Syntax.TypeExpr :=
  ⟨s 26,.named ⟨s 27,⟨⟨⟨s 28,"Word"⟩,[]⟩⟩⟩ none⟩
private def body (s : Nat → Syntax.SourceSpan) : Syntax.Block :=
  ⟨s 29,[⟨s 30,.letDecl ⟨s 31,"p"⟩ (some (annotation s)) (some (init s))⟩,
    ⟨s 32,.returnStmt (some (returned s))⟩]⟩
private def source (s : Nat → Syntax.SourceSpan) : Syntax.Expr :=
  ⟨s 33,.lambda (s 34) ⟨s 35,[⟨s 36,.inferred ⟨s 37,"p"⟩⟩]⟩ none (body s)⟩
private def call (s : Nat → Syntax.SourceSpan) (fn arg : Syntax.Expr) : Syntax.Expr := ⟨s 38,.call fn ⟨s 39,[arg]⟩⟩
private def argument (s : Nat → Syntax.SourceSpan) : Syntax.Expr :=
  ⟨s 44,.binary (ref s 40 "c") ⟨s 45,.add⟩ (lit s 42 "1")⟩
private def decision (w : Core.Word) := decide (w.add one < two)
private def value (w : Core.Word) : Core.Value := .word (if decision w then (w.add one).mul two else (w.add one).bitNot)
private def retCore : Core.Expr := .ifE ((Core.Expr.var 0).wordLt (.word two))
  (.binary .wordMul (.var 0) (.word two)) (.unary .wordNot (.var 0))
private def core : Core.Expr := .letE (.binary .wordAdd (.var 0) (.word one)) retCore
private def cost (w : Core.Word) : Nat := 5 + (11 + (if decision w then 5 else 3) + 2) + 2
private def entry (o : Resolved.DeclarationId) (t : LocalTypeInputs) := t.bindFresh o "p" .word
private def env (o : Resolved.DeclarationId) (t : LocalTypeInputs) (e : Resolved.Environment) (w : Core.Word) : Resolved.Environment :=
  (Resolved.freshLocalId o t.ids,.word w)::e
private def text := "(lam(p){let p:Word=p + 1;return (p < 2) ? p * 2 : ~p;})(c + 1)"
private def file (s : String) : Syntax.SourceFile := ⟨⟨.main,"word-strict-data.sol"⟩,s⟩
private def sp (a b : Nat) : Syntax.SourceSpan := ⟨(file "").id,a,b⟩
private def ranges : List Syntax.SourceSpan :=
  [(19,20),(19,20),(23,24),(23,24),(19,24),(21,22),(33,34),(33,34),(37,38),(37,38),
   (33,38),(35,36),(32,39),(42,43),(42,43),(46,47),(46,47),(42,47),(44,45),(51,52),
   (51,52),(50,52),(50,51),(32,52),(40,41),(48,49),(14,18),(14,18),(14,18),(7,54),
   (8,25),(12,13),(25,53),(1,54),(1,4),(4,7),(5,6),(5,6),(0,62),(55,62),(56,57),
   (56,57),(60,61),(60,61),(56,61),(58,59),(0,55)].map (fun p => sp p.1 p.2)
private def spans (i : Nat) := ranges.getD i (sp 0 0)
private def whole (s : Nat → Syntax.SourceSpan) : Syntax.Expr := call s ⟨s 46,.group (source s)⟩ (argument s)
private def parse : IO {actual : Syntax.Expr // actual=whole spans} := do
  let f := file text
  let .ok lexed := Syntax.Lexer.lex f | throw (IO.userError "Word lexer")
  let .ok actual next := Syntax.Parser.expression (Syntax.Parser.State.initial f lexed) | throw (IO.userError "Word parser")
  check (next.file==f && lexed.diagnostics.isEmpty && next.diagnostics.isEmpty && next.atEnd && actual==whole spans) "whole handwritten AST/EOF/diagnostics"
  match shape : actual with
  | ⟨s38,.call ⟨s46,.group ⟨s33,.lambda s34 ⟨s35,[⟨s36,.inferred ⟨s37,"p"⟩⟩]⟩ none
      ⟨s29,[⟨s30,.letDecl ⟨s31,"p"⟩ (some ⟨s26,.named ⟨s27,⟨⟨⟨s28,"Word"⟩,[]⟩⟩⟩ none⟩)
        (some ⟨s4,.binary ⟨s0,.identifier ⟨s1,"p"⟩⟩ ⟨s5,.add⟩ ⟨s2,.literal ⟨s3,.decimal "1"⟩⟩⟩)⟩,
        ⟨s32,.returnStmt (some ⟨s23,.conditional ⟨s12,.group ⟨s10,.binary ⟨s6,.identifier ⟨s7,"p"⟩⟩ ⟨s11,.less⟩ ⟨s8,.literal ⟨s9,.decimal "2"⟩⟩⟩⟩ s24
          ⟨s17,.binary ⟨s13,.identifier ⟨s14,"p"⟩⟩ ⟨s18,.multiply⟩ ⟨s15,.literal ⟨s16,.decimal "2"⟩⟩⟩ s25
          ⟨s21,.unary ⟨s22,.bitNot⟩ ⟨s19,.identifier ⟨s20,"p"⟩⟩⟩⟩)⟩]⟩⟩⟩
      ⟨s39,[⟨s44,.binary ⟨s40,.identifier ⟨s41,"c"⟩⟩ ⟨s45,.add⟩ ⟨s42,.literal ⟨s43,.decimal "1"⟩⟩⟩]⟩⟩ =>
    let ss := [s0,s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16,s17,s18,s19,s20,s21,s22,s23,s24,s25,s26,s27,s28,s29,s30,s31,s32,s33,s34,s35,s36,s37,s38,s39,s40,s41,s42,s43,s44,s45,s46]
    if exactRanges : ss=ranges then
      have reconstruct : actual=whole (fun i => ss.getD i (sp 0 0)) := by rw [shape]; rfl
      return ⟨actual,reconstruct.trans (congrArg (fun xs => whole (fun i => xs.getD i (sp 0 0))) exactRanges)⟩
    else throw (IO.userError "all 47 handwritten ranges")
  | _ => throw (IO.userError "exact Word lambda/binding/conditional/call shape")
private def picked : Syntax.Expr := ⟨sp 0 9,.call ⟨sp 0 6,.identifier ⟨sp 0 6,"picked"⟩⟩ ⟨sp 6 9,[⟨sp 7 8,.identifier ⟨sp 7 8,"w"⟩⟩]⟩⟩
private def parseSaved : IO {actual : Syntax.Expr // actual=picked} := do
  let f := file "picked(w)"
  let .ok lexed := Syntax.Lexer.lex f | throw (IO.userError "saved lexer")
  let .ok actual next := Syntax.Parser.expression (Syntax.Parser.State.initial f lexed) | throw (IO.userError "saved parser")
  check (next.file==f && lexed.diagnostics.isEmpty && next.diagnostics.isEmpty && next.atEnd && actual==picked) "saved full AST/EOF/diagnostics"
  match shape : actual with
  | ⟨a,.call ⟨b,.identifier ⟨c,"picked"⟩⟩ ⟨d,[⟨e,.identifier ⟨f,"w"⟩⟩]⟩⟩ =>
    if exactRanges : a=sp 0 9 ∧ b=sp 0 6 ∧ c=sp 0 6 ∧ d=sp 6 9 ∧ e=sp 7 8 ∧ f=sp 7 8 then
      return ⟨actual,by rcases exactRanges with ⟨rfl,rfl,rfl,rfl,rfl,rfl⟩; exact shape⟩
    else throw (IO.userError "saved six exact ranges")
  | _ => throw (IO.userError "saved actual AST shape")
private def owner : Resolved.DeclarationId := ⟨⟨.main,⟨[⟨"WordStrictData",by decide⟩],by decide⟩⟩,301⟩
private def sid (n : Nat) : Resolved.LocalId := ⟨owner,n⟩
private def caller : Resolved.DeclarationId := {owner with declarationIndex:=991}
private def cid (n : Nat) : Resolved.LocalId := ⟨caller,n⟩
private def inputs : LocalTypeInputs := ⟨[⟨"c",sid 7,.word⟩,⟨"p",sid 31,.word⟩,⟨"tail",cid 700,.unit⟩,⟨"p",cid 701,.word⟩],by decide⟩
private def environment (c : Core.Word) (q : Core.Value) : Resolved.Environment :=
  [(sid 7,.word c),(sid 31,q),(cid 700,.cellRef .word 900),(cid 701,q)]
private def names : LocalNameTable := [("picked",cid 7),("w",cid 900),("p",sid 31),("picked",cid 7)]
private def rows (fn : RuntimeValue) (w : Core.Word) : Resolved.LocalScope RuntimeValue :=
  [(cid 900,.word w),(cid 7,fn),(sid 31,fn),(cid 7,.unit),(cid 701,.hostFunction .storageWrite)]
private def coreRuns {e s c v k} (p : Core.Steps k (.initial c e s) (.final v s)) : IO Unit := do
  proof p
  for fuel in [0,k-1,k,k+3] do
    match run : Core.runStateful fuel (.initial c e s) with
    | .done a z => proof (Core.evaluation_deterministic (Core.runStateful_evaluation_sound run) (Core.steps_from_initial_sound p)); check (fuel≥k && a==v && z==s) "Core independent cost/full endpoints"
    | .outOfFuel _ => check (fuel<k) "Core independent exhaustion"
    | .fault _ _ => throw (IO.userError "Core fault")
private def closedRuns {o n e s src v} (d : Nat) (old : ClosedSourceExpressionEvaluates o n e s src v s)
    (after : ∀ {a z}, ClosedSourceExpressionEvaluates o n e s src a z → IO Unit) : IO Unit := do
  proof old
  for fuel in [0,d-1,d,d+3] do
    match run : evaluateClosedSourceExpression? fuel o n e s src with
    | none => check (fuel<d) "closed fixture depth exhaustion"
    | some _ => have actual := evaluateClosedSourceExpression?_sound run; proof (actual.deterministic old); after actual; check (fuel≥d) "closed fixture depth success"
private def endpoint {P : RuntimeValue → List RuntimeValue → Prop} {v : Core.Value} {s : Core.Store}
    (both : ∀ a z, P a z ↔ a=RuntimeValue.ofCore v ∧ z=heap s) {a z} (actual : P a z) : IO Unit := do
  let equal := (both a z).mp actual
  proof ((both a z).mpr equal)
  check (a.toCore?==some v && z.mapM RuntimeValue.toCore?==some s) "both directions/full actual endpoints"
private def consumeCore {P : Prop} {e s c v a z} (old : Core.Evaluates e s c v s)
    (image : P ↔ ∃ x t, a=RuntimeValue.ofCore x ∧ z=heap t ∧ Core.Evaluates e s c x t) (actual : P) : IO Unit := do
  have equal : a=RuntimeValue.ofCore v ∧ z=heap s := by
    obtain ⟨x,t,hx,ht,run⟩ := image.mp actual
    obtain ⟨rfl,rfl⟩ := Core.evaluation_deterministic run old; exact ⟨hx,ht⟩
  proof (image.mpr ⟨v,s,equal.1,equal.2,old⟩)
  check (a.toCore?==some v && z.mapM RuntimeValue.toCore?==some s) "independent Core reverse/full actual endpoint"
private def calleeOf (src : Syntax.Expr) : Syntax.Expr := match src with | ⟨_,.call fn _⟩ => fn | _ => src
private def argumentOf (src : Syntax.Expr) : Syntax.Expr := match src with | ⟨_,.call _ ⟨_,[a]⟩⟩ => a | _ => src
private def ungroup (src : Syntax.Expr) : Syntax.Expr := match src with | ⟨_,.group fn⟩ => fn | _ => src
private def bodyOf (src : Syntax.Expr) : Syntax.Block := match src with | ⟨_,.lambda _ _ _ b⟩ => b | _ => ⟨sp 0 0,[]⟩
private def exercise (c : Core.Word) (q : Core.Value) (st : Core.Store) : IO Unit := do
  let ⟨actual,actualEq⟩ ← parse
  let ⟨savedActual,savedEq⟩ ← parseSaved
  let actualFn := ungroup (calleeOf actual)
  let actualArg := argumentOf actual
  let actualBody := bodyOf actualFn
  have actualFnEq : actualFn=source spans := by simp only [actualFn,actualEq,whole,call,calleeOf,ungroup]
  have actualArgEq : actualArg=argument spans := by simp only [actualArg,actualEq,whole,call,argumentOf]
  have actualBodyEq : actualBody=body spans := by simp only [actualBody,actualFnEq,source,bodyOf]
  let e := environment c q
  let w := c.add one
  have same : e.ids=inputs.context.ids := rfl
  have h := ExpectedWordStrictDataImages.body_original_and_all_actual_images spans owner inputs e st w same
  have gate : ClosedSourceDataBody (body spans) := h.1
  have checked : elaborateExpectedComputationLambda? elaborateLocalExpression? [(["Word"],.word)] owner inputs (source spans) (.function .word .word)=some (.lambda .word .word core) := h.2.1
  have beta : ClosedSourceBodyEvaluates owner (entry owner inputs).names (up (env owner inputs e w)) (heap st) (body spans) (RuntimeValue.ofCore (value w)) (heap st) := h.2.2.1
  have bodyPath (k) : Core.Steps (cost w) ⟨.eval core (.word w::e.values),k,st⟩ ⟨.ret (value w),k,st⟩ := h.2.2.2.2.1 k
  have bodyExact : ∀ a z, ClosedSourceBodyEvaluates owner (entry owner inputs).names (up (env owner inputs e w)) (heap st) (body spans) a z ↔ a=RuntimeValue.ofCore (value w) ∧ z=heap st := h.2.2.2.2.2
  have argOld : ClosedSourceExpressionEvaluates owner inputs.names (up e) (heap st) (argument spans) (.word w) (heap st) := by
    simpa only [argument,ref,lit,RuntimeValue.ofCore,w] using ClosedSourceExpressionEvaluates.strictWordBinary
      (owner:=owner) (names:=inputs.names) (captured:=up e) (initialStore:=heap st) (span:=spans 44) (operatorSpan:=spans 45)
      (leftWord:=c) (rightWord:=one)
      (.reference (span:=spans 40) (name:=⟨spans 41,"c"⟩) .head (by simp only [up,e,environment,List.map_cons,RuntimeValue.ofCore]; exact .head))
      (.wordLiteral (span:=spans 42) (interpretWordLiteral?_iff.mp (show interpretWordLiteral? ⟨spans 43,.decimal "1"⟩=some one from rfl))) StrictWordBinaryDenotes.add
  have madeOld : ClosedSourceExpressionEvaluates owner inputs.names (up e) (heap st) (source spans)
      (.sourceClosure (source spans) owner inputs.names (up e)) (heap st) := .creation .inferred
  have actualMadeOld : ClosedSourceExpressionEvaluates owner inputs.names (up e) (heap st) actualFn
      (.sourceClosure actualFn owner inputs.names (up e)) (heap st) := by rw [actualFnEq]; exact madeOld
  have actualArgOld : ClosedSourceExpressionEvaluates owner inputs.names (up e) (heap st) actualArg (.word w) (heap st) := by rw [actualArgEq]; exact argOld
  have betaCall : ClosedSourceBodyEvaluates owner (("p",Resolved.freshLocalId owner (inputs.names.map Prod.snd))::inputs.names)
      ((Resolved.freshLocalId owner (inputs.names.map Prod.snd),.word w)::up e) (heap st) (body spans) (RuntimeValue.ofCore (value w)) (heap st) := by
    simpa only [entry,env,LocalTypeInputs.bindFresh_names,LocalTypeInputs.names_ids,up,List.map_cons,RuntimeValue.ofCore] using beta
  have grouped : ClosedSourceExpressionEvaluates owner inputs.names (up e) (heap st) actual (RuntimeValue.ofCore (value w)) (heap st) := by
    rw [actualEq]; exact .call .inferred (.group madeOld) argOld betaCall
  proof beta; proof h.2.2.2.1; proof bodyPath; proof grouped
  check (decide (Resolved.freshLocalId owner inputs.ids=sid 32 ∧ Resolved.freshLocalId owner (entry owner inputs).ids=sid 33)) "two fresh shadows preserve old opaque p"
  coreRuns (bodyPath [])
  for fuel in [0,5,6,9] do
    match run : evaluateClosedSourceBody? fuel owner (entry owner inputs).names (up (env owner inputs e w)) (heap st) actualBody with
    | none => check (fuel<6) "body fixture depth exhaustion"
    | some (a,z) => endpoint (a:=a) (z:=z) bodyExact (by simpa only [actualBodyEq] using evaluateClosedSourceBody?_sound run); check (fuel≥6) "body fixture depth success"
  closedRuns 2 actualArgOld (fun a => proof (a.deterministic actualArgOld))
  closedRuns 1 actualMadeOld (fun a => proof (a.deterministic actualMadeOld))
  match made : evaluateClosedSourceExpression? 1 owner inputs.names (up e) (heap st) actualFn with
  | none => throw (IO.userError "actual creation")
  | some (actualClosure,creationStore) =>
    have creation : ClosedSourceExpressionEvaluates owner inputs.names (up e) (heap st) (source spans) actualClosure creationStore := by simpa only [actualFnEq] using evaluateClosedSourceExpression?_sound made
    have ceq := creation.deterministic madeOld
    check ((match actualClosure with | .sourceClosure sf so sn se => sf==actualFn && so==owner && sn==inputs.names && se.mapM (fun r => (r.2.toCore?).map (r.1,·))==some e | _ => false) && creationStore.mapM RuntimeValue.toCore?==some st) "all saved creation fields"
    let cr := rows actualClosure w
    let fn := calleeOf savedActual
    let arg := argumentOf savedActual
    have fnEq : fn=(⟨sp 0 6,.identifier ⟨sp 0 6,"picked"⟩⟩ : Syntax.Expr) := by simp only [fn,savedEq,picked,calleeOf]
    have argEq : arg=(⟨sp 7 8,.identifier ⟨sp 7 8,"w"⟩⟩ : Syntax.Expr) := by simp only [arg,savedEq,picked,argumentOf]
    have fetchOld : ClosedSourceExpressionEvaluates caller names cr creationStore fn actualClosure creationStore := by rw [fnEq]; exact .reference .head (.tail (by decide) .head)
    have savedArg : ClosedSourceExpressionEvaluates caller names cr creationStore arg (.word w) (heap st) := by rw [ceq.2,argEq]; exact .reference (.tail (by change "picked" ≠ "w"; decide) .head) .head
    let savedCoreRows := [Core.Value.closure .word .word core e.values,.word w,q,.cellRef .word 900]
    have savedCorePath : Core.Steps (1+1+cost w+3) (.initial (.apply (.var 0) (.var 1)) savedCoreRows st) (.final (value w) st) :=
      CostStepComposition.apply (.cons (.var rfl) .refl) (.cons (.var rfl) .refl) (bodyPath [])
    coreRuns savedCorePath
    match fetched : evaluateClosedSourceExpression? 1 caller names cr creationStore fn with
    | none => throw (IO.userError "actual saved callee")
    | some (actualFn,calleeStore) =>
      have fe := evaluateClosedSourceExpression?_sound fetched
      have feq := fe.deterministic fetchOld
      match arun : evaluateClosedSourceExpression? 1 caller names cr calleeStore arg with
      | none => throw (IO.userError "actual saved argument")
      | some (actualArg,argumentStore) =>
        have ae := evaluateClosedSourceExpression?_sound arun
        have aeq := (show ClosedSourceExpressionEvaluates caller names cr creationStore arg actualArg argumentStore from by simpa only [feq.2] using ae).deterministic savedArg
        match brun : evaluateClosedSourceBody? 6 owner (entry owner inputs).names ((Resolved.freshLocalId owner inputs.ids,actualArg)::up e) argumentStore actualBody with
        | none => throw (IO.userError "actual body from actual saved argument")
        | some (bv,bs) =>
          have bodyActual := evaluateClosedSourceBody?_sound brun
          have alignedBody : ClosedSourceBodyEvaluates owner (entry owner inputs).names (up (env owner inputs e w)) (heap st) (body spans) bv bs := by
            simpa only [aeq.1,aeq.2,actualBodyEq,env,up,List.map_cons,RuntimeValue.ofCore] using bodyActual
          proof (alignedBody.deterministic beta)
          endpoint (a:=bv) (z:=bs) bodyExact alignedBody
          have actualCallee : ClosedSourceExpressionEvaluates caller names cr creationStore fn
              (.sourceClosure (source spans) owner inputs.names (up e)) calleeStore := by simpa only [feq.1,ceq.1] using fe
          have actualArgument : ClosedSourceExpressionEvaluates caller names cr calleeStore arg (.word w) argumentStore := by simpa only [aeq.1] using ae
          have actualBeta : ClosedSourceBodyEvaluates owner (("p",Resolved.freshLocalId owner (inputs.names.map Prod.snd))::inputs.names)
              ((Resolved.freshLocalId owner (inputs.names.map Prod.snd),.word w)::up e) argumentStore (body spans) bv bs := by
            simpa only [aeq.1,actualBodyEq,entry,LocalTypeInputs.bindFresh_names,LocalTypeInputs.names_ids] using bodyActual
          have actualCall : ClosedSourceExpressionEvaluates caller names cr creationStore
              ⟨sp 0 9,.call fn ⟨sp 6 9,[arg]⟩⟩ bv bs := .call .inferred actualCallee actualArgument actualBeta
          have actualSavedCall : ClosedSourceExpressionEvaluates caller names cr creationStore savedActual bv bs := by
            rw [savedEq]; simpa only [fnEq,argEq,picked] using actualCall
          proof actualSavedCall
          consumeCore (a:=bv) (z:=bs) (Core.steps_from_initial_sound (bodyPath []))
            (closedSourceExpectedDataLambda_invocation_core_iff (callSpan:=sp 0 9) (argumentsSpan:=sp 6 9) .inferred gate checked same
              actualCallee (by simpa only [aeq.2,RuntimeValue.ofCore,heap] using actualArgument)) actualCall
        let ss := fun i => if i=38 then sp 0 9 else if i=39 then sp 6 9 else spans i
        have creation1 : ClosedSourceExpressionEvaluates owner inputs.names (up e) (heap st) (source ss) actualClosure creationStore := creation
        have fetched1 : ClosedSourceExpressionEvaluates caller names cr creationStore fn actualClosure creationStore := by simpa only [feq.1,feq.2] using fe
        have arg1 : ClosedSourceExpressionEvaluates caller names cr creationStore arg (.word w) (heap st) := by simpa only [feq.2,aeq.1,aeq.2] using ae
        have all := ExpectedWordStrictDataImages.calls_original_and_all_actual_images ss owner inputs e st c same (sid 7) .head .head 0 .head caller names cr fn arg actualClosure creationStore creation1 fetched1 arg1
        have path := all.2.2.1
        have savedOld : ClosedSourceExpressionEvaluates caller names cr creationStore (call ss fn arg) (RuntimeValue.ofCore (value w)) (heap st) := all.2.2.2.2.1
        have savedExact : ∀ a z, ClosedSourceExpressionEvaluates caller names cr creationStore (call ss fn arg) a z ↔ a=RuntimeValue.ofCore (value w) ∧ z=heap st := all.2.2.2.2.2.2
        coreRuns (path [])
        have actualSaved : ClosedSourceExpressionEvaluates caller names cr creationStore savedActual (RuntimeValue.ofCore (value w)) creationStore := by rw [savedEq,ceq.2]; simpa [ceq.2,call,ss,fnEq,argEq,picked] using savedOld
        closedRuns 7 actualSaved (fun {a z} run => endpoint (a:=a) (z:=z) savedExact (by simpa [savedEq,call,ss,fnEq,argEq,picked] using run))
        have original := ExpectedWordStrictDataImages.calls_original_and_all_actual_images spans owner inputs e st c same (sid 7) .head .head 0 .head caller names cr fn arg actualClosure creationStore creation fetched1 arg1
        have full := original.2.2.1; have direct := original.2.2.2.1; have exactDirect := original.2.2.2.2.2.1
        coreRuns (full [])
        closedRuns 7 direct (fun run => endpoint exactDirect run)
        closedRuns 7 grouped (fun {a z} run => consumeCore (a:=a) (z:=z) (Core.steps_from_initial_sound (bodyPath []))
          (closedSourceExpectedDataLambda_invocation_core_iff (callSpan:=spans 38) (argumentsSpan:=spans 39) .inferred gate checked same
            (.group (span:=spans 46) madeOld) (by simpa only [RuntimeValue.ofCore,heap] using argOld))
          (by simpa only [actualEq,whole,call] using run))
end Tests.ParsedExpectedWordStrictDataBridge
open Tests.ParsedExpectedWordStrictDataBridge in
def Tests.frontendParsedExpectedWordStrictDataBridgeTests : IO Unit := do
  let q := Solcore.Core.Value.closure .unit .word (.var 99) [.hostFunction .storageWrite,.cellRef .unit 700]
  let mut count := 0
  for c in [0,1,2^256-1,2^256-2,2^255] do
    for st in [[],[q,.cellRef .word 900,.hostFunction .storageWrite,.unit]] do
      exercise (Solcore.Core.Word.ofNatModulo c) q st; count := count+1
  check (count==10) "five boundary Words/two stores/both branches"
end

section
-- leanmerge: from Solcore.Test.FrontendParsedExpectedWordUnaryDataBridge
set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace Tests.ParsedExpectedWordUnaryDataBridge
open Solcore Solcore.Frontend
private def check (b : Bool) (s : String) : IO Unit := unless b do throw (IO.userError s)
private def proof {p : Prop} (_ : p) : IO Unit := pure ()
private def owner : Resolved.DeclarationId := ⟨⟨.main,⟨[⟨"ParsedWordData",by decide⟩],by decide⟩⟩,297⟩
private def sid (n : Nat) : Resolved.LocalId := ⟨owner,n⟩
private def foreign (n : Nat) : Resolved.LocalId := ⟨{owner with declarationIndex:=901},n⟩
private def inputs : LocalTypeInputs := ⟨[⟨"p",sid 7,.word⟩,⟨"q",sid 31,.unit⟩,⟨"w",sid 11,.word⟩,⟨"extra",foreign 700,.unit⟩,⟨"p",foreign 701,.word⟩],by decide⟩
private def types : TypeNameTable := [(["Word"],.word)]
private def up (e : Resolved.Environment) := e.map (fun r => (r.1,RuntimeValue.ofCore r.2))
private def heap (s : Core.Store) := s.map RuntimeValue.ofCore
private def env (w : Core.Word) (q : Core.Value) : Resolved.Environment := [(sid 7,.word w),(sid 31,q),(sid 11,.word w),(foreign 700,.cellRef .word 900),(foreign 701,.word w)]
private abbrev Child (n : LocalNameTable) (t : Resolved.Context) (s : Syntax.Expr) (c : Core.Expr) (v : Core.Ty) := ∃ r, ResolvesLocalExpression n s r ∧ Resolved.Lowers t.ids r c ∧ Resolved.HasType t r v
private structure EC (t : LocalTypeInputs) (e : Resolved.Environment) (s : Core.Store) (src : Syntax.Expr) where
  core : Core.Expr
  type : Core.Ty
  value : Core.Value
  cost : Nat
  depth : Nat
  gate : ClosedSourceDataExpression src
  elaboration : Child t.names t.context src core type
  old : LocalExpressionEvaluatesWithCost t.names e s src value s cost
  closed : ClosedSourceExpressionEvaluates owner t.names (up e) (heap s) src (RuntimeValue.ofCore value) (heap s)
private theorem mapped {e : Resolved.Environment} {i : Resolved.LocalId} {v : Core.Value} (h : Resolved.LocalScope.Lookup e i v) : Resolved.LocalScope.Lookup (up e) i (RuntimeValue.ofCore v) := by
  induction h with | head => exact .head | tail different _ ih => exact .tail different ih
private theorem path {t e s src} (h : EC t e s src) (same : e.ids=t.context.ids) (k : List Core.Frame) : Core.Steps h.cost ⟨.eval h.core e.values,k,s⟩ ⟨.ret h.value,k,s⟩ := by
  obtain ⟨r,res,low,_⟩ := h.elaboration; exact h.old.toStepsWithContinuation res (same ▸ low) k
private def expr (t : LocalTypeInputs) (e : Resolved.Environment) (s : Core.Store) (src : Syntax.Expr) : IO (EC t e s src) := do
  match shape : src with
  | ⟨_,.identifier name⟩ =>
    match named : t.names.lookup? name.value with
    | some i => match typed : t.context.lookup? i, found : e.lookup? i, indexed : Resolved.LocalScope.index? t.context.ids i with
      | some ty,some v,some n => return ⟨.var n,ty,v,1,1,by rw [shape]; exact .reference,
          by rw [shape]; exact ⟨.var i,.identifier (LocalNameTable.lookup?_iff.mp named),.var (Resolved.LocalScope.index?_iff.mp indexed),.var (Resolved.LocalScope.lookup?_iff.mp typed)⟩,
          by rw [shape]; exact .identifier (LocalNameTable.lookup?_iff.mp named) (Resolved.LocalScope.lookup?_iff.mp found),
          by rw [shape]; exact .reference (LocalNameTable.lookup?_iff.mp named) (mapped (Resolved.LocalScope.lookup?_iff.mp found))⟩
      | _,_,_ => throw (IO.userError "independent original row")
    | none => throw (IO.userError "independent original name")
  | ⟨_,.unary ⟨_,.bitNot⟩ child⟩ =>
    let h ← expr t e s child
    if ht : h.type=.word then
      match hv : h.value with
      | .word w => return ⟨.unary .wordNot h.core,.word,.word w.bitNot,h.cost+2,h.depth+1,by rw [shape]; exact .bitNot h.gate,
          by obtain ⟨r,a,b,c⟩ := h.elaboration; rw [shape]; exact ⟨.unary .wordNot r,.bitNot a,.unary b,.unary (by simpa only [ht,Core.UnaryOp.operandType] using c)⟩,
          by rw [shape]; exact .bitNot (hv ▸ h.old),by rw [shape]; simpa only [RuntimeValue.ofCore] using ClosedSourceExpressionEvaluates.bitNot (by simpa only [hv,RuntimeValue.ofCore] using h.closed)⟩
      | _ => throw (IO.userError "independent Word operand payload")
    else throw (IO.userError "independent Word static operand")
  | ⟨_,.tuple ⟨_,[left,right]⟩⟩ =>
    let l ← expr t e s left; let r ← expr t e s right
    return ⟨.pair l.core r.core,.product l.type r.type,.pair l.value r.value,l.cost+r.cost+3,max l.depth r.depth+1,
      by rw [shape]; exact .pair l.gate r.gate,
      by obtain ⟨a,ar,al,aty⟩ := l.elaboration; obtain ⟨b,br,bl,bt⟩ := r.elaboration; rw [shape]; exact ⟨.pair a b,.pair ar br,.pair al bl,.pair aty bt⟩,
      by rw [shape]; exact .pair l.old r.old,by rw [shape]; simpa only [RuntimeValue.ofCore] using ClosedSourceExpressionEvaluates.pair l.closed r.closed⟩
  | _ => throw (IO.userError "bounded identifier/unary/pair original")
termination_by sizeOf src
private structure BC (t : LocalTypeInputs) (e : Resolved.Environment) (s : Core.Store) (src : Syntax.Block) where
  core : Core.Expr
  value : Core.Value
  cost : Nat
  depth : Nat
  gate : ClosedSourceDataBody src
  elaboration : ComputationReturnTreeElaborates Child types owner t src core (.product .word .unit)
  old : ComputationReturnTreeEvaluates LocalExpressionEvaluates owner t.names e s src value s
  oldCost : ComputationReturnTreeEvaluatesWithCost LocalExpressionEvaluatesWithCost owner t.names e s src value s cost
  closed : ClosedSourceBodyEvaluates owner t.names (up e) (heap s) src (RuntimeValue.ofCore value) (heap s)
  path : ∀ k, Core.Steps cost ⟨.eval core e.values,k,s⟩ ⟨.ret value,k,s⟩
private def body (t : LocalTypeInputs) (e : Resolved.Environment) (s : Core.Store) (src : Syntax.Block) (same : e.ids=t.context.ids) : IO (BC t e s src) := do
  match shape : src with
  | ⟨bs,[⟨_,.letDecl name (some ⟨_,.named ann none⟩) (some init)⟩,⟨rs,.returnStmt (some result)⟩]⟩ =>
    let h ← expr t e s init
    if typed : types.lookup? (qualifiedTypeNameKey ann)=some .word ∧ h.type=.word then
      let t1 := t.bindFresh owner name.value .word
      let e1 : Resolved.Environment := (Resolved.freshLocalId owner t.ids,h.value)::e
      have same1 : e1.ids=t1.context.ids := by simpa only [e1,t1,LocalTypeInputs.bindFresh_context,Resolved.LocalScope.ids,List.map_cons] using congrArg (List.cons _) same
      let r ← expr t1 e1 s result
      if rt : r.type=.product .word .unit then
        return ⟨.letE h.core r.core,r.value,h.cost+r.cost+2,max h.depth (r.depth+1)+1,by rw [shape]; exact .binding h.gate (.expression r.gate),
          by rw [shape]; exact .binding (.named (TypeNameTable.lookup?_iff.mp typed.1)) (typed.2 ▸ h.elaboration) (.expression (rt ▸ r.elaboration)),
          by rw [shape]; apply ComputationReturnTreeEvaluates.binding h.old.erase; simpa only [e1,t1,LocalTypeInputs.bindFresh_names,LocalTypeInputs.names_ids] using ComputationReturnTreeEvaluates.expression (blockSpan:=bs) (returnSpan:=rs) (owner:=owner) r.old.erase,
          by rw [shape]; apply ComputationReturnTreeEvaluatesWithCost.binding h.old; simpa only [e1,t1,LocalTypeInputs.bindFresh_names,LocalTypeInputs.names_ids] using ComputationReturnTreeEvaluatesWithCost.expression (blockSpan:=bs) (returnSpan:=rs) (owner:=owner) r.old,
          by rw [shape]; apply ClosedSourceBodyEvaluates.binding h.closed; simpa only [e1,t1,LocalTypeInputs.bindFresh_names,LocalTypeInputs.names_ids,up,List.map_cons] using ClosedSourceBodyEvaluates.expression (blockSpan:=bs) (returnSpan:=rs) r.closed,
          fun k => CostStepComposition.letE (path h same _) (by simpa only [e1,Resolved.LocalScope.values,List.map_cons] using path r same1 k)⟩
      else throw (IO.userError "independent Word/opaque pair")
    else throw (IO.userError "independent Word shadow")
  | _ => throw (IO.userError "original shadow/return")
private def exprImages {t e s src} (h : EC t e s src) (same : e.ids=t.context.ids) {v st} (actual : ClosedSourceExpressionEvaluates owner t.names (up e) (heap s) src v st) : IO Unit := do
  have imageEq : v=RuntimeValue.ofCore h.value ∧ st=heap s := by
    obtain ⟨r,res,low,_⟩ := h.elaboration
    have lb := (h.gate.local_evaluates_iff (owner:=owner)).mpr (h.gate.local_evaluates_iff.mp actual)
    have ci := h.gate.core_evaluates_iff res (same ▸ low) (owner:=owner) (initialStore:=s) (actualValue:=v) (actualFinal:=st)
    have cb := ci.mpr (ci.mp lb)
    obtain ⟨a,b,hv,hs,ev⟩ := ci.mp cb
    have eq := Core.evaluation_deterministic ev (Core.steps_from_initial_sound (path h same [])); simpa only [eq.1,eq.2,heap] using And.intro hv hs
  proof imageEq; check (v.toCore?==some h.value && st.mapM RuntimeValue.toCore?==some s) "actual argument image after both directions"
private def bodyImages {t e s src} (h : BC t e s src) (same : e.ids=t.context.ids) {v st} (actual : ClosedSourceBodyEvaluates owner t.names (up e) (heap s) src v st) : IO Unit := do
  have checked := (elaborateComputationReturnTree?_iff elaborateLocalExpression?_iff).mpr h.elaboration
  let localImage := h.gate.local_evaluates_iff
  let coreImage := h.gate.core_evaluates_iff checked same
  proof (localImage.mp actual); proof (localImage.mpr (localImage.mp actual)); proof (coreImage.mp actual); proof (coreImage.mpr (coreImage.mp actual))
  have imageEq : v=RuntimeValue.ofCore h.value ∧ st=heap s := by obtain ⟨a,b,hv,hs,ev⟩ := coreImage.mp actual; have eq := Core.evaluation_deterministic ev (Core.steps_from_initial_sound (h.path [])); simpa only [eq.1,eq.2,heap] using And.intro hv hs
  proof imageEq; check (v.toCore?==some h.value && st.mapM RuntimeValue.toCore?==some s) "actual body image after both directions"
private def text := "(lam(p){let p:Word=~p;return(p,q);})(~w)"
private def file (s : String) : Syntax.SourceFile := ⟨⟨.main,"parsed-word-unary-data.sol"⟩,s⟩
private def sp (a b : Nat) : Syntax.SourceSpan := ⟨(file text).id,a,b⟩
private def ref (a b : Nat) (n : String) : Syntax.Expr := ⟨sp a b,.identifier ⟨sp a b,n⟩⟩
private def expected : Syntax.Expr :=
  let b : Syntax.Block := ⟨sp 7 35,[⟨sp 8 22,.letDecl ⟨sp 12 13,"p"⟩ (some ⟨sp 14 18,.named ⟨sp 14 18,⟨⟨⟨sp 14 18,"Word"⟩,[]⟩⟩⟩ none⟩) (some ⟨sp 19 21,.unary ⟨sp 19 20,.bitNot⟩ (ref 20 21 "p")⟩)⟩,
    ⟨sp 22 34,.returnStmt (some ⟨sp 28 33,.tuple ⟨sp 28 33,[ref 29 30 "p",ref 31 32 "q"]⟩⟩)⟩]⟩
  let f : Syntax.Expr := ⟨sp 1 35,.lambda (sp 1 4) ⟨sp 4 7,[⟨sp 5 6,.inferred ⟨sp 5 6,"p"⟩⟩]⟩ none b⟩
  ⟨sp 0 40,.call ⟨sp 0 36,.group f⟩ ⟨sp 36 40,[⟨sp 37 39,.unary ⟨sp 37 38,.bitNot⟩ (ref 38 39 "w")⟩]⟩⟩
private def savedExpected : Syntax.Expr := ⟨sp 0 10,.call (ref 0 6 "picked") ⟨sp 6 10,[⟨sp 7 9,.unary ⟨sp 7 8,.bitNot⟩ (ref 8 9 "w")⟩]⟩⟩
private def parsed (s : String) (want : Syntax.Expr) : IO Syntax.Expr := do
  let f := file s
  let .ok lexed := Syntax.Lexer.lex f | throw (IO.userError "lexer")
  match Syntax.Parser.expression (Syntax.Parser.State.initial f lexed) with
  | .ok src next => check (next.file==f && lexed.diagnostics.isEmpty && next.diagnostics.isEmpty && next.atEnd && src.span==Syntax.SourceSpan.fullFile f && src==want) "exact original AST, every range/source, EOF/diagnostics"; return src
  | _ => throw (IO.userError "parser")
private def caller : Resolved.DeclarationId := {owner with declarationIndex:=299}
private def cid (n : Nat) : Resolved.LocalId := ⟨caller,n⟩
private def names : LocalNameTable := [("picked",cid 7),("w",cid 900),("q",cid 42),("picked",cid 7)]
private def rows (fn : RuntimeValue) (w : Core.Word) : Resolved.LocalScope RuntimeValue := [(cid 900,.word w),(cid 7,fn),(cid 42,fn),(cid 7,.unit),(foreign 999,fn)]
private def coreRuns {e s c v k} (p : Core.Steps k (.initial c e s) (.final v s)) : IO Unit := do
  proof p
  for fuel in [0,k-1,k,k+3] do
    match run : Core.runStateful fuel (.initial c e s) with
    | .done value final => proof (Core.evaluation_deterministic (Core.runStateful_evaluation_sound run) (Core.steps_from_initial_sound p)); check (fuel≥k && value==v && final==s) "Core independently counted endpoint"
    | .outOfFuel _ => check (fuel<k) "Core independently counted exhaustion"
    | .fault _ _ => throw (IO.userError "Core fault")
private def closedRuns {o n e s src v} (d : Nat) (old : ClosedSourceExpressionEvaluates o n e s src v s)
    (after : ∀ {a z}, ClosedSourceExpressionEvaluates o n e s src a z → IO Unit) : IO Unit := do
  proof old
  for fuel in [0,d-1,d,d+3] do
    match run : evaluateClosedSourceExpression? fuel o n e s src with
    | none => check (fuel<d) "independent depth exhaustion"
    | some (_,_) => have actual := evaluateClosedSourceExpression?_sound run; proof (actual.deterministic old); after actual; check (fuel≥d) "independent closed depth/full endpoint"
private def consume {p : Prop} {e s c v a z} (old : Core.Evaluates e s c v s)
    (image : p ↔ ∃ value final, a=RuntimeValue.ofCore value ∧ z=heap final ∧ Core.Evaluates e s c value final) (actual : p) : IO Unit := do
  have forward := image.mp actual; proof forward; proof (image.mpr forward)
  have equal : a=RuntimeValue.ofCore v ∧ z=heap s := by obtain ⟨x,t,hx,ht,run⟩ := forward; have eq := Core.evaluation_deterministic run old; simpa only [eq.1,eq.2] using And.intro hx ht
  proof equal; check (a.toCore?==some v && z.mapM RuntimeValue.toCore?==some s) "full actual call image after mp/mpr"
private def reject {o n e s src} (no : ∀ a z, ¬ ClosedSourceExpressionEvaluates o n e s src a z) : IO Unit := do
  proof no
  for d in [0,1,4,5,8] do
    match run : evaluateClosedSourceExpression? d o n e s src with
    | none => pure ()
    | some _ => False.elim (no _ _ (evaluateClosedSourceExpression?_sound run))
private def exercise (w : Core.Word) (q : Core.Value) (s : Core.Store) : IO Unit := do
  let src ← parsed text expected; let picked ← parsed "picked(~w)" savedExpected; let e := env w q
  match original : src, savedShape : picked with
  | ⟨cs,.call ⟨gs,.group fs⟩ ⟨args,[arg]⟩⟩,⟨pcs,.call ⟨fnSpan,.identifier ⟨fnName,"picked"⟩⟩ ⟨pas,[⟨uas,.unary ⟨uos,.bitNot⟩ ⟨ws,.identifier ⟨wn,"w"⟩⟩⟩]⟩⟩ =>
    match fsShape : fs with
    | ⟨_,.lambda _ ⟨_,[⟨_,.inferred p⟩]⟩ none b⟩ =>
      have shape : SourceUnaryLambdaShape fs p b := by rw [fsShape]; exact .inferred
      let ac ← expr inputs e s arg
      let inner := inputs.bindFresh owner p.value .word
      let ie : Resolved.Environment := (Resolved.freshLocalId owner inputs.ids,ac.value)::e
      have same : e.ids=inputs.context.ids := rfl
      have same1 : ie.ids=inner.context.ids := by simpa only [ie,inner,LocalTypeInputs.bindFresh_context,Resolved.LocalScope.ids,List.map_cons] using congrArg (List.cons _) same
      let bc ← body inner ie s b same1
      have declaration : ExpectedUnaryLambdaHeaderDeclares types owner inputs fs (.function .word (.product .word .unit)) ⟨inner,b,.word,.product .word .unit⟩ := by rw [fsShape]; exact .lambda .inferred .omitted
      have expectedLambda : ExpectedComputationLambdaElaborates Child types owner inputs fs (.lambda .word (.product .word .unit) bc.core) (.function .word (.product .word .unit)) := .lambda declaration .word (.product .word .unit) bc.elaboration
      have checked := (elaborateExpectedComputationLambda?_iff elaborateLocalExpression?_iff).mpr expectedLambda
      let saved := RuntimeValue.sourceClosure fs owner inputs.names (up e)
      have creation : ClosedSourceExpressionEvaluates owner inputs.names (up e) (heap s) ⟨gs,.group fs⟩ saved (heap s) := .group (.creation shape)
      have directCreation : ClosedSourceExpressionEvaluates owner inputs.names (up e) (heap s) fs saved (heap s) := .creation shape
      have beta : ClosedSourceBodyEvaluates owner ((p.value,Resolved.freshLocalId owner (inputs.names.map Prod.snd))::inputs.names) ((Resolved.freshLocalId owner (inputs.names.map Prod.snd),RuntimeValue.ofCore ac.value)::up e) (heap s) b (RuntimeValue.ofCore bc.value) (heap s) := by simpa only [ie,inner,LocalTypeInputs.bindFresh_names,LocalTypeInputs.names_ids,up,List.map_cons] using bc.closed
      have whole : ClosedSourceExpressionEvaluates owner inputs.names (up e) (heap s) src (RuntimeValue.ofCore bc.value) (heap s) := by rw [original]; exact .call shape creation ac.closed beta
      let direct : Syntax.Expr := ⟨cs,.call fs ⟨args,[arg]⟩⟩
      have directOld : ClosedSourceExpressionEvaluates owner inputs.names (up e) (heap s) direct (RuntimeValue.ofCore bc.value) (heap s) := .call shape directCreation ac.closed beta
      have betaPath (k) : Core.Steps bc.cost ⟨.eval bc.core (ac.value::e.values),k,s⟩ ⟨.ret bc.value,k,s⟩ := by simpa only [ie,Resolved.LocalScope.values,List.map_cons] using bc.path k
      let core := Core.Expr.apply (.lambda .word (.product .word .unit) bc.core) ac.core
      have full (k) : Core.Steps (1+ac.cost+bc.cost+3) ⟨.eval core e.values,k,s⟩ ⟨.ret bc.value,k,s⟩ := CostStepComposition.apply (.cons .lambda .refl) (path ac same _) (betaPath [])
      let depth := max 2 (max ac.depth bc.depth)+1
      proof expectedLambda; proof ac.old; proof bc.oldCost; proof whole; proof directOld; proof (full [])
      check (decide (ac.core=.unary .wordNot (.var 2) ∧ bc.core=.letE (.unary .wordNot (.var 0)) (.pair (.var 0) (.var 3)) ∧ ac.cost=3 ∧ bc.cost=10 ∧ depth=5 ∧ p.value="p" ∧ Resolved.freshLocalId owner inputs.ids=sid 32 ∧ Resolved.freshLocalId owner inner.ids=sid 33 ∧ ac.value=.word w.bitNot ∧ bc.value=.pair (.word w.bitNot.bitNot) q)) "independent literal typing/Core/cost/depth/endpoints"
      if argValue : ac.value=.word w.bitNot then
        let savedCore := Core.Expr.apply (.var 0) (.unary .wordNot (.var 1))
        let savedCoreRows := [Core.Value.closure .word (.product .word .unit) bc.core e.values,.word w,q]
        have savedPath : Core.Steps (1+3+bc.cost+3) (.initial savedCore savedCoreRows s) (.final bc.value s) :=
          CostStepComposition.apply (.cons (.var rfl) .refl) (CostStepComposition.unary (.cons (.var rfl) .refl) rfl) (by simpa only [argValue,Core.State.initial,Core.State.final] using betaPath [])
        coreRuns savedPath
        coreRuns (full []); coreRuns (betaPath []); coreRuns (path ac same [])
        match made : evaluateClosedSourceExpression? 2 owner inputs.names (up e) (heap s) ⟨gs,.group fs⟩ with
        | none => throw (IO.userError "actual grouped creation")
        | some (actualClosure,calleeStore) =>
          have madeEq := (evaluateClosedSourceExpression?_sound made).deterministic creation
          match arun : evaluateClosedSourceExpression? ac.depth owner inputs.names (up e) calleeStore arg with
          | none => throw (IO.userError "actual argument after callee store")
          | some (actualArg,argumentStore) =>
            have ae := evaluateClosedSourceExpression?_sound arun
            have ae0 : ClosedSourceExpressionEvaluates owner inputs.names (up e) (heap s) arg actualArg argumentStore := by rw [madeEq.2] at ae; exact ae
            exprImages ac same ae0
            have argEq := ae0.deterministic ac.closed
            have fnEval : ClosedSourceExpressionEvaluates owner inputs.names (up e) (heap s) ⟨gs,.group fs⟩ saved calleeStore := by simpa only [madeEq.1] using evaluateClosedSourceExpression?_sound made
            have argEval : ClosedSourceExpressionEvaluates owner inputs.names (up e) calleeStore arg (RuntimeValue.ofCore ac.value) (heap s) := by simpa only [argEq.1,argEq.2] using ae
            match brun : evaluateClosedSourceBody? bc.depth owner inner.names ((Resolved.freshLocalId owner inputs.ids,actualArg)::up e) argumentStore b with
            | none => throw (IO.userError "actual body after argument store")
            | some (bv,bst) =>
              have be := evaluateClosedSourceBody?_sound brun
              have normalized : ClosedSourceBodyEvaluates owner inner.names (up ie) (heap s) b bv bst := by simpa only [argEq.1,argEq.2,ie,up,List.map_cons] using be
              bodyImages bc same1 normalized
            closedRuns depth whole (fun {a z} actual => consume (a:=a) (z:=z) (Core.steps_from_initial_sound (betaPath [])) (closedSourceExpectedDataLambda_invocation_core_iff shape bc.gate checked same fnEval argEval (callSpan:=cs) (argumentsSpan:=args) (actualValue:=a) (actualFinal:=z)) (by simpa only [original] using actual))
            have directImage {a z} : ClosedSourceExpressionEvaluates owner inputs.names (up e) (heap s) direct a z ↔ ∃ v t, a=RuntimeValue.ofCore v ∧ z=heap t ∧ Core.Evaluates e.values s core v t := by
              obtain ⟨r,res,low,_⟩ := ac.elaboration
              exact closedSourceExpectedDataLambda_application_core_iff shape bc.gate checked same ac.gate res (same ▸ low)
            closedRuns depth directOld (fun actual => consume (Core.steps_from_initial_sound (full [])) directImage actual)
            let cr := rows actualClosure w
            have fn : ClosedSourceExpressionEvaluates caller names cr calleeStore ⟨fnSpan,.identifier ⟨fnName,"picked"⟩⟩ saved calleeStore := by rw [← madeEq.1]; exact .reference .head (.tail (by decide) .head)
            have savedArg : ClosedSourceExpressionEvaluates caller names cr calleeStore ⟨uas,.unary ⟨uos,.bitNot⟩ ⟨ws,.identifier ⟨wn,"w"⟩⟩⟩ (RuntimeValue.ofCore ac.value) (heap s) := by rw [madeEq.2,argValue]; simp only [RuntimeValue.ofCore]; apply ClosedSourceExpressionEvaluates.bitNot; exact .reference (.tail (by change "picked" ≠ "w"; decide) .head) .head
            have savedOld : ClosedSourceExpressionEvaluates caller names cr calleeStore picked (RuntimeValue.ofCore bc.value) calleeStore := by rw [madeEq.2,savedShape]; exact .call shape (by simpa only [madeEq.2] using fn) (by simpa only [madeEq.2] using savedArg) beta
            proof fn; proof savedArg; proof savedOld
            match fetched : evaluateClosedSourceExpression? 1 caller names cr calleeStore ⟨fnSpan,.identifier ⟨fnName,"picked"⟩⟩ with
            | none => throw (IO.userError "actual saved callee")
            | some (actualFn,savedCalleeStore) =>
              have feq := (evaluateClosedSourceExpression?_sound fetched).deterministic fn
              match sar : evaluateClosedSourceExpression? 2 caller names cr savedCalleeStore ⟨uas,.unary ⟨uos,.bitNot⟩ ⟨ws,.identifier ⟨wn,"w"⟩⟩⟩ with
              | none => throw (IO.userError "actual saved argument")
              | some (sa,sas) =>
                have sae := evaluateClosedSourceExpression?_sound sar
                have sae0 : ClosedSourceExpressionEvaluates caller names cr calleeStore ⟨uas,.unary ⟨uos,.bitNot⟩ ⟨ws,.identifier ⟨wn,"w"⟩⟩⟩ sa sas := by rw [feq.2] at sae; exact sae
                have seq := sae0.deterministic savedArg
                have sf : ClosedSourceExpressionEvaluates caller names cr calleeStore ⟨fnSpan,.identifier ⟨fnName,"picked"⟩⟩ saved savedCalleeStore := by simpa only [feq.1] using evaluateClosedSourceExpression?_sound fetched
                have se : ClosedSourceExpressionEvaluates caller names cr savedCalleeStore ⟨uas,.unary ⟨uos,.bitNot⟩ ⟨ws,.identifier ⟨wn,"w"⟩⟩⟩ (RuntimeValue.ofCore ac.value) (heap s) := by simpa only [seq.1,seq.2] using sae
                match sbr : evaluateClosedSourceBody? bc.depth owner inner.names ((Resolved.freshLocalId owner inputs.ids,sa)::up e) sas b with
                | none => throw (IO.userError "actual saved body")
                | some (sv,ss) => bodyImages bc same1 (v:=sv) (st:=ss) (by simpa only [seq.1,seq.2,ie,up,List.map_cons] using evaluateClosedSourceBody?_sound sbr)
                closedRuns depth savedOld (fun {a z} actual => consume (a:=a) (z:=z) (Core.steps_from_initial_sound (betaPath [])) (closedSourceExpectedDataLambda_invocation_core_iff shape bc.gate checked same sf se (callSpan:=pcs) (argumentsSpan:=pas) (actualValue:=a) (actualFinal:=z)) (by simpa only [savedShape] using actual))
        let wrong : Syntax.Expr := ⟨cs,.unary ⟨cs,.bitNot⟩ (ref 0 1 "bad")⟩
        have admitted : ClosedSourceDataExpression wrong := .bitNot .reference
        have badOperand : ClosedSourceExpressionEvaluates owner [("bad",sid 1)] [(sid 1,.bool true)] (heap s) (ref 0 1 "bad") (.bool true) (heap s) := .reference .head .head
        have impossible : ∀ a z, ¬ ClosedSourceExpressionEvaluates owner [("bad",sid 1)] [(sid 1,.bool true)] (heap s) wrong a z := by
          intro a z ev; dsimp only [wrong] at ev; cases ev with | bitNot child => have eq := child.deterministic badOperand; cases eq.1 | creation sh => cases sh
        proof admitted; proof badOperand; reject impossible
        let over : Syntax.Expr := ⟨cs,.unary ⟨cs,.bitNot⟩ src⟩
        have excluded : ¬ ClosedSourceDataExpression over := by intro gate; dsimp only [over] at gate; cases gate with | bitNot child => rw [original] at child; cases child
        proof excluded
        match val : bc.value with
        | .pair x y =>
          have no : ∀ a z, ¬ ClosedSourceExpressionEvaluates owner inputs.names (up e) (heap s) over a z := by
            intro a z ev; dsimp only [over] at ev; cases ev with
            | bitNot child => have eq := child.deterministic whole; simp only [val,RuntimeValue.ofCore] at eq; cases eq.1
            | creation sh => cases sh
          reject no
        | _ => throw (IO.userError "independent original pair endpoint required")
      else throw (IO.userError "independent argument endpoint")
    | _ => throw (IO.userError "actual inferred lambda")
  | _,_ => throw (IO.userError "actual grouped and saved call")
end Tests.ParsedExpectedWordUnaryDataBridge
open Tests.ParsedExpectedWordUnaryDataBridge in
def Tests.frontendParsedExpectedWordUnaryDataBridgeTests : IO Unit := do
  let q := Solcore.Core.Value.closure .unit .word (.var 99) [.hostFunction .storageWrite,.cellRef .unit 700]
  for w in [Solcore.Core.Word.ofNatModulo 0,Solcore.Core.Word.ofNatModulo 1,Solcore.Core.Word.ofNatModulo (2^256-1)] do
    for s in [[],[q,.cellRef .word 900,.hostFunction .storageWrite,.unit]] do exercise w q s
end

section
-- leanmerge: from Solcore.Test.FrontendStrictWordDataBoundaryProperties
/- Admission is recursive syntax, not runtime typing, successful evaluation or
whole name resolution. Conversely original calls can succeed outside this gate. -/
set_option autoImplicit false
namespace Tests.StrictWordDataBoundary
open Solcore Solcore.Frontend

private def reference (span : Syntax.SourceSpan) (name : Syntax.Identifier) : Syntax.Expr :=
  ⟨span,.identifier name⟩
private def binary (span opSpan : Syntax.SourceSpan) (op : Syntax.BinaryOp)
    (left right : Syntax.Expr) : Syntax.Expr := ⟨span,.binary left ⟨opSpan,op⟩ right⟩

theorem admitted_non_word_operands_still_never_succeed
    (owner : Resolved.DeclarationId) (names : LocalNameTable)
    (captured : Resolved.LocalScope RuntimeValue) (store : List RuntimeValue)
    (span opSpan goodSpan badSpan : Syntax.SourceSpan)
    (op : Syntax.BinaryOp) (notAnd : op ≠ .logicalAnd) (notOr : op ≠ .logicalOr)
    (goodName badName : Syntax.Identifier) (goodId badId : Resolved.LocalId)
    (word : Core.Word) (bad : RuntimeValue) (notWord : ∀ w, bad ≠ .word w)
    (goodNamed : LocalNameTable.Lookup names goodName.value goodId)
    (badNamed : LocalNameTable.Lookup names badName.value badId)
    (goodFound : Resolved.LocalScope.Lookup captured goodId (.word word))
    (badFound : Resolved.LocalScope.Lookup captured badId bad) :
    ClosedSourceDataExpression (binary span opSpan op
      (reference badSpan badName) (reference goodSpan goodName)) ∧
    ClosedSourceDataExpression (binary span opSpan op
      (reference goodSpan goodName) (reference badSpan badName)) ∧
    ClosedSourceExpressionEvaluates owner names captured store
      (reference goodSpan goodName) (.word word) store ∧
    ClosedSourceExpressionEvaluates owner names captured store
      (reference badSpan badName) bad store ∧
    ∀ actual final,
      (¬ ClosedSourceExpressionEvaluates owner names captured store
        (binary span opSpan op (reference badSpan badName) (reference goodSpan goodName)) actual final) ∧
      (¬ ClosedSourceExpressionEvaluates owner names captured store
        (binary span opSpan op (reference goodSpan goodName) (reference badSpan badName)) actual final) := by
  have independent := ClosedStrictWordBinaryNegative.non_word_reference_on_either_side_never_succeeds
    owner names captured store span opSpan goodSpan badSpan op notAnd notOr
    goodName badName goodId badId word bad notWord goodNamed badNamed goodFound badFound
  exact ⟨.strictWordBinary .reference .reference notAnd notOr,
    .strictWordBinary .reference .reference notAnd notOr,independent⟩

theorem admitted_zero_never_skips_a_missing_operand
    (owner : Resolved.DeclarationId) (names : LocalNameTable)
    (captured : Resolved.LocalScope RuntimeValue) (store : List RuntimeValue)
    (span opSpan zeroSpan missingSpan : Syntax.SourceSpan)
    (op : Syntax.BinaryOp) (notAnd : op ≠ .logicalAnd) (notOr : op ≠ .logicalOr)
    (zeroName missingName : Syntax.Identifier) (zeroId : Resolved.LocalId)
    (zeroNamed : LocalNameTable.Lookup names zeroName.value zeroId)
    (zeroFound : Resolved.LocalScope.Lookup captured zeroId (.word Core.Word.zero))
    (missing : LocalNameTable.lookup? names missingName.value = none ∨
      ∃ id, LocalNameTable.Lookup names missingName.value id ∧ Resolved.LocalScope.lookup? captured id = none) :
    ClosedSourceDataExpression (binary span opSpan op
      (reference zeroSpan zeroName) (reference missingSpan missingName)) ∧
    ClosedSourceDataExpression (binary span opSpan op
      (reference missingSpan missingName) (reference zeroSpan zeroName)) ∧
    ClosedSourceExpressionEvaluates owner names captured store
      (reference zeroSpan zeroName) (.word Core.Word.zero) store ∧
    ∀ actual final,
      (¬ ClosedSourceExpressionEvaluates owner names captured store
        (binary span opSpan op (reference zeroSpan zeroName) (reference missingSpan missingName)) actual final) ∧
      (¬ ClosedSourceExpressionEvaluates owner names captured store
        (binary span opSpan op (reference missingSpan missingName) (reference zeroSpan zeroName)) actual final) := by
  have independent := ClosedStrictWordBinaryNegative.zero_never_skips_a_missing_reference_on_either_side
    owner names captured store span opSpan zeroSpan missingSpan op notAnd notOr
    zeroName missingName zeroId zeroNamed zeroFound missing
  exact ⟨.strictWordBinary .reference .reference notAnd notOr,
    .strictWordBinary .reference .reference notAnd notOr,independent⟩

theorem admitted_addition_does_not_imply_name_resolution
    (names : LocalNameTable) (span opSpan missingSpan : Syntax.SourceSpan)
    (name : Syntax.Identifier) (missing : LocalNameTable.lookup? names name.value = none) :
    ClosedSourceDataExpression (binary span opSpan .add
      (reference missingSpan name) (reference missingSpan name)) ∧
    ∀ resolved, ¬ ResolvesLocalExpression names
      (binary span opSpan .add (reference missingSpan name) (reference missingSpan name)) resolved := by
  refine ⟨.strictWordBinary .reference .reference (by decide) (by decide),?_⟩
  intro resolved resolution
  cases resolution with
  | add left _ =>
      cases left with
      | identifier named =>
          have found := LocalNameTable.lookup?_iff.mpr named
          rw [missing] at found
          cases found

private def identityBody (s : Nat → Syntax.SourceSpan) : Syntax.Block :=
  ⟨s 0,[⟨s 1,.returnStmt (some (reference (s 2) ⟨s 3,"p"⟩))⟩]⟩
private def identity (s : Nat → Syntax.SourceSpan) : Syntax.Expr :=
  ⟨s 4,.lambda (s 5) ⟨s 6,[⟨s 7,.inferred ⟨s 8,"p"⟩⟩]⟩ none (identityBody s)⟩
private def call (s : Nat → Syntax.SourceSpan) (argument : Syntax.Expr) : Syntax.Expr :=
  ⟨s 9,.call (identity s) ⟨s 10,[argument]⟩⟩

/-- Actual creation, argument and body evidence build a successful strict original
path. The call/lambda exclusion of the syntax-only Core-image gate is retained. -/
theorem original_call_operand_succeeds_outside_the_data_gate
    (owner : Resolved.DeclarationId) (names : LocalNameTable)
    (captured : Resolved.LocalScope RuntimeValue) (store : List RuntimeValue)
    (s : Nat → Syntax.SourceSpan) (name : Syntax.Identifier) (id : Resolved.LocalId)
    (word : Core.Word) (named : LocalNameTable.Lookup names name.value id)
    (found : Resolved.LocalScope.Lookup captured id (.word word))
    (op : Syntax.BinaryOp) (result : Core.Value) (meaning : StrictWordBinaryDenotes op word word result) :
    let argument := reference (s 11) name
    let src := binary (s 12) (s 13) op (call s argument) argument
    ClosedSourceExpressionEvaluates owner names captured store (identity s)
      (.sourceClosure (identity s) owner names captured) store ∧
    ClosedSourceExpressionEvaluates owner names captured store argument (.word word) store ∧
    ClosedSourceBodyEvaluates owner
      (("p",Resolved.freshLocalId owner (names.map Prod.snd))::names)
      ((Resolved.freshLocalId owner (names.map Prod.snd),.word word)::captured)
      store (identityBody s) (.word word) store ∧
    ClosedSourceExpressionEvaluates owner names captured store (call s argument) (.word word) store ∧
    ClosedSourceExpressionEvaluates owner names captured store src (RuntimeValue.ofCore result) store ∧
    (¬ ClosedSourceDataExpression (identity s)) ∧
    (¬ ClosedSourceDataExpression (call s argument)) ∧
    ¬ ClosedSourceDataExpression src := by
  dsimp only
  have created : ClosedSourceExpressionEvaluates owner names captured store (identity s)
      (.sourceClosure (identity s) owner names captured) store := .creation .inferred
  have argument : ClosedSourceExpressionEvaluates owner names captured store
      (reference (s 11) name) (.word word) store := .reference named found
  have body : ClosedSourceBodyEvaluates owner
      (("p",Resolved.freshLocalId owner (names.map Prod.snd))::names)
      ((Resolved.freshLocalId owner (names.map Prod.snd),.word word)::captured)
      store (identityBody s) (.word word) store := .expression (.reference .head .head)
  have invoked : ClosedSourceExpressionEvaluates owner names captured store
      (call s (reference (s 11) name)) (.word word) store := .call .inferred created argument body
  have original : ClosedSourceExpressionEvaluates owner names captured store
      (binary (s 12) (s 13) op (call s (reference (s 11) name)) (reference (s 11) name))
      (RuntimeValue.ofCore result) store := .strictWordBinary invoked argument meaning
  have noLambda : ¬ ClosedSourceDataExpression (identity s) := by intro gate; cases gate
  have noCall : ¬ ClosedSourceDataExpression (call s (reference (s 11) name)) := by intro gate; cases gate
  refine ⟨created,argument,body,invoked,original,noLambda,noCall,?_⟩
  intro gate
  cases gate with
  | logicalAnd _ _ => exact meaning.operator_is_strict.1 rfl
  | logicalOr _ _ => exact meaning.operator_is_strict.2 rfl
  | strictWordBinary left _ _ _ => exact noCall left

end Tests.StrictWordDataBoundary
end

section
-- leanmerge: from Solcore.Test.FrontendStrictWordDataImageProperties
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
  | .shiftLeft | .shiftRight | .uncheckedAdd | .uncheckedSubtract | .uncheckedMultiply | .uncheckedDivide | .uncheckedModulo
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
  | .shiftLeft | .shiftRight | .uncheckedAdd | .uncheckedSubtract | .uncheckedMultiply | .uncheckedDivide | .uncheckedModulo
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
end
