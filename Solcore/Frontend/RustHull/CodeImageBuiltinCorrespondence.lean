import Solcore.Frontend.RustHull.CodeImageSemantics
import Solcore.Frontend.RustHull.MemoryCopyBuiltinCorrespondence

/-! The actual outer compiler resolves the code-image guard and packed copying.
A known image reaches the existing source copy theorem; an unavailable image
returns its language fault before memory expansion or helper allocation. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.CodeImageBuiltinCorrespondence
open Core Correspondence PureCallCorrespondence EffectBuiltinCorrespondence
open CodeImageSemantics (Operation)

theorem inner_arity (operation : Operation) {scope : Scope}
    {arguments : List Core.Expr} {lowered : Lowered}
    (compiled : Effects.lowerBuiltin scope operation.name arguments = .ok lowered) :
    arguments.length = 3 := by
  cases operation <;>
    rcases arguments with _ | ⟨first, _ | ⟨second, _ | ⟨third, _ | ⟨fourth, rest⟩⟩⟩⟩
  all_goals first
    | rfl
    | change Except.error _ = Except.ok lowered at compiled
      cases compiled

theorem components (operation : Operation) {scope : Scope} {destination source length : Core.Expr} {lowered : Lowered}
    (compiled : Effects.lowerBuiltin scope operation.name [destination, source, length] = .ok lowered) :
    ∃ memory size code known,
      Effects.reference scope "memory" WordMapping.type = .ok memory ∧
      Effects.reference scope "memorySize" .word = .ok size ∧
      Effects.reference scope "code" WordMapping.type = .ok code ∧
      Effects.reference scope "codeKnown" .bool = .ok known ∧
      lowered = ⟨.unit, .ifE (.loadCell known)
        (Memory.copyPackedFrom memory size destination (.loadCell code) source length)
        (LanguageResult.failure .unit (.word (Word.ofNatModulo 15)))⟩ := by
  have expanded : (do
      let raw ← (do
        let memory ← Effects.reference scope "memory" WordMapping.type
        let size ← Effects.reference scope "memorySize" .word
        let code ← Effects.reference scope "code" WordMapping.type
        let guarded ← Effects.requireCode scope .unit
          (Memory.copyPackedFrom memory size destination (.loadCell code) source length)
        pure (Lowered.mk .unit guarded) : LowerM Lowered)
      pure raw) = .ok lowered := by
    cases operation <;> exact compiled
  obtain ⟨memory, memoryCompiled, expanded⟩ := lower_bind_eq_ok.mp expanded
  obtain ⟨size, sizeCompiled, expanded⟩ := lower_bind_eq_ok.mp expanded
  obtain ⟨code, codeCompiled, expanded⟩ := lower_bind_eq_ok.mp expanded
  obtain ⟨guarded, guardCompiled, returned⟩ := lower_bind_eq_ok.mp expanded
  obtain ⟨known, knownCompiled, guardResult⟩ := lower_bind_eq_ok.mp guardCompiled
  cases Except.ok.inj guardResult
  exact ⟨memory, size, code, known, memoryCompiled, sizeCompiled, codeCompiled, knownCompiled,
    (Except.ok.inj returned).symm⟩

theorem preserves (operation : Operation)
    {scope : Scope} {expected : Core.Ty} {arguments : List Lowered} {lowered : Lowered}
    (compiled : lowerBuiltin scope operation.name expected arguments = .ok lowered)
    {image : Option (List UInt8)} {sourceType : Ty} {sources : List Semantics.Value}
    {state finalState : MemorySemantics.State} {result : Semantics.Result Semantics.Value}
    (called : CodeImageSemantics.Builtin image operation.name sourceType sources state result finalState)
    {targets : List Core.Value} (related : ArgumentsRel arguments sources targets)
    {slots : List EffectSlot} {mapping : Renaming} {environment : Environment}
    {initial store : Store} {memoryLocation sizeLocation codeLocation knownLocation : Nat}
    (runtime : EffectEnvironmentRel slots scope mapping environment)
    (memoryMember : ⟨"memory", WordMapping.type, memoryLocation⟩ ∈ slots)
    (sizeMember : ⟨"memorySize", .word, sizeLocation⟩ ∈ slots)
    (codeMember : ⟨"code", WordMapping.type, codeLocation⟩ ∈ slots)
    (knownMember : ⟨"codeKnown", .bool, knownLocation⟩ ∈ slots)
    (codeRead : store.read? codeLocation = some (WordMapping.encode (Memory.packBytes (image.getD []))))
    (knownRead : store.read? knownLocation = some (.bool image.isSome))
    (stateRelated : MemoryCorrespondence.StateRel memoryLocation sizeLocation state store)
    (packed : Evaluates environment initial ((packArguments arguments).expression.rename mapping)
      (.inRight .word (ScalarExecution.bundleValues targets)) store) :
    ∃ target finalStore,
      ResultRel lowered.type result target ∧
      Evaluates environment initial (lowered.expression.rename mapping) target finalStore ∧
      MemoryCorrespondence.StateRel memoryLocation sizeLocation finalState finalStore ∧
      MemoryCorrespondence.Frame memoryLocation sizeLocation store finalStore := by
  have supported : Effects.supports operation.name = true := by cases operation <;> rfl
  obtain ⟨words, raw, rawCompiled, typed, loweredEqual⟩ := outer_components supported compiled
  have arity : arguments.length = 3 := by
    simpa only [List.length_map, List.length_range] using inner_arity operation rawCompiled
  obtain ⟨destinationExpr, sourceExpr, lengthExpr, destination, source, length, rfl, rfl, rfl⟩ :=
    MemoryCopyBuiltinCorrespondence.three_words related words arity
  obtain ⟨memory, size, code, known, memoryCompiled, sizeCompiled, codeCompiled, knownCompiled, rfl⟩ :=
    components operation rawCompiled
  cases typed
  cases loweredEqual
  let input := Value.pair (.word destination) (.pair (.word source) (.word length))
  let inputType := Core.Ty.product .word (.product .word .word)
  have runtime' := runtime.temporary inputType input
  generalize named : operation.name = name at called
  cases called with
  | copy sourceOperation executed =>
      cases executed with
      | unknown absent =>
          subst image
          refine ⟨.inLeft .unit (.word (Word.ofNatModulo 15)), store, .language _, ?_, stateRelated, .refl _ _ _⟩
          apply LanguageResult.bind_success .unit packed
          exact .ifFalse (.loadCell (reference_evaluates runtime' knownMember knownCompiled store) knownRead) (.inLeft .word)
      | copied present executed =>
          subst image
          obtain ⟨target, finalStore, resultRelated, evaluated, finalRelated, frame⟩ :=
            MemoryCopyCorrespondence.copyPackedFrom_preserves executed stateRelated
              (reference_evaluates runtime' memoryMember memoryCompiled store)
              (reference_evaluates runtime' sizeMember sizeCompiled store)
              (.first (.var (index := 0) rfl))
              (.loadCell (reference_evaluates runtime' codeMember codeCompiled store) codeRead)
              (.first (.second (.var (index := 0) rfl)))
              (by apply Evaluates.second; apply Evaluates.second; apply Evaluates.var (index := 0); rfl)
          refine ⟨target, finalStore, resultRelated, ?_, finalRelated, frame⟩
          apply LanguageResult.bind_success .unit packed
          apply Evaluates.ifTrue (.loadCell (reference_evaluates runtime' knownMember knownCompiled store) knownRead)
          rw [MemoryCopyCorrespondence.copyPackedFrom_rename]
          exact evaluated

end Solcore.Frontend.RustHull.CodeImageBuiltinCorrespondence
