import Solcore.Frontend.SourceCoreCompatibleDataMatches
import Solcore.SourceSemantics.Dynamic.Pattern

/-! Static receipts for the actual compatible pattern compiler. Constructor
syntax includes its retained raw registry guard, and matcher typing uses the
actual ambient definitions. The structural tree has no runtime meaning fields. -/

set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatiblePatternCertificates
open Frontend Frontend.SourceInference
open SourceCoreCompatibleDataMatches

abbrev Compilation := SourceCoreCompatibleDataMatches.Context

def wildcardPattern (type : Core.Ty) : Pattern :=
  ⟨type, [], [], .lambda type (.sum .unit .unit) (.inRight .unit .unit)⟩

def binderPattern (type : Core.Ty) (binder : TypedBinder) : Pattern :=
  ⟨type, [(binder, type)], [], .lambda type (.sum .unit type) (.inRight .unit (.var 0))⟩

def tuplePattern (type : Core.Ty) (children : List Pattern) (types : List Core.Ty) : Pattern :=
  let bindings := children.flatMap (·.bindings)
  let output := bundleType (bindings.map Prod.snd)
  ⟨type, bindings, children.flatMap (·.requirements),
    .lambda type (.sum .unit output) (matchChildren output children (childValues types) [])⟩

def constructorPattern (type : Core.Ty) (constructor : Core.ConstructorId)
    (definition : Core.DataDefinition) (metadata : Core.Word) (children : List Pattern) (types : List Core.Ty) : Pattern :=
  let bindings := children.flatMap (·.bindings)
  let output := bundleType (bindings.map Prod.snd)
  let branches := definition.constructorPayloadTypes.zipIdx.map fun (_, index) =>
    if index = constructor.index then rawConstructor metadata output
      (matchChildren output children (types.zipIdx.map fun (_, index) =>
        SourceCoreDataExpressions.projectPacked index types (.second (.var 0))) []) else .inLeft output .unit
  ⟨type, bindings, children.flatMap (·.requirements),
    .lambda type (.sum .unit output) (.matchData constructor.owner (.sum .unit output) (.var 0) branches)⟩

mutual
  inductive Tree (compilation : Compilation) (source : TypedSource) (site : StatementId)
      (span : Syntax.SourceSpan) (scope : Scope) :
      TypeSystem.Ty → List MatchPatternInstruction → Pattern → List MatchPatternInstruction → Prop where
    | wildcard {expected type rest}
        (projection : projected compilation source expected = .ok type) :
        Tree compilation source site span scope expected (.wildcard :: rest) (wildcardPattern type) rest
    | binder {expected type binder rest}
        (projection : projected compilation source expected = .ok type)
        (sourceType : binder.scheme.body = expected)
        (valid : SourceCoreCompatibleDataExpressions.lowerBinder compilation.checked source scope binder = .ok type) :
        Tree compilation source site span scope expected (.binder binder :: rest) (binderPattern type binder) rest
    | literal {expected type literal resolution matcher rest}
        (projection : projected compilation source expected = .ok type)
        (validated : literalMatcher compilation site span expected literal resolution = .ok matcher) :
        Tree compilation source site span scope expected (.integerLiteral literal resolution :: rest)
          ⟨type, [], [resolution.requirement], matcher⟩ rest
    | tuple {expected type count types instructions rest children coreTypes}
        (projection : projected compilation source expected = .ok type)
        (unpacked : unpackTypes count expected = some types)
        (childrenTyped : Forest compilation source site span scope types instructions children rest)
        (projectedChildren : types.mapM (projected compilation source) = .ok coreTypes) :
        Tree compilation source site span scope expected (.tuple count :: instructions)
          (tuplePattern type children coreTypes) rest
    | constructor {expected type instantiation arity constructor definition metadata instructions rest children coreTypes}
        (projection : projected compilation source expected = .ok type)
        (result : instantiation.resultType = expected)
        (count : arity = instantiation.payloadTypes.length)
        (resolved : compilation.checked.resolveConstructor instantiation = .ok constructor)
        (coreType : type = .namedData constructor.owner)
        (raw : compilation.values.registry.id? (.constructor instantiation) = some metadata)
        (childrenTyped : Forest compilation source site span scope instantiation.payloadTypes instructions children rest)
        (projectedChildren : instantiation.payloadTypes.mapM (projected compilation source) = .ok coreTypes)
        (registered : compilation.checked.catalog.definitions[constructor.owner.index]? = some definition) :
        Tree compilation source site span scope expected (.constructor instantiation arity :: instructions)
          (constructorPattern type constructor definition metadata children coreTypes) rest

  inductive Forest (compilation : Compilation) (source : TypedSource) (site : StatementId)
      (span : Syntax.SourceSpan) (scope : Scope) : List TypeSystem.Ty → List MatchPatternInstruction →
      List Pattern → List MatchPatternInstruction → Prop where
    | nil {instructions} : Forest compilation source site span scope [] instructions [] instructions
    | cons {type types instructions afterHead rest head tail}
        (headTyped : Tree compilation source site span scope type instructions head afterHead)
        (tailTyped : Forest compilation source site span scope types afterHead tail rest) :
        Forest compilation source site span scope (type :: types) instructions (head :: tail) rest
end

/-- Both parts follow the same traversal budget used by the existing compiler;
there is no second pattern parsing or matching algorithm in the certificate. -/
theorem trees_of_compile (fuel : Nat) (compilation : Compilation) (source : TypedSource)
    (site : StatementId) (span : Syntax.SourceSpan) (scope : Scope) :
    (∀ expected instructions pattern rest,
      compileOne compilation source site span scope fuel expected instructions = .ok (pattern, rest) →
      Tree compilation source site span scope expected instructions pattern rest) ∧
    (∀ types instructions patterns rest,
      compileMany compilation source site span scope fuel types instructions = .ok (patterns, rest) →
      Forest compilation source site span scope types instructions patterns rest) := by
  induction fuel with
  | zero =>
    constructor
    · intro expected instructions pattern rest accepted
      simp [compileOne] at accepted
    · intro types instructions patterns rest accepted
      cases types with
      | nil =>
        simp [compileMany, pure, Except.pure] at accepted
        rcases accepted with ⟨rfl, rfl⟩
        exact .nil
      | cons => simp [compileMany] at accepted
  | succ fuel ih =>
    constructor
    · intro expected instructions pattern rest accepted
      cases instructions with
      | nil => simp [compileOne] at accepted
      | cons instruction instructions =>
        cases projection : projected compilation source expected with
        | error error => simp [compileOne, projection, bind, Except.bind] at accepted
        | ok type =>
          cases instruction with
          | wildcard =>
            simp [compileOne, projection, bind, Except.bind, pure, Except.pure] at accepted
            rcases accepted with ⟨rfl, rfl⟩
            exact .wildcard projection
          | binder binder =>
            by_cases sourceType : binder.scheme.body = expected
            · cases valid : SourceCoreCompatibleDataExpressions.lowerBinder compilation.checked source scope binder with
              | error error => simp [compileOne, projection, sourceType, valid, bind, Except.bind] at accepted
              | ok actual =>
                by_cases same : type = actual
                · subst actual
                  simp [compileOne, projection, sourceType, valid, SourceCoreBasic.ensureType,
                    bind, Except.bind, pure, Except.pure] at accepted
                  rcases accepted with ⟨rfl, rfl⟩
                  exact .binder projection sourceType valid
                · simp [compileOne, projection, sourceType, valid, SourceCoreBasic.ensureType, same,
                    bind, Except.bind] at accepted
            · simp [compileOne, projection, sourceType, bind, Except.bind] at accepted
          | integerLiteral literal resolution =>
            cases validated : literalMatcher compilation site span expected literal resolution with
            | error error => simp [compileOne, projection, validated, bind, Except.bind] at accepted
            | ok matcher =>
              simp [compileOne, projection, validated, bind, Except.bind, pure, Except.pure] at accepted
              rcases accepted with ⟨rfl, rfl⟩
              exact .literal projection validated
          | tuple count =>
            cases unpacked : unpackTypes count expected with
            | none => simp [compileOne, projection, unpacked, bind, Except.bind, pure, Except.pure] at accepted
            | some types =>
              cases compiled : compileMany compilation source site span scope fuel types instructions with
              | error error => simp [compileOne, projection, unpacked, compiled, bind, Except.bind, pure, Except.pure] at accepted
              | ok result =>
                obtain ⟨children, after⟩ := result
                cases projectedChildren : types.mapM (projected compilation source) with
                | error error => simp [compileOne, projection, unpacked, compiled, projectedChildren, bind, Except.bind, pure, Except.pure] at accepted
                | ok coreTypes =>
                  simp [compileOne, projection, unpacked, compiled, projectedChildren, bind, Except.bind, pure, Except.pure] at accepted
                  rcases accepted with ⟨rfl, rfl⟩
                  exact .tuple projection unpacked (ih.2 _ _ _ _ compiled) projectedChildren
          | constructor instantiation arity =>
            by_cases result : instantiation.resultType = expected
            · by_cases count : arity = instantiation.payloadTypes.length
              · cases resolved : compilation.checked.resolveConstructor instantiation with
                | error error => simp [compileOne, projection, result, count, resolved, Except.mapError, bind, Except.bind] at accepted
                | ok constructor =>
                  by_cases same : type = .namedData constructor.owner
                  · cases raw : compilation.values.registry.id? (.constructor instantiation) with
                    | none => simp [compileOne, projection, result, count, resolved, Except.mapError, SourceCoreBasic.ensureType, same, raw, bind, Except.bind] at accepted
                    | some metadata =>
                      cases compiled : compileMany compilation source site span scope fuel instantiation.payloadTypes instructions with
                        | error error => simp [compileOne, projection, result, count, resolved, Except.mapError, SourceCoreBasic.ensureType, same, raw, compiled, bind, Except.bind, pure, Except.pure] at accepted
                        | ok compiledPair =>
                          obtain ⟨children, after⟩ := compiledPair
                          cases projectedChildren : instantiation.payloadTypes.mapM (projected compilation source) with
                          | error error => simp [compileOne, projection, result, count, resolved, Except.mapError, SourceCoreBasic.ensureType, same, raw, compiled, projectedChildren, bind, Except.bind, pure, Except.pure] at accepted
                          | ok coreTypes =>
                            cases registered : compilation.checked.catalog.definitions[constructor.owner.index]? with
                            | none => simp [compileOne, projection, result, count, resolved, Except.mapError, SourceCoreBasic.ensureType, same, raw, compiled, projectedChildren, registered, bind, Except.bind, pure, Except.pure] at accepted
                            | some definition =>
                              simp [compileOne, projection, result, count, resolved, Except.mapError, SourceCoreBasic.ensureType, same, raw, compiled, projectedChildren, registered, bind, Except.bind, pure, Except.pure] at accepted
                              rcases accepted with ⟨rfl, rfl⟩
                              have tree := Tree.constructor projection result count resolved same raw
                                (ih.2 _ _ _ _ compiled) projectedChildren registered
                              simpa [constructorPattern, same] using tree
                  · simp [compileOne, projection, result, count, resolved, Except.mapError, SourceCoreBasic.ensureType, same, bind, Except.bind] at accepted
              · simp [compileOne, projection, result, count, bind, Except.bind] at accepted
            · simp [compileOne, projection, result, bind, Except.bind] at accepted
    · intro types instructions patterns rest accepted
      cases types with
      | nil =>
        simp [compileMany, pure, Except.pure] at accepted
        rcases accepted with ⟨rfl, rfl⟩
        exact .nil
      | cons type types =>
        cases headResult : compileOne compilation source site span scope fuel type instructions with
        | error error => simp [compileMany, headResult, bind, Except.bind] at accepted
        | ok headPair =>
          obtain ⟨head, afterHead⟩ := headPair
          cases tailResult : compileMany compilation source site span scope fuel types afterHead with
          | error error => simp [compileMany, headResult, tailResult, bind, Except.bind] at accepted
          | ok tailPair =>
            obtain ⟨tail, afterTail⟩ := tailPair
            simp [compileMany, headResult, tailResult, bind, Except.bind, pure, Except.pure] at accepted
            rcases accepted with ⟨rfl, rfl⟩
            exact .cons (ih.1 _ _ _ _ headResult) (ih.2 _ _ _ _ tailResult)


/-- Accepted lowering retains the actual source-root instruction stream and
its complete static tree, along with requirement and binding uniqueness checks. -/
structure Certificate (compilation : Compilation) (source : TypedSource) (scope : Scope)
    (site : StatementId) (span : Syntax.SourceSpan) (expected : TypeSystem.Ty)
    (pattern : TypedMatchPattern) (compiled : Pattern) : Prop where
  owned : site.occurrence.owner = source.owner
  type : pattern.type = expected
  tree : ∃ instructions, rootInstructions compilation pattern.source pattern.resolution = .ok instructions ∧
    Tree compilation source site span scope expected instructions compiled []
  requirements : compiled.requirements = pattern.requirements
  distinctIds : (compiled.bindings.map (·.1.id)).Nodup
  distinctNames : (compiled.bindings.map (·.1.name)).Nodup

theorem certificate_of_compilePattern (compilation : Compilation) (fuel : Nat)
    (source : TypedSource) (scope : Scope) (site : StatementId) (span : Syntax.SourceSpan)
    (expected : TypeSystem.Ty) (pattern : TypedMatchPattern)
    (compiled : CertifiedPattern compilation.definitions)
    (accepted : compilePattern compilation fuel source scope site span expected pattern = .ok compiled) :
    Certificate compilation source scope site span expected pattern compiled.pattern := by
  by_cases owned : site.occurrence.owner = source.owner
  · by_cases type : pattern.type = expected
    · cases root : rootInstructions compilation pattern.source pattern.resolution with
      | error error => simp [compilePattern, owned, type, root, bind, Except.bind] at accepted
      | ok instructions =>
        cases built : compileOne compilation source site span scope fuel expected instructions with
        | error error => simp [compilePattern, owned, type, root, built, bind, Except.bind] at accepted
        | ok result =>
          obtain ⟨lowered, rest⟩ := result
          by_cases exhausted : rest = []
          · subst rest
            by_cases requirements : lowered.requirements = pattern.requirements
            · by_cases ids : (lowered.bindings.map (·.1.id)).Nodup
              · by_cases names : (lowered.bindings.map (·.1.name)).Nodup
                · simp only [compilePattern, owned, ne_eq, not_true_eq_false, ↓reduceIte,
                    type, root, built, bind, Except.bind, List.isEmpty_nil, requirements,
                    decide_true, Bool.true_and, ids, names] at accepted
                  split at accepted
                  · simp only [pure, Except.pure, Except.ok.injEq] at accepted
                    subst compiled
                    exact ⟨owned, type, ⟨instructions, root,
                      (trees_of_compile fuel compilation source site span scope).1 _ _ _ _ built⟩,
                      requirements, ids, names⟩
                  · simp at accepted
                · simp [compilePattern, owned, type, root, built, requirements, ids, names, bind, Except.bind] at accepted
              · simp [compilePattern, owned, type, root, built, requirements, ids, bind, Except.bind] at accepted
            · simp [compilePattern, owned, type, root, built, requirements, bind, Except.bind] at accepted
          · simp [compilePattern, owned, type, root, built, exhausted, bind, Except.bind] at accepted
    · simp [compilePattern, owned, type, bind, Except.bind] at accepted
  · simp [compilePattern, owned, bind, Except.bind] at accepted

theorem unpackTypes_length {count : Nat} {type : TypeSystem.Ty} {types : List TypeSystem.Ty}
    (unpacked : unpackTypes count type = some types) : types.length = count := by
  induction count using Nat.strongRecOn generalizing type types with
  | ind count ih =>
    cases count with
    | zero =>
      simp only [unpackTypes] at unpacked
      split at unpacked <;> simp_all
    | succ count =>
      cases count with
      | zero =>
        simp [unpackTypes] at unpacked
        subst types
        rfl
      | succ count =>
        cases type <;> simp only [unpackTypes] at unpacked
        all_goals try contradiction
        rename_i left right
        cases rest : unpackTypes (count + 1) right with
        | none => simp [rest] at unpacked
        | some tail =>
          simp [rest] at unpacked
          subst types
          have length := ih (count + 1) (by omega) rest
          simp [length]

theorem Tree.skips {compilation : Compilation} {source : TypedSource} {site : StatementId}
    {span : Syntax.SourceSpan} {scope : Scope} {expected : TypeSystem.Ty}
    {instructions rest : List MatchPatternInstruction} {pattern : Pattern}
    (tree : Tree compilation source site span scope expected instructions pattern rest) :
    Dynamic.PatternInstructionSkips instructions rest := by
  induction tree using Tree.rec
      (motive_2 := fun types instructions _ rest _ => Dynamic.PatternInstructionsSkip instructions types.length rest) with
  | wildcard => exact .wildcard
  | binder => exact .binder
  | literal => exact .integerLiteral
  | tuple projection unpacked children projectedChildren ih =>
    exact .tuple ((unpackTypes_length unpacked) ▸ ih)
  | constructor projection result count resolved coreType raw children projectedChildren registered ih =>
    exact .constructor (count.symm ▸ ih)
  | nil => exact .zero
  | cons head tail headIH tailIH => exact .succ headIH tailIH

theorem Forest.skips {compilation : Compilation} {source : TypedSource} {site : StatementId}
    {span : Syntax.SourceSpan} {scope : Scope} {types : List TypeSystem.Ty}
    {instructions rest : List MatchPatternInstruction} {patterns : List Pattern}
    (forest : Forest compilation source site span scope types instructions patterns rest) :
    Dynamic.PatternInstructionsSkip instructions types.length rest := by
  induction forest using Forest.rec
      (motive_1 := fun _ instructions _ rest _ => Dynamic.PatternInstructionSkips instructions rest) with
  | wildcard => exact .wildcard
  | binder => exact .binder
  | literal => exact .integerLiteral
  | tuple projection unpacked children projectedChildren ih =>
    exact .tuple ((unpackTypes_length unpacked) ▸ ih)
  | constructor projection result count resolved coreType raw children projectedChildren registered ih =>
    exact .constructor (count.symm ▸ ih)
  | nil => exact .zero
  | cons head tail headIH tailIH => exact .succ headIH tailIH


/-- Root spelling and groups are connected to the independent source carrier.
Only the signature catalog is shared with compilation. -/
theorem rootInstructions_sound (compilation : Compilation) (context : Context)
    (signatures : context.signatures = compilation.signatures)
    (spelling : MatchPatternSource) (resolution : MatchPatternResolution)
    (instructions : List MatchPatternInstruction)
    (accepted : rootInstructions compilation spelling resolution = .ok instructions) :
    ∃ arity, instructions = matchPatternResolutionInstructions resolution arity ∧
      MatchPatternSourceRepresents context spelling resolution arity := by
  induction spelling generalizing resolution instructions with
  | wildcard span marker =>
    cases resolution <;> simp only [rootInstructions] at accepted
    all_goals try contradiction
    simp only [pure, Except.pure, Except.ok.injEq] at accepted
    subst instructions
    exact ⟨0, rfl, .wildcard⟩
  | integerLiteral span literal =>
    cases resolution <;> simp only [rootInstructions] at accepted
    all_goals try contradiction
    rename_i raw resolution
    by_cases same : literal.value = raw
    · simp [same, pure, Except.pure] at accepted
      subst instructions
      exact ⟨0, rfl, .integerLiteral same⟩
    · simp [same, Functor.map, Except.map] at accepted
  | binder span name =>
    cases resolution <;> simp only [rootInstructions] at accepted
    all_goals try contradiction
    rename_i binder
    by_cases same : binder.name = name
    · simp [same, pure, Except.pure] at accepted
      subst instructions
      exact ⟨0, rfl, .binder same⟩
    · simp [same, Functor.map, Except.map] at accepted
  | tuple span count =>
    cases resolution <;> simp only [rootInstructions] at accepted
    all_goals try contradiction
    simp only [pure, Except.pure, Except.ok.injEq] at accepted
    subst instructions
    exact ⟨count, rfl, .tuple⟩
  | constructor span dot qualifiers name count =>
    cases resolution <;> simp only [rootInstructions] at accepted
    all_goals try contradiction
    rename_i instantiation arguments
    generalize selectedEq : compilation.signatures.dataTypes.filter
      (fun signature => decide (signature.id = instantiation.constructor.dataType)) = selected at accepted
    cases selected with
    | nil => contradiction
    | cons signature tail =>
      cases tail with
      | cons => contradiction
      | nil =>
        dsimp only at accepted
        generalize constructorEq : signature.constructors.filter
          (fun constructor => decide (constructor.id = instantiation.constructor)) = constructors at accepted
        cases constructors with
        | nil => contradiction
        | cons constructor rest =>
          cases rest with
          | cons => contradiction
          | nil =>
            dsimp only at accepted
            by_cases same : constructor.name = name
            · simp [same, pure, Except.pure] at accepted
              subst instructions
              refine ⟨count, rfl, .constructor ?_⟩
              have selectedMember : signature ∈ compilation.signatures.dataTypes.filter
                  (fun signature => decide (signature.id = instantiation.constructor.dataType)) := by
                rw [selectedEq]; simp
              have constructorMember : constructor ∈ signature.constructors.filter
                  (fun constructor => decide (constructor.id = instantiation.constructor)) := by
                rw [constructorEq]; simp
              simp only [List.mem_filter, decide_eq_true_eq] at selectedMember constructorMember
              exact ⟨signature, signatures ▸ selectedMember.1, constructor, constructorMember.1,
                constructorMember.2, same⟩
            · simp [same, Functor.map, Except.map] at accepted
  | group span inner ih =>
    obtain ⟨arity, instructionsEq, represents⟩ := ih _ _ accepted
    exact ⟨arity, instructionsEq, .group represents⟩

end Solcore.SourceSemantics.CoreLowering.CompatiblePatternCertificates
