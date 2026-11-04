import Solcore.Frontend.SourceCoreCompatibleDataMatches
import Solcore.SourceSemantics.Dynamic.Pattern
import Solcore.SourceSemantics.CoreLowering.Internal.Callable.IndexedAllocation
import Solcore.SourceSemantics.CoreLowering.Internal.Compatible.Statements
import Solcore.SourceSemantics.CoreLowering.Internal.Compatible.MappingsAndEquality
import Solcore.SourceSemantics.CoreLowering.Internal.Compatible.ExpressionPrimitives
import Solcore.Core.Correspondence
import Solcore.SourceSemantics.CoreLowering.Internal.Data.Patterns
import Solcore.SourceSemantics.CoreLowering.Internal.Compatible.ExpressionReads
import Solcore.SourceSemantics.Dynamic.PatternCompletenessProperties
import Solcore.SourceSemantics.CoreLowering.Internal.Callable.IndexedParameters
import Solcore.SourceSemantics.CoreLowering.Internal.Compatible.Paths
import Solcore.SourceSemantics.CoreLowering.Internal.Data.Matches
import Solcore.SourceSemantics.CoreLowering.CoreClosedRenaming
import Solcore.SourceSemantics.Patterns
import Solcore.SourceSemantics.CoreLowering.Internal.Protected.StateExpressions
import Solcore.SourceSemantics.CoreLowering.CoreContinuationSize
import Solcore.SourceSemantics.CoreLowering.Internal.Protected.StateAllocation

/-!
# Compatible matches: patterns and arms

Certificates, values, execution and decisions of patterns, and arm allocation and prefixes.
-/

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CompatiblePatternCertificates
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
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CompatibleMatchArmCertificates
/-! Static receipts for the actual compatible match arm allocator. The
packed binding values and loaded scrutinee are lexical temporaries; captures
skip both and retain the real hidden source reference. No evaluation premise
is stored in the tree. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleMatchArmCertificates
open Core Frontend SourceInference
open CallableIndexedAllocationCompletion
abbrev Binding := TypedBinder × Ty
abbrev Scope := SourceCoreSourceCells.Scope

def request (source : TypedSource) (scope : Scope) (index : Nat) (binding : Binding) : SourceCoreSourceCells.Request :=
  ⟨source, scope, Renaming.comp (Renaming.insertion 0)
    (Renaming.comp (Renaming.insertion (index + 1)) (Renaming.insertion index)),
    binding.1, binding.2, some (.var 0)⟩

inductive Tree (layouts : SourceCoreAllocationLayouts.Prepared)
    (owner : SourceSpecialization.SpecializationKey) (active : TypeSystem.Substitution)
    (layout : SourceCoreCallableIndexedFrames.Layout) (globals : Nat)
    (onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error)
    (source : TypedSource) (types : List Ty) (output : Ty) (body : Expr) :
    Scope → Nat → List Binding → Expr → Prop where
  | nil {scope index} : Tree layouts owner active layout globals onError source types output body scope index [] body
  | cons {scope index binder payload bindings code}
      (allocation : SourceCoreAllocationLayouts.Allocation layouts owner active (request source scope index (binder, payload)))
      (annotation : SourceCoreCallableIndexedAllocationFrames.Annotated layout globals
        (layouts.allocatorAt owner active onError) (request source scope index (binder, payload)))
      (same : annotation.original = allocation.expression)
      (tail : Tree layouts owner active layout globals onError source types output body
        ((binder.id, payload) :: scope) (index + 1) bindings code) :
      Tree layouts owner active layout globals onError source types output body scope index ((binder, payload) :: bindings)
        (LanguageResult.bind output
          (LanguageResult.success (SourceCoreDataExpressions.projectPacked index types (.var index)))
          (.letE annotation.expression (code.weakenAt 1)))

private def step (allocate : SourceCoreSourceCells.Allocator) (source : TypedSource) (scope : Scope)
    (all : List Binding) (output : Ty) (item : Binding × Nat) (body : Expr) : Except SourceCoreBasic.Error Expr :=
  SourceCoreSourceCells.letInitialized (some allocate) source
    ((all.take item.2).reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope)
    (Renaming.comp (Renaming.insertion (item.2 + 1)) (Renaming.insertion item.2)) item.1.1 output item.1.2
    (LanguageResult.success (SourceCoreDataExpressions.projectPacked item.2 (all.map Prod.snd) (.var item.2))) body

private theorem of_fold {layouts : SourceCoreAllocationLayouts.Prepared}
    {owner : SourceSpecialization.SpecializationKey} {active : TypeSystem.Substitution}
    {layout : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
    (onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error)
    (source : TypedSource) (scope : Scope) (all done bindings : List Binding)
    (split : all = done ++ bindings) (output : Ty) (body : Expr) {code : Expr}
    (accepted : (bindings.zipIdx done.length).foldrM
      (step (SourceCoreCallableIndexedAllocationFrames.allocator layout globals
        (layouts.allocatorAt owner active onError)) source scope all output) body = .ok code) :
    Tree layouts owner active layout globals onError source (all.map Prod.snd) output body
      (done.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope) done.length bindings code := by
  induction bindings generalizing done code with
  | nil =>
    simp only [List.zipIdx_nil, List.foldrM_nil] at accepted
    cases accepted
    exact .nil
  | cons binding rest ih =>
    simp only [List.zipIdx_cons, List.foldrM_cons] at accepted
    cases tail : (rest.zipIdx (done.length + 1)).foldrM
        (step (SourceCoreCallableIndexedAllocationFrames.allocator layout globals
          (layouts.allocatorAt owner active onError)) source scope all output) body with
    | error error => simp [tail, bind, Except.bind] at accepted
    | ok next =>
      simp only [tail, bind, Except.bind] at accepted
      have nextTree := ih (done := done ++ [binding]) (by simpa [List.append_assoc] using split)
        (by simpa using tail)
      have prior : all.take done.length = done := by rw [split]; simp
      simp only [step, prior, SourceCoreSourceCells.letInitialized, bind, Except.bind] at accepted
      change (SourceCoreCallableIndexedAllocationFrames.allocator layout globals
          (layouts.allocatorAt owner active onError)
          (request source (done.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope) done.length binding) >>= fun v =>
          pure (LanguageResult.bind output
            (LanguageResult.success (SourceCoreDataExpressions.projectPacked done.length (all.map Prod.snd) (.var done.length)))
            (.letE v (next.weakenAt 1)))) = .ok code at accepted
      cases allocationAccepted : SourceCoreCallableIndexedAllocationFrames.allocator layout globals
          (layouts.allocatorAt owner active onError)
          (request source (done.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope) done.length binding) with
      | error error => simp only [allocationAccepted, bind, Except.bind, reduceCtorEq] at accepted
      | ok allocationCode =>
        have accepted' : LanguageResult.bind output
            (LanguageResult.success (SourceCoreDataExpressions.projectPacked done.length (all.map Prod.snd) (.var done.length)))
            (.letE allocationCode (next.weakenAt 1)) = code := by
          simpa only [allocationAccepted, bind, Except.bind, pure, Except.pure, Except.ok.injEq] using accepted
        obtain ⟨allocation, annotation, same, emitted⟩ := accepted_receipts onError allocationAccepted
        rw [← accepted', emitted]
        apply Tree.cons allocation annotation same
        simpa using nextTree

/-- The real compiler fold supplies each marked allocation receipt and its
exact lexical insertions. The body is still an arbitrary continuation. -/
theorem of_accepted {layouts : SourceCoreAllocationLayouts.Prepared}
    {owner : SourceSpecialization.SpecializationKey} {active : TypeSystem.Substitution}
    {layout : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
    (onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error)
    {context : SourceCoreCompatibleDataMatches.Context}
    {source : TypedSource} {scope : Scope} {bindings : List Binding} {output : Ty} {body code : Expr}
    (allocator : context.sourceCells = some
      (SourceCoreCallableIndexedAllocationFrames.allocator layout globals (layouts.allocatorAt owner active onError)))
    (accepted : SourceCoreCompatibleDataMatches.bindArmWithAllocator context source scope bindings output body = .ok code) :
    Tree layouts owner active layout globals onError source (bindings.map Prod.snd) output
      (body.weakenAt bindings.length) scope 0 bindings code := by
  unfold SourceCoreCompatibleDataMatches.bindArmWithAllocator at accepted
  simp only [allocator] at accepted
  exact of_fold onError source scope bindings [] bindings rfl output (body.weakenAt bindings.length) accepted

end Solcore.SourceSemantics.CoreLowering.CompatibleMatchArmCertificates
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CompatibleMatchCertificates
/-! Static certificates for the actual general match compiler. Expression and
body certificates are supplied by the caller's structural compiler proof; the
extraction assumptions mention only successful compilation, never evaluation.
The hidden scrutinee occurs in the Core scope. It is not a source lexical binder;
a later heap/environment correspondence must retain that distinction. -/

set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleMatchCertificates
open Frontend Frontend.SourceInference SourceCoreCompatibleDataMatches

abbrev ExpressionCertificate := Scope → ExpressionId → SourceCoreBasic.LoweredExpr → Prop
abbrev BodyCertificate := Scope → List StatementId → Core.Expr → Prop

def armScope (scope : Scope) (pattern : Pattern) : Scope :=
  pattern.bindings.foldl (fun scope binding => (binding.1.id, binding.2) :: scope) scope

inductive Arms (compilation : SourceCoreCompatibleDataMatches.Context) (source : TypedSource) (site : StatementId)
    (scope : Scope) (expected : TypeSystem.Ty) (bodyCertificate : BodyCertificate) :
    List TypedMatchCase → List (Pattern × Core.Expr) → Prop where
  | nil : Arms compilation source site scope expected bodyCertificate [] []
  | cons {arm rest pattern body arms}
      (patternCertificate : CompatiblePatternCertificates.Certificate compilation source scope site
        arm.span expected arm.pattern pattern)
      (typed : Core.HasType [] pattern.matcher pattern.functionType compilation.definitions)
      (bodyCertified : bodyCertificate (armScope scope pattern) arm.body body)
      (tail : Arms compilation source site scope expected bodyCertificate rest arms) :
      Arms compilation source site scope expected bodyCertificate (arm :: rest) ((pattern, body) :: arms)

inductive Fallback (bodyCertificate : BodyCertificate) (scope : Scope) (resultType : Core.Ty) :
    Option (List StatementId) → Core.Expr → Prop where
  | none : Fallback bodyCertificate scope resultType none (Core.LocalLoop.fallthrough resultType)
  | some {statements body} (certificate : bodyCertificate scope statements body) :
      Fallback bodyCertificate scope resultType (some statements) body

def hiddenBinder (_source : TypedSource) (node : StatementNode) (resolution : MatchResolution)
    (scrutinee : ExpressionNode) : TypedBinder := {
  id := resolution.hiddenScrutinee, name := "",
  scheme := ⟨[], SourceCoreRawMetadata.runtimeType scrutinee.type⟩, span := some node.span }

/-- The emitted arm fold stores only actual compiler receipts. Semantic
children are supplied by the enclosing concrete recursive statement tree. -/
inductive Branches (compilation : SourceCoreCompatibleDataMatches.Context) (source : TypedSource)
    (scope : Scope) (outputType : Core.Ty) (fallback : Core.Expr) :
    List (Pattern × Core.Expr) → Core.Expr → Prop where
  | nil : Branches compilation source scope outputType fallback [] (fallback.weakenAt 0)
  | cons {pattern body arms allocated next}
      (allocation : bindArmWithAllocator compilation source scope pattern.bindings outputType
        (body.weakenAt pattern.bindings.length) = .ok allocated)
      (tail : Branches compilation source scope outputType fallback arms next) :
      Branches compilation source scope outputType fallback ((pattern, body) :: arms)
        (.caseE (.apply pattern.matcher (.var 0)) (next.weakenAt 0) allocated)

/-- The certificate follows the actual hidden marked allocator and branch
fold, including the retained raw source scrutinee type and runtime marker type. -/
inductive Certificate (compilation : SourceCoreCompatibleDataMatches.Context) (source : TypedSource) (scope : Scope)
    (id : StatementId) (resolution : MatchResolution) (resultType : Core.Ty)
    (internalReason : Core.Word) (expressionCertificate : ExpressionCertificate)
    (bodyCertificate : BodyCertificate) : Core.Expr → Prop where
  | matchWith {node statementType scrutineeNode type scrutinee arms fallback branches code}
      (read : SourceCoreCompatibleDataExpressions.readStatement compilation.checked source id = .ok (node, statementType))
      (statementTypeValid : statementType = .unit ∨ statementType = resultType)
      (form : node.form = .matchWith resolution)
      (requirements : resolution.requirements = resolution.cases.flatMap (·.pattern.requirements))
      (hiddenOwned : resolution.hiddenScrutinee.owner = source.owner)
      (hiddenFresh : scope.any (fun entry => decide (entry.1 = resolution.hiddenScrutinee)) = false)
      (scrutineeOwned : resolution.scrutinee.occurrence.owner = source.owner)
      (scrutineeFound : source.lookupExpression? resolution.scrutinee = some scrutineeNode)
      (projection : projected compilation source scrutineeNode.type = .ok type)
      (expression : expressionCertificate scope resolution.scrutinee scrutinee)
      (sameType : type = scrutinee.type)
      (armCertificates : Arms compilation source id ((resolution.hiddenScrutinee, type) :: scope)
        scrutineeNode.type bodyCertificate resolution.cases arms)
      (fallbackCertificate : Fallback bodyCertificate ((resolution.hiddenScrutinee, type) :: scope)
        resultType resolution.defaultBody fallback)
      (branchesCertified : Branches compilation source ((resolution.hiddenScrutinee, type) :: scope)
        (Core.LocalLoop.controlType resultType) fallback arms branches)
      (hiddenCompiled : SourceCoreSourceCells.letInitialized compilation.sourceCells source scope Core.Renaming.id
        (hiddenBinder source node resolution scrutineeNode) (Core.LocalLoop.controlType resultType) type scrutinee.expression
        (.caseE (.loadCell (.var 0))
          (Core.LanguageResult.failure (Core.LocalLoop.controlType resultType) (.word internalReason)) branches) = .ok code) :
      Certificate compilation source scope id resolution resultType internalReason expressionCertificate bodyCertificate code

private theorem bind_ok {α β ε : Type} {computation : Except ε α} {next : α → Except ε β}
    {result : β} (accepted : computation >>= next = .ok result) :
    ∃ value, computation = .ok value ∧ next value = .ok result := by
  cases computation with
  | error => cases accepted
  | ok value => exact ⟨value, rfl, accepted⟩

private theorem arms_of_mapM {compilation : SourceCoreCompatibleDataMatches.Context} {source : TypedSource} {site : StatementId}
    {scope : Scope} {expected : TypeSystem.Ty} {bodyCertificate : BodyCertificate}
    {lowerBody : BodyLowerer} {fuel : Nat} {resultType : Core.Ty}
    {reasonAt : ExpressionId → Core.Word} {internalReason : Core.Word}
    (bodyExtract : ∀ scope statements code,
      lowerBody fuel source scope statements resultType reasonAt internalReason = .ok code →
      bodyCertificate scope statements code)
    {cases : List TypedMatchCase} {arms : List (Pattern × Core.Expr)}
    (accepted : cases.mapM (fun arm => do
      let pattern ← compilePattern compilation fuel source scope site arm.span expected arm.pattern
      let body ← lowerBody fuel source (armScope scope pattern.pattern) arm.body resultType reasonAt internalReason
      pure (pattern.pattern, body)) = .ok arms) :
    Arms compilation source site scope expected bodyCertificate cases arms := by
  induction cases generalizing arms with
  | nil =>
    simp only [List.mapM_nil, pure, Except.pure, Except.ok.injEq] at accepted
    subst arms
    exact .nil
  | cons arm rest ih =>
    simp only [List.mapM_cons] at accepted
    obtain ⟨head, acceptedHead, accepted⟩ := bind_ok accepted
    obtain ⟨tail, acceptedTail, accepted⟩ := bind_ok accepted
    simp only [pure, Except.pure, Except.ok.injEq] at accepted
    subst arms
    obtain ⟨pattern, compiled, acceptedHead⟩ := bind_ok acceptedHead
    obtain ⟨body, bodyAccepted, acceptedHead⟩ := bind_ok acceptedHead
    simp only [pure, Except.pure, Except.ok.injEq] at acceptedHead
    subst head
    exact .cons (CompatiblePatternCertificates.certificate_of_compilePattern _ _ _ _ _ _ _ _ _ compiled)
      pattern.typed (bodyExtract _ _ _ bodyAccepted) (ih acceptedTail)

private theorem branches_of_fold
    {compilation : SourceCoreCompatibleDataMatches.Context} {source : TypedSource} {scope : Scope}
    {outputType : Core.Ty} {fallback code : Core.Expr} {arms : List (Pattern × Core.Expr)}
    (accepted : arms.foldrM (fun ((pattern, body) : Pattern × Core.Expr) (next : Core.Expr) => do
      let allocated ← bindArmWithAllocator compilation source scope pattern.bindings outputType
        (body.weakenAt pattern.bindings.length)
      pure (Core.Expr.caseE (.apply pattern.matcher (.var 0)) (next.weakenAt 0) allocated))
      (fallback.weakenAt 0) = .ok code) :
    Branches compilation source scope outputType fallback arms code := by
  induction arms generalizing code with
  | nil => simp only [List.foldrM_nil] at accepted; cases accepted; exact .nil
  | cons head rest ih =>
    obtain ⟨pattern, body⟩ := head
    simp only [List.foldrM_cons] at accepted
    obtain ⟨next, compiledNext, accepted⟩ := bind_ok accepted
    obtain ⟨allocated, compiledArm, accepted⟩ := bind_ok accepted
    cases accepted
    exact .cons compiledArm (ih compiledNext)

/-- The actual compiler's success supplies all match metadata and pattern
certificates. Callback extraction is static and uses the exact child budget and
scope; it can be discharged by an enclosing compiler's structural induction. -/
theorem certificate_of_lowerWithReasons
    {compilation : SourceCoreCompatibleDataMatches.Context} {lowerExpression : ExpressionLowerer} {lowerBody : BodyLowerer}
    {fuel : Nat} {source : TypedSource} {scope : Scope} {id : StatementId}
    {resolution : MatchResolution} {resultType : Core.Ty}
    {reasonAt : ExpressionId → Core.Word} {internalReason : Core.Word} {code : Core.Expr}
    {expressionCertificate : ExpressionCertificate} {bodyCertificate : BodyCertificate}
    (expressionExtract : ∀ childFuel scope id result,
      lowerExpression childFuel source scope id reasonAt = .ok result → expressionCertificate scope id result)
    (bodyExtract : ∀ childFuel scope statements code,
      lowerBody childFuel source scope statements resultType reasonAt internalReason = .ok code →
      bodyCertificate scope statements code)
    (accepted : lowerWithReasons compilation lowerExpression lowerBody fuel source scope id resolution
      resultType reasonAt internalReason = .ok code) :
    Certificate compilation source scope id resolution resultType internalReason expressionCertificate bodyCertificate code := by
  cases fuel with
  | zero => simp [lowerWithReasons] at accepted
  | succ fuel =>
    simp only [lowerWithReasons] at accepted
    obtain ⟨⟨node, statementType⟩, read, accepted⟩ := bind_ok accepted
    by_cases allowed : statementType = .unit ∨ statementType = resultType
    · simp only [Bool.or_eq_true, decide_eq_true_eq] at accepted
      simp only [allowed, ↓reduceIte, pure, Except.pure, bind, Except.bind] at accepted
      by_cases form : node.form = .matchWith resolution
      · simp only [form, ↓reduceIte] at accepted
        by_cases requirements : resolution.requirements = resolution.cases.flatMap (·.pattern.requirements)
        · simp only [requirements, ↓reduceIte] at accepted
          by_cases hiddenOwned : resolution.hiddenScrutinee.owner = source.owner
          · simp only [hiddenOwned, ne_eq, not_true_eq_false, ↓reduceIte] at accepted
            cases hiddenFresh : scope.any (fun entry => decide (entry.1 = resolution.hiddenScrutinee)) with
            | true => simp [hiddenFresh] at accepted
            | false =>
              simp only [hiddenFresh, Bool.false_eq_true, ↓reduceIte] at accepted
              by_cases scrutineeOwned : resolution.scrutinee.occurrence.owner = source.owner
              · simp only [scrutineeOwned, not_true_eq_false, ↓reduceIte] at accepted
                cases scrutineeFound : source.lookupExpression? resolution.scrutinee with
                | none => simp [scrutineeFound] at accepted
                | some scrutineeNode =>
                  simp only [scrutineeFound] at accepted
                  obtain ⟨type, projection, accepted⟩ := bind_ok accepted
                  obtain ⟨scrutinee, loweredExpression, accepted⟩ := bind_ok accepted
                  obtain ⟨checked, typeAccepted, accepted⟩ := bind_ok accepted
                  have sameType : type = scrutinee.type := by
                    unfold SourceCoreBasic.ensureType at typeAccepted
                    split at typeAccepted
                    · assumption
                    · cases typeAccepted
                  obtain ⟨arms, compiledArms, accepted⟩ := bind_ok accepted
                  have armCertificates := arms_of_mapM (bodyExtract fuel) compiledArms
                  have finish : ∀ fallback,
                      Fallback bodyCertificate ((resolution.hiddenScrutinee, type) :: scope)
                        resultType resolution.defaultBody fallback →
                      ((do
                        let branches ← arms.foldrM (fun ((pattern, body) : Pattern × Core.Expr) (next : Core.Expr) => do
                          let allocated ← bindArmWithAllocator compilation source
                            ((resolution.hiddenScrutinee, type) :: scope) pattern.bindings
                            (Core.LocalLoop.controlType resultType) (body.weakenAt pattern.bindings.length)
                          pure (Core.Expr.caseE (.apply pattern.matcher (.var 0)) (next.weakenAt 0) allocated))
                          (fallback.weakenAt 0)
                        SourceCoreSourceCells.letInitialized compilation.sourceCells source scope Core.Renaming.id
                          (hiddenBinder source node resolution scrutineeNode) (Core.LocalLoop.controlType resultType) type
                          scrutinee.expression (.caseE (.loadCell (.var 0))
                            (Core.LanguageResult.failure (Core.LocalLoop.controlType resultType) (.word internalReason))
                            branches)) = .ok code) →
                      Certificate compilation source scope id resolution resultType internalReason
                        expressionCertificate bodyCertificate code := by
                    intro fallback certified accepted
                    obtain ⟨branches, compiledBranches, compiledHidden⟩ := bind_ok accepted
                    exact .matchWith read allowed form requirements hiddenOwned hiddenFresh
                      scrutineeOwned scrutineeFound projection (expressionExtract _ _ _ _ loweredExpression) sameType
                      armCertificates certified (branches_of_fold compiledBranches) compiledHidden
                  cases fallbackForm : resolution.defaultBody with
                  | none =>
                    simp only [fallbackForm] at accepted
                    exact finish _ (by rw [fallbackForm]; exact .none) accepted
                  | some statements =>
                    simp only [fallbackForm] at accepted
                    obtain ⟨fallback, compiledFallback, accepted⟩ := bind_ok accepted
                    exact finish fallback (by rw [fallbackForm]; exact .some (bodyExtract _ _ _ _ compiledFallback)) accepted
              · simp [scrutineeOwned] at accepted
          · simp [hiddenOwned] at accepted
        · simp [requirements] at accepted
      · simp [form] at accepted
    · simp [allowed, bind, Except.bind] at accepted

end Solcore.SourceSemantics.CoreLowering.CompatibleMatchCertificates
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CompatiblePatternValues
/-! Source-shaped product inversion for compatible match inputs. Function
carriers are native products too, so inversion uses the retained source runtime
view and authentic constructor metadata. No function observation or evaluation
law is required to preserve arbitrary bound payloads. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatiblePatternValues
open Core Frontend SourceInference GeneralHeap DataPatternValues CompatiblePayload
open CompatibleConstructorMetadata
variable {checked : SourceCoreCompatibleCatalog.Checked} {registry : SourceCoreRawMetadata.Registry}
  {ambient : AmbientDefinitions checked.catalog.definitions} {functions : FunctionModel checked.catalog ambient}
  {mapping : LocationMap} {world : StoreTyping}

private theorem unit_view {expected : TypeSystem.Ty} {source : Dynamic.Value} {value : Value} {type : Ty}
    (represented : ValueRep checked registry functions mapping world expected source value type) :
    SourceCoreRawMetadata.runtimeType expected = .unit → source = .unit ∧ value = .unit ∧ type = .unit := by
  induction represented using CompatiblePayload.ValueRep.rec (motive_2 := fun _ _ _ _ _ => True)
    (motive_3 := fun _ _ _ _ _ _ _ => True) (motive_4 := fun _ _ _ _ => True) with
  | unit => intro _; exact ⟨rfl, rfl, rfl⟩
  | bool | word | integer | product | function | proxy | mappingValue =>
    intro impossible
    simp [SourceCoreRawMetadata.runtimeType, TypeSystem.Ty.unit, TypeSystem.Ty.bool,
      TypeSystem.Ty.word, TypeSystem.Ty.integer] at impossible
  | constructed metadata owner selected projected registered payloads _ =>
    intro impossible
    obtain ⟨signature, constructor, arguments, _, _, _, _, _, result⟩ := facts (constructor_authenticated metadata owner)
    have parts := congrArg SourceCoreDataCatalog.nominalParts impossible
    rw [result, runtimeType_nominal, DataPatternAuthenticity.nominalParts_nominal] at parts
    simp [SourceCoreDataCatalog.nominalParts, TypeSystem.Ty.unit] at parts
  | compatible same related ih => intro viewed; exact ih (same.symm.trans viewed)
  | nil | cons | empty | entry | absent | present => trivial

/-- Normalized Unit inputs really contain Unit, including staged aliases. -/
theorem unit_fields {expected : TypeSystem.Ty} {source : Dynamic.Value} {value : Value} {type : Ty}
    (represented : ValueRep checked registry functions mapping world expected source value type)
    (viewed : SourceCoreRawMetadata.runtimeType expected = .unit) :
    source = .unit ∧ value = .unit ∧ type = .unit := unit_view represented viewed

private def ProductFields (expected : TypeSystem.Ty) (source : Dynamic.Value) (value : Value) (type : Ty) : Prop :=
  ∀ left right, SourceCoreRawMetadata.runtimeType expected =
      .product (SourceCoreRawMetadata.runtimeType left) (SourceCoreRawMetadata.runtimeType right) →
    ∃ first second a b aType bType, source = .product first second ∧ value = .pair a b ∧
      type = .product aType bType ∧
      ValueRep checked registry functions mapping world left first a aType ∧
      ValueRep checked registry functions mapping world right second b bType

private theorem product_view {expected : TypeSystem.Ty} {source : Dynamic.Value} {value : Value} {type : Ty}
    (represented : ValueRep checked registry functions mapping world expected source value type) :
    ProductFields (checked := checked) (registry := registry) (functions := functions)
      (mapping := mapping) (world := world) expected source value type := by
  induction represented using CompatiblePayload.ValueRep.rec (motive_2 := fun _ _ _ _ _ => True)
    (motive_3 := fun _ _ _ _ _ _ _ => True) (motive_4 := fun _ _ _ _ => True) with
  | unit | bool | word | integer | function | proxy | mappingValue =>
    intro left right impossible
    simp [SourceCoreRawMetadata.runtimeType, TypeSystem.Ty.unit, TypeSystem.Ty.bool,
      TypeSystem.Ty.word, TypeSystem.Ty.integer] at impossible
  | product first second firstIH secondIH =>
    intro left right viewed
    have same := TypeSystem.Ty.product.inj viewed
    exact ⟨_, _, _, _, _, _, rfl, rfl, rfl, .compatible same.1.symm first, .compatible same.2.symm second⟩
  | constructed metadata owner selected projected registered payloads _ =>
    intro left right impossible
    obtain ⟨signature, constructor, arguments, _, _, _, _, _, result⟩ := facts (constructor_authenticated metadata owner)
    have parts := congrArg SourceCoreDataCatalog.nominalParts impossible
    rw [result, runtimeType_nominal, DataPatternAuthenticity.nominalParts_nominal] at parts
    simp [SourceCoreDataCatalog.nominalParts] at parts
  | compatible same related ih => intro left right viewed; exact ih left right (same.symm.trans viewed)
  | nil | cons | empty | entry | absent | present => trivial

/-- Source products preserve component representations, raw aliases and native
types, even when the components are closures, mappings or proxies. -/
theorem product_fields {left right : TypeSystem.Ty} {source : Dynamic.Value} {value : Value} {type : Ty}
    (represented : ValueRep checked registry functions mapping world (.product left right) source value type) :
    ∃ first second a b aType bType, source = .product first second ∧ value = .pair a b ∧
      type = .product aType bType ∧
      ValueRep checked registry functions mapping world left first a aType ∧
      ValueRep checked registry functions mapping world right second b bType :=
  product_view represented left right rfl

private theorem nominal_source {expected : TypeSystem.Ty} {source : Dynamic.Value} {value : Value} {type : Ty}
    (represented : ValueRep checked registry functions mapping world expected source value type) :
    ∀ declaration arguments,
      SourceCoreDataCatalog.nominalParts (SourceCoreRawMetadata.runtimeType expected) = some (declaration, arguments) →
      ∃ metadata sources, source = .constructed metadata sources := by
  induction represented using CompatiblePayload.ValueRep.rec (motive_2 := fun _ _ _ _ _ => True)
    (motive_3 := fun _ _ _ _ _ _ _ => True) (motive_4 := fun _ _ _ _ => True) with
  | unit | bool | word | integer | product | function | proxy | mappingValue =>
    intro declaration arguments impossible
    simp [SourceCoreRawMetadata.runtimeType, SourceCoreDataCatalog.nominalParts,
      TypeSystem.Ty.unit, TypeSystem.Ty.bool, TypeSystem.Ty.word, TypeSystem.Ty.integer] at impossible
  | constructed => intro _ _ _; exact ⟨_, _, rfl⟩
  | compatible same related ih => intro declaration arguments viewed; exact ih declaration arguments (same ▸ viewed)
  | nil | cons | empty | entry | absent | present => trivial

/-- A nominal source view recovers an authenticated constructor and its exact
raw payload vector; native tag shape alone is not used as source authenticity. -/
theorem nominal_fields {expected : TypeSystem.Ty} {source : Dynamic.Value} {value : Value} {type : Ty}
    (represented : ValueRep checked registry functions mapping world expected source value type)
    {declaration : Resolved.DeclarationId} {arguments : List TypeSystem.Ty}
    (nominal : SourceCoreDataCatalog.nominalParts (SourceCoreRawMetadata.runtimeType expected) = some (declaration, arguments)) :
    ∃ metadata sources tag id values types, source = .constructed metadata sources ∧
      value = .constructed tag (.pair (.word id) (packValues values)) ∧ type = .namedData tag.owner ∧
      ConstructorFields checked registry functions mapping world expected metadata tag id sources values types := by
  obtain ⟨metadata, sources, sourceEq⟩ := nominal_source represented _ _ nominal
  obtain ⟨tag, id, values, types, nativeEq, typeEq, fields⟩ := constructor_fields represented sourceEq
  exact ⟨metadata, sources, tag, id, values, types, sourceEq, nativeEq, typeEq, fields⟩

/-- Unpack exactly the arity accepted by the actual compiler. The singleton
case retains an entire function carrier, rather than projecting its fields. -/
theorem unpack {expected : TypeSystem.Ty} {source : Dynamic.Value} {value : Value} {type : Ty}
    {count : Nat} {types : List TypeSystem.Ty}
    (unpacked : SourceCoreCompatibleDataMatches.unpackTypes count expected = some types)
    (represented : ValueRep checked registry functions mapping world expected source value type) :
    ∃ sources values coreTypes, ValuesRep checked registry functions mapping world types sources values coreTypes ∧
      Dynamic.ValuesPack sources source ∧ value = packValues values ∧
      type = SourceCoreCompatibleCatalog.packTypes coreTypes := by
  induction count using Nat.strongRecOn generalizing expected source value type types with
  | ind count ih =>
    cases count with
    | zero =>
      simp only [SourceCoreCompatibleDataMatches.unpackTypes] at unpacked
      split at unpacked
      · rename_i same
        subst expected
        cases unpacked
        obtain ⟨rfl, rfl, rfl⟩ := unit_fields represented rfl
        exact ⟨[], [], [], .nil, .nil, rfl, rfl⟩
      · contradiction
    | succ count =>
      cases count with
      | zero => cases unpacked; exact ⟨[source], [value], [type], .cons represented .nil, .singleton _, rfl, rfl⟩
      | succ count =>
        cases expected <;> simp only [SourceCoreCompatibleDataMatches.unpackTypes] at unpacked
        all_goals try contradiction
        rename_i leftType rightType
        cases rest : SourceCoreCompatibleDataMatches.unpackTypes (count + 1) rightType with
        | none => simp [rest] at unpacked
        | some tail =>
          simp [rest] at unpacked
          subst types
          obtain ⟨first, second, a, b, aType, bType, rfl, rfl, rfl, firstRep, secondRep⟩ := product_fields represented
          obtain ⟨sources, values, coreTypes, tailRep, packing, valueEq, typeEq⟩ := ih (count + 1) (by omega) rest secondRep
          have lengths := CompatiblePayload.ValuesRep.length tailRep
          have typeLength := CompatiblePatternCertificates.unpackTypes_length rest
          cases sources with
          | nil => simp only [List.length_nil] at lengths; omega
          | cons head sources =>
            cases values with
            | nil => simp only [List.length_nil, List.length_cons] at lengths; omega
            | cons value values =>
              cases coreTypes with
              | nil => simp only [List.length_nil, List.length_cons] at lengths; omega
              | cons coreType coreTypes =>
                exact ⟨first :: head :: sources, a :: value :: values, aType :: coreType :: coreTypes,
                  .cons firstRep tailRep, .cons packing,
                  by simp only [packValues]; rw [valueEq],
                  by simp only [SourceCoreCompatibleCatalog.packTypes]; rw [typeEq]⟩
end Solcore.SourceSemantics.CoreLowering.CompatiblePatternValues
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CompatiblePatternLeaves
/-! Actual compatible wildcard, binder and numeric patterns preserve the
general payload relation, including functions, mappings and proxies. Numeric
leaves use the independent evidence ledger. No input matcher execution or
separate runtime type witness is required. Composite patterns are subsequent
consumers of the static certificate. -/

set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatiblePatternLeaves
open Core Frontend Frontend.SourceInference
open SourceCoreCompatibleDataMatches CompatiblePatternCertificates DataPatternValues
open GeneralHeap CompatiblePayload

structure ContextValid (compilation : Compilation) (context : Context) : Prop where
  signatures : context.signatures = compilation.signatures
  ledger : context.solvedRequirements = compilation.solvedRequirements
  valid : RequirementLedgerWellFormed context

inductive LiteralCode (compilation : Compilation) (literal : Syntax.CoreLiteralValue)
    (resolution : IntegerLiteralResolution) : TypeSystem.Ty → Expr → Prop where
  | word
      (target : resolution.targetType = .word)
      (meaning : NumericLiteralDenotes literal resolution.rawValue)
      (requirement : ∃ solved ∈ compilation.solvedRequirements, solved.id = resolution.requirement ∧
        solved.predicate = ProgramSignatures.builtinIntPredicate .word) :
      LiteralCode compilation literal resolution .word
        (.lambda .word (.sum .unit .unit)
          (.ifE (.binary .wordEq (.var 0) (.word (Word.ofNatModulo resolution.rawValue)))
            (.inRight .unit .unit) (.inLeft .unit .unit)))
  | integer
      (target : resolution.targetType = .integer)
      (meaning : NumericLiteralDenotes literal resolution.rawValue)
      (requirement : ∃ solved ∈ compilation.solvedRequirements, solved.id = resolution.requirement ∧
        solved.predicate = ProgramSignatures.builtinIntPredicate .integer) :
      LiteralCode compilation literal resolution .integer
        (.lambda .integer (.sum .unit .unit)
          (.ifE (.binary .integerEq (.var 0) (.integer (Int.ofNat resolution.rawValue)))
            (.inRight .unit .unit) (.inLeft .unit .unit)))

theorem literalMatcher_sound (compilation : Compilation) (site : StatementId) (span : Syntax.SourceSpan)
    (type : TypeSystem.Ty) (literal : Syntax.CoreLiteralValue) (resolution : IntegerLiteralResolution)
    (matcher : Expr) (accepted : literalMatcher compilation site span type literal resolution = .ok matcher) :
    LiteralCode compilation literal resolution type matcher := by
  cases type with
  | constructor constructor =>
    cases constructor with
    | declaration => simp [literalMatcher, bind, Except.bind] at accepted
    | builtin builtin =>
      cases builtin with
      | unit | bool => simp [literalMatcher, bind, Except.bind] at accepted
      | word =>
        let node : ExpressionNode := ⟨⟨site.occurrence⟩, span, .word, .integerLiteral literal resolution, [resolution.requirement], [], none⟩
        cases validated : SourceCoreElaboration.validateWordIntegerLiteral compilation.solvedRequirements node literal resolution with
        | error error =>
          simp only [node, TypeSystem.Ty.word] at validated
          simp [literalMatcher, validated, Except.mapError, bind, Except.bind] at accepted
        | ok validatedValue =>
          simp only [node, TypeSystem.Ty.word] at validated
          have certificate := SourceCoreElaboration.validateWordIntegerLiteral_sound validated
          have same : matcher = .lambda .word (.sum .unit .unit)
              (.ifE (.binary .wordEq (.var 0) (.word validatedValue.value)) (.inRight .unit .unit) (.inLeft .unit .unit)) := by
            simpa [literalMatcher, validated, Except.mapError, bind, Except.bind, pure, Except.pure] using accepted.symm
          rw [same, certificate.value]
          exact .word certificate.targetType certificate.meaning certificate.solved
      | integer =>
        let node : ExpressionNode := ⟨⟨site.occurrence⟩, span, .integer, .integerLiteral literal resolution, [resolution.requirement], [], none⟩
        cases validated : SourceCoreElaboration.validateNativeIntegerLiteral compilation.solvedRequirements node literal resolution with
        | error error =>
          simp only [node, TypeSystem.Ty.integer] at validated
          simp [literalMatcher, validated, Except.mapError, bind, Except.bind] at accepted
        | ok validatedValue =>
          simp only [node, TypeSystem.Ty.integer] at validated
          have certificate := SourceCoreElaboration.validateNativeIntegerLiteral_sound validated
          have same : matcher = .lambda .integer (.sum .unit .unit)
              (.ifE (.binary .integerEq (.var 0) (.integer validatedValue.value)) (.inRight .unit .unit) (.inLeft .unit .unit)) := by
            simpa [literalMatcher, validated, Except.mapError, bind, Except.bind, pure, Except.pure] using accepted.symm
          rw [same, certificate.value]
          exact .integer certificate.targetType certificate.meaning certificate.solved
  | «variable» | parameter | application | product | function | mapping | proxy | comptime | error =>
    simp [literalMatcher, bind, Except.bind] at accepted

/-- Ordered source binding records correspond to the values packed in Core's
successful result, retaining exact binder identity and metadata. -/
inductive BindingsRep (checked : SourceCoreCompatibleCatalog.Checked) (registry : SourceCoreRawMetadata.Registry)
    {ambient : AmbientDefinitions checked.catalog.definitions} (functions : FunctionModel checked.catalog ambient)
    (mapping : LocationMap) (world : StoreTyping) :
    List (TypedBinder × Ty) → List (TypedBinder × Dynamic.Value) → List Value → Prop where
  | nil : BindingsRep checked registry functions mapping world [] [] []
  | cons {binder : TypedBinder} {type : Ty} {source : Dynamic.Value} {value : Value}
      {binders : List (TypedBinder × Ty)} {sources : List (TypedBinder × Dynamic.Value)} {values : List Value}
      (head : ValueRep checked registry functions mapping world binder.scheme.body source value type) (tail : BindingsRep checked registry functions mapping world binders sources values) :
      BindingsRep checked registry functions mapping world ((binder, type) :: binders) ((binder, source) :: sources) (value :: values)

inductive OutcomeRep (checked : SourceCoreCompatibleCatalog.Checked) (registry : SourceCoreRawMetadata.Registry)
    {ambient : AmbientDefinitions checked.catalog.definitions} (functions : FunctionModel checked.catalog ambient)
    (mapping : LocationMap) (world : StoreTyping) (context : Context)
    (pattern : TypedMatchPattern) (compiled : Pattern) (sourceValue : Dynamic.Value) : Value → Prop where
  | matched {bindings : List (TypedBinder × Dynamic.Value)} {values : List Value}
      (meaning : Dynamic.PatternMatches context pattern sourceValue bindings)
      (represented : BindingsRep checked registry functions mapping world compiled.bindings bindings values) :
      OutcomeRep checked registry functions mapping world context pattern compiled sourceValue (.inRight .unit (packValues values))
  | noMatch (meaning : Dynamic.PatternDoesNotMatch context pattern sourceValue) :
      OutcomeRep checked registry functions mapping world context pattern compiled sourceValue (.inLeft (bundleType compiled.bindingTypes) .unit)

inductive LeafResolution : MatchPatternResolution → Prop where
  | wildcard : LeafResolution .wildcard
  | binder (binder : TypedBinder) : LeafResolution (.binder binder)
  | literal (literal : Syntax.CoreLiteralValue) (resolution : IntegerLiteralResolution) :
      LeafResolution (.integerLiteral literal resolution)

private theorem proves {compilation : Compilation} {context : Context} (valid : ContextValid compilation context)
    {requirement : RequirementId} {predicate : ProgramPredicate}
    (retained : ∃ solved ∈ compilation.solvedRequirements, solved.id = requirement ∧ solved.predicate = predicate) :
    RequirementProves context requirement predicate := by
  obtain ⟨solved, member, identifier, same⟩ := retained
  have member : solved ∈ context.solvedRequirements := by rw [valid.ledger]; exact member
  exact ⟨solved, ⟨member, identifier⟩, same, valid.valid.entriesValid solved member⟩

/-- Only a reached numeric resolution needs an independent requirement proof.
No source or native execution law is part of this condition. -/
def NumericRequirements (context : Context) (resolution : MatchPatternResolution) : Prop :=
  ∀ literal numeric, resolution = .integerLiteral literal numeric →
    RequirementProves context numeric.requirement numeric.predicate

theorem LiteralCode.constructs_word_with_requirement {context : Context}
    {literal : Syntax.CoreLiteralValue} {resolution : IntegerLiteralResolution}
    (target : resolution.targetType = .word)
    (meaning : NumericLiteralDenotes literal resolution.rawValue)
    (requirement : RequirementProves context resolution.requirement resolution.predicate) :
    Dynamic.ResolvedIntegerLiteralConstructs context literal resolution (.word (Word.ofNatModulo resolution.rawValue)) := by
  cases resolution with
  | mk raw type requirementId =>
    dsimp at target
    subst type
    exact .word meaning requirement

theorem LiteralCode.constructs_integer_with_requirement {context : Context}
    {literal : Syntax.CoreLiteralValue} {resolution : IntegerLiteralResolution}
    (target : resolution.targetType = .integer)
    (meaning : NumericLiteralDenotes literal resolution.rawValue)
    (requirement : RequirementProves context resolution.requirement resolution.predicate) :
    Dynamic.ResolvedIntegerLiteralConstructs context literal resolution (.integer (Int.ofNat resolution.rawValue)) := by
  cases resolution with
  | mk raw type requirementId =>
    dsimp at target
    subst type
    exact .integer meaning requirement

theorem LiteralCode.constructs_word {compilation : Compilation} {context : Context}
    {literal : Syntax.CoreLiteralValue} {resolution : IntegerLiteralResolution}
    (valid : ContextValid compilation context) (target : resolution.targetType = .word)
    (meaning : NumericLiteralDenotes literal resolution.rawValue)
    (requirement : ∃ solved ∈ compilation.solvedRequirements, solved.id = resolution.requirement ∧
      solved.predicate = ProgramSignatures.builtinIntPredicate .word) :
    Dynamic.ResolvedIntegerLiteralConstructs context literal resolution (.word (Word.ofNatModulo resolution.rawValue)) := by
  exact LiteralCode.constructs_word_with_requirement target meaning
    (by simpa only [IntegerLiteralResolution.predicate, target] using proves valid requirement)


theorem LiteralCode.constructs_integer {compilation : Compilation} {context : Context}
    {literal : Syntax.CoreLiteralValue} {resolution : IntegerLiteralResolution}
    (valid : ContextValid compilation context) (target : resolution.targetType = .integer)
    (meaning : NumericLiteralDenotes literal resolution.rawValue)
    (requirement : ∃ solved ∈ compilation.solvedRequirements, solved.id = resolution.requirement ∧
      solved.predicate = ProgramSignatures.builtinIntPredicate .integer) :
    Dynamic.ResolvedIntegerLiteralConstructs context literal resolution (.integer (Int.ofNat resolution.rawValue)) := by
  exact LiteralCode.constructs_integer_with_requirement target meaning
    (by simpa only [IntegerLiteralResolution.predicate, target] using proves valid requirement)


private theorem projected_word (compilation : Compilation) (source : TypedSource) :
    projected compilation source TypeSystem.Ty.word = .ok .word := rfl
private theorem projected_integer (compilation : Compilation) (source : TypedSource) :
    projected compilation source TypeSystem.Ty.integer = .ok .integer := rfl

theorem LeafResolution.bindings_unique {context : Context} {pattern : TypedMatchPattern}
    {value : Dynamic.Value} {left right : List (TypedBinder × Dynamic.Value)}
    (leaf : LeafResolution pattern.resolution)
    (first : Dynamic.PatternMatches context pattern value left)
    (second : Dynamic.PatternMatches context pattern value right) : left = right := by
  rcases pattern with ⟨spelling, type, resolution, requirements⟩
  cases first with
  | intro firstSource firstMatch =>
    cases second with
    | intro secondSource secondMatch =>
      cases leaf <;>
        simp only [Dynamic.PatternResolutionMatches, matchPatternResolutionInstructions] at firstMatch secondMatch <;>
        cases firstMatch <;> cases secondMatch <;> rfl

theorem LeafResolution.excludes {context : Context} {pattern : TypedMatchPattern}
    {value : Dynamic.Value} {bindings : List (TypedBinder × Dynamic.Value)}
    (leaf : LeafResolution pattern.resolution)
    (failure : Dynamic.PatternDoesNotMatch context pattern value)
    (matched : Dynamic.PatternMatches context pattern value bindings) : False := by
  rcases pattern with ⟨spelling, type, resolution, requirements⟩
  cases failure with
  | intro failedSource failedMatch =>
    cases matched with
    | intro matchedSource matchedMatch =>
      cases leaf <;>
        simp only [Dynamic.PatternResolutionDoesNotMatch, Dynamic.PatternResolutionMatches,
          matchPatternResolutionInstructions] at failedMatch matchedMatch <;>
        exact failedMatch.mismatch _ matchedMatch

private theorem ordinary_numeric {compilation : Compilation} {context : Context}
    {source : TypedSource} {scope : Scope} {site : StatementId} {span : Syntax.SourceSpan}
    {expected : TypeSystem.Ty} {pattern : TypedMatchPattern} {compiled : Pattern}
    (certificate : Certificate compilation source scope site span expected pattern compiled)
    (valid : ContextValid compilation context) : NumericRequirements context pattern.resolution := by
  intro literal numeric form
  rcases pattern with ⟨spelling, patternType, resolution, requirements⟩
  dsimp only at form
  subst resolution
  obtain ⟨instructions, root, tree⟩ := certificate.tree
  obtain ⟨_, instructionsEq, _⟩ := rootInstructions_sound compilation context valid.signatures
    spelling (.integerLiteral literal numeric) instructions root
  subst instructions
  cases tree with
  | literal projection validated =>
    have code := literalMatcher_sound compilation site span expected literal numeric _ validated
    cases code with
    | word target meaning retained | integer target meaning retained =>
      simpa only [IntegerLiteralResolution.predicate, target] using proves valid retained

/-- Every accepted leaf pattern produces its independent source outcome in
finite Core steps, packs the exact ordered bindings, and preserves the store. -/
theorem leaf_preserves_with_requirements {compilation : Compilation} {context : Context}
    {source : TypedSource} {scope : Scope} {site : StatementId} {span : Syntax.SourceSpan}
    {expected : TypeSystem.Ty} {pattern : TypedMatchPattern} {compiled : Pattern}
    (certificate : Certificate compilation source scope site span expected pattern compiled)
    (signatures : context.signatures = compilation.signatures)
    (numeric : NumericRequirements context pattern.resolution) (leaf : LeafResolution pattern.resolution)
    {registry : SourceCoreRawMetadata.Registry} {ambient : AmbientDefinitions compilation.checked.catalog.definitions}
    {functions : FunctionModel compilation.checked.catalog ambient} {mapping : LocationMap}
    {sourceValue : Dynamic.Value} {value : Value} {world : StoreTyping}
    (represented : ValueRep compilation.checked registry functions mapping world expected sourceValue value compiled.type)
    (environment : Environment) (store : Store) :
    ∃ outcome, OutcomeRep compilation.checked registry functions mapping world context pattern compiled sourceValue outcome ∧
      Evaluates (value :: environment) store (.apply compiled.matcher (.var 0)) outcome store := by
  rcases pattern with ⟨spelling, patternType, resolution, requirements⟩
  obtain ⟨instructions, root, tree⟩ := certificate.tree
  obtain ⟨arity, instructionsEq, sourceRep⟩ := rootInstructions_sound compilation context signatures
    spelling resolution instructions root
  subst instructions
  cases leaf with
  | wildcard =>
    cases tree with
    | wildcard projection =>
      refine ⟨.inRight .unit .unit, .matched (bindings := []) (values := []) ?_ .nil, ?_⟩
      · exact .intro sourceRep .wildcard
      exact SourceCoreCompatibleDataMatches.wildcard_evaluates environment store _ value
  | binder binder =>
    cases tree with
    | binder projection sourceType binderValid =>
      refine ⟨.inRight .unit value, .matched (bindings := [(binder, sourceValue)]) (values := [value]) ?_ (.cons (sourceType.symm ▸ represented) .nil), ?_⟩
      · exact .intro sourceRep .binder
      exact SourceCoreCompatibleDataMatches.binder_evaluates environment store _ value
  | literal literal resolution =>
    cases tree with
    | literal projection validated =>
      have code := literalMatcher_sound compilation site span expected literal resolution _ validated
      cases code with
      | word target meaning retained =>
        have coreType := projection
        rw [projected_word] at coreType
        cases coreType
        obtain ⟨actual, rfl, rfl⟩ := CompatibleExpressionPrimitives.word_fields represented
        have constructs := LiteralCode.constructs_word_with_requirement target meaning (numeric _ _ rfl)
        by_cases same : actual = Word.ofNatModulo resolution.rawValue
        · subst actual
          refine ⟨.inRight .unit .unit, .matched (values := []) (.intro sourceRep (.integerLiteral constructs)) .nil, ?_⟩
          exact .apply .lambda (.var rfl)
            (.ifTrue (.binary (.var rfl) .word (by simp [BinaryOp.apply])) (.inRight .unit))
        · refine ⟨.inLeft .unit .unit, .noMatch (.intro sourceRep ⟨.integerLiteral, ?_⟩), ?_⟩
          · intro bindings matched
            cases matched with
            | integerLiteral construction => exact same (Dynamic.Value.word.inj (construction.functional constructs))
          · exact .apply .lambda (.var rfl)
              (.ifFalse (.binary (.var rfl) .word (by simp [BinaryOp.apply, same])) (.inLeft .unit))
      | integer target meaning retained =>
        have coreType := projection
        rw [projected_integer] at coreType
        cases coreType
        obtain ⟨actual, rfl, rfl⟩ := CompatibleExpressionPrimitives.integer_fields represented
        have constructs := LiteralCode.constructs_integer_with_requirement target meaning (numeric _ _ rfl)
        by_cases same : actual = Int.ofNat resolution.rawValue
        · subst actual
          refine ⟨.inRight .unit .unit, .matched (values := []) (.intro sourceRep (.integerLiteral constructs)) .nil, ?_⟩
          exact .apply .lambda (.var rfl)
            (.ifTrue (.binary (.var rfl) .integer (by simp [BinaryOp.apply])) (.inRight .unit))
        · refine ⟨.inLeft .unit .unit, .noMatch (.intro sourceRep ⟨.integerLiteral, ?_⟩), ?_⟩
          · intro bindings matched
            cases matched with
            | integerLiteral construction => exact same (Dynamic.Value.integer.inj (construction.functional constructs))
          · exact .apply .lambda (.var rfl)
              (.ifFalse (.binary (.var rfl) .integer (by
                simp only [BinaryOp.apply, Option.some.injEq, Value.bool.injEq, beq_eq_false_iff_ne]
                exact same)) (.inLeft .unit))


theorem leaf_preserves {compilation : Compilation} {context : Context}
    {source : TypedSource} {scope : Scope} {site : StatementId} {span : Syntax.SourceSpan}
    {expected : TypeSystem.Ty} {pattern : TypedMatchPattern} {compiled : Pattern}
    (certificate : Certificate compilation source scope site span expected pattern compiled)
    (valid : ContextValid compilation context) (leaf : LeafResolution pattern.resolution)
    {registry : SourceCoreRawMetadata.Registry} {ambient : AmbientDefinitions compilation.checked.catalog.definitions}
    {functions : FunctionModel compilation.checked.catalog ambient} {mapping : LocationMap}
    {sourceValue : Dynamic.Value} {value : Value} {world : StoreTyping}
    (represented : ValueRep compilation.checked registry functions mapping world expected sourceValue value compiled.type)
    (environment : Environment) (store : Store) :
    ∃ outcome, OutcomeRep compilation.checked registry functions mapping world context pattern compiled sourceValue outcome ∧
      Evaluates (value :: environment) store (.apply compiled.matcher (.var 0)) outcome store :=
  leaf_preserves_with_requirements certificate valid.signatures (ordinary_numeric certificate valid)
    leaf represented environment store



private theorem apply_lambda_var {environment : Environment} {store finalStore : Store}
    {value result : Value} {input output : Ty} {body : Expr}
    (completed : Evaluates (value :: environment) store (.apply (.lambda input output body) (.var 0)) result finalStore) :
    Evaluates (value :: value :: environment) store body result finalStore := by
  cases completed with
  | apply function argument body =>
    cases function
    cases argument with
    | var found =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at found
      cases found
      exact body

private theorem word_matcher_inv {environment : Environment} {store finalStore : Store}
    {actual expected : Word} {outcome : Value}
    (completed : Evaluates (.word actual :: environment) store
      (.ifE (.binary .wordEq (.var 0) (.word expected)) (.inRight .unit .unit) (.inLeft .unit .unit))
      outcome finalStore) :
    ((actual = expected ∧ outcome = .inRight .unit .unit) ∨
      (actual ≠ expected ∧ outcome = .inLeft .unit .unit)) ∧ finalStore = store := by
  cases completed with
  | ifTrue condition branch =>
    cases condition with
    | binary left right applied =>
      cases left with
      | var found =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at found
        cases found
        cases right
        cases branch with
        | inRight unit =>
          cases unit
          exact ⟨.inl ⟨by simpa [BinaryOp.apply] using applied, rfl⟩, rfl⟩
  | ifFalse condition branch =>
    cases condition with
    | binary left right applied =>
      cases left with
      | var found =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at found
        cases found
        cases right
        cases branch with
        | inLeft unit =>
          cases unit
          exact ⟨.inr ⟨by simpa [BinaryOp.apply] using applied, rfl⟩, rfl⟩

private theorem integer_matcher_inv {environment : Environment} {store finalStore : Store}
    {actual expected : Int} {outcome : Value}
    (completed : Evaluates (.integer actual :: environment) store
      (.ifE (.binary .integerEq (.var 0) (.integer expected)) (.inRight .unit .unit) (.inLeft .unit .unit))
      outcome finalStore) :
    ((actual = expected ∧ outcome = .inRight .unit .unit) ∨
      (actual ≠ expected ∧ outcome = .inLeft .unit .unit)) ∧ finalStore = store := by
  cases completed with
  | ifTrue condition branch =>
    cases condition with
    | binary left right applied =>
      cases left with
      | var found =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at found
        cases found
        cases right
        cases branch with
        | inRight unit =>
          cases unit
          exact ⟨.inl ⟨by simpa [BinaryOp.apply] using applied, rfl⟩, rfl⟩
  | ifFalse condition branch =>
    cases condition with
    | binary left right applied =>
      cases left with
      | var found =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at found
        cases found
        cases right
        cases branch with
        | inLeft unit =>
          cases unit
          exact ⟨.inr ⟨by simpa [BinaryOp.apply] using applied, rfl⟩, rfl⟩

/-- Reflection consumes only the original native application, comparison and
sum-tag derivations. It never replays preservation or assumes source execution. -/
theorem leaf_reflects_with_requirements {compilation : Compilation} {context : Context}
    {source : TypedSource} {scope : Scope} {site : StatementId} {span : Syntax.SourceSpan}
    {expected : TypeSystem.Ty} {pattern : TypedMatchPattern} {compiled : Pattern}
    (certificate : Certificate compilation source scope site span expected pattern compiled)
    (signatures : context.signatures = compilation.signatures)
    (numeric : NumericRequirements context pattern.resolution) (leaf : LeafResolution pattern.resolution)
    {registry : SourceCoreRawMetadata.Registry} {ambient : AmbientDefinitions compilation.checked.catalog.definitions}
    {functions : FunctionModel compilation.checked.catalog ambient} {mapping : LocationMap}
    {sourceValue : Dynamic.Value} {value : Value} {world : StoreTyping}
    (represented : ValueRep compilation.checked registry functions mapping world expected sourceValue value compiled.type)
    {environment : Environment} {store finalStore : Store} {outcome : Value}
    (completed : Evaluates (value :: environment) store (.apply compiled.matcher (.var 0)) outcome finalStore) :
    OutcomeRep compilation.checked registry functions mapping world context pattern compiled sourceValue outcome ∧
      finalStore = store := by
  rcases pattern with ⟨spelling, patternType, resolution, requirements⟩
  obtain ⟨instructions, root, tree⟩ := certificate.tree
  obtain ⟨arity, instructionsEq, sourceRep⟩ := rootInstructions_sound compilation context signatures
    spelling resolution instructions root
  subst instructions
  cases leaf with
  | wildcard =>
    cases tree with
    | wildcard projection =>
      have body := apply_lambda_var completed
      cases body with
      | inRight unit =>
        cases unit
        exact ⟨.matched (bindings := []) (values := []) (.intro sourceRep .wildcard) .nil, rfl⟩
  | binder binder =>
    cases tree with
    | binder projection sourceType binderValid =>
      have body := apply_lambda_var completed
      cases body with
      | inRight result =>
        cases result with
        | var found =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at found
          cases found
          exact ⟨.matched (bindings := [(binder, sourceValue)]) (values := [value])
            (.intro sourceRep .binder) (.cons (sourceType.symm ▸ represented) .nil), rfl⟩
  | literal literal resolution =>
    cases tree with
    | literal projection validated =>
      have code := literalMatcher_sound compilation site span expected literal resolution _ validated
      cases code with
      | word target meaning retained =>
        have coreType := projection
        rw [projected_word] at coreType
        cases coreType
        obtain ⟨actual, rfl, rfl⟩ := CompatibleExpressionPrimitives.word_fields represented
        have constructs := LiteralCode.constructs_word_with_requirement target meaning (numeric _ _ rfl)
        obtain ⟨result, sameStore⟩ := word_matcher_inv (apply_lambda_var completed)
        rcases result with ⟨same, rfl⟩ | ⟨different, rfl⟩
        · subst actual
          exact ⟨.matched (values := []) (.intro sourceRep (.integerLiteral constructs)) .nil, sameStore⟩
        · refine ⟨.noMatch (.intro sourceRep ⟨.integerLiteral, ?_⟩), sameStore⟩
          intro bindings matched
          cases matched with
          | integerLiteral construction => exact different (Dynamic.Value.word.inj (construction.functional constructs))
      | integer target meaning retained =>
        have coreType := projection
        rw [projected_integer] at coreType
        cases coreType
        obtain ⟨actual, rfl, rfl⟩ := CompatibleExpressionPrimitives.integer_fields represented
        have constructs := LiteralCode.constructs_integer_with_requirement target meaning (numeric _ _ rfl)
        obtain ⟨result, sameStore⟩ := integer_matcher_inv (apply_lambda_var completed)
        rcases result with ⟨same, rfl⟩ | ⟨different, rfl⟩
        · subst actual
          exact ⟨.matched (values := []) (.intro sourceRep (.integerLiteral constructs)) .nil, sameStore⟩
        · refine ⟨.noMatch (.intro sourceRep ⟨.integerLiteral, ?_⟩), sameStore⟩
          intro bindings matched
          cases matched with
          | integerLiteral construction => exact different (Dynamic.Value.integer.inj (construction.functional constructs))

/-- Public entry consumes actual compiler success; the structural certificate
is obtained internally and is never an extra caller obligation. -/
theorem compilePattern_leaf_preserves (compilation : Compilation) (fuel : Nat)
    (source : TypedSource) (scope : Scope) (site : StatementId) (span : Syntax.SourceSpan)
    (expected : TypeSystem.Ty) (pattern : TypedMatchPattern)
    (compiled : CertifiedPattern compilation.definitions)
    (accepted : compilePattern compilation fuel source scope site span expected pattern = .ok compiled)
    (context : Context) (valid : ContextValid compilation context) (leaf : LeafResolution pattern.resolution)
    {registry : SourceCoreRawMetadata.Registry} {ambient : AmbientDefinitions compilation.checked.catalog.definitions}
    {functions : FunctionModel compilation.checked.catalog ambient} {mapping : LocationMap}
    {sourceValue : Dynamic.Value} {value : Value} {world : StoreTyping}
    (represented : ValueRep compilation.checked registry functions mapping world expected sourceValue value compiled.pattern.type)
    (environment : Environment) (store : Store) :
    ∃ outcome, OutcomeRep compilation.checked registry functions mapping world context pattern compiled.pattern sourceValue outcome ∧
      Evaluates (value :: environment) store (.apply compiled.pattern.matcher (.var 0)) outcome store :=
  leaf_preserves (certificate_of_compilePattern compilation fuel source scope site span expected pattern compiled accepted)
    valid leaf represented environment store

/-- Any completed native leaf matcher reconstructs independent source meaning
and leaves every surrounding cell unchanged. -/
theorem compilePattern_leaf_reflects (compilation : Compilation) (fuel : Nat)
    (source : TypedSource) (scope : Scope) (site : StatementId) (span : Syntax.SourceSpan)
    (expected : TypeSystem.Ty) (pattern : TypedMatchPattern)
    (compiled : CertifiedPattern compilation.definitions)
    (accepted : compilePattern compilation fuel source scope site span expected pattern = .ok compiled)
    (context : Context) (valid : ContextValid compilation context) (leaf : LeafResolution pattern.resolution)
    {registry : SourceCoreRawMetadata.Registry} {ambient : AmbientDefinitions compilation.checked.catalog.definitions}
    {functions : FunctionModel compilation.checked.catalog ambient} {mapping : LocationMap}
    {sourceValue : Dynamic.Value} {value : Value} {world : StoreTyping}
    (represented : ValueRep compilation.checked registry functions mapping world expected sourceValue value compiled.pattern.type)
    {environment : Environment} {store finalStore : Store} {outcome : Value}
    (completed : Evaluates (value :: environment) store (.apply compiled.pattern.matcher (.var 0)) outcome finalStore) :
    OutcomeRep compilation.checked registry functions mapping world context pattern compiled.pattern sourceValue outcome ∧
      finalStore = store :=
  let certificate := certificate_of_compilePattern compilation fuel source scope site span expected pattern compiled accepted
  leaf_reflects_with_requirements certificate valid.signatures (ordinary_numeric certificate valid)
    leaf represented completed


/-- A supplied independent success fixes exact source binding order. No
evaluation of the generated matcher is assumed. -/
theorem compilePattern_leaf_success_preserves (compilation : Compilation) (fuel : Nat)
    (source : TypedSource) (scope : Scope) (site : StatementId) (span : Syntax.SourceSpan)
    (expected : TypeSystem.Ty) (pattern : TypedMatchPattern)
    (compiled : CertifiedPattern compilation.definitions)
    (accepted : compilePattern compilation fuel source scope site span expected pattern = .ok compiled)
    (context : Context) (valid : ContextValid compilation context) (leaf : LeafResolution pattern.resolution)
    {registry : SourceCoreRawMetadata.Registry} {ambient : AmbientDefinitions compilation.checked.catalog.definitions}
    {functions : FunctionModel compilation.checked.catalog ambient} {mapping : LocationMap}
    {sourceValue : Dynamic.Value} {value : Value} {world : StoreTyping}
    (represented : ValueRep compilation.checked registry functions mapping world expected sourceValue value compiled.pattern.type)
    {bindings : List (TypedBinder × Dynamic.Value)} (matched : Dynamic.PatternMatches context pattern sourceValue bindings)
    (environment : Environment) (store : Store) :
    ∃ values, BindingsRep compilation.checked registry functions mapping world compiled.pattern.bindings bindings values ∧
      Evaluates (value :: environment) store (.apply compiled.pattern.matcher (.var 0))
        (.inRight .unit (packValues values)) store := by
  obtain ⟨outcome, meaning, evaluated⟩ := compilePattern_leaf_preserves compilation fuel source scope site span
    expected pattern compiled accepted context valid leaf represented environment store
  cases meaning with
  | matched actual bindingsRep =>
    have same := leaf.bindings_unique actual matched
    exact ⟨_, same ▸ bindingsRep, evaluated⟩
  | noMatch failure => exact False.elim (leaf.excludes failure matched)

/-- Independent source rejection returns the native no-match tag, with no
bindings or store changes escaping the matcher. -/
theorem compilePattern_leaf_failure_preserves (compilation : Compilation) (fuel : Nat)
    (source : TypedSource) (scope : Scope) (site : StatementId) (span : Syntax.SourceSpan)
    (expected : TypeSystem.Ty) (pattern : TypedMatchPattern)
    (compiled : CertifiedPattern compilation.definitions)
    (accepted : compilePattern compilation fuel source scope site span expected pattern = .ok compiled)
    (context : Context) (valid : ContextValid compilation context) (leaf : LeafResolution pattern.resolution)
    {registry : SourceCoreRawMetadata.Registry} {ambient : AmbientDefinitions compilation.checked.catalog.definitions}
    {functions : FunctionModel compilation.checked.catalog ambient} {mapping : LocationMap}
    {sourceValue : Dynamic.Value} {value : Value} {world : StoreTyping}
    (represented : ValueRep compilation.checked registry functions mapping world expected sourceValue value compiled.pattern.type)
    (failure : Dynamic.PatternDoesNotMatch context pattern sourceValue)
    (environment : Environment) (store : Store) :
    Evaluates (value :: environment) store (.apply compiled.pattern.matcher (.var 0))
      (.inLeft (bundleType compiled.pattern.bindingTypes) .unit) store := by
  obtain ⟨outcome, meaning, evaluated⟩ := compilePattern_leaf_preserves compilation fuel source scope site span
    expected pattern compiled accepted context valid leaf represented environment store
  cases meaning with
  | matched actual bindingsRep => exact False.elim (leaf.excludes failure actual)
  | noMatch actual => exact evaluated

/-- The finite abstract result is the result of every completed machine run;
its sufficient fuel budget is independent of compilation fuel. -/
theorem compilePattern_leaf_run_preserves (compilation : Compilation) (compilationFuel : Nat)
    (source : TypedSource) (scope : Scope) (site : StatementId) (span : Syntax.SourceSpan)
    (expected : TypeSystem.Ty) (pattern : TypedMatchPattern)
    (compiled : CertifiedPattern compilation.definitions)
    (accepted : compilePattern compilation compilationFuel source scope site span expected pattern = .ok compiled)
    (context : Context) (valid : ContextValid compilation context) (leaf : LeafResolution pattern.resolution)
    {registry : SourceCoreRawMetadata.Registry} {ambient : AmbientDefinitions compilation.checked.catalog.definitions}
    {functions : FunctionModel compilation.checked.catalog ambient} {mapping : LocationMap}
    {sourceValue : Dynamic.Value} {value : Value} {world : StoreTyping}
    (represented : ValueRep compilation.checked registry functions mapping world expected sourceValue value compiled.pattern.type)
    (environment : Environment) (store : Store) :
    ∃ outcome, OutcomeRep compilation.checked registry functions mapping world context pattern compiled.pattern sourceValue outcome ∧
      (∃ required, ∀ fuel, required ≤ fuel →
        runStateful fuel (State.initial (.apply compiled.pattern.matcher (.var 0)) (value :: environment) store) = .done outcome store) ∧
      (∀ fuel actual finalStore,
        runStateful fuel (State.initial (.apply compiled.pattern.matcher (.var 0)) (value :: environment) store) = .done actual finalStore →
        actual = outcome ∧ finalStore = store) := by
  obtain ⟨outcome, meaning, evaluated⟩ := compilePattern_leaf_preserves compilation compilationFuel source scope site span
    expected pattern compiled accepted context valid leaf represented environment store
  exact ⟨outcome, meaning, evaluation_runStateful_complete_with_sufficient_fuel evaluated,
    fun _ _ _ ran => evaluation_deterministic (runStateful_evaluation_sound ran) evaluated⟩

end Solcore.SourceSemantics.CoreLowering.CompatiblePatternLeaves
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CompatiblePatternExecution
/-! Pure execution of the actual compatible matcher combinators. Child bundles
retain general typed payloads, remain lexical, and never change the store. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatiblePatternExecution
open Core Frontend SourceInference DataEquality
open DataPatternValues DataPatternExecution CompatiblePayload CompatiblePatternLeaves SourceCoreCompatibleDataMatches
variable {checked : SourceCoreCompatibleCatalog.Checked} {registry : SourceCoreRawMetadata.Registry}
  {ambient : AmbientDefinitions checked.catalog.definitions} {functions : FunctionModel checked.catalog ambient}
  {mapping : GeneralHeap.LocationMap} {world : StoreTyping}

theorem bindings_length {binders : List (TypedBinder × Ty)} {sources : List (TypedBinder × Dynamic.Value)} {values : List Value}
    (represented : BindingsRep checked registry functions mapping world binders sources values) : binders.length = values.length := by
  induction represented with
  | nil => rfl
  | cons head tail ih => simp [ih]

theorem bindings_append {a c : List (TypedBinder × Ty)} {b d : List (TypedBinder × Dynamic.Value)} {v w : List Value}
    (left : BindingsRep checked registry functions mapping world a b v)
    (right : BindingsRep checked registry functions mapping world c d w) :
    BindingsRep checked registry functions mapping world (a ++ c) (b ++ d) (v ++ w) := by
  induction left with
  | nil => exact right
  | cons head tail ih => exact .cons head ih

theorem bundle_evaluates {environment : Environment} {store : Store} {expressions : List Expr} {values : List Value}
    (evaluations : ListRel (fun expression value => Evaluates environment store expression value store) expressions values) :
    Evaluates environment store (bundle expressions) (packValues values) store := by
  induction evaluations with
  | nil => exact .unit
  | cons head tail ih =>
    cases tail with
    | nil => exact head
    | cons second rest => exact .pair head ih

/-- The same closed matcher can be applied in any surrounding environment;
the input expression is a pure projection path. -/
def MatcherRuns (pattern : Pattern) (input : Value) (bindings : List Value) : Prop :=
  ∀ environment store expression, Selects environment expression input →
    Evaluates environment store (.apply pattern.matcher expression)
      (.inRight .unit (packValues bindings)) store

/-- A child vector extends an already selected binding accumulated in source order. -/
def ChildrenRun (patterns : List Pattern) (inputs bindings : List Value) : Prop :=
  ∀ environment store expressions accumulated accumulatedValues outputType,
    ListRel (Selects environment) expressions inputs →
    ListRel (Selects environment) accumulated accumulatedValues →
    Evaluates environment store (matchChildren outputType patterns expressions accumulated)
      (.inRight .unit (packValues (accumulatedValues ++ bindings))) store

theorem ChildrenRun.nil : ChildrenRun [] [] [] := by
  intro environment store expressions accumulated accumulatedValues outputType selected previous
  cases selected
  simpa [matchChildren] using Evaluates.inRight
    (leftType := Ty.unit) (bundle_evaluates (ListRel.map previous fun _ _ path => path.evaluates store))

theorem ChildrenRun.cons {pattern : Pattern} {patterns : List Pattern} {input : Value}
    {inputs headBindings tailBindings : List Value}
    (length : pattern.bindingTypes.length = headBindings.length)
    (head : MatcherRuns pattern input headBindings) (tail : ChildrenRun patterns inputs tailBindings) :
    ChildrenRun (pattern :: patterns) (input :: inputs) (headBindings ++ tailBindings) := by
  intro environment store expressions accumulated accumulatedValues outputType selected previous
  cases selected with
  | cons inputSelected restSelected =>
    apply Evaluates.caseRight (head environment store _ inputSelected)
    have projections := projectionList_selects (environment := packValues headBindings :: environment)
      (expression := .var 0) (types := pattern.bindingTypes) (values := headBindings) (.var rfl) length
    have result := tail (packValues headBindings :: environment) store _ _ _ outputType
      (selects_weaken_list restSelected _) (ListRel.append (selects_weaken_list previous _) projections)
    simpa [List.append_assoc] using result

def MatcherFails (pattern : Pattern) (input : Value) : Prop :=
  ∀ environment store expression, Selects environment expression input →
    Evaluates environment store (.apply pattern.matcher expression)
      (.inLeft (bundleType pattern.bindingTypes) .unit) store

def ChildrenFail (patterns : List Pattern) (inputs : List Value) : Prop :=
  ∀ environment store expressions accumulated accumulatedValues outputType,
    ListRel (Selects environment) expressions inputs →
    ListRel (Selects environment) accumulated accumulatedValues →
    Evaluates environment store (matchChildren outputType patterns expressions accumulated)
      (.inLeft outputType .unit) store

theorem ChildrenFail.head {pattern : Pattern} {patterns : List Pattern} {input : Value} {inputs : List Value}
    (failed : MatcherFails pattern input) : ChildrenFail (pattern :: patterns) (input :: inputs) := by
  intro environment store expressions accumulated accumulatedValues outputType selected previous
  cases selected with
  | cons inputSelected restSelected => exact .caseLeft (failed _ _ _ inputSelected) (.inLeft .unit)

theorem ChildrenFail.tail {pattern : Pattern} {patterns : List Pattern} {input : Value}
    {inputs bindings : List Value} (length : pattern.bindingTypes.length = bindings.length)
    (head : MatcherRuns pattern input bindings) (tail : ChildrenFail patterns inputs) :
    ChildrenFail (pattern :: patterns) (input :: inputs) := by
  intro environment store expressions accumulated accumulatedValues outputType selected previous
  cases selected with
  | cons inputSelected restSelected =>
    apply Evaluates.caseRight (head environment store _ inputSelected)
    have projections := projectionList_selects (environment := packValues bindings :: environment)
      (expression := .var 0) (types := pattern.bindingTypes) (values := bindings) (.var rfl) length
    exact tail (packValues bindings :: environment) store _ _ _ outputType
      (selects_weaken_list restSelected _) (ListRel.append (selects_weaken_list previous _) projections)


theorem projectedList_catalog {compilation : CompatiblePatternCertificates.Compilation} {source : TypedSource}
    {types : List TypeSystem.Ty} {coreTypes : List Ty}
    (projected : types.mapM (SourceCoreCompatibleDataMatches.projected compilation source) = .ok coreTypes) :
    types.mapM compilation.checked.catalog.project = .ok coreTypes := by
  induction types generalizing coreTypes with
  | nil => simp [List.mapM_nil, pure, Except.pure] at projected; subst coreTypes; rfl
  | cons type types ih =>
    cases head : SourceCoreCompatibleDataMatches.projected compilation source type with
    | error error => simp [List.mapM_cons, head, bind, Except.bind] at projected
    | ok native =>
      cases tail : types.mapM (SourceCoreCompatibleDataMatches.projected compilation source) with
      | error error => simp [List.mapM_cons, head, tail, bind, Except.bind] at projected
      | ok natives =>
        simp [List.mapM_cons, head, tail, bind, Except.bind, pure, Except.pure] at projected
        subst coreTypes
        have first := CompatibleExpressionReads.projectType_of_accepted head
        simp [List.mapM_cons, first, ih tail, bind, Except.bind, pure, Except.pure]
end Solcore.SourceSemantics.CoreLowering.CompatiblePatternExecution
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CompatiblePatternMetadata
/-! The actual raw constructor guard agrees with independent source matching.
Authentic declarations have a unique parameter domain; the ordered argument
lookup therefore recovers every retained substitution entry. Constructor tags
or native type equality alone do not justify this exact metadata identity. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatiblePatternMetadata
open Core Frontend SourceInference TypeSystem CompatiblePayload CompatibleConstructorMetadata

private theorem lookup_cons (parameters : List TypeParameterId) (candidate : TypeParameterId)
    (value : TypeSystem.Ty) (tail : ParameterSubstitution) (missing : candidate ∉ parameters) :
    parameters.mapM (ParameterSubstitution.lookup? ((candidate, value) :: tail)) = parameters.mapM tail.lookup? := by
  induction parameters with
  | nil => rfl
  | cons parameter rest ih =>
    simp only [List.mem_cons, not_or] at missing
    rw [List.mapM_cons, List.mapM_cons]
    rw [show ParameterSubstitution.lookup? ((candidate, value) :: tail) parameter = tail.lookup? parameter by
      simp only [ParameterSubstitution.lookup?, if_neg missing.1]]
    rw [ih missing.2]

private theorem ordered_lookup (substitution : ParameterSubstitution) (unique : (substitution.map Prod.fst).Nodup) :
    (substitution.map Prod.fst).mapM substitution.lookup? = some (substitution.map Prod.snd) := by
  induction substitution with
  | nil => rfl
  | cons entry rest ih =>
    obtain ⟨parameter, value⟩ := entry
    simp only [List.map_cons, List.nodup_cons] at unique
    rw [List.map_cons, List.mapM_cons]
    rw [show ParameterSubstitution.lookup? ((parameter, value) :: rest) parameter = some value by
      simp [ParameterSubstitution.lookup?]]
    rw [lookup_cons _ _ _ _ unique.1, ih unique.2]
    rfl

theorem metadata_eq {signatures : ProgramSignatures} {left right : DataConstructorInstantiation}
    (valid : SignatureCatalogWellFormed signatures)
    (first : SourceCoreRawMetadata.constructorAuthentic signatures left = true)
    (second : SourceCoreRawMetadata.constructorAuthentic signatures right = true)
    (agrees : Dynamic.ConstructorInstantiationsAgree left right) : left = right := by
  obtain ⟨leftSignature, leftConstructor, leftArguments, leftData, leftCtor, leftKeys, leftMapped, leftPayloads, leftResult⟩ := facts first
  obtain ⟨rightSignature, rightConstructor, rightArguments, rightData, rightCtor, rightKeys, rightMapped, rightPayloads, rightResult⟩ := facts second
  have constructor := agrees.constructor_eq
  rw [constructor] at leftData
  have sameSignature := (List.cons.inj (leftData.symm.trans rightData)).1
  subst rightSignature
  have member : leftSignature ∈ signatures.dataTypes :=
    (List.mem_filter.mp (leftData ▸ (show leftSignature ∈ [leftSignature] by simp))).1
  have unique := (valid.data_parameters leftSignature member).1
  have arguments : leftArguments = rightArguments := by
    have same := congrArg SourceCoreDataCatalog.nominalParts (leftResult.symm.trans (agrees.result_type_eq.trans rightResult))
    simpa only [DataPatternAuthenticity.nominalParts_nominal, Option.some.injEq, Prod.mk.injEq, true_and] using same
  have leftValues := ordered_lookup left.parameterSubstitution (leftKeys.symm ▸ unique)
  have rightValues := ordered_lookup right.parameterSubstitution (rightKeys.symm ▸ unique)
  rw [leftKeys] at leftValues
  rw [rightKeys] at rightValues
  have leftValues := Option.some.inj (leftValues.symm.trans leftMapped)
  have rightValues := Option.some.inj (rightValues.symm.trans rightMapped)
  have firstZip := List.zip_of_prod leftKeys leftValues
  have secondZip := List.zip_of_prod rightKeys rightValues
  rw [arguments] at firstZip
  have substitution := firstZip.trans secondZip.symm
  cases left
  cases right
  cases constructor
  cases substitution
  cases agrees.payload_types_eq
  cases agrees.result_type_eq
  rfl

theorem raw_guard_iff {checked : SourceCoreCompatibleCatalog.Checked}
    {registry : SourceCoreRawMetadata.Registry} {actual expected : DataConstructorInstantiation} {left right : Word}
    (valid : SignatureCatalogWellFormed checked.signatures)
    (owner : registry.signatures = checked.signatures)
    (first : MetadataRep registry (.constructor actual) left)
    (second : MetadataRep registry (.constructor expected) right) :
    left = right ↔ Dynamic.ConstructorInstantiationsAgree actual expected := by
  constructor
  · intro same
    have exactMetadata := (first.ids_equal_iff second).mp same
    cases exactMetadata
    exact .refl _
  · intro agree
    have same := metadata_eq valid (constructor_authenticated first owner) (constructor_authenticated second owner) agree
    exact (first.ids_equal_iff second).mpr (congrArg SourceCoreRawMetadata.Metadata.constructor same)

end Solcore.SourceSemantics.CoreLowering.CompatiblePatternMetadata
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CompatiblePatternSuccess
/-! Every independently successful source pattern is preserved by the actual
compatible compiler, for arbitrary finite nesting and general payload leaves.
Authentic raw constructor guards and ordered binding bundles are retained. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatiblePatternSuccess
open Core Frontend SourceInference GeneralHeap DataPatternValues DataPatternExecution DataEquality
open CompatiblePayload CompatiblePatternLeaves CompatiblePatternCertificates CompatiblePatternExecution
open SourceCoreCompatibleDataMatches
variable {compilation : Compilation} {registry : SourceCoreRawMetadata.Registry}
  {ambient : AmbientDefinitions compilation.checked.catalog.definitions}
  {functions : FunctionModel compilation.checked.catalog ambient} {mapping : LocationMap} {world : StoreTyping}

theorem Tree.projected {source : TypedSource} {site : StatementId} {span : Syntax.SourceSpan} {scope : Scope}
    {type : TypeSystem.Ty} {instructions rest : List MatchPatternInstruction} {pattern : Pattern}
    (tree : Tree compilation source site span scope type instructions pattern rest) :
    compilation.checked.catalog.project type = .ok pattern.type := by
  cases tree <;> apply CompatibleExpressionReads.projectType_of_accepted <;> assumption

private theorem literal_success {context : Context} {literal : Syntax.CoreLiteralValue}
    {resolution : IntegerLiteralResolution} {expected : TypeSystem.Ty} {matcher : Expr}
    {source : TypedSource} {sourceValue : Dynamic.Value} {value : Value} {type : Ty}
    (projection : projected compilation source expected = .ok type)
    (code : LiteralCode compilation literal resolution expected matcher)
    (constructed : Dynamic.ResolvedIntegerLiteralConstructs context literal resolution sourceValue)
    (represented : ValueRep compilation.checked registry functions mapping world expected sourceValue value type) :
    CompatiblePatternExecution.MatcherRuns ⟨type, [], [resolution.requirement], matcher⟩ value [] := by
  cases constructed with
  | word meaning evidence =>
    cases code with
    | word target numeric retained =>
      have typeEq : type = .word := Except.ok.inj projection.symm
      subst type
      obtain ⟨actual, sameSource, sameNative⟩ := CompatibleExpressionPrimitives.word_fields represented
      have same := Dynamic.Value.word.inj sameSource
      subst actual
      subst value
      intro environment store expression selected
      exact .apply .lambda (selected.evaluates store)
        (.ifTrue (.binary (.var rfl) .word (by simp [BinaryOp.apply])) (.inRight .unit))
    | integer target => cases target
  | integer meaning evidence =>
    cases code with
    | word target => cases target
    | integer target numeric retained =>
      have typeEq : type = .integer := Except.ok.inj projection.symm
      subst type
      obtain ⟨actual, sameSource, sameNative⟩ := CompatibleExpressionPrimitives.integer_fields represented
      have same := Dynamic.Value.integer.inj sameSource
      subst actual
      subst value
      intro environment store expression selected
      exact .apply .lambda (selected.evaluates store)
        (.ifTrue (.binary (.var rfl) .integer (by simp [BinaryOp.apply])) (.inRight .unit))

def TreeSuccess (context : Context) (type : TypeSystem.Ty) (instructions : List MatchPatternInstruction)
    (pattern : Pattern) (rest : List MatchPatternInstruction) : Prop :=
  ∀ source value bindings sourceRest,
    ValueRep compilation.checked registry functions mapping world type source value pattern.type →
    Dynamic.PatternInstructionMatches context source instructions bindings sourceRest →
    ∃ values, sourceRest = rest ∧
      BindingsRep compilation.checked registry functions mapping world pattern.bindings bindings values ∧
      CompatiblePatternExecution.MatcherRuns pattern value values

def ForestSuccess (context : Context) (types : List TypeSystem.Ty) (instructions : List MatchPatternInstruction)
    (patterns : List Pattern) (rest : List MatchPatternInstruction) : Prop :=
  ∀ sources values coreTypes bindings sourceRest,
    ValuesRep compilation.checked registry functions mapping world types sources values coreTypes →
    Dynamic.PatternInstructionsMatch context sources instructions bindings sourceRest →
    ∃ boundValues, sourceRest = rest ∧
      BindingsRep compilation.checked registry functions mapping world (patterns.flatMap (·.bindings)) bindings boundValues ∧
      CompatiblePatternExecution.ChildrenRun patterns values boundValues

/-- The structural induction closes all child matcher obligations. Compilation
registry words can be transported into the actual extended input registry. -/
theorem Tree.success {context : Context} {source : TypedSource} {site : StatementId} {span : Syntax.SourceSpan}
    {scope : Scope} {type : TypeSystem.Ty} {instructions rest : List MatchPatternInstruction} {pattern : Pattern}
    (catalogValid : SignatureCatalogWellFormed compilation.checked.signatures)
    (extended : SourceCoreRawMetadata.Extends compilation.values.registry registry)
    (tree : Tree compilation source site span scope type instructions pattern rest) :
    TreeSuccess (compilation := compilation) (registry := registry) (functions := functions)
      (mapping := mapping) (world := world) context type instructions pattern rest := by
  induction tree using Tree.rec
    (motive_2 := fun types instructions patterns rest _ =>
      ForestSuccess (compilation := compilation) (registry := registry) (functions := functions)
        (mapping := mapping) (world := world) context types instructions patterns rest) with
  | wildcard projection =>
    intro source value bindings sourceRest represented matched
    cases matched
    exact ⟨[], rfl, .nil, fun _ store _ selected => .apply .lambda (selected.evaluates store) (.inRight .unit)⟩
  | binder projection sourceType valid =>
    intro source value bindings sourceRest represented matched
    cases matched
    exact ⟨[value], rfl, .cons (sourceType.symm ▸ represented) .nil,
      fun _ store _ selected => .apply .lambda (selected.evaluates store) (.inRight (.var rfl))⟩
  | literal projection validated =>
    intro sourceValue value bindings sourceRest represented matched
    cases matched with
    | integerLiteral construction =>
      exact ⟨[], rfl, .nil, literal_success projection (literalMatcher_sound compilation _ _ _ _ _ _ validated) construction represented⟩
  | @tuple expected coreType count types instructions rest children coreTypes projection unpacked childrenTree projectedChildren ih =>
    intro sourceValue value bindings sourceRest represented matched
    cases matched with
    | tuple packed arity matchedChildren =>
      obtain ⟨sourceValues, values, actualTypes, valueReps, packing, valueEq, typeEq⟩ := CompatiblePatternValues.unpack unpacked represented
      have lengths := CompatiblePayload.ValuesRep.length valueReps
      have elementsEq := Dynamic.ValuesPack.injective_of_length_eq packed packing
        (arity.trans ((unpackTypes_length unpacked).symm.trans lengths.1))
      subst sourceValues
      subst value
      obtain ⟨boundValues, restEq, bindingRep, childrenRun⟩ := ih _ _ _ _ _ valueReps matchedChildren
      refine ⟨boundValues, restEq, bindingRep, ?_⟩
      intro environment store expression selected
      apply Evaluates.apply .lambda (selected.evaluates store)
      have nativeTypes : actualTypes = coreTypes := Except.ok.inj (valueReps.projection.symm.trans (projectedList_catalog projectedChildren))
      subst actualTypes
      have paths := projectionList_selects (environment := packValues values :: environment)
        (expression := .var 0) (.var rfl) (lengths.2.2.symm.trans lengths.2.1)
      simpa [tuplePattern, childValues] using childrenRun _ store _ [] [] _ paths .nil
  | @constructor expected coreType instantiation count constructor definition metadata instructions rest children coreTypes
      projection result arity resolved sameType raw childrenTree projectedChildren registered ih =>
    intro sourceValue value bindings sourceRest represented matched
    cases matched with
    | constructor agree countEq matchedChildren =>
      obtain ⟨tag, actualId, values, actualTypes, valueEq, typeEq, fields⟩ := constructor_fields represented rfl
      have authentic := CompatibleConstructorMetadata.resolved_facts resolved
      have sourceEq := CompatiblePatternMetadata.metadata_eq catalogValid
        (constructor_authenticated fields.metadataRep fields.registryOwner) authentic.1 agree
      rw [sourceEq] at fields
      have tagEq := Option.some.inj (fields.selected.symm.trans authentic.2)
      subst tag
      have expectedRep : MetadataRep registry (.constructor instantiation) metadata :=
        ⟨extended.lookup (SourceCoreRawMetadata.Registry.id?_reconstruct raw)⟩
      have idEq := (fields.metadataRep.ids_equal_iff expectedRep).mpr rfl
      subst actualId
      subst value
      obtain ⟨boundValues, restEq, bindingRep, childrenRun⟩ := ih _ _ _ _ _ fields.payloads matchedChildren
      refine ⟨boundValues, restEq, bindingRep, ?_⟩
      intro environment store expression selected
      apply Evaluates.apply .lambda (selected.evaluates store)
      have lookup : definition.constructorPayloadTypes[constructor.index]? =
          some (.product .word (SourceCoreCompatibleCatalog.packTypes actualTypes)) := by
        simpa [DataEnvironment.lookupConstructorPayloadType?, DataEnvironment.lookupDataType?, registered] using fields.registered
      have branchLookup : (definition.constructorPayloadTypes.zipIdx.map fun (_, index) =>
          if index = constructor.index then rawConstructor metadata
            (bundleType ((children.flatMap (·.bindings)).map Prod.snd))
            (matchChildren (bundleType ((children.flatMap (·.bindings)).map Prod.snd)) children
              (coreTypes.zipIdx.map fun (_, index) => SourceCoreDataExpressions.projectPacked index coreTypes (.second (.var 0))) [])
          else .inLeft (bundleType ((children.flatMap (·.bindings)).map Prod.snd)) .unit)[constructor.index]? =
          some (rawConstructor metadata (bundleType ((children.flatMap (·.bindings)).map Prod.snd))
            (matchChildren (bundleType ((children.flatMap (·.bindings)).map Prod.snd)) children
              (coreTypes.zipIdx.map fun (_, index) => SourceCoreDataExpressions.projectPacked index coreTypes (.second (.var 0))) [])) := by
        simp [List.getElem?_map, List.getElem?_zipIdx, lookup]
      apply Evaluates.matchData (.var rfl) rfl branchLookup
      apply rawConstructor_matches
      have nativeTypes : actualTypes = coreTypes := Except.ok.inj (fields.payloads.projection.symm.trans (projectedList_catalog projectedChildren))
      subst actualTypes
      have lengths := CompatiblePayload.ValuesRep.length fields.payloads
      have paths := projectionList_selects
        (environment := .pair (.word metadata) (packValues values) :: .constructed constructor (.pair (.word metadata) (packValues values)) :: environment)
        (expression := .second (.var 0)) (Selects.second (.var rfl)) (lengths.2.2.symm.trans lengths.2.1)
      simpa [constructorPattern, Pattern.bindingTypes] using childrenRun _ store _ [] [] _ paths .nil
  | nil =>
    intro sources values coreTypes bindings sourceRest represented matched
    cases represented
    cases matched
    exact ⟨[], rfl, .nil, CompatiblePatternExecution.ChildrenRun.nil⟩
  | @cons type types instructions afterHead rest head tail headTree tailTree headIH tailIH =>
    intro sources values coreTypes bindings sourceRest represented matched
    cases represented with
    | cons valueRep valuesRep =>
      have sameType := Except.ok.inj (valueRep.projection.symm.trans (Tree.projected headTree))
      subst sameType
      cases matched with
      | cons headMatch tailMatch =>
        obtain ⟨headValues, headRestEq, headBindings, headRun⟩ := headIH _ _ _ _ valueRep headMatch
        subst headRestEq
        obtain ⟨tailValues, tailRestEq, tailBindings, tailRun⟩ := tailIH _ _ _ _ _ valuesRep tailMatch
        exact ⟨headValues ++ tailValues, tailRestEq, bindings_append headBindings tailBindings,
          CompatiblePatternExecution.ChildrenRun.cons (by simpa [Pattern.bindingTypes] using bindings_length headBindings) headRun tailRun⟩

/-- Public success preservation extracts the structural tree from actual
compiler acceptance and preserves the independent source binding sequence. -/
theorem compilePattern_success_preserves (compilation : Compilation) (fuel : Nat)
    (source : TypedSource) (scope : Scope) (site : StatementId) (span : Syntax.SourceSpan)
    (expected : TypeSystem.Ty) (pattern : TypedMatchPattern) (compiled : CertifiedPattern compilation.definitions)
    (accepted : compilePattern compilation fuel source scope site span expected pattern = .ok compiled)
    (context : Context) (signatures : context.signatures = compilation.signatures)
    (catalogValid : SignatureCatalogWellFormed compilation.checked.signatures)
    {registry : SourceCoreRawMetadata.Registry} {ambient : AmbientDefinitions compilation.checked.catalog.definitions}
    {functions : FunctionModel compilation.checked.catalog ambient} {mapping : LocationMap} {world : StoreTyping}
    (extended : SourceCoreRawMetadata.Extends compilation.values.registry registry)
    {sourceValue : Dynamic.Value} {value : Value} {bindings : List (TypedBinder × Dynamic.Value)}
    (represented : ValueRep compilation.checked registry functions mapping world expected sourceValue value compiled.pattern.type)
    (matched : Dynamic.PatternMatches context pattern sourceValue bindings) :
    ∃ values, BindingsRep compilation.checked registry functions mapping world compiled.pattern.bindings bindings values ∧
      CompatiblePatternExecution.MatcherRuns compiled.pattern value values := by
  have certificate := certificate_of_compilePattern compilation fuel source scope site span expected pattern compiled accepted
  obtain ⟨instructions, root, tree⟩ := certificate.tree
  obtain ⟨arity, instructionsEq, sourceRep⟩ := rootInstructions_sound compilation context signatures _ _ _ root
  cases matched with
  | intro spelling matched =>
    have arityEq := Dynamic.MatchPatternSourceRepresents.rootArity_eq sourceRep spelling
    subst arityEq
    subst instructions
    obtain ⟨values, _, bindingsRep, runs⟩ := Tree.success catalogValid extended tree _ _ _ _ represented matched
    exact ⟨values, bindingsRep, runs⟩

/-- A source success finishes with a separate sufficient machine budget;
every completed run has the same ordered native bundle and original store. -/
theorem compilePattern_success_run (compilation : Compilation) (fuel : Nat)
    (source : TypedSource) (scope : Scope) (site : StatementId) (span : Syntax.SourceSpan)
    (expected : TypeSystem.Ty) (pattern : TypedMatchPattern) (compiled : CertifiedPattern compilation.definitions)
    (accepted : compilePattern compilation fuel source scope site span expected pattern = .ok compiled)
    (context : Context) (signatures : context.signatures = compilation.signatures)
    (catalogValid : SignatureCatalogWellFormed compilation.checked.signatures)
    {registry : SourceCoreRawMetadata.Registry} {ambient : AmbientDefinitions compilation.checked.catalog.definitions}
    {functions : FunctionModel compilation.checked.catalog ambient} {mapping : LocationMap} {world : StoreTyping}
    (extended : SourceCoreRawMetadata.Extends compilation.values.registry registry)
    {sourceValue : Dynamic.Value} {value : Value} {bindings : List (TypedBinder × Dynamic.Value)}
    (represented : ValueRep compilation.checked registry functions mapping world expected sourceValue value compiled.pattern.type)
    (matched : Dynamic.PatternMatches context pattern sourceValue bindings) (environment : Environment) (store : Store) :
    ∃ values, BindingsRep compilation.checked registry functions mapping world compiled.pattern.bindings bindings values ∧
      (∃ required, ∀ fuel, required ≤ fuel → runStateful fuel
        (.initial (.apply compiled.pattern.matcher (.var 0)) (value :: environment) store) = .done (.inRight .unit (packValues values)) store) ∧
      (∀ fuel outcome after, runStateful fuel
        (.initial (.apply compiled.pattern.matcher (.var 0)) (value :: environment) store) = .done outcome after →
        outcome = .inRight .unit (packValues values) ∧ after = store) := by
  obtain ⟨values, represented, runs⟩ := compilePattern_success_preserves compilation fuel source scope site span expected pattern
    compiled accepted context signatures catalogValid extended represented matched
  have evaluated := runs (value :: environment) store (.var 0) (.var rfl)
  exact ⟨values, represented, evaluation_runStateful_complete_with_sufficient_fuel evaluated,
    fun _ _ _ ran => evaluation_deterministic (runStateful_evaluation_sound ran) evaluated⟩
end Solcore.SourceSemantics.CoreLowering.CompatiblePatternSuccess
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CompatiblePatternDecision
/-! Complete finite decisions for the actual compatible matcher tree. Every
recursive child obligation is discharged by the tree induction. Exact raw
constructor identity is checked before traversing any payload child. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatiblePatternDecision
open Core Frontend SourceInference GeneralHeap DataPatternValues DataPatternExecution DataEquality
open CompatiblePayload CompatiblePatternLeaves CompatiblePatternCertificates CompatiblePatternExecution
open SourceCoreCompatibleDataMatches
variable {compilation : Compilation} {registry : SourceCoreRawMetadata.Registry}
  {ambient : AmbientDefinitions compilation.checked.catalog.definitions}
  {functions : FunctionModel compilation.checked.catalog ambient} {mapping : LocationMap} {world : StoreTyping}

/- A numeric occurrence names its actual leaf in the same compiler tree.
Tuple and constructor children retain the original ordered forest. -/
mutual
  inductive Tree.NumericAt {source : TypedSource} {site : StatementId} {span : Syntax.SourceSpan}
      {scope : Scope} : {type : TypeSystem.Ty} → {instructions : List MatchPatternInstruction} →
      {pattern : Pattern} → {rest : List MatchPatternInstruction} →
      Tree compilation source site span scope type instructions pattern rest → IntegerLiteralResolution → Prop where
    | literal {type native literal resolution matcher rest} {projection : projected compilation source type = .ok native}
        {validated : literalMatcher compilation site span type literal resolution = .ok matcher} :
        Tree.NumericAt (Tree.literal (rest := rest) projection validated) resolution
    | tuple {expected type count types instructions rest children coreTypes resolution}
        {projection : projected compilation source expected = .ok type}
        {unpacked : unpackTypes count expected = some types}
        {tree : Forest compilation source site span scope types instructions children rest}
        {projectedChildren : types.mapM (projected compilation source) = .ok coreTypes}
        (child : Forest.NumericAt tree resolution) :
        Tree.NumericAt (Tree.tuple projection unpacked tree projectedChildren) resolution
    | constructor {expected type instantiation arity constructor definition metadata instructions rest children coreTypes resolution}
        {projection : projected compilation source expected = .ok type}
        {result : instantiation.resultType = expected} {count : arity = instantiation.payloadTypes.length}
        {resolved : compilation.checked.resolveConstructor instantiation = .ok constructor}
        {coreType : type = .namedData constructor.owner}
        {raw : compilation.values.registry.id? (.constructor instantiation) = some metadata}
        {tree : Forest compilation source site span scope instantiation.payloadTypes instructions children rest}
        {projectedChildren : instantiation.payloadTypes.mapM (projected compilation source) = .ok coreTypes}
        {registered : compilation.checked.catalog.definitions[constructor.owner.index]? = some definition}
        (child : Forest.NumericAt tree resolution) :
        Tree.NumericAt (Tree.constructor projection result count resolved coreType raw tree projectedChildren registered) resolution
  inductive Forest.NumericAt {source : TypedSource} {site : StatementId} {span : Syntax.SourceSpan}
      {scope : Scope} : {types : List TypeSystem.Ty} → {instructions : List MatchPatternInstruction} →
      {patterns : List Pattern} → {rest : List MatchPatternInstruction} →
      Forest compilation source site span scope types instructions patterns rest → IntegerLiteralResolution → Prop where
    | head {type types instructions afterHead rest head tail resolution}
        {first : Tree compilation source site span scope type instructions head afterHead}
        {remaining : Forest compilation source site span scope types afterHead tail rest}
        (child : Tree.NumericAt first resolution) : Forest.NumericAt (Forest.cons first remaining) resolution
    | tail {type types instructions afterHead rest head tail resolution}
        {first : Tree compilation source site span scope type instructions head afterHead}
        {remaining : Forest compilation source site span scope types afterHead tail rest}
        (child : Forest.NumericAt remaining resolution) : Forest.NumericAt (Forest.cons first remaining) resolution
end

def Tree.LiteralSites (literals : IntegerLiteralResolution → Prop)
    {source site span scope type instructions pattern rest}
    (tree : Tree compilation source site span scope type instructions pattern rest) : Prop :=
  ∀ resolution, Tree.NumericAt tree resolution → literals resolution

def Forest.LiteralSites (literals : IntegerLiteralResolution → Prop)
    {source site span scope types instructions patterns rest}
    (tree : Forest compilation source site span scope types instructions patterns rest) : Prop :=
  ∀ resolution, Forest.NumericAt tree resolution → literals resolution

/-- Actual leaf acceptance supplies static evidence, without selecting another
compiler traversal or discarding any unused requirement row. -/
theorem Tree.literalSites {source site span scope type instructions pattern rest}
    (tree : Tree compilation source site span scope type instructions pattern rest)
    (literals : IntegerLiteralResolution → Prop)
    (leaf : ∀ expected literal resolution matcher,
      literalMatcher compilation site span expected literal resolution = .ok matcher → literals resolution) :
    Tree.LiteralSites literals tree := by
  intro resolution occurrence
  induction occurrence using Tree.NumericAt.rec
    (motive_2 := fun _ resolution _ => literals resolution) with
  | @literal type native literal resolution matcher rest projection validated => exact leaf _ _ _ _ validated
  | tuple _ ih | constructor _ ih | head _ ih | tail _ ih => exact ih

private theorem ordinary_requirement {context : Context} (valid : ContextValid compilation context)
    {site span expected literal resolution matcher}
    (accepted : literalMatcher compilation site span expected literal resolution = .ok matcher) :
    RequirementProves context resolution.requirement resolution.predicate := by
  have code := literalMatcher_sound compilation site span expected literal resolution matcher accepted
  cases code with
  | word target meaning retained | integer target meaning retained =>
    obtain ⟨row, member, identifier, predicate⟩ := retained
    have inContext : row ∈ context.solvedRequirements := by rw [valid.ledger]; exact member
    refine ⟨row, ⟨inContext, identifier⟩, ?_, valid.valid.entriesValid row inContext⟩
    simpa [IntegerLiteralResolution.predicate, target] using predicate

def TreeDecision (context : Context) (type : TypeSystem.Ty) (instructions : List MatchPatternInstruction)
    (pattern : Pattern) (rest : List MatchPatternInstruction) : Prop :=
  ∀ source value, ValueRep compilation.checked registry functions mapping world type source value pattern.type →
    (∃ bindings values, Dynamic.PatternInstructionMatches context source instructions bindings rest ∧
      BindingsRep compilation.checked registry functions mapping world pattern.bindings bindings values ∧
      CompatiblePatternExecution.MatcherRuns pattern value values) ∨ CompatiblePatternExecution.MatcherFails pattern value

def ForestDecision (context : Context) (types : List TypeSystem.Ty) (instructions : List MatchPatternInstruction)
    (patterns : List Pattern) (rest : List MatchPatternInstruction) : Prop :=
  ∀ sources values coreTypes, ValuesRep compilation.checked registry functions mapping world types sources values coreTypes →
    (∃ bindings boundValues, Dynamic.PatternInstructionsMatch context sources instructions bindings rest ∧
      BindingsRep compilation.checked registry functions mapping world (patterns.flatMap (·.bindings)) bindings boundValues ∧
      CompatiblePatternExecution.ChildrenRun patterns values boundValues) ∨ CompatiblePatternExecution.ChildrenFail patterns values

theorem Tree.decides_with_literals {context : Context} {source : TypedSource} {site : StatementId} {span : Syntax.SourceSpan}
    {scope : Scope} {type : TypeSystem.Ty} {instructions rest : List MatchPatternInstruction} {pattern : Pattern}
    (literals : IntegerLiteralResolution → Prop)
    (requirements : ∀ resolution, literals resolution → RequirementProves context resolution.requirement resolution.predicate)
    (extended : SourceCoreRawMetadata.Extends compilation.values.registry registry)
    (tree : Tree compilation source site span scope type instructions pattern rest)
    (sites : Tree.LiteralSites literals tree) :
    TreeDecision (compilation := compilation) (registry := registry) (functions := functions)
      (mapping := mapping) (world := world) context type instructions pattern rest := by
  revert sites
  induction tree using Tree.rec
    (motive_2 := fun types instructions patterns rest forest =>
      Forest.LiteralSites literals forest → ForestDecision (compilation := compilation) (registry := registry) (functions := functions)
        (mapping := mapping) (world := world) context types instructions patterns rest) with
  | wildcard projection =>
    intro sites source value represented
    exact .inl ⟨[], [], .wildcard, .nil, fun _ store _ selected => .apply .lambda (selected.evaluates store) (.inRight .unit)⟩
  | binder projection sourceType binderValid =>
    intro sites source value represented
    exact .inl ⟨[(_, source)], [value], .binder, .cons (sourceType.symm ▸ represented) .nil,
      fun _ store _ selected => .apply .lambda (selected.evaluates store) (.inRight (.var rfl))⟩
  | @literal expected coreType literal resolution matcher rest projection validated =>
    intro sites sourceValue value represented
    have code := literalMatcher_sound compilation _ _ _ _ _ _ validated
    cases code with
    | word target meaning retained =>
      have typeEq : _ = Ty.word := Except.ok.inj projection.symm
      subst typeEq
      obtain ⟨actual, rfl, rfl⟩ := CompatibleExpressionPrimitives.word_fields represented
      by_cases same : actual = Word.ofNatModulo resolution.rawValue
      · subst actual
        exact .inl ⟨[], [], .integerLiteral (LiteralCode.constructs_word_with_requirement target meaning (requirements resolution (sites resolution (.literal (projection := projection) (validated := validated))))), .nil,
          fun _ store _ selected => .apply .lambda (selected.evaluates store)
            (.ifTrue (.binary (.var rfl) .word (by simp [BinaryOp.apply])) (.inRight .unit))⟩
      · exact .inr (fun _ store _ selected => .apply .lambda (selected.evaluates store)
          (.ifFalse (.binary (.var rfl) .word (by simp [BinaryOp.apply, same])) (.inLeft .unit)))
    | integer target meaning retained =>
      have typeEq : _ = Ty.integer := Except.ok.inj projection.symm
      subst typeEq
      obtain ⟨actual, rfl, rfl⟩ := CompatibleExpressionPrimitives.integer_fields represented
      by_cases same : actual = Int.ofNat resolution.rawValue
      · subst actual
        exact .inl ⟨[], [], .integerLiteral (LiteralCode.constructs_integer_with_requirement target meaning (requirements resolution (sites resolution (.literal (projection := projection) (validated := validated))))), .nil,
          fun _ store _ selected => .apply .lambda (selected.evaluates store)
            (.ifTrue (.binary (.var rfl) .integer (by simp [BinaryOp.apply])) (.inRight .unit))⟩
      · exact .inr (fun _ store _ selected => .apply .lambda (selected.evaluates store)
          (.ifFalse (.binary (.var rfl) .integer (by
            simp only [BinaryOp.apply, Option.some.injEq, Value.bool.injEq, beq_eq_false_iff_ne]
            exact same)) (.inLeft .unit)))
  | @tuple expected coreType count types instructions rest children coreTypes projection unpacked childrenTree projectedChildren ih =>
    intro sites sourceValue value represented
    obtain ⟨sources, values, actualTypes, valueReps, packing, valueEq, typeEq⟩ := CompatiblePatternValues.unpack unpacked represented
    subst value
    have nativeTypes : actualTypes = coreTypes := Except.ok.inj (valueReps.projection.symm.trans (projectedList_catalog projectedChildren))
    subst actualTypes
    have lengths := CompatiblePayload.ValuesRep.length valueReps
    have length := lengths.2.2.symm.trans lengths.2.1
    cases ih (fun resolution occurrence => sites resolution (.tuple (projection := projection) (unpacked := unpacked) (projectedChildren := projectedChildren) occurrence)) _ _ _ valueReps with
    | inl success =>
      obtain ⟨bindings, boundValues, matched, bindingRep, childrenRun⟩ := success
      refine .inl ⟨bindings, boundValues, .tuple packing (lengths.1.symm.trans (unpackTypes_length unpacked)) matched, bindingRep, ?_⟩
      intro environment store expression selected
      apply Evaluates.apply .lambda (selected.evaluates store)
      have paths := projectionList_selects (environment := packValues values :: environment) (expression := .var 0) (.var rfl) length
      simpa [tuplePattern, Pattern.bindingTypes, childValues] using childrenRun _ store _ [] [] _ paths .nil
    | inr failed =>
      refine .inr ?_
      intro environment store expression selected
      apply Evaluates.apply .lambda (selected.evaluates store)
      have paths := projectionList_selects (environment := packValues values :: environment) (expression := .var 0) (.var rfl) length
      simpa [tuplePattern, Pattern.bindingTypes, childValues] using failed _ store _ [] [] _ paths .nil
  | @constructor expected coreType instantiation count constructor definition metadata instructions rest children coreTypes
      projection result arity resolved sameType raw childrenTree projectedChildren registered ih =>
    intro sites sourceValue value represented
    obtain ⟨signature, declaration, arguments, _, _, _, _, _, nominalResult⟩ :=
      CompatibleConstructorMetadata.facts (CompatibleConstructorMetadata.resolved_facts resolved).1
    have nominal : SourceCoreDataCatalog.nominalParts (SourceCoreRawMetadata.runtimeType expected) =
        some (signature.id, arguments.map SourceCoreRawMetadata.runtimeType) := by
      rw [← result, nominalResult, CompatibleConstructorMetadata.runtimeType_nominal, DataPatternAuthenticity.nominalParts_nominal]
    obtain ⟨actual, sources, tag, actualId, values, actualTypes, rfl, valueEq, typeEq, fields⟩ := CompatiblePatternValues.nominal_fields represented nominal
    subst value
    have ownerEq : tag.owner = constructor.owner := Ty.namedData.inj (typeEq.symm.trans sameType)
    have lookup : definition.constructorPayloadTypes[tag.index]? =
        some (.product .word (SourceCoreCompatibleCatalog.packTypes actualTypes)) := by
      simpa [DataEnvironment.lookupConstructorPayloadType?, DataEnvironment.lookupDataType?, ownerEq, registered] using fields.registered
    by_cases sameTag : tag = constructor
    · subst tag
      have branchLookup : (definition.constructorPayloadTypes.zipIdx.map fun (_, index) =>
          if index = constructor.index then rawConstructor metadata (bundleType ((children.flatMap (fun (p : Pattern) => p.bindings)).map Prod.snd))
            (matchChildren (bundleType ((children.flatMap (fun (p : Pattern) => p.bindings)).map Prod.snd)) children
              (coreTypes.zipIdx.map fun (item : Ty × Nat) => SourceCoreDataExpressions.projectPacked item.2 coreTypes (.second (.var 0))) [])
          else .inLeft (bundleType ((children.flatMap (fun (p : Pattern) => p.bindings)).map Prod.snd)) .unit)[constructor.index]? =
          some (rawConstructor metadata (bundleType ((children.flatMap (fun (p : Pattern) => p.bindings)).map Prod.snd))
            (matchChildren (bundleType ((children.flatMap (fun (p : Pattern) => p.bindings)).map Prod.snd)) children
              (coreTypes.zipIdx.map fun (item : Ty × Nat) => SourceCoreDataExpressions.projectPacked item.2 coreTypes (.second (.var 0))) [])) := by
        simp [List.getElem?_map, List.getElem?_zipIdx, lookup]
      by_cases sameId : actualId = metadata
      · have expectedRep : MetadataRep registry (.constructor instantiation) metadata :=
          ⟨extended.lookup (SourceCoreRawMetadata.Registry.id?_reconstruct raw)⟩
        have sourceEq := SourceCoreRawMetadata.Metadata.constructor.inj ((fields.metadataRep.ids_equal_iff expectedRep).mp sameId)
        rw [sourceEq] at fields
        subst actualId
        have nativeTypes : actualTypes = coreTypes := Except.ok.inj (fields.payloads.projection.symm.trans (projectedList_catalog projectedChildren))
        subst actualTypes
        have lengths := CompatiblePayload.ValuesRep.length fields.payloads
        have length := lengths.2.2.symm.trans lengths.2.1
        cases ih (fun resolution occurrence => sites resolution (.constructor (projection := projection) (result := result) (count := arity) (resolved := resolved) (coreType := sameType) (raw := raw) (projectedChildren := projectedChildren) (registered := registered) occurrence)) _ _ _ fields.payloads with
        | inl success =>
          obtain ⟨bindings, boundValues, matched, bindingRep, childrenRun⟩ := success
          refine .inl ⟨bindings, boundValues,
            .constructor ⟨congrArg (·.constructor) sourceEq, congrArg (·.payloadTypes) sourceEq, congrArg (·.resultType) sourceEq⟩
              (lengths.1.symm.trans arity.symm) matched, bindingRep, ?_⟩
          intro environment store expression selected
          apply Evaluates.apply .lambda (selected.evaluates store)
          apply Evaluates.matchData (.var rfl) rfl branchLookup
          apply rawConstructor_matches
          have paths := projectionList_selects
            (environment := .pair (.word metadata) (packValues values) :: .constructed constructor (.pair (.word metadata) (packValues values)) :: environment)
            (expression := .second (.var 0)) (Selects.second (.var rfl)) length
          simpa [constructorPattern, Pattern.bindingTypes] using childrenRun _ store _ [] [] _ paths .nil
        | inr failed =>
          refine .inr ?_
          intro environment store expression selected
          apply Evaluates.apply .lambda (selected.evaluates store)
          apply Evaluates.matchData (.var rfl) rfl branchLookup
          apply rawConstructor_matches
          have paths := projectionList_selects
            (environment := .pair (.word metadata) (packValues values) :: .constructed constructor (.pair (.word metadata) (packValues values)) :: environment)
            (expression := .second (.var 0)) (Selects.second (.var rfl)) length
          simpa [constructorPattern, Pattern.bindingTypes] using failed _ store _ [] [] _ paths .nil
      · refine .inr ?_
        intro environment store expression selected
        apply Evaluates.apply .lambda (selected.evaluates store)
        apply Evaluates.matchData (.var rfl) rfl branchLookup
        exact rawConstructor_misses _ store actualId metadata sameId _ _ _
    · have indexDifferent : tag.index ≠ constructor.index := by
        intro indices
        apply sameTag
        cases tag; cases constructor; cases ownerEq; cases indices; rfl
      have branchLookup : (definition.constructorPayloadTypes.zipIdx.map fun (_, index) =>
          if index = constructor.index then rawConstructor metadata (bundleType ((children.flatMap (fun (p : Pattern) => p.bindings)).map Prod.snd))
            (matchChildren (bundleType ((children.flatMap (fun (p : Pattern) => p.bindings)).map Prod.snd)) children
              (coreTypes.zipIdx.map fun (item : Ty × Nat) => SourceCoreDataExpressions.projectPacked item.2 coreTypes (.second (.var 0))) [])
          else .inLeft (bundleType ((children.flatMap (fun (p : Pattern) => p.bindings)).map Prod.snd)) .unit)[tag.index]? =
          some (.inLeft (bundleType ((children.flatMap (fun (p : Pattern) => p.bindings)).map Prod.snd)) .unit) := by
        simp [List.getElem?_map, List.getElem?_zipIdx, lookup, indexDifferent]
      exact .inr (fun _ store _ selected => .apply .lambda (selected.evaluates store)
        (.matchData (.var rfl) ownerEq branchLookup (.inLeft .unit)))
  | nil sites =>
    intro sources values coreTypes represented
    cases represented
    exact .inl ⟨[], [], .nil, .nil, CompatiblePatternExecution.ChildrenRun.nil⟩
  | @cons type types instructions afterHead rest head tail headTree tailTree headIH tailIH sites =>
    intro sources values coreTypes represented
    cases represented with
    | cons valueRep valuesRep =>
      have sameType := Except.ok.inj (valueRep.projection.symm.trans (CompatiblePatternSuccess.Tree.projected headTree))
      subst sameType
      cases headIH (fun resolution occurrence => sites resolution (.head (remaining := tailTree) occurrence)) _ _ valueRep with
      | inr failed => exact .inr (CompatiblePatternExecution.ChildrenFail.head failed)
      | inl success =>
        obtain ⟨headBindings, headValues, headMatch, headBindingRep, headRun⟩ := success
        have length : head.bindingTypes.length = headValues.length := by simpa [Pattern.bindingTypes] using bindings_length headBindingRep
        cases tailIH (fun resolution occurrence => sites resolution (.tail (first := headTree) occurrence)) _ _ _ valuesRep with
        | inr failed => exact .inr (CompatiblePatternExecution.ChildrenFail.tail length headRun failed)
        | inl success =>
          obtain ⟨tailBindings, tailValues, tailMatch, tailBindingRep, tailRun⟩ := success
          exact .inl ⟨headBindings ++ tailBindings, headValues ++ tailValues, .cons headMatch tailMatch,
            bindings_append headBindingRep tailBindingRep, CompatiblePatternExecution.ChildrenRun.cons length headRun tailRun⟩

theorem Tree.decides {context : Context} {source : TypedSource} {site : StatementId} {span : Syntax.SourceSpan}
    {scope : Scope} {type : TypeSystem.Ty} {instructions rest : List MatchPatternInstruction} {pattern : Pattern}
    (valid : ContextValid compilation context) (extended : SourceCoreRawMetadata.Extends compilation.values.registry registry)
    (tree : Tree compilation source site span scope type instructions pattern rest) :
    TreeDecision (compilation := compilation) (registry := registry) (functions := functions)
      (mapping := mapping) (world := world) context type instructions pattern rest := by
  exact Tree.decides_with_literals (fun resolution => RequirementProves context resolution.requirement resolution.predicate)
    (fun _ proof => proof) extended tree (Tree.literalSites tree _ (fun _ _ _ _ accepted => ordinary_requirement valid accepted))

/-- Strip only the original application; the operand is the retained pure
projection. No matcher or source execution is replayed. -/
private theorem apply_lambda_inv {environment : Environment} {store after : Store}
    {expression body : Expr} {input output : Ty} {value result : Value}
    (selected : Selects environment expression value)
    (completed : Evaluates environment store (.apply (.lambda input output body) expression) result after) :
    Evaluates (value :: environment) store body result after := by
  cases completed with
  | apply function argument body =>
    cases function
    obtain ⟨rfl, rfl⟩ := evaluation_deterministic argument (selected.evaluates store)
    exact body

private theorem match_data_inv {environment : Environment} {store after : Store}
    {constructor : ConstructorId} {payload outcome : Value} {owner : DataTypeId} {output : Ty} {branches : List Expr}
    (completed : Evaluates (.constructed constructor payload :: environment) store
      (.matchData owner output (.var 0) branches) outcome after) :
    ∃ branch, branches[constructor.index]? = some branch ∧
      Evaluates (payload :: .constructed constructor payload :: environment) store branch outcome after := by
  cases completed with
  | matchData scrutinee owner found selected =>
    cases scrutinee with
    | var observed =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at observed
      cases observed
      exact ⟨_, found, selected⟩

private theorem raw_guard_inv {environment : Environment} {store after : Store}
    {actual expected : Word} {payload outcome : Value} {output : Ty} {child : Expr}
    (completed : Evaluates (.pair (.word actual) payload :: environment) store
      (rawConstructor expected output child) outcome after) :
    (actual = expected ∧ Evaluates (.pair (.word actual) payload :: environment) store child outcome after) ∨
      (actual ≠ expected ∧ outcome = .inLeft output .unit ∧ after = store) := by
  cases completed with
  | ifTrue condition branch =>
    cases condition with
    | binary left right applied =>
      cases left with
      | first operand =>
        cases operand with
        | var found =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at found
          cases found
          cases right
          exact .inl ⟨by simpa [BinaryOp.apply] using applied, branch⟩
  | ifFalse condition branch =>
    cases condition with
    | binary left right applied =>
      cases left with
      | first operand =>
        cases operand with
        | var found =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at found
          cases found
          cases right
          cases branch with
          | inLeft unit =>
            cases unit
            exact .inr ⟨by simpa [BinaryOp.apply] using applied, rfl, rfl⟩

private theorem word_matcher_inv {environment : Environment} {store finalStore : Store}
    {actual expected : Word} {outcome : Value}
    (completed : Evaluates (.word actual :: environment) store
      (.ifE (.binary .wordEq (.var 0) (.word expected)) (.inRight .unit .unit) (.inLeft .unit .unit))
      outcome finalStore) :
    ((actual = expected ∧ outcome = .inRight .unit .unit) ∨
      (actual ≠ expected ∧ outcome = .inLeft .unit .unit)) ∧ finalStore = store := by
  cases completed with
  | ifTrue condition branch =>
    cases condition with
    | binary left right applied =>
      cases left with
      | var found =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at found
        cases found
        cases right
        cases branch with
        | inRight unit =>
          cases unit
          exact ⟨.inl ⟨by simpa [BinaryOp.apply] using applied, rfl⟩, rfl⟩
  | ifFalse condition branch =>
    cases condition with
    | binary left right applied =>
      cases left with
      | var found =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at found
        cases found
        cases right
        cases branch with
        | inLeft unit =>
          cases unit
          exact ⟨.inr ⟨by simpa [BinaryOp.apply] using applied, rfl⟩, rfl⟩

private theorem integer_matcher_inv {environment : Environment} {store finalStore : Store}
    {actual expected : Int} {outcome : Value}
    (completed : Evaluates (.integer actual :: environment) store
      (.ifE (.binary .integerEq (.var 0) (.integer expected)) (.inRight .unit .unit) (.inLeft .unit .unit))
      outcome finalStore) :
    ((actual = expected ∧ outcome = .inRight .unit .unit) ∨
      (actual ≠ expected ∧ outcome = .inLeft .unit .unit)) ∧ finalStore = store := by
  cases completed with
  | ifTrue condition branch =>
    cases condition with
    | binary left right applied =>
      cases left with
      | var found =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at found
        cases found
        cases right
        cases branch with
        | inRight unit =>
          cases unit
          exact ⟨.inl ⟨by simpa [BinaryOp.apply] using applied, rfl⟩, rfl⟩
  | ifFalse condition branch =>
    cases condition with
    | binary left right applied =>
      cases left with
      | var found =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at found
        cases found
        cases right
        cases branch with
        | inLeft unit =>
          cases unit
          exact ⟨.inr ⟨by simpa [BinaryOp.apply] using applied, rfl⟩, rfl⟩

private theorem bundle_inv {environment : Environment} {store after : Store}
    {expressions : List Expr} {values : List Value} {result : Value}
    (selected : ListRel (Selects environment) expressions values)
    (completed : Evaluates environment store (bundle expressions) result after) :
    result = packValues values ∧ after = store := by
  induction selected generalizing store after result with
  | nil => cases completed; exact ⟨rfl, rfl⟩
  | cons head tail ih =>
    cases tail with
    | nil => exact evaluation_deterministic completed (head.evaluates store)
    | cons second remaining =>
      cases completed with
      | pair left right =>
        obtain ⟨rfl, rfl⟩ := evaluation_deterministic left (head.evaluates store)
        obtain ⟨rfl, rfl⟩ := ih right
        exact ⟨rfl, rfl⟩

/-- Direct observations of the original native matcher. A failure tag is kept
as such; source non-match is established only by excluding a hypothetical
successful source match, after this inversion has completed. -/
def TreeReflection (context : Context) (type : TypeSystem.Ty) (instructions : List MatchPatternInstruction)
    (pattern : Pattern) (rest : List MatchPatternInstruction) : Prop :=
  ∀ source value, ValueRep compilation.checked registry functions mapping world type source value pattern.type →
    ∀ environment store expression, Selects environment expression value → ∀ outcome after,
      Evaluates environment store (.apply pattern.matcher expression) outcome after →
      ((∃ bindings values, Dynamic.PatternInstructionMatches context source instructions bindings rest ∧
        BindingsRep compilation.checked registry functions mapping world pattern.bindings bindings values ∧
        outcome = .inRight .unit (packValues values)) ∨ outcome = .inLeft (bundleType pattern.bindingTypes) .unit) ∧
      after = store

def ForestReflection (context : Context) (types : List TypeSystem.Ty) (instructions : List MatchPatternInstruction)
    (patterns : List Pattern) (rest : List MatchPatternInstruction) : Prop :=
  ∀ sources values coreTypes, ValuesRep compilation.checked registry functions mapping world types sources values coreTypes →
    ∀ environment store expressions accumulated accumulatedValues outputType,
      ListRel (Selects environment) expressions values → ListRel (Selects environment) accumulated accumulatedValues →
      ∀ outcome after, Evaluates environment store (matchChildren outputType patterns expressions accumulated) outcome after →
      ((∃ bindings boundValues, Dynamic.PatternInstructionsMatch context sources instructions bindings rest ∧
        BindingsRep compilation.checked registry functions mapping world (patterns.flatMap (·.bindings)) bindings boundValues ∧
        outcome = .inRight .unit (packValues (accumulatedValues ++ boundValues))) ∨ outcome = .inLeft outputType .unit) ∧
      after = store

theorem Tree.reflects_with_literals {context : Context} {source : TypedSource} {site : StatementId} {span : Syntax.SourceSpan}
    {scope : Scope} {type : TypeSystem.Ty} {instructions rest : List MatchPatternInstruction} {pattern : Pattern}
    (literals : IntegerLiteralResolution → Prop)
    (requirements : ∀ resolution, literals resolution → RequirementProves context resolution.requirement resolution.predicate)
    (extended : SourceCoreRawMetadata.Extends compilation.values.registry registry)
    (tree : Tree compilation source site span scope type instructions pattern rest)
    (sites : Tree.LiteralSites literals tree) :
    TreeReflection (compilation := compilation) (registry := registry) (functions := functions)
      (mapping := mapping) (world := world) context type instructions pattern rest := by
  revert sites
  induction tree using Tree.rec
    (motive_2 := fun types instructions patterns rest forest => Forest.LiteralSites literals forest →
      ForestReflection (compilation := compilation) (registry := registry) (functions := functions)
        (mapping := mapping) (world := world) context types instructions patterns rest) with
  | wildcard projection =>
    intro sites source value represented environment store expression selected outcome after completed
    have body := apply_lambda_inv selected completed
    cases body with
    | inRight unit =>
      cases unit
      exact ⟨.inl ⟨[], [], .wildcard, .nil, rfl⟩, rfl⟩
  | binder projection sourceType binderValid =>
    intro sites source value represented environment store expression selected outcome after completed
    have body := apply_lambda_inv selected completed
    cases body with
    | inRight valueRun =>
      cases valueRun with
      | var found =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at found
        cases found
        exact ⟨.inl ⟨[(_, source)], [value], .binder, .cons (sourceType.symm ▸ represented) .nil, rfl⟩, rfl⟩
  | @literal expected coreType literal resolution matcher rest projection validated =>
    intro sites sourceValue value represented environment store expression selected outcome after completed
    have requirement := requirements resolution (sites resolution (.literal (projection := projection) (validated := validated)))
    have code := literalMatcher_sound compilation _ _ _ _ _ _ validated
    cases code with
    | word target meaning retained =>
      have typeEq : _ = Ty.word := Except.ok.inj projection.symm
      subst typeEq
      obtain ⟨actual, rfl, rfl⟩ := CompatibleExpressionPrimitives.word_fields represented
      obtain ⟨observed, sameStore⟩ := word_matcher_inv (apply_lambda_inv selected completed)
      refine ⟨?_, sameStore⟩
      rcases observed with ⟨rfl, rfl⟩ | ⟨_, rfl⟩
      · exact .inl ⟨[], [], .integerLiteral (LiteralCode.constructs_word_with_requirement target meaning requirement), .nil, rfl⟩
      · exact .inr rfl
    | integer target meaning retained =>
      have typeEq : _ = Ty.integer := Except.ok.inj projection.symm
      subst typeEq
      obtain ⟨actual, rfl, rfl⟩ := CompatibleExpressionPrimitives.integer_fields represented
      obtain ⟨observed, sameStore⟩ := integer_matcher_inv (apply_lambda_inv selected completed)
      refine ⟨?_, sameStore⟩
      rcases observed with ⟨rfl, rfl⟩ | ⟨_, rfl⟩
      · exact .inl ⟨[], [], .integerLiteral (LiteralCode.constructs_integer_with_requirement target meaning requirement), .nil, rfl⟩
      · exact .inr rfl
  | @tuple expected coreType count types instructions rest children coreTypes projection unpacked childrenTree projectedChildren ih =>
    intro sites sourceValue value represented environment store expression selected outcome after completed
    obtain ⟨sources, values, actualTypes, valueReps, packing, valueEq, typeEq⟩ := CompatiblePatternValues.unpack unpacked represented
    subst value
    have nativeTypes : actualTypes = coreTypes := Except.ok.inj (valueReps.projection.symm.trans (projectedList_catalog projectedChildren))
    subst actualTypes
    have lengths := CompatiblePayload.ValuesRep.length valueReps
    have length := lengths.2.2.symm.trans lengths.2.1
    have paths := projectionList_selects (environment := packValues values :: environment) (expression := .var 0) (.var rfl) length
    have body := apply_lambda_inv selected completed
    obtain ⟨observed, sameStore⟩ := ih
      (fun resolution occurrence => sites resolution (.tuple (projection := projection) (unpacked := unpacked) (projectedChildren := projectedChildren) occurrence))
      _ _ _ valueReps _ store _ [] [] _ paths .nil outcome after body
    refine ⟨?_, sameStore⟩
    rcases observed with ⟨bindings, boundValues, matched, bindingRep, same⟩ | failed
    · exact .inl ⟨bindings, boundValues, .tuple packing (lengths.1.symm.trans (unpackTypes_length unpacked)) matched, bindingRep, same⟩
    · exact .inr failed
  | @constructor expected coreType instantiation count constructor definition metadata instructions rest children coreTypes
      projection result arity resolved sameType raw childrenTree projectedChildren registered ih =>
    intro sites sourceValue value represented environment store expression selected outcome after completed
    obtain ⟨signature, declaration, arguments, _, _, _, _, _, nominalResult⟩ :=
      CompatibleConstructorMetadata.facts (CompatibleConstructorMetadata.resolved_facts resolved).1
    have nominal : SourceCoreDataCatalog.nominalParts (SourceCoreRawMetadata.runtimeType expected) =
        some (signature.id, arguments.map SourceCoreRawMetadata.runtimeType) := by
      rw [← result, nominalResult, CompatibleConstructorMetadata.runtimeType_nominal, DataPatternAuthenticity.nominalParts_nominal]
    obtain ⟨actual, sources, tag, actualId, values, actualTypes, rfl, valueEq, typeEq, fields⟩ := CompatiblePatternValues.nominal_fields represented nominal
    subst value
    have ownerEq : tag.owner = constructor.owner := Ty.namedData.inj (typeEq.symm.trans sameType)
    have lookup : definition.constructorPayloadTypes[tag.index]? =
        some (.product .word (SourceCoreCompatibleCatalog.packTypes actualTypes)) := by
      simpa [DataEnvironment.lookupConstructorPayloadType?, DataEnvironment.lookupDataType?, ownerEq, registered] using fields.registered
    have body := apply_lambda_inv selected completed
    obtain ⟨branch, branchFound, branchEval⟩ := match_data_inv body
    by_cases sameTag : tag = constructor
    · subst tag
      have branchLookup : (definition.constructorPayloadTypes.zipIdx.map fun (_, index) =>
          if index = constructor.index then rawConstructor metadata (bundleType ((children.flatMap (fun (p : Pattern) => p.bindings)).map Prod.snd))
            (matchChildren (bundleType ((children.flatMap (fun (p : Pattern) => p.bindings)).map Prod.snd)) children
              (coreTypes.zipIdx.map fun (item : Ty × Nat) => SourceCoreDataExpressions.projectPacked item.2 coreTypes (.second (.var 0))) [])
          else .inLeft (bundleType ((children.flatMap (fun (p : Pattern) => p.bindings)).map Prod.snd)) .unit)[constructor.index]? =
          some (rawConstructor metadata (bundleType ((children.flatMap (fun (p : Pattern) => p.bindings)).map Prod.snd))
            (matchChildren (bundleType ((children.flatMap (fun (p : Pattern) => p.bindings)).map Prod.snd)) children
              (coreTypes.zipIdx.map fun (item : Ty × Nat) => SourceCoreDataExpressions.projectPacked item.2 coreTypes (.second (.var 0))) [])) := by
        simp [List.getElem?_map, List.getElem?_zipIdx, lookup]
      have sameBranch := Option.some.inj (branchFound.symm.trans branchLookup)
      subst branch
      rcases raw_guard_inv branchEval with ⟨sameId, childEval⟩ | ⟨differentId, failed, sameStore⟩
      · have expectedRep : MetadataRep registry (.constructor instantiation) metadata :=
          ⟨extended.lookup (SourceCoreRawMetadata.Registry.id?_reconstruct raw)⟩
        have sourceEq := SourceCoreRawMetadata.Metadata.constructor.inj ((fields.metadataRep.ids_equal_iff expectedRep).mp sameId)
        rw [sourceEq] at fields
        subst actualId
        have nativeTypes : actualTypes = coreTypes := Except.ok.inj (fields.payloads.projection.symm.trans (projectedList_catalog projectedChildren))
        subst actualTypes
        have lengths := CompatiblePayload.ValuesRep.length fields.payloads
        have length := lengths.2.2.symm.trans lengths.2.1
        have paths := projectionList_selects
          (environment := .pair (.word metadata) (packValues values) :: .constructed constructor (.pair (.word metadata) (packValues values)) :: environment)
          (expression := .second (.var 0)) (Selects.second (.var rfl)) length
        obtain ⟨observed, sameStore⟩ := ih
          (fun resolution occurrence => sites resolution (.constructor (projection := projection) (result := result) (count := arity) (resolved := resolved) (coreType := sameType) (raw := raw) (projectedChildren := projectedChildren) (registered := registered) occurrence))
          _ _ _ fields.payloads _ store _ [] [] _ paths .nil outcome after childEval
        refine ⟨?_, sameStore⟩
        rcases observed with ⟨bindings, boundValues, matched, bindingRep, same⟩ | failed
        · exact .inl ⟨bindings, boundValues,
            .constructor ⟨congrArg (·.constructor) sourceEq, congrArg (·.payloadTypes) sourceEq, congrArg (·.resultType) sourceEq⟩
              (lengths.1.symm.trans arity.symm) matched, bindingRep, same⟩
        · exact .inr failed
      · exact ⟨.inr failed, sameStore⟩
    · have indexDifferent : tag.index ≠ constructor.index := by
        intro indices
        apply sameTag
        cases tag; cases constructor; cases ownerEq; cases indices; rfl
      have branchLookup : (definition.constructorPayloadTypes.zipIdx.map fun (_, index) =>
          if index = constructor.index then rawConstructor metadata (bundleType ((children.flatMap (fun (p : Pattern) => p.bindings)).map Prod.snd))
            (matchChildren (bundleType ((children.flatMap (fun (p : Pattern) => p.bindings)).map Prod.snd)) children
              (coreTypes.zipIdx.map fun (item : Ty × Nat) => SourceCoreDataExpressions.projectPacked item.2 coreTypes (.second (.var 0))) [])
          else .inLeft (bundleType ((children.flatMap (fun (p : Pattern) => p.bindings)).map Prod.snd)) .unit)[tag.index]? =
          some (.inLeft (bundleType ((children.flatMap (fun (p : Pattern) => p.bindings)).map Prod.snd)) .unit) := by
        simp [List.getElem?_map, List.getElem?_zipIdx, lookup, indexDifferent]
      have sameBranch := Option.some.inj (branchFound.symm.trans branchLookup)
      subst branch
      cases branchEval with
      | inLeft unit =>
        cases unit
        exact ⟨.inr rfl, rfl⟩
  | nil sites =>
    intro sources values coreTypes represented environment store expressions accumulated accumulatedValues outputType selected previous outcome after completed
    cases represented
    cases selected
    cases completed with
    | inRight bundle =>
      obtain ⟨rfl, rfl⟩ := bundle_inv previous bundle
      exact ⟨.inl ⟨[], [], .nil, .nil, by simp⟩, rfl⟩
  | @cons type types instructions afterHead rest head tail headTree tailTree headIH tailIH sites =>
    intro sources values coreTypes represented environment store expressions accumulated accumulatedValues outputType selected previous outcome after completed
    cases represented with
    | cons valueRep valuesRep =>
      have sameType := Except.ok.inj (valueRep.projection.symm.trans (CompatiblePatternSuccess.Tree.projected headTree))
      subst sameType
      cases selected with
      | cons inputSelected restSelected =>
        cases completed with
        | caseLeft first branch =>
          obtain ⟨observed, rfl⟩ := headIH
            (fun resolution occurrence => sites resolution (.head (remaining := tailTree) occurrence))
            _ _ valueRep environment store _ inputSelected _ _ first
          rcases observed with ⟨bindings, boundValues, matched, bindingRep, impossible⟩ | failed
          · cases impossible
          · cases failed
            cases branch with
            | inLeft unit =>
              cases unit
              exact ⟨.inr rfl, rfl⟩
        | caseRight first branch =>
          obtain ⟨observed, rfl⟩ := headIH
            (fun resolution occurrence => sites resolution (.head (remaining := tailTree) occurrence))
            _ _ valueRep environment store _ inputSelected _ _ first
          rcases observed with ⟨headBindings, headValues, headMatch, headBindingRep, same⟩ | impossible
          · cases same
            have length : head.bindingTypes.length = headValues.length := by
              simpa [Pattern.bindingTypes] using bindings_length headBindingRep
            have projections := projectionList_selects (environment := packValues headValues :: environment)
              (expression := .var 0) (types := head.bindingTypes) (values := headValues) (.var rfl) length
            obtain ⟨tailObserved, sameStore⟩ := tailIH
              (fun resolution occurrence => sites resolution (.tail (first := headTree) occurrence))
              _ _ _ valuesRep (packValues headValues :: environment) _ _ _ _ outputType
              (selects_weaken_list restSelected _) (ListRel.append (selects_weaken_list previous _) projections)
              outcome after branch
            refine ⟨?_, sameStore⟩
            rcases tailObserved with ⟨tailBindings, tailValues, tailMatch, tailBindingRep, same⟩ | failed
            · exact .inl ⟨headBindings ++ tailBindings, headValues ++ tailValues, .cons headMatch tailMatch,
                bindings_append headBindingRep tailBindingRep, by simpa [List.append_assoc] using same⟩
            · exact .inr failed
          · cases impossible

/-- The actual root instructions and the original full certificate are retained.
Support is indexed by the very tree carried here, including ordered children. -/
structure WithLiterals (literals : IntegerLiteralResolution → Prop) (compilation : Compilation)
    (source : TypedSource) (scope : Scope) (site : StatementId) (span : Syntax.SourceSpan)
    (expected : TypeSystem.Ty) (pattern : TypedMatchPattern) (compiled : Pattern) : Prop where
  original : CompatiblePatternCertificates.Certificate compilation source scope site span expected pattern compiled
  supported : ∃ instructions, rootInstructions compilation pattern.source pattern.resolution = .ok instructions ∧
    ∃ tree : Tree compilation source site span scope expected instructions compiled [], Tree.LiteralSites literals tree

theorem WithLiterals.of_certificate {source scope site span expected pattern compiled}
    (certificate : CompatiblePatternCertificates.Certificate compilation source scope site span expected pattern compiled)
    (literals : IntegerLiteralResolution → Prop)
    (leaf : ∀ expected literal resolution matcher,
      literalMatcher compilation site span expected literal resolution = .ok matcher → literals resolution) :
    WithLiterals literals compilation source scope site span expected pattern compiled := by
  obtain ⟨instructions, root, tree⟩ := certificate.tree
  exact ⟨certificate, instructions, root, tree, Tree.literalSites tree literals leaf⟩

section SupportedMeaning
variable {source : TypedSource} {scope : Scope} {site : StatementId} {span : Syntax.SourceSpan}
  {expected : TypeSystem.Ty} {pattern : TypedMatchPattern} {compiled : Pattern}
  {context : Context} {literals : IntegerLiteralResolution → Prop}
  (receipt : WithLiterals literals compilation source scope site span expected pattern compiled)
  (signatures : context.signatures = compilation.signatures)
  (requirements : ∀ resolution, literals resolution → RequirementProves context resolution.requirement resolution.predicate)
  (catalogValid : SignatureCatalogWellFormed compilation.checked.signatures)
  (extended : SourceCoreRawMetadata.Extends compilation.values.registry registry)

include receipt signatures requirements catalogValid extended in
theorem preserves_with_literals {sourceValue : Dynamic.Value} {value : Value}
    (represented : ValueRep compilation.checked registry functions mapping world expected sourceValue value compiled.type)
    (environment : Environment) (store : Store) :
    ∃ outcome, OutcomeRep compilation.checked registry functions mapping world context pattern compiled sourceValue outcome ∧
      Evaluates (value :: environment) store (.apply compiled.matcher (.var 0)) outcome store := by
  obtain ⟨instructions, root, tree, sites⟩ := receipt.supported
  obtain ⟨arity, instructionsEq, sourceRep⟩ := rootInstructions_sound compilation context signatures _ _ _ root
  cases Tree.decides_with_literals literals requirements extended tree sites sourceValue value represented with
  | inl success =>
    obtain ⟨bindings, values, matched, bindingRep, runs⟩ := success
    subst instructions
    exact ⟨.inRight .unit (packValues values), .matched (.intro sourceRep matched) bindingRep,
      runs (value :: environment) store (.var 0) (.var rfl)⟩
  | inr failed =>
    have evaluated := failed (value :: environment) store (.var 0) (.var rfl)
    refine ⟨.inLeft (bundleType compiled.bindingTypes) .unit, .noMatch (.intro sourceRep ?_), evaluated⟩
    subst instructions
    refine ⟨CompatiblePatternCertificates.Tree.skips tree, ?_⟩
    intro bindings matched
    obtain ⟨values, _, _, runs⟩ := CompatiblePatternSuccess.Tree.success catalogValid extended tree _ _ _ _ represented matched
    have impossible := (evaluation_deterministic evaluated (runs (value :: environment) store (.var 0) (.var rfl))).1
    cases impossible

include receipt signatures requirements catalogValid extended in
/-- The actual native derivation is inverted before constructing the source
outcome. Only a hypothetical contradictory source success uses success preservation. -/
theorem reflects_with_literals {sourceValue : Dynamic.Value} {value : Value}
    (represented : ValueRep compilation.checked registry functions mapping world expected sourceValue value compiled.type)
    {environment : Environment} {store after : Store} {outcome : Value}
    (completed : Evaluates (value :: environment) store (.apply compiled.matcher (.var 0)) outcome after) :
    OutcomeRep compilation.checked registry functions mapping world context pattern compiled sourceValue outcome ∧ after = store := by
  obtain ⟨instructions, root, tree, sites⟩ := receipt.supported
  obtain ⟨arity, instructionsEq, sourceRep⟩ := rootInstructions_sound compilation context signatures _ _ _ root
  obtain ⟨observed, sameStore⟩ := Tree.reflects_with_literals literals requirements extended tree sites
    sourceValue value represented (value :: environment) store (.var 0) (.var rfl) outcome after completed
  refine ⟨?_, sameStore⟩
  subst instructions
  rcases observed with ⟨bindings, values, matched, bindingRep, rfl⟩ | rfl
  · exact .matched (.intro sourceRep matched) bindingRep
  · refine .noMatch (.intro sourceRep ⟨CompatiblePatternCertificates.Tree.skips tree, ?_⟩)
    intro bindings matched
    obtain ⟨values, _, _, runs⟩ := CompatiblePatternSuccess.Tree.success catalogValid extended tree _ _ _ _ represented matched
    have impossible := (evaluation_deterministic completed (runs (value :: environment) store (.var 0) (.var rfl))).1
    cases impossible
end SupportedMeaning

/-- Actual compatible compilation decides a represented input independently
of Core execution. Failure excludes every source binding sequence by success
preservation and native determinism, including raw guard mismatches. -/
theorem compilePattern_preserves (compilation : Compilation) (compilationFuel : Nat)
    (source : TypedSource) (scope : Scope) (site : StatementId) (span : Syntax.SourceSpan)
    (expected : TypeSystem.Ty) (pattern : TypedMatchPattern) (compiled : CertifiedPattern compilation.definitions)
    (accepted : compilePattern compilation compilationFuel source scope site span expected pattern = .ok compiled)
    (context : Context) (valid : ContextValid compilation context)
    (catalogValid : SignatureCatalogWellFormed compilation.checked.signatures)
    {registry : SourceCoreRawMetadata.Registry} {ambient : AmbientDefinitions compilation.checked.catalog.definitions}
    {functions : FunctionModel compilation.checked.catalog ambient} {mapping : LocationMap} {world : StoreTyping}
    (extended : SourceCoreRawMetadata.Extends compilation.values.registry registry)
    {sourceValue : Dynamic.Value} {value : Value}
    (represented : ValueRep compilation.checked registry functions mapping world expected sourceValue value compiled.pattern.type)
    (environment : Environment) (store : Store) :
    ∃ outcome, OutcomeRep compilation.checked registry functions mapping world context pattern compiled.pattern sourceValue outcome ∧
      Evaluates (value :: environment) store (.apply compiled.pattern.matcher (.var 0)) outcome store := by
  have certificate := certificate_of_compilePattern compilation compilationFuel source scope site span expected pattern compiled accepted
  exact preserves_with_literals (WithLiterals.of_certificate certificate
    (fun resolution => RequirementProves context resolution.requirement resolution.predicate)
    (fun _ _ _ _ accepted => ordinary_requirement valid accepted)) valid.signatures
    (fun _ proof => proof) catalogValid extended represented environment store

/-- Any completed compatible matcher reconstructs an independent source match
or non-match and preserves the exact initial store. -/
theorem compilePattern_reflects (compilation : Compilation) (compilationFuel : Nat)
    (source : TypedSource) (scope : Scope) (site : StatementId) (span : Syntax.SourceSpan)
    (expected : TypeSystem.Ty) (pattern : TypedMatchPattern) (compiled : CertifiedPattern compilation.definitions)
    (accepted : compilePattern compilation compilationFuel source scope site span expected pattern = .ok compiled)
    (context : Context) (valid : ContextValid compilation context)
    (catalogValid : SignatureCatalogWellFormed compilation.checked.signatures)
    {registry : SourceCoreRawMetadata.Registry} {ambient : AmbientDefinitions compilation.checked.catalog.definitions}
    {functions : FunctionModel compilation.checked.catalog ambient} {mapping : LocationMap} {world : StoreTyping}
    (extended : SourceCoreRawMetadata.Extends compilation.values.registry registry)
    {sourceValue : Dynamic.Value} {value : Value}
    (represented : ValueRep compilation.checked registry functions mapping world expected sourceValue value compiled.pattern.type)
    {environment : Environment} {store after : Store} {outcome : Value}
    (completed : Evaluates (value :: environment) store (.apply compiled.pattern.matcher (.var 0)) outcome after) :
    OutcomeRep compilation.checked registry functions mapping world context pattern compiled.pattern sourceValue outcome ∧ after = store := by
  have certificate := certificate_of_compilePattern compilation compilationFuel source scope site span expected pattern compiled accepted
  exact reflects_with_literals (WithLiterals.of_certificate certificate
    (fun resolution => RequirementProves context resolution.requirement resolution.predicate)
    (fun _ _ _ _ accepted => ordinary_requirement valid accepted)) valid.signatures
    (fun _ proof => proof) catalogValid extended represented completed

/-- Enough machine fuel computes the independent outcome, and every completed
machine execution agrees with it. Compilation fuel is a separate parameter. -/
theorem compilePattern_run_preserves (compilation : Compilation) (compilationFuel : Nat)
    (source : TypedSource) (scope : Scope) (site : StatementId) (span : Syntax.SourceSpan)
    (expected : TypeSystem.Ty) (pattern : TypedMatchPattern) (compiled : CertifiedPattern compilation.definitions)
    (accepted : compilePattern compilation compilationFuel source scope site span expected pattern = .ok compiled)
    (context : Context) (valid : ContextValid compilation context)
    (catalogValid : SignatureCatalogWellFormed compilation.checked.signatures)
    {registry : SourceCoreRawMetadata.Registry} {ambient : AmbientDefinitions compilation.checked.catalog.definitions}
    {functions : FunctionModel compilation.checked.catalog ambient} {mapping : LocationMap} {world : StoreTyping}
    (extended : SourceCoreRawMetadata.Extends compilation.values.registry registry)
    {sourceValue : Dynamic.Value} {value : Value}
    (represented : ValueRep compilation.checked registry functions mapping world expected sourceValue value compiled.pattern.type)
    (environment : Environment) (store : Store) :
    ∃ outcome, OutcomeRep compilation.checked registry functions mapping world context pattern compiled.pattern sourceValue outcome ∧
      (∃ required, ∀ fuel, required ≤ fuel → runStateful fuel
        (.initial (.apply compiled.pattern.matcher (.var 0)) (value :: environment) store) = .done outcome store) ∧
      (∀ fuel actual after, runStateful fuel
        (.initial (.apply compiled.pattern.matcher (.var 0)) (value :: environment) store) = .done actual after →
        actual = outcome ∧ after = store) := by
  obtain ⟨outcome, meaning, evaluated⟩ := compilePattern_preserves compilation compilationFuel source scope site span expected
    pattern compiled accepted context valid catalogValid extended represented environment store
  exact ⟨outcome, meaning, evaluation_runStateful_complete_with_sufficient_fuel evaluated,
    fun _ _ _ ran => evaluation_deterministic (runStateful_evaluation_sound ran) evaluated⟩

/-- Every independent non-match preserves absence, with no candidate binding
bundle or allocation escaping the pure matcher. -/
theorem compilePattern_failure_preserves (compilation : Compilation) (compilationFuel : Nat)
    (source : TypedSource) (scope : Scope) (site : StatementId) (span : Syntax.SourceSpan)
    (expected : TypeSystem.Ty) (pattern : TypedMatchPattern) (compiled : CertifiedPattern compilation.definitions)
    (accepted : compilePattern compilation compilationFuel source scope site span expected pattern = .ok compiled)
    (context : Context) (valid : ContextValid compilation context)
    (catalogValid : SignatureCatalogWellFormed compilation.checked.signatures)
    {registry : SourceCoreRawMetadata.Registry} {ambient : AmbientDefinitions compilation.checked.catalog.definitions}
    {functions : FunctionModel compilation.checked.catalog ambient} {mapping : LocationMap} {world : StoreTyping}
    (extended : SourceCoreRawMetadata.Extends compilation.values.registry registry)
    {sourceValue : Dynamic.Value} {value : Value}
    (represented : ValueRep compilation.checked registry functions mapping world expected sourceValue value compiled.pattern.type)
    (failure : Dynamic.PatternDoesNotMatch context pattern sourceValue) (environment : Environment) (store : Store) :
    Evaluates (value :: environment) store (.apply compiled.pattern.matcher (.var 0))
      (.inLeft (bundleType compiled.pattern.bindingTypes) .unit) store := by
  obtain ⟨outcome, meaning, evaluated⟩ := compilePattern_preserves compilation compilationFuel source scope site span expected
    pattern compiled accepted context valid catalogValid extended represented environment store
  cases meaning with
  | matched matched bindings => exact False.elim (failure.excludes matched)
  | noMatch => exact evaluated
end Solcore.SourceSemantics.CoreLowering.CompatiblePatternDecision
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CompatibleMatchDecision
/-! Ordered arm selection from the actual match compiler's static certificate.
Every tested matcher has an independent source match/non-match and a finite,
store-preserving Core execution. The selected binder bundle is authenticated at
its retained source declaration types. Nested statement execution and binder
allocation are subsequent consumers of this decision certificate. -/

set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleMatchDecision
open Core Frontend Frontend.SourceInference
open SourceCoreCompatibleDataMatches CompatiblePatternCertificates DataPatternValues CompatiblePatternLeaves
open CompatiblePatternExecution CompatiblePatternSuccess CompatiblePayload CompatiblePatternDecision DataEquality
open CompatibleMatchCertificates GeneralHeap
variable {compilation : Compilation} {registry : SourceCoreRawMetadata.Registry}
  {ambient : AmbientDefinitions compilation.checked.catalog.definitions}
  {functions : FunctionModel compilation.checked.catalog ambient} {mapping : LocationMap} {world : StoreTyping}


/-- Literal support is indexed by the same ordered compiler arm receipt. -/
inductive Arms.LiteralSites (literals : IntegerLiteralResolution → Prop)
    {source site scope expected bodyCertificate} :
    {cases : List TypedMatchCase} → {arms : List (Pattern × Expr)} →
    Arms compilation source site scope expected bodyCertificate cases arms → Prop where
  | nil : Arms.LiteralSites literals .nil
  | cons {arm : TypedMatchCase} {rest : List TypedMatchCase} {pattern : Pattern} {body : Expr} {arms : List (Pattern × Expr)}
      {patternCertificate : CompatiblePatternCertificates.Certificate compilation source scope site arm.span expected arm.pattern pattern}
      {typed : HasType [] pattern.matcher pattern.functionType compilation.definitions}
      {bodyCertified : bodyCertificate (armScope scope pattern) arm.body body}
      {tail : Arms compilation source site scope expected bodyCertificate rest arms}
      (head : CompatiblePatternDecision.WithLiterals literals compilation source scope site arm.span expected arm.pattern pattern)
      (remaining : Arms.LiteralSites literals tail) :
      Arms.LiteralSites literals (.cons patternCertificate typed bodyCertified tail)

/-- Actual accepted pattern leaves supply support for each occurrence, including
repeated patterns and repeated requirement IDs. -/
theorem Arms.literalSites {source site scope expected bodyCertificate cases arms}
    (certificates : Arms compilation source site scope expected bodyCertificate cases arms)
    (literals : IntegerLiteralResolution → Prop)
    (leaf : ∀ span expected literal resolution matcher,
      literalMatcher compilation site span expected literal resolution = .ok matcher → literals resolution) :
    Arms.LiteralSites literals certificates := by
  induction certificates with
  | nil => exact .nil
  | cons pattern typed body tail ih =>
    exact .cons (patternCertificate := pattern) (typed := typed) (bodyCertified := body) (CompatiblePatternDecision.WithLiterals.of_certificate pattern literals
      (fun expected literal resolution matcher accepted => leaf _ expected literal resolution matcher accepted)) ih

inductive Certificate.LiteralSites (literals : IntegerLiteralResolution → Prop)
    {source scope id resolution resultType internalReason expressionCertificate bodyCertificate} :
    {code : Expr} → CompatibleMatchCertificates.Certificate compilation source scope id resolution resultType internalReason
      expressionCertificate bodyCertificate code → Prop where
  | matchWith {node statementType scrutineeNode type scrutinee arms fallback branches code}
      {read : SourceCoreCompatibleDataExpressions.readStatement compilation.checked source id = .ok (node, statementType)}
      {statementTypeValid : statementType = .unit ∨ statementType = resultType}
      {form : node.form = .matchWith resolution}
      {requirements : resolution.requirements = resolution.cases.flatMap (·.pattern.requirements)}
      {hiddenOwned : resolution.hiddenScrutinee.owner = source.owner}
      {hiddenFresh : scope.any (fun entry => decide (entry.1 = resolution.hiddenScrutinee)) = false}
      {scrutineeOwned : resolution.scrutinee.occurrence.owner = source.owner}
      {scrutineeFound : source.lookupExpression? resolution.scrutinee = some scrutineeNode}
      {projection : projected compilation source scrutineeNode.type = .ok type}
      {expression : expressionCertificate scope resolution.scrutinee scrutinee}
      {sameType : type = scrutinee.type}
      {armCertificates : Arms compilation source id ((resolution.hiddenScrutinee, type) :: scope)
        scrutineeNode.type bodyCertificate resolution.cases arms}
      {fallbackCertificate : Fallback bodyCertificate ((resolution.hiddenScrutinee, type) :: scope)
        resultType resolution.defaultBody fallback}
      {branchesCertified : Branches compilation source ((resolution.hiddenScrutinee, type) :: scope)
        (Core.LocalLoop.controlType resultType) fallback arms branches}
      {hiddenCompiled : SourceCoreSourceCells.letInitialized compilation.sourceCells source scope Core.Renaming.id
        (hiddenBinder source node resolution scrutineeNode) (Core.LocalLoop.controlType resultType) type scrutinee.expression
        (.caseE (.loadCell (.var 0))
          (Core.LanguageResult.failure (Core.LocalLoop.controlType resultType) (.word internalReason)) branches) = .ok code}
      (supported : Arms.LiteralSites literals armCertificates) :
      Certificate.LiteralSites literals (.matchWith read statementTypeValid form requirements hiddenOwned hiddenFresh
        scrutineeOwned scrutineeFound projection expression sameType armCertificates fallbackCertificate branchesCertified hiddenCompiled)

theorem Certificate.literalSites
    {source scope id resolution resultType internalReason expressionCertificate bodyCertificate code}
    (certificate : CompatibleMatchCertificates.Certificate compilation source scope id resolution resultType internalReason
      expressionCertificate bodyCertificate code)
    (literals : IntegerLiteralResolution → Prop)
    (leaf : ∀ span expected literal resolution matcher,
      literalMatcher compilation id span expected literal resolution = .ok matcher → literals resolution) :
    Certificate.LiteralSites literals certificate := by
  cases certificate with
  | matchWith read allowed form requirements hiddenOwned hiddenFresh scrutineeOwned scrutineeFound projection
      expression sameType arms fallback branches hiddenCompiled =>
    exact .matchWith (read := read) (statementTypeValid := allowed) (form := form) (requirements := requirements)
      (hiddenOwned := hiddenOwned) (hiddenFresh := hiddenFresh) (scrutineeOwned := scrutineeOwned)
      (scrutineeFound := scrutineeFound) (projection := projection) (expression := expression) (sameType := sameType)
      (fallbackCertificate := fallback) (branchesCertified := branches) (hiddenCompiled := hiddenCompiled)
      (Arms.literalSites arms literals leaf)

private theorem ordinary_requirement {context : SourceSemantics.Context}
    (valid : ContextValid compilation context) {site span expected literal resolution matcher}
    (accepted : literalMatcher compilation site span expected literal resolution = .ok matcher) :
    RequirementProves context resolution.requirement resolution.predicate := by
  have code := literalMatcher_sound compilation site span expected literal resolution matcher accepted
  cases code with
  | word target meaning retained | integer target meaning retained =>
    obtain ⟨row, member, identifier, predicate⟩ := retained
    have inContext : row ∈ context.solvedRequirements := by rw [valid.ledger]; exact member
    refine ⟨row, ⟨inContext, identifier⟩, ?_, valid.valid.entriesValid row inContext⟩
    simpa [IntegerLiteralResolution.predicate, target] using predicate

theorem Arms.ordinary_sites {source site scope expected bodyCertificate cases arms}
    (certificates : Arms compilation source site scope expected bodyCertificate cases arms)
    {context : SourceSemantics.Context} (valid : ContextValid compilation context) :
    Arms.LiteralSites (fun resolution => RequirementProves context resolution.requirement resolution.predicate) certificates :=
  Arms.literalSites certificates _ (fun _ _ _ _ _ accepted => ordinary_requirement valid accepted)

theorem Certificate.ordinary_sites
    {source scope id resolution resultType internalReason expressionCertificate bodyCertificate code}
    (certificate : CompatibleMatchCertificates.Certificate compilation source scope id resolution resultType internalReason
      expressionCertificate bodyCertificate code)
    {context : SourceSemantics.Context} (valid : ContextValid compilation context) :
    Certificate.LiteralSites (fun resolution => RequirementProves context resolution.requirement resolution.predicate) certificate :=
  Certificate.literalSites certificate _ (fun _ _ _ _ _ accepted => ordinary_requirement valid accepted)

/-- Both alternatives expose the generated matcher's exact pure execution.
No source matching judgment is supplied to the theorem. -/
theorem pattern_decides_with_literals {context : SourceSemantics.Context}
    {source : TypedSource} {scope : Scope} {site : StatementId} {span : Syntax.SourceSpan}
    {expected : TypeSystem.Ty} {pattern : TypedMatchPattern} {compiled : Pattern}
    (_certificate : CompatiblePatternCertificates.Certificate compilation source scope site span expected pattern compiled)
    (literals : IntegerLiteralResolution → Prop)
    (signatures : context.signatures = compilation.signatures)
    (requirements : ∀ numeric, literals numeric → RequirementProves context numeric.requirement numeric.predicate)
    (sites : CompatiblePatternDecision.WithLiterals literals compilation source scope site span expected pattern compiled)
    (catalogValid : SignatureCatalogWellFormed compilation.checked.signatures)
    (extended : SourceCoreRawMetadata.Extends compilation.values.registry registry)
    {sourceValue : Dynamic.Value} {value : Value} {payload : Ty}
    (represented : CompatiblePayload.ValueRep compilation.checked registry functions mapping world expected sourceValue value payload) :
    (∃ bindings values, Dynamic.PatternMatches context pattern sourceValue bindings ∧
      CompatiblePatternLeaves.BindingsRep compilation.checked registry functions mapping world compiled.bindings bindings values ∧
      MatcherRuns compiled value values) ∨
    (Dynamic.PatternDoesNotMatch context pattern sourceValue ∧ MatcherFails compiled value) := by
  obtain ⟨instructions, root, tree, supported⟩ := sites.supported
  obtain ⟨arity, instructionsEq, sourceRep⟩ := rootInstructions_sound compilation context signatures _ _ _ root
  have payloadEq : payload = compiled.type := Except.ok.inj
    (represented.projection.symm.trans (CompatiblePatternSuccess.Tree.projected tree))
  cases payloadEq
  cases CompatiblePatternDecision.Tree.decides_with_literals literals requirements extended tree supported sourceValue value represented with
  | inl success =>
    obtain ⟨bindings, values, matched, bindingRep, executes⟩ := success
    subst instructions
    have sourceMatch : Dynamic.PatternMatches context pattern sourceValue bindings := .intro sourceRep matched
    exact .inl ⟨bindings, values, sourceMatch,
      bindingRep, executes⟩
  | inr failed =>
    refine .inr ⟨.intro sourceRep ?_, failed⟩
    subst instructions
    refine ⟨CompatiblePatternCertificates.Tree.skips tree, ?_⟩
    intro bindings matched
    obtain ⟨values, _, _, executes⟩ := CompatiblePatternSuccess.Tree.success catalogValid extended tree sourceValue value bindings [] represented matched
    have impossible := (evaluation_deterministic (failed [value] [] (.var 0) (.var rfl))
      (executes [value] [] (.var 0) (.var rfl))).1
    cases impossible

theorem pattern_decides {context : SourceSemantics.Context}
    {source : TypedSource} {scope : Scope} {site : StatementId} {span : Syntax.SourceSpan}
    {expected : TypeSystem.Ty} {pattern : TypedMatchPattern} {compiled : Pattern}
    (certificate : CompatiblePatternCertificates.Certificate compilation source scope site span expected pattern compiled)
    (valid : ContextValid compilation context)
    (catalogValid : SignatureCatalogWellFormed compilation.checked.signatures)
    (extended : SourceCoreRawMetadata.Extends compilation.values.registry registry)
    {sourceValue : Dynamic.Value} {value : Value} {payload : Ty}
    (represented : CompatiblePayload.ValueRep compilation.checked registry functions mapping world expected sourceValue value payload) :
    (∃ bindings values, Dynamic.PatternMatches context pattern sourceValue bindings ∧
      CompatiblePatternLeaves.BindingsRep compilation.checked registry functions mapping world compiled.bindings bindings values ∧
      MatcherRuns compiled value values) ∨
    (Dynamic.PatternDoesNotMatch context pattern sourceValue ∧ MatcherFails compiled value) := by
  exact pattern_decides_with_literals certificate _ valid.signatures (fun _ proof => proof)
    (CompatiblePatternDecision.WithLiterals.of_certificate certificate _
      (fun _ _ _ _ accepted => ordinary_requirement valid accepted)) catalogValid extended represented

/-- The first matching arm wins. The default carries its own static body
certificate, and no-branch has precisely the compiler's fallthrough code. -/
inductive Decision (compilation : Compilation) (context : SourceSemantics.Context)
    (registry : SourceCoreRawMetadata.Registry) {ambient : AmbientDefinitions compilation.checked.catalog.definitions}
    (functions : FunctionModel compilation.checked.catalog ambient) (mapping : LocationMap) (world : StoreTyping)
    (scope : Scope) (bodyCertificate : BodyCertificate) (resultType : Ty)
    (sourceValue : Dynamic.Value) (value : Value) :
    List TypedMatchCase → List (Pattern × Expr) → Option (List StatementId) → Expr →
      Dynamic.MatchCaseSelection → Prop where
  | head {arm rest pattern body arms fallback fallbackCode bindings values}
      (matched : Dynamic.PatternMatches context arm.pattern sourceValue bindings)
      (bindingsRepresented : CompatiblePatternLeaves.BindingsRep compilation.checked registry functions mapping world
        pattern.bindings bindings values)
      (runs : MatcherRuns pattern value values)
      (bodyCertified : bodyCertificate (armScope scope pattern) arm.body body) :
      Decision compilation context registry functions mapping world scope bodyCertificate resultType sourceValue value
        (arm :: rest) ((pattern, body) :: arms) fallback fallbackCode (.arm arm.body bindings)
  | tail {arm rest pattern body arms fallback fallbackCode selection}
      (notMatched : Dynamic.PatternDoesNotMatch context arm.pattern sourceValue)
      (fails : MatcherFails pattern value)
      (next : Decision compilation context registry functions mapping world scope bodyCertificate resultType sourceValue value
        rest arms fallback fallbackCode selection) :
      Decision compilation context registry functions mapping world scope bodyCertificate resultType sourceValue value
        (arm :: rest) ((pattern, body) :: arms) fallback fallbackCode selection
  | default {statements code} (bodyCertified : bodyCertificate scope statements code) :
      Decision compilation context registry functions mapping world scope bodyCertificate resultType sourceValue value [] [] (some statements)
        code (.default statements)
  | noBranch :
      Decision compilation context registry functions mapping world scope bodyCertificate resultType sourceValue value [] [] none
        (LocalLoop.fallthrough resultType) .noBranch

theorem Decision.source {context : SourceSemantics.Context}
    {scope : Scope} {bodyCertificate : BodyCertificate} {resultType : Ty}
    {sourceValue : Dynamic.Value} {value : Value} {cases : List TypedMatchCase} {arms : List (Pattern × Expr)}
    {fallback : Option (List StatementId)} {fallbackCode : Expr} {selection : Dynamic.MatchCaseSelection}
    (decision : Decision compilation context registry functions mapping world scope bodyCertificate resultType sourceValue value
      cases arms fallback fallbackCode selection) :
    Dynamic.MatchCasesSelect context sourceValue cases fallback selection := by
  induction decision with
  | head matched => exact .head matched
  | tail notMatched _ _ ih => exact .tail notMatched ih
  | default => exact .default
  | noBranch => exact .noBranch

/-- The source arm selection and each pure matcher execution are consequences
of the actual compiler certificates, source evidence validity, and represented
input. Child statement evaluation is not assumed or concluded here. -/
theorem Arms.decides_with_literals {context : SourceSemantics.Context}
    {source : TypedSource} {site : StatementId} {scope : Scope} {expected : TypeSystem.Ty}
    {bodyCertificate : BodyCertificate} {cases : List TypedMatchCase} {arms : List (Pattern × Expr)}
    {resultType : Ty} {fallback : Option (List StatementId)} {fallbackCode : Expr}
    (certificates : Arms compilation source site scope expected bodyCertificate cases arms)
    (fallbackCertificate : Fallback bodyCertificate scope resultType fallback fallbackCode)
    (literals : IntegerLiteralResolution → Prop)
    (signatures : context.signatures = compilation.signatures)
    (requirements : ∀ numeric, literals numeric → RequirementProves context numeric.requirement numeric.predicate)
    (sites : Arms.LiteralSites literals certificates)
    (catalogValid : SignatureCatalogWellFormed compilation.checked.signatures)
    (extended : SourceCoreRawMetadata.Extends compilation.values.registry registry)
    {sourceValue : Dynamic.Value} {value : Value} {payload : Ty}
    (represented : CompatiblePayload.ValueRep compilation.checked registry functions mapping world expected sourceValue value payload) :
    ∃ selection, Decision compilation context registry functions mapping world scope bodyCertificate resultType sourceValue value
      cases arms fallback fallbackCode selection := by
  revert sites
  induction certificates with
  | nil =>
    intro sites
    cases fallbackCertificate with
    | none => exact ⟨_, .noBranch⟩
    | some certified => exact ⟨_, .default certified⟩
  | cons certificate typed bodyCertified tail ih =>
    intro sites
    cases sites with
    | cons headSupported tailSupported =>
      cases pattern_decides_with_literals certificate literals signatures requirements headSupported catalogValid extended represented with
      | inl matched =>
        obtain ⟨bindings, values, matched, representedBindings, runs⟩ := matched
        exact ⟨_, .head matched representedBindings runs bodyCertified⟩
      | inr failed =>
        obtain ⟨selection, next⟩ := ih tailSupported
        exact ⟨selection, .tail failed.1 failed.2 next⟩
theorem Arms.decides {context : SourceSemantics.Context}
    {source : TypedSource} {site : StatementId} {scope : Scope} {expected : TypeSystem.Ty}
    {bodyCertificate : BodyCertificate} {cases : List TypedMatchCase} {arms : List (Pattern × Expr)}
    {resultType : Ty} {fallback : Option (List StatementId)} {fallbackCode : Expr}
    (certificates : Arms compilation source site scope expected bodyCertificate cases arms)
    (fallbackCertificate : Fallback bodyCertificate scope resultType fallback fallbackCode)
    (valid : ContextValid compilation context)
    (catalogValid : SignatureCatalogWellFormed compilation.checked.signatures)
    (extended : SourceCoreRawMetadata.Extends compilation.values.registry registry)
    {sourceValue : Dynamic.Value} {value : Value} {payload : Ty}
    (represented : CompatiblePayload.ValueRep compilation.checked registry functions mapping world expected sourceValue value payload) :
    ∃ selection, Decision compilation context registry functions mapping world scope bodyCertificate resultType sourceValue value
      cases arms fallback fallbackCode selection := by
  exact Arms.decides_with_literals certificates fallbackCertificate _ valid.signatures (fun _ proof => proof)
    (Arms.ordinary_sites certificates valid) catalogValid extended represented

/-- A certified whole match always has an independent ordered source arm
selection for a represented scrutinee. Execution of that arm is a separate
statement correspondence obligation. -/
theorem Certificate.source_selects_with_literals {context : SourceSemantics.Context}
    {source : TypedSource} {scope : Scope} {id : StatementId} {resolution : MatchResolution}
    {resultType : Ty} {internalReason : Word} {expressionCertificate : ExpressionCertificate}
    {bodyCertificate : BodyCertificate} {code : Expr}
    (certificate : CompatibleMatchCertificates.Certificate compilation source scope id resolution resultType internalReason
      expressionCertificate bodyCertificate code)
    (literals : IntegerLiteralResolution → Prop)
    (signatures : context.signatures = compilation.signatures)
    (requirements : ∀ numeric, literals numeric → RequirementProves context numeric.requirement numeric.predicate)
    (sites : Certificate.LiteralSites literals certificate)
    (catalogValid : SignatureCatalogWellFormed compilation.checked.signatures)
    (extended : SourceCoreRawMetadata.Extends compilation.values.registry registry) {node : ExpressionNode}
    (found : source.lookupExpression? resolution.scrutinee = some node)
    {sourceValue : Dynamic.Value} {value : Value} {payload : Ty}
    (represented : CompatiblePayload.ValueRep compilation.checked registry functions mapping world node.type sourceValue value payload) :
    ∃ selection, Dynamic.MatchCasesSelect context sourceValue resolution.cases resolution.defaultBody selection := by
  cases sites with
  | @matchWith statementNode statementType scrutineeNode type scrutinee compiledArms fallbackCode branches code
      read allowed form ownedRequirements hiddenOwned hiddenFresh scrutineeOwned scrutineeFound projection
      expression sameType arms fallback branchesCompiled hiddenCompiled supported =>
    have same := Option.some.inj (found.symm.trans scrutineeFound)
    subst node
    obtain ⟨selection, decision⟩ := Arms.decides_with_literals arms fallback literals signatures requirements supported
      catalogValid extended represented
    exact ⟨selection, decision.source⟩

theorem Certificate.source_selects {context : SourceSemantics.Context}
    {source : TypedSource} {scope : Scope} {id : StatementId} {resolution : MatchResolution}
    {resultType : Ty} {internalReason : Word} {expressionCertificate : ExpressionCertificate}
    {bodyCertificate : BodyCertificate} {code : Expr}
    (certificate : CompatibleMatchCertificates.Certificate compilation source scope id resolution resultType internalReason
      expressionCertificate bodyCertificate code)
    (valid : ContextValid compilation context)
    (catalogValid : SignatureCatalogWellFormed compilation.checked.signatures)
    (extended : SourceCoreRawMetadata.Extends compilation.values.registry registry) {node : ExpressionNode}
    (found : source.lookupExpression? resolution.scrutinee = some node)
    {sourceValue : Dynamic.Value} {value : Value} {payload : Ty}
    (represented : CompatiblePayload.ValueRep compilation.checked registry functions mapping world node.type sourceValue value payload) :
    ∃ selection, Dynamic.MatchCasesSelect context sourceValue resolution.cases resolution.defaultBody selection := by
  exact Certificate.source_selects_with_literals certificate _ valid.signatures (fun _ proof => proof)
    (Certificate.ordinary_sites certificate valid) catalogValid extended found represented

end Solcore.SourceSemantics.CoreLowering.CompatibleMatchDecision
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CompatibleMatchArmAllocation
/-! Two-way finite continuation agreement for the actual marked compatible
match arm prefix. Only a completely matched arm allocates source binders. The
source map receives payload references; frame snapshots and markers extend
only the native typing world. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleMatchArmAllocation
open Core Frontend SourceInference GeneralHeap CoreProof ReadOnly DataEquality
open CallableIndexedHistory CompatibleMatchArmCertificates CallableIndexedAllocationCompletion
open CallableIndexedParameterMeaning (Arguments)

private theorem selects_rename {environment target : Environment} {expression : Expr} {value : Value} {ξ : Renaming}
    (selected : Selects environment expression value) (agrees : EnvironmentsAgree ξ environment target) :
    Selects target (expression.rename ξ) value := by
  induction selected with
  | var found => exact .var (agrees found)
  | first _ ih => exact .first ih
  | second _ ih => exact .second ih

private theorem agree_insert {canonical actual : Environment} {ξ : Renaming}
    (agrees : EnvironmentsAgree ξ canonical actual) (value : Value) :
    EnvironmentsAgree (Renaming.comp (Renaming.insertion 0) ξ) canonical (value :: actual) := by
  intro index selected found
  exact agrees found

/-- Prefix completion constructs independent binder allocation, the represented
heap, and a two-way finite continuation agreement. Source arguments may contain
closures and the initial store may contain arbitrary typed administrative cells. -/
theorem Tree.prefix {layouts : SourceCoreAllocationLayouts.Prepared}
    {owner : SourceSpecialization.SpecializationKey} {active : TypeSystem.Substitution}
    {layout : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
    {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error}
    {source : TypedSource} {types : List Ty} {output : Ty} {body : Expr}
    {scope : Scope} {start : Nat} {bindings : List Binding} {code : Expr}
    (tree : Tree layouts owner active layout globals onError source types output body scope start bindings code)
    {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection} {nativeDefinitions : DataEnvironment}
    {model : GenericHeap.PayloadModel catalog projects nativeDefinitions}
    (definitions : layouts.definitions = nativeDefinitions)
    (registered : layout.Registered nativeDefinitions)
    {mapping : LocationMap} {world : StoreTyping} {sources : List Dynamic.Value} {values : List Value}
    (represented : Arguments model mapping world bindings sources values)
    {administrative : Core.Context} {environment : Dynamic.Environment} {canonical logical actual : Environment}
    {heap : Dynamic.Heap} {store : Store} {ξ : Renaming}
    {allTypes : List Ty} {allValues : List Value} {named : Bool} {contextLocation : Location} {native : NativeFrame}
    (environments : DataHeap.EnvRepresents catalog mapping world administrative scope environment canonical nativeDefinitions)
    (heaps : GenericHeap.HeapRepresents model mapping world heap store)
    (sourceLayout : EnvironmentsAgree (Renaming.comp (Renaming.insertion (start + 1)) (Renaming.insertion start)) canonical logical)
    (actualLayout : EnvironmentsAgree ξ logical actual)
    (bundleSlot : logical[start]? = some (DataPatternValues.packValues allValues))
    (types_eq : types = allTypes)
    (bundleLength : allTypes.length = allValues.length)
    (valuesSelected : ∀ {index value}, values[index]? = some value → allValues[start + index]? = some value)
    (kinds : ∀ binding ∈ bindings, source.inputs.any (fun input => decide (input.id = binding.1.id)) = named)
    (reference : canonical[scope.length + (if named then 0 else 1) + globals]? = some (.cellRef layout.type contextLocation))
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode layout native))
    (unmapped : contextLocation ∉ mapping) :
    ∃ finalEnvironment finalHeap finalCanonical finalLogical finalActual finalStore finalMap finalWorld finalEmbedding,
      Dynamic.BindersAllocate environment heap (bindings.map Prod.fst) sources finalEnvironment finalHeap ∧
      DataHeap.EnvRepresents catalog finalMap finalWorld administrative
        (bindings.foldl (fun scope binding => (binding.1.id, binding.2) :: scope) scope)
        finalEnvironment finalCanonical nativeDefinitions ∧
      GenericHeap.HeapRepresents model finalMap finalWorld finalHeap finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧
      EnvironmentsAgree (DataMatchCoreAllocation.liftMany bindings.length (Renaming.comp (Renaming.insertion (start + 1)) (Renaming.insertion start)))
        finalCanonical finalLogical ∧
      EnvironmentsAgree finalEmbedding finalLogical finalActual ∧
      (∃ added : Environment, added.length = bindings.length ∧
        finalCanonical = added ++ canonical ∧ finalLogical = added ++ logical) ∧
      ContinuationAgreement actual store (code.rename ξ) finalActual finalStore (body.rename finalEmbedding) := by
  induction tree generalizing mapping world environment canonical logical actual heap store ξ sources values with
  | nil =>
    cases represented
    exact ⟨environment, heap, canonical, logical, actual, store, mapping, world, ξ,
      .nil _ _, environments, heaps, .refl _, .refl _, .refl _ _, sourceLayout, actualLayout, ⟨[], rfl, rfl, rfl⟩, .refl _ _ _⟩
  | @cons scope start binder payload bindings next allocation annotation same tail ih =>
    cases represented with
    | @cons _ _ sourceValue value _ sourceValues nativeValues head rest =>
      have selected : allValues[start]? = some value := by simpa using valuesSelected (index := 0) rfl
      have projection := DataPatternValues.projectPacked_selects (Selects.var bundleSlot) bundleLength start selected
      rw [← types_eq] at projection
      have initializer : Evaluates actual store
          ((LanguageResult.success (SourceCoreDataExpressions.projectPacked start types (.var start))).rename ξ)
          (.inRight .word value) store := .inRight ((selects_rename projection actualLayout).evaluates store)
      have canonicalLayout : EnvironmentsAgree (request source scope start (binder, payload)).references
          canonical (value :: logical) := agree_insert sourceLayout value
      have referenceAt : (value :: logical)[SourceCoreCallableIndexedAllocationFrames.referenceIndex globals
          (request source scope start (binder, payload))]? = some (.cellRef layout.type contextLocation) := by
        have found := canonicalLayout reference
        have kind := kinds (binder, payload) (by simp)
        change source.inputs.any (fun input => decide (input.id = binder.id)) = named at kind
        have isNamed : SourceCoreCallableIndexedAllocationFrames.isNamedInput (request source scope start (binder, payload)) = named := kind
        simp only [SourceCoreCallableIndexedAllocationFrames.referenceIndex, isNamed]
        exact found
      obtain ⟨captured, allocationEval, nextHeaps, nextReference, frame⟩ :=
        CallableIndexedOrdinaryAllocation.preserves allocation annotation same definitions registered environments
          canonicalLayout heaps referenceAt read (.initialized rfl rfl) (.initialized head) Dynamic.Heap.Allocates.append
      let nextRef := Value.cellRef (OptionalCell.cellType payload) (store.length + 2)
      have nextEnvironments := CallableIndexedOrdinaryAllocation.bind_environment (id := binder.id) environments nextReference
      have nextSourceLayout : EnvironmentsAgree (Renaming.comp (Renaming.insertion (start + 2)) (Renaming.insertion (start + 1)))
          (nextRef :: canonical) (nextRef :: logical) := by
        intro index selectedValue found
        have selected := sourceLayout.lift nextRef found
        simpa only [Renaming.lift_comp, Renaming.lift_insertion, Nat.add_assoc] using selected
      have nextActualLayout : EnvironmentsAgree (Renaming.comp (Renaming.insertion 0) ξ).lift
          (nextRef :: logical) (nextRef :: value :: actual) := by
        have inserted : EnvironmentsAgree (Renaming.comp (Renaming.insertion 0) ξ) logical (value :: actual) := agree_insert actualLayout value
        intro index selectedValue found
        exact inserted.lift nextRef found
      have renamedAllocation := CallableIndexedAllocationRenaming.transport allocation annotation same (Or.inr rfl)
        allocationEval (actualLayout.lift value)
      have bound : contextLocation < store.length := (List.getElem?_eq_some_iff.mp read).1
      obtain ⟨stillUnmapped, stillRead⟩ := frame contextLocation unmapped bound
      have nextRead := stillRead.trans read
      have nextSelected : ∀ {index selectedValue}, nativeValues[index]? = some selectedValue →
          allValues[(start + 1) + index]? = some selectedValue := by
        intro index selectedValue found
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using valuesSelected (index := index + 1) found
      obtain ⟨finalEnvironment, finalHeap, finalCanonical, finalLogical, finalActual, finalStore,
        finalMap, finalWorld, finalEmbedding, allocated, finalEnvironments, finalHeaps, maps, worlds,
        finalFrame, finalSourceLayout, finalActualLayout, spine, agreement⟩ :=
        ih (rest.extend (show LocationMap.Extends mapping (mapping ++ [store.length + 2]) from ⟨_, rfl⟩)
          (show WorldExtends world (world ++ [layout.type, allocation.entry.layout.type, OptionalCell.cellType payload]) from ⟨_, rfl⟩))
          nextEnvironments nextHeaps nextSourceLayout nextActualLayout
          (show (nextRef :: logical)[start + 1]? = some (DataPatternValues.packValues allValues) from bundleSlot)
          nextSelected (fun binding member => kinds binding (List.mem_cons_of_mem _ member))
          (show (nextRef :: canonical)[(((binder.id, payload) :: scope).length + (if named then 0 else 1) + globals)]? =
            some (.cellRef layout.type contextLocation) from by
              have nextIndex : (((binder.id, payload) :: scope).length + (if named then 0 else 1) + globals) =
                  (scope.length + (if named then 0 else 1) + globals) + 1 := by simp only [List.length_cons]; omega
              rw [nextIndex]
              exact reference)
          nextRead stillUnmapped
      refine ⟨finalEnvironment, finalHeap, finalCanonical, finalLogical, finalActual, finalStore,
        finalMap, finalWorld, finalEmbedding, .cons .append allocated, finalEnvironments, finalHeaps,
        (show LocationMap.Extends mapping (mapping ++ [store.length + 2]) from ⟨_, rfl⟩).trans maps,
        (show WorldExtends world (world ++ [layout.type, allocation.entry.layout.type, OptionalCell.cellType payload]) from ⟨_, rfl⟩).trans worlds,
        frame.trans finalFrame, ?_, finalActualLayout, ?_, ?_⟩
      · intro index selectedValue found
        simpa only [List.length_cons, DataMatchCoreAllocation.liftMany, Renaming.lift_comp, Renaming.lift_insertion] using finalSourceLayout found
      · obtain ⟨added, length, canonicalEq, logicalEq⟩ := spine
        exact ⟨added ++ [nextRef], by simp [length], by simpa [List.append_assoc, nextRef, request] using canonicalEq,
          by simpa [List.append_assoc, nextRef, request] using logicalEq⟩
      · simp only [LoopStatements.rename_insert_lift] at agreement
        apply ContinuationAgreement.trans ?_ agreement
        simpa only [LanguageResult.bind, Expr.rename, Renaming.lift, LoopRenaming.weakenOne, nextRef, request] using
          (ContinuationAgreement.bind initializer).trans (ContinuationAgreement.letE renamedAllocation)

end Solcore.SourceSemantics.CoreLowering.CompatibleMatchArmAllocation
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CompatibleMatchArmPrefix
/-! The selected compatible arm reaches the canonical source lexical scope
through its actual marked allocator, skipping both successful bundle and
loaded scrutinee. The continuation agreement has both finite directions and
retains arbitrary captured function values and administrative store cells. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleMatchArmPrefix
open Core Frontend SourceInference GeneralHeap DataEquality CoreProof ReadOnly DataPatternValues
open CompatibleMatchArmAllocation
open DataMatchCoreAllocation
open CompatibleMatchArmCertificates (Scope)

/-- The matcher's retained binder records feed the common ordinary payload
allocator without dropping their raw source type or function provenance. -/
theorem bindings_arguments
    {checked : SourceCoreCompatibleCatalog.Checked} {registry : SourceCoreRawMetadata.Registry}
    {ambient : AmbientDefinitions checked.catalog.definitions}
    {functions : CompatiblePayload.FunctionModel checked.catalog ambient}
    {mapping : LocationMap} {world : StoreTyping}
    {bindings : List (TypedBinder × Ty)} {sources : List (TypedBinder × Dynamic.Value)} {values : List Value}
    (represented : CompatiblePatternLeaves.BindingsRep checked registry functions mapping world bindings sources values) :
    CallableIndexedParameterMeaning.Arguments (CompatibleAmbientHeap.payloadModel checked registry functions)
      mapping world bindings (sources.map Prod.snd) values := by
  induction represented with
  | nil => exact .nil
  | cons head tail ih => exact .cons head ih

theorem bindings_identical
    {checked : SourceCoreCompatibleCatalog.Checked} {registry : SourceCoreRawMetadata.Registry}
    {ambient : AmbientDefinitions checked.catalog.definitions}
    {functions : CompatiblePayload.FunctionModel checked.catalog ambient}
    {mapping : LocationMap} {world : StoreTyping}
    {bindings : List (TypedBinder × Ty)} {sources : List (TypedBinder × Dynamic.Value)} {values : List Value}
    (represented : CompatiblePatternLeaves.BindingsRep checked registry functions mapping world bindings sources values) :
    bindings.map Prod.fst = sources.map Prod.fst := by
  induction represented with
  | nil => rfl
  | cons head tail ih => simp [ih]

private theorem liftMany_twoInsertions (count cutoff : Nat) :
    liftMany count (Renaming.comp (Renaming.insertion cutoff) (Renaming.insertion cutoff)) =
      Renaming.comp (Renaming.insertion (cutoff + count)) (Renaming.insertion (cutoff + count)) := by
  induction count generalizing cutoff with
  | zero => rfl
  | succ count ih =>
    simp only [liftMany, Renaming.lift_comp, Renaming.lift_insertion, ih]
    congr 2 <;> omega

/-- This is the successful branch emitted by compatible match lowering,
including its two hidden lexical slots. The result relates the arm's ordinary lexical scope
to its actual Core environment and transforms the body syntax with the same
embedding. Both finite evaluation directions retain the exact final store. -/
theorem bindArm_prefix {layouts : SourceCoreAllocationLayouts.Prepared}
    {owner : SourceSpecialization.SpecializationKey} {active : TypeSystem.Substitution}
    {layout : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
    {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error}
    {source : TypedSource} {context : SourceCoreCompatibleDataMatches.Context}
    {catalog : SourceCoreDataCatalog.Catalog}
    {projects : GenericHeap.Projection} {nativeDefinitions : DataEnvironment}
    {model : GenericHeap.PayloadModel catalog projects nativeDefinitions}
    {bindings : List (TypedBinder × Ty)} {sources : List Dynamic.Value} {values : List Value}
    {mapping : LocationMap} {world : StoreTyping} {administrativeContext : Core.Context}
    {scope : Scope} {environment : Dynamic.Environment} {canonical actual : Environment}
    {heap : Dynamic.Heap} {store : Store} {ξ : Renaming}
    (represented : CallableIndexedParameterMeaning.Arguments model mapping world bindings sources values)
    {scrutinee : Value} {outputType : Ty} {body code : Expr}
    (definitions : layouts.definitions = nativeDefinitions) (registered : layout.Registered nativeDefinitions)
    (allocator : context.sourceCells = some (SourceCoreCallableIndexedAllocationFrames.allocator layout globals
      (layouts.allocatorAt owner active onError)))
    (accepted : SourceCoreCompatibleDataMatches.bindArmWithAllocator context source scope bindings outputType
      (body.weakenAt bindings.length) = .ok code)
    {named : Bool} {contextLocation : Location} {native : CallableIndexedHistory.NativeFrame}
    (kinds : ∀ binding ∈ bindings, source.inputs.any (fun input => decide (input.id = binding.1.id)) = named)
    (reference : canonical[scope.length + (if named then 0 else 1) + globals]? = some (.cellRef layout.type contextLocation))
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode layout native))
    (unmapped : contextLocation ∉ mapping)
    (environments : DataHeap.EnvRepresents catalog mapping world administrativeContext scope environment canonical nativeDefinitions)
    (heaps : GenericHeap.HeapRepresents model mapping world heap store)
    (actualLayout : EnvironmentsAgree ξ (packValues values :: scrutinee :: canonical) actual) :
    ∃ finalEnvironment finalHeap finalCanonical finalActual finalStore finalMap finalWorld finalEmbedding,
      Dynamic.BindersAllocate environment heap (bindings.map Prod.fst) sources
        finalEnvironment finalHeap ∧
      DataHeap.EnvRepresents catalog finalMap finalWorld administrativeContext
        (bindings.foldl (fun scope binding => (binding.1.id, binding.2) :: scope) scope)
        finalEnvironment finalCanonical nativeDefinitions ∧
      GenericHeap.HeapRepresents model finalMap finalWorld finalHeap finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧
      EnvironmentsAgree finalEmbedding finalCanonical finalActual ∧
      ContinuationAgreement actual store
        (code.rename ξ)
        finalActual finalStore (body.rename finalEmbedding) := by
  let κ := Renaming.comp (Renaming.insertion 0) (Renaming.insertion 0)
  have sourceLayout : EnvironmentsAgree κ canonical (packValues values :: scrutinee :: canonical) := by
    intro index value found
    exact found
  have length : (bindings.map Prod.snd).length = values.length := by
    simpa using represented.length.2
  obtain ⟨finalEnvironment, finalHeap, finalCanonical, finalLogical, finalActual, finalStore, finalMap,
    finalWorld, finalEmbedding, allocated, finalEnv, finalHeapRep, maps, worlds, frame,
    finalSourceLayout, finalActualLayout, _, agreement⟩ :=
    CompatibleMatchArmAllocation.Tree.prefix
      (CompatibleMatchArmCertificates.of_accepted onError allocator accepted) definitions registered represented
      environments heaps sourceLayout actualLayout (start := 0) rfl rfl length
      (fun {_ _} found => by simpa using found) kinds reference read unmapped
  refine ⟨finalEnvironment, finalHeap, finalCanonical, finalActual, finalStore, finalMap,
    finalWorld, Renaming.comp finalEmbedding (liftMany bindings.length κ), allocated, finalEnv,
    finalHeapRep, maps, worlds, frame, ?_, ?_⟩
  · intro index value found
    exact finalActualLayout (finalSourceLayout found)
  · have same : ((body.weakenAt bindings.length).weakenAt bindings.length).rename finalEmbedding =
        body.rename (Renaming.comp finalEmbedding (liftMany bindings.length κ)) := by
      simp only [κ, liftMany_twoInsertions, Nat.zero_add]
      rw [← Expr.rename_insertion, ← Expr.rename_insertion, Expr.rename_comp, Expr.rename_comp]
      rfl
    rw [same] at agreement
    exact agreement


end Solcore.SourceSemantics.CoreLowering.CompatibleMatchArmPrefix
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CompatibleMatchBranchesPrefix
/-! Under an arbitrary payload model containing the finite pattern values, the
emitted ordered match branches reach exactly the selected arm/default
continuation, allocating only the successful arm's binders. This is a complete
prefix correspondence (wrap and unwrap), not a supplied child evaluation. The
selected body's own statement correspondence is a separate structural proof. -/

set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleMatchBranchesPrefix
open Core Frontend Frontend.SourceInference GeneralHeap DataHeap
open SourceCoreCompatibleDataMatches DataPatternValues CompatiblePatternLeaves CompatiblePatternExecution
open CompatibleMatchCertificates CompatibleMatchDecision CoreProof ReadOnly

open DataMatchBranchPrefix CompatibleMatchArmPrefix

private theorem case_right {environment : Environment} {before middle : Store}
    {scrutinee left right : Expr} {leftType : Ty} {value : Value}
    (evaluated : Evaluates environment before scrutinee (.inRight leftType value) middle) :
    ContinuationAgreement environment before (.caseE scrutinee left right) (value :: environment) middle right := by
  constructor
  · intro result finalStore body; exact .caseRight evaluated body
  · intro result finalStore evaluation
    obtain ⟨_, sized⟩ := evaluation_has_size evaluation
    obtain ⟨_, _, body⟩ := sized.case_right evaluated
    exact body.sound

private theorem case_left {environment : Environment} {before middle : Store}
    {scrutinee left right : Expr} {rightType : Ty} {value : Value}
    (evaluated : Evaluates environment before scrutinee (.inLeft rightType value) middle) :
    ContinuationAgreement environment before (.caseE scrutinee left right) (value :: environment) middle left := by
  constructor
  · intro result finalStore body; exact .caseLeft evaluated body
  · intro result finalStore evaluation
    obtain ⟨_, sized⟩ := evaluation_has_size evaluation
    obtain ⟨_, _, body⟩ := sized.case_left evaluated
    exact body.sound

/-- The entire attempted-arm fold has no other finite result than execution
of its selected, related continuation. The initial store may contain arbitrary
typed administrative functions, and the body itself is unrestricted syntax. -/
theorem Decision.prefix {compilation : SourceCoreCompatibleDataMatches.Context} {context : SourceSemantics.Context}
    {registry : SourceCoreRawMetadata.Registry} {ambient : AmbientDefinitions compilation.checked.catalog.definitions}
    {functions : CompatiblePayload.FunctionModel compilation.checked.catalog ambient}
    {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
    {active : TypeSystem.Substitution} {layout : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
    {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error}
    (definitions : layouts.definitions = ambient.definitions) (registered : layout.Registered ambient.definitions)
    (allocator : compilation.sourceCells = some (SourceCoreCallableIndexedAllocationFrames.allocator layout globals
      (layouts.allocatorAt owner active onError)))
    {mapping : LocationMap} {world : StoreTyping}
    {source : TypedSource} {site : StatementId} {scope : Scope} {expected : TypeSystem.Ty}
    {bodyCertificate : BodyCertificate} {resultType : Ty}
    {sourceValue : Dynamic.Value} {value : Value} {cases : List TypedMatchCase} {arms : List (Pattern × Expr)}
    {fallback : Option (List StatementId)} {fallbackCode : Expr} {selection : Dynamic.MatchCaseSelection}
    (decision : Decision compilation context registry functions mapping world scope bodyCertificate resultType sourceValue value
      cases arms fallback fallbackCode selection)
    (certificates : Arms compilation source site scope expected bodyCertificate cases arms)
    {administrativeContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment}
    {heap : Dynamic.Heap} {store : Store} {ξ : Renaming} {branches : Expr}
    (branchesCompiled : Branches compilation source scope (LocalLoop.controlType resultType) fallbackCode arms branches)
    (kinds : ∀ item ∈ arms, ∀ binding ∈ item.1.bindings, source.inputs.any (fun input => decide (input.id = binding.1.id)) = false)
    {contextLocation : Location} {native : CallableIndexedHistory.NativeFrame}
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef layout.type contextLocation))
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode layout native))
    (unmapped : contextLocation ∉ mapping)
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog compilation.checked.catalog) mapping world administrativeContext scope environment canonical ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents compilation.checked registry functions mapping world heap store)
    (actualLayout : EnvironmentsAgree ξ (value :: canonical) actual) :
    ∃ finalScope finalEnvironment finalHeap finalCanonical finalActual finalStore finalMap finalWorld finalEmbedding body,
      SelectedBody bodyCertificate scope environment heap resultType selection finalScope finalEnvironment finalHeap body ∧
      DataHeap.EnvRepresents (CompatibleEquality.storageCatalog compilation.checked.catalog) finalMap finalWorld administrativeContext
        finalScope finalEnvironment finalCanonical ambient.definitions ∧
      CompatibleAmbientHeap.HeapRepresents compilation.checked registry functions finalMap finalWorld finalHeap finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧
      EnvironmentsAgree finalEmbedding finalCanonical finalActual ∧
      ContinuationAgreement actual store
        (branches.rename ξ)
        finalActual finalStore (body.rename finalEmbedding) := by
  induction decision generalizing actual ξ branches with
  | @head arm rest pattern body arms fallback fallbackCode bindings values matched bindingsRepresented runs certified =>
    cases certificates with
    | cons certificate matcherTyped bodyCertified tail =>
      have matchedCore : Evaluates actual store ((Expr.apply pattern.matcher (.var 0)).rename ξ)
          (.inRight .unit (packValues values)) store := by
        rw [Expr.rename, closed_rename matcherTyped ξ]
        exact runs actual store (.var (ξ 0)) (.var (actualLayout (index := 0) rfl))
      cases branchesCompiled with
      | cons allocation tailBranches =>
        obtain ⟨finalEnvironment, finalHeap, finalCanonical, finalActual, finalStore, finalMap, finalWorld,
          finalEmbedding, allocated, finalEnv, finalHeapRep, maps, worlds, frame, finalLayout, agreement⟩ :=
          CompatibleMatchArmPrefix.bindArm_prefix (bindings_arguments bindingsRepresented) definitions registered allocator allocation
            (named := false) (kinds (pattern, body) (by simp)) reference read unmapped
            environments heaps (actualLayout.lift (packValues values))
        have bindings := bindings_identical bindingsRepresented
        rw [bindings] at allocated
        exact ⟨_, finalEnvironment, finalHeap, finalCanonical, finalActual, finalStore, finalMap, finalWorld,
          finalEmbedding, body, .arm bindings allocated certified,
          finalEnv, finalHeapRep, maps, worlds, frame, finalLayout, (case_right matchedCore).trans agreement⟩
  | @tail arm rest pattern body arms fallback fallbackCode selection notMatched fails next ih =>
    cases certificates with
    | cons certificate matcherTyped bodyCertified tail =>
      have failedCore : Evaluates actual store ((Expr.apply pattern.matcher (.var 0)).rename ξ)
          (.inLeft (bundleType pattern.bindingTypes) .unit) store := by
        rw [Expr.rename, closed_rename matcherTyped ξ]
        exact fails actual store (.var (ξ 0)) (.var (actualLayout (index := 0) rfl))
      have nextLayout : EnvironmentsAgree (Renaming.comp (Renaming.insertion 0) ξ)
          (value :: canonical) (.unit :: actual) := by
        intro index foundValue found
        exact actualLayout found
      cases branchesCompiled with
      | cons allocation tailBranches =>
        obtain ⟨finalScope, finalEnvironment, finalHeap, finalCanonical, finalActual, finalStore, finalMap, finalWorld,
          finalEmbedding, body, choice, finalEnv, finalHeapRep, maps, worlds, frame, finalLayout, agreement⟩ :=
          ih tail tailBranches (fun item member => kinds item (List.mem_cons_of_mem _ member)) nextLayout
        refine ⟨finalScope, finalEnvironment, finalHeap, finalCanonical, finalActual, finalStore, finalMap, finalWorld,
          finalEmbedding, body, choice, finalEnv, finalHeapRep, maps, worlds, frame, finalLayout, ?_⟩
        simp only [LoopStatements.rename_insert] at agreement
        simp only [Expr.rename, LoopRenaming.weakenZero]
        exact (case_left failedCore).trans agreement
  | default certified =>
    cases branchesCompiled
    refine ⟨scope, environment, heap, canonical, actual, store, mapping, world,
      Renaming.comp ξ (Renaming.insertion 0), _, .default certified, environments, heaps,
      .refl _, .refl _, .refl _ _, ?_, ?_⟩
    · intro index foundValue found
      exact actualLayout (index := index + 1) found
    · simp only [← Expr.rename_insertion, Expr.rename_comp]
      exact .refl _ _ _
  | noBranch =>
    cases branchesCompiled
    refine ⟨scope, environment, heap, canonical, actual, store, mapping, world,
      Renaming.comp ξ (Renaming.insertion 0), _, .noBranch, environments, heaps,
      .refl _, .refl _, .refl _ _, ?_, ?_⟩
    · intro index foundValue found
      exact actualLayout (index := index + 1) found
    · simp only [← Expr.rename_insertion, Expr.rename_comp]
      exact .refl _ _ _

end Solcore.SourceSemantics.CoreLowering.CompatibleMatchBranchesPrefix
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CompatiblePatternSourceBinders
/-! The actual pattern compiler and independent source typing consume the
same prefix program. This yields the complete ordered source binders without
running a matcher or inferring source metadata from a native type. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatiblePatternSourceBinders
open Core Frontend SourceInference SourceCoreCompatibleDataMatches
open CompatiblePatternCertificates

theorem Tree.source_binders
    {compilation : Compilation} {source : TypedSource} {site : StatementId}
    {span : Syntax.SourceSpan} {scope : Scope} {expected : TypeSystem.Ty}
    {instructions rest : List MatchPatternInstruction} {compiled : Pattern}
    (tree : Tree compilation source site span scope expected instructions compiled rest) :
    ∀ {context : SourceSemantics.Context} {sourceType : TypeSystem.Ty}
      {requirements : List RequirementId} {binders : List TypedBinder}
      {sourceRest : List MatchPatternInstruction},
      PatternInstructionHasType context instructions sourceType requirements binders sourceRest →
      sourceRest = rest ∧ compiled.bindings.map Prod.fst = binders := by
  induction tree using Tree.rec
      (motive_2 := fun types instructions patterns rest _ =>
        ∀ {context : SourceSemantics.Context} {sourceTypes : List TypeSystem.Ty}
          {requirements : List RequirementId} {binders : List TypedBinder}
          {sourceRest : List MatchPatternInstruction},
          PatternInstructionsHaveTypes context instructions sourceTypes requirements binders sourceRest →
          sourceTypes.length = types.length →
          sourceRest = rest ∧ (patterns.flatMap (·.bindings)).map Prod.fst = binders) with
  | wildcard => intro context sourceType requirements binders sourceRest typed; cases typed; exact ⟨rfl, rfl⟩
  | binder => intro context sourceType requirements binders sourceRest typed; cases typed; exact ⟨rfl, rfl⟩
  | literal => intro context sourceType requirements binders sourceRest typed; cases typed; exact ⟨rfl, rfl⟩
  | tuple projection unpacked children projectedChildren ih =>
    intro context sourceType requirements binders sourceRest typed
    cases typed with
    | tuple arity elements =>
      exact ih elements (arity.symm.trans (unpackTypes_length unpacked).symm)
  | constructor projection result count resolved coreType raw children projectedChildren registered ih =>
    intro context sourceType requirements binders sourceRest typed
    cases typed with
    | constructor valid arity arguments => exact ih arguments rfl
  | nil =>
    rename_i context sourceTypes requirements binders sourceRest typed length
    have empty : sourceTypes = [] := List.length_eq_zero_iff.mp length
    subst sourceTypes
    cases typed
    exact ⟨rfl, rfl⟩
  | cons head tail headIH tailIH =>
    rename_i context sourceTypes requirements binders sourceRest typed length
    cases sourceTypes with
    | nil => simp at length
    | cons sourceType sourceTypes =>
      cases typed with
      | cons first remaining =>
        obtain ⟨rfl, firstBinders⟩ := headIH first
        obtain ⟨rfl, remainingBinders⟩ := tailIH remaining (Nat.succ.inj length)
        exact ⟨rfl, by simp only [List.flatMap_cons, List.map_append, firstBinders, remainingBinders]⟩

theorem source_arity_unique
    {firstContext secondContext : SourceSemantics.Context}
    {spelling : MatchPatternSource} {resolution : MatchPatternResolution} {first second : Nat}
    (left : MatchPatternSourceRepresents firstContext spelling resolution first)
    (right : MatchPatternSourceRepresents secondContext spelling resolution second) : first = second := by
  induction left with
  | wildcard => cases right; rfl
  | integerLiteral => cases right; rfl
  | binder => cases right; rfl
  | constructor => cases right; rfl
  | tuple => cases right; rfl
  | group inner ih => cases right with | group other => exact ih other

theorem instruction_binders
    {context : SourceSemantics.Context} {instructions rest : List MatchPatternInstruction}
    {type : TypeSystem.Ty} {requirements : List RequirementId} {binders : List TypedBinder}
    (typed : PatternInstructionHasType context instructions type requirements binders rest) :
    SourceCoreDataPlaces.instructionBinders instructions =
      binders ++ SourceCoreDataPlaces.instructionBinders rest := by
  induction typed using PatternInstructionHasType.rec
      (motive_2 := fun instructions _ _ binders rest _ =>
        SourceCoreDataPlaces.instructionBinders instructions =
          binders ++ SourceCoreDataPlaces.instructionBinders rest) with
  | wildcard => rfl
  | integerLiteral => rfl
  | binder => rfl
  | constructor valid arity arguments ih => exact ih
  | tuple arity elements ih => exact ih
  | nil => rfl
  | cons head tail headIH tailIH => rw [headIH, tailIH, List.append_assoc]

theorem pattern_binders
    {context : SourceSemantics.Context} {pattern : TypedMatchPattern}
    {type : TypeSystem.Ty} {binders : List TypedBinder} {arity : Nat}
    (typed : TypedMatchPatternHasType context pattern type binders arity) :
    SourceCoreDataPlaces.patternBinders pattern = binders := by
  have consumed := instruction_binders typed.resolution_type
  cases resolution : pattern.resolution <;>
    simpa [SourceCoreDataPlaces.patternBinders, resolution, MatchPatternResolutionHasType,
      matchPatternResolutionInstructions, SourceCoreDataPlaces.instructionBinders] using consumed

theorem Certificate.source_binders
    {compilation : Compilation} {source : TypedSource} {scope : Scope} {site : StatementId}
    {span : Syntax.SourceSpan} {expected : TypeSystem.Ty} {pattern : TypedMatchPattern} {compiled : Pattern}
    (certificate : Certificate compilation source scope site span expected pattern compiled)
    {context : SourceSemantics.Context} {binders : List TypedBinder} {arity : Nat}
    (signatures : context.signatures = compilation.signatures)
    (typed : TypedMatchPatternHasType context pattern expected binders arity) :
    compiled.bindings.map Prod.fst = binders := by
  obtain ⟨instructions, root, tree⟩ := certificate.tree
  obtain ⟨actualArity, sameInstructions, sourceRoot⟩ := rootInstructions_sound compilation context signatures
    pattern.source pattern.resolution instructions root
  have sameArity := source_arity_unique sourceRoot typed.source_represents
  subst actualArity
  subst instructions
  exact (Tree.source_binders tree typed.resolution_type).2

end Solcore.SourceSemantics.CoreLowering.CompatiblePatternSourceBinders
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CompatibleMatchTypedArmAllocation
/-! Two-way finite continuation agreement for the actual marked compatible
match arm prefix. Only a completely matched arm allocates source binders. The
source map receives payload references; frame snapshots and markers extend
only the native typing world. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleMatchTypedArmAllocation
open Core Frontend SourceInference GeneralHeap CoreProof ReadOnly DataEquality
open CallableIndexedHistory CompatibleMatchArmCertificates CallableIndexedAllocationCompletion
open CallableIndexedParameterMeaning (Arguments)
universe u v
abbrev prefixContext := CallableIndexedParameterTyped.prefixContext

private theorem selects_rename {environment target : Environment} {expression : Expr} {value : Value} {ξ : Renaming}
    (selected : Selects environment expression value) (agrees : EnvironmentsAgree ξ environment target) :
    Selects target (expression.rename ξ) value := by
  induction selected with
  | var found => exact .var (agrees found)
  | first _ ih => exact .first ih
  | second _ ih => exact .second ih

private theorem agree_insert {canonical actual : Environment} {ξ : Renaming}
    (agrees : EnvironmentsAgree ξ canonical actual) (value : Value) :
    EnvironmentsAgree (Renaming.comp (Renaming.insertion 0) ξ) canonical (value :: actual) := by
  intro index selected found
  exact agrees found

/-- Prefix completion constructs independent binder allocation, the represented
heap, and a two-way finite continuation agreement. Source arguments may contain
closures and the initial store may contain arbitrary typed administrative cells. -/
theorem Stateful.prefix_cells_sized {layouts : SourceCoreAllocationLayouts.Prepared}
    {owner : SourceSpecialization.SpecializationKey} {active : TypeSystem.Substitution}
    {layout : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
    {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error}
    {allocationSource : TypedSource} {types : List Ty} {output : Ty} {body : Expr}
    {scope : Scope} {start : Nat} {bindings : List Binding} {code : Expr}
    (tree : Tree layouts owner active layout globals onError allocationSource types output body scope start bindings code)
    {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection} {nativeDefinitions : DataEnvironment}
    {model : GenericHeap.PayloadModel catalog projects nativeDefinitions}
    {cells : GenericHeap.CellModel nativeDefinitions}
    (ordinaryCells : GenericHeap.OrdinaryCells model cells)
    {Records : Type v} (protocol : ProtectedStateTransition.Protocol.{u, v} Records)
    (producer : ProtectedStateTransition.CellAllocation.Producer (catalog := catalog) protocol layouts layout cells)
    (stateBindings : ProtectedStateTransition.Bindings protocol)
    (definitions : layouts.definitions = nativeDefinitions)
    (registered : layout.Registered nativeDefinitions)
    {mapping : LocationMap} {world : StoreTyping} {sources : List Dynamic.Value} {values : List Value}
    (represented : Arguments model mapping world bindings sources values)
    {administrative actualContext : Core.Context} {environment : Dynamic.Environment} {canonical logical actual : Environment}
    {heap : Dynamic.Heap} {store : Store} {ξ : Renaming}
    {allTypes : List Ty} {allValues : List Value} {named : Bool} {contextLocation : Location} {native : NativeFrame}
    (environments : DataHeap.EnvRepresents catalog mapping world administrative scope environment canonical nativeDefinitions)
    (heaps : GenericHeap.CellHeapRepresents cells mapping world heap store)
    (sourceLayout : EnvironmentsAgree (Renaming.comp (Renaming.insertion (start + 1)) (Renaming.insertion start)) canonical logical)
    (actualLayout : EnvironmentsAgree ξ logical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext nativeDefinitions)
    (bundleSlot : logical[start]? = some (DataPatternValues.packValues allValues))
    (types_eq : types = allTypes)
    (bundleLength : allTypes.length = allValues.length)
    (valuesSelected : ∀ {index value}, values[index]? = some value → allValues[start + index]? = some value)
    (kinds : ∀ binding ∈ bindings, allocationSource.inputs.any (fun input => decide (input.id = binding.1.id)) = named)
    (reference : canonical[scope.length + (if named then 0 else 1) + globals]? = some (.cellRef layout.type contextLocation))
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode layout native))
    (unmapped : contextLocation ∉ mapping)
    (initial : protocol.State ⟨scope, mapping, world, heap, store, canonical⟩)
    (readyAt : ProtectedStateTransition.CellAllocation.ReadyAt producer contextLocation native) :
    ∃ finalEnvironment finalHeap finalCanonical finalLogical finalActual finalStore finalMap finalWorld finalEmbedding,
      Dynamic.BindersAllocate environment heap (bindings.map Prod.fst) sources finalEnvironment finalHeap ∧
      DataHeap.EnvRepresents catalog finalMap finalWorld administrative
        (bindings.foldl (fun scope binding => (binding.1.id, binding.2) :: scope) scope)
        finalEnvironment finalCanonical nativeDefinitions ∧
      GenericHeap.CellHeapRepresents cells finalMap finalWorld finalHeap finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧
      EnvironmentsAgree (DataMatchCoreAllocation.liftMany bindings.length (Renaming.comp (Renaming.insertion (start + 1)) (Renaming.insertion start)))
        finalCanonical finalLogical ∧
      EnvironmentsAgree finalEmbedding finalLogical finalActual ∧
      (∃ added : Environment, added.length = bindings.length ∧
        finalCanonical = added ++ canonical ∧ finalLogical = added ++ logical) ∧
      RuntimeEnvironmentHasTypes finalWorld finalActual (prefixContext bindings actualContext) nativeDefinitions ∧
      ContinuationSize false actual store (code.rename ξ) finalActual finalStore (body.rename finalEmbedding) ∧
      ∃ final : protocol.State
          ⟨bindings.foldl (fun scope binding => (binding.1.id, binding.2) :: scope) scope,
            finalMap, finalWorld, finalHeap, finalStore, finalCanonical⟩,
        protocol.Relates initial final ∧ Nonempty (ProtectedStateTransition.ReturnTo protocol scope canonical
          (bindings.foldl (fun scope binding => (binding.1.id, binding.2) :: scope) scope) finalCanonical) := by
  induction tree generalizing mapping world environment canonical logical actual heap store ξ sources values actualContext with
  | nil =>
    cases represented
    exact ⟨environment, heap, canonical, logical, actual, store, mapping, world, ξ,
      .nil _ _, environments, heaps, .refl _, .refl _, .refl _ _, sourceLayout, actualLayout, ⟨[], rfl, rfl, rfl⟩, actualTyped, .refl _ _ _, initial, protocol.refl initial, ⟨ProtectedStateTransition.ReturnTo.refl protocol _ canonical⟩⟩
  | @cons scope start binder payload bindings next allocation annotation same tail ih =>
    cases represented with
    | @cons _ _ sourceValue value _ sourceValues nativeValues head rest =>
      have selected : allValues[start]? = some value := by simpa using valuesSelected (index := 0) rfl
      have projection := DataPatternValues.projectPacked_selects (Selects.var bundleSlot) bundleLength start selected
      rw [← types_eq] at projection
      have initializer : Evaluates actual store
          ((LanguageResult.success (SourceCoreDataExpressions.projectPacked start types (.var start))).rename ξ)
          (.inRight .word value) store := .inRight ((selects_rename projection actualLayout).evaluates store)
      have canonicalLayout : EnvironmentsAgree (request allocationSource scope start (binder, payload)).references
          canonical (value :: logical) := agree_insert sourceLayout value
      have referenceAt : (value :: logical)[SourceCoreCallableIndexedAllocationFrames.referenceIndex globals
          (request allocationSource scope start (binder, payload))]? = some (.cellRef layout.type contextLocation) := by
        have found := canonicalLayout reference
        have kind := kinds (binder, payload) (by simp)
        change allocationSource.inputs.any (fun input => decide (input.id = binder.id)) = named at kind
        have isNamed : SourceCoreCallableIndexedAllocationFrames.isNamedInput (request allocationSource scope start (binder, payload)) = named := kind
        simp only [SourceCoreCallableIndexedAllocationFrames.referenceIndex, isNamed]
        exact found
      obtain ⟨captured, _captures, _captureTyped, allocationEval, nextHeaps, nextReference, frame, allocationState⟩ :=
        producer.complete allocation annotation same definitions registered environments
          canonicalLayout heaps referenceAt read (.initialized rfl rfl) (ordinaryCells.inject (.initialized head)) (.ordinary Dynamic.Heap.Allocates.append) initial (readyAt initial read)
      obtain ⟨nextState, allocationRelated⟩ := allocationState
      let nextRef := Value.cellRef (OptionalCell.cellType payload) (store.length + 2)
      have nextEnvironments := CallableIndexedOrdinaryAllocation.bind_environment (id := binder.id) environments nextReference
      have nextSourceLayout : EnvironmentsAgree (Renaming.comp (Renaming.insertion (start + 2)) (Renaming.insertion (start + 1)))
          (nextRef :: canonical) (nextRef :: logical) := by
        intro index selectedValue found
        have selected := sourceLayout.lift nextRef found
        simpa only [Renaming.lift_comp, Renaming.lift_insertion, Nat.add_assoc] using selected
      have nextActualLayout : EnvironmentsAgree (Renaming.comp (Renaming.insertion 0) ξ).lift
          (nextRef :: logical) (nextRef :: value :: actual) := by
        have inserted : EnvironmentsAgree (Renaming.comp (Renaming.insertion 0) ξ) logical (value :: actual) := agree_insert actualLayout value
        intro index selectedValue found
        exact inserted.lift nextRef found
      have renamedAllocation := CallableIndexedAllocationRenaming.transport allocation annotation same (Or.inr rfl)
        allocationEval (actualLayout.lift value)
      have bound : contextLocation < store.length := (List.getElem?_eq_some_iff.mp read).1
      obtain ⟨stillUnmapped, stillRead⟩ := frame contextLocation unmapped bound
      have nextRead := stillRead.trans read
      have nextSelected : ∀ {index selectedValue}, nativeValues[index]? = some selectedValue →
          allValues[(start + 1) + index]? = some selectedValue := by
        intro index selectedValue found
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using valuesSelected (index := index + 1) found
      obtain ⟨finalEnvironment, finalHeap, finalCanonical, finalLogical, finalActual, finalStore,
        finalMap, finalWorld, finalEmbedding, allocated, finalEnvironments, finalHeaps, maps, worlds,
        finalFrame, finalSourceLayout, finalActualLayout, spine, finalTyped, agreement, finalState, tailRelated, ⟨tailReturn⟩⟩ :=
        ih (rest.extend (show LocationMap.Extends mapping (mapping ++ [store.length + 2]) from ⟨_, rfl⟩)
          (show WorldExtends world (world ++ [layout.type, allocation.entry.layout.type, OptionalCell.cellType payload]) from ⟨_, rfl⟩))
          nextEnvironments nextHeaps nextSourceLayout nextActualLayout
          (show RuntimeEnvironmentHasTypes
              (world ++ [layout.type, allocation.entry.layout.type, OptionalCell.cellType payload])
              (nextRef :: value :: actual) (OptionalCell.referenceType payload :: payload :: actualContext) nativeDefinitions from
            .cons (.cellRef nextReference.typed)
              (.cons ((model.runtime_hasType head).weaken ⟨_, rfl⟩) (actualTyped.weaken ⟨_, rfl⟩)))
          (show (nextRef :: logical)[start + 1]? = some (DataPatternValues.packValues allValues) from bundleSlot)
          nextSelected (fun binding member => kinds binding (List.mem_cons_of_mem _ member))
          (show (nextRef :: canonical)[(((binder.id, payload) :: scope).length + (if named then 0 else 1) + globals)]? =
            some (.cellRef layout.type contextLocation) from by
              have nextIndex : (((binder.id, payload) :: scope).length + (if named then 0 else 1) + globals) =
                  (scope.length + (if named then 0 else 1) + globals) + 1 := by simp only [List.length_cons]; omega
              rw [nextIndex]
              exact reference)
          nextRead stillUnmapped nextState
      refine ⟨finalEnvironment, finalHeap, finalCanonical, finalLogical, finalActual, finalStore,
        finalMap, finalWorld, finalEmbedding, .cons .append allocated, finalEnvironments, finalHeaps,
        (show LocationMap.Extends mapping (mapping ++ [store.length + 2]) from ⟨_, rfl⟩).trans maps,
        (show WorldExtends world (world ++ [layout.type, allocation.entry.layout.type, OptionalCell.cellType payload]) from ⟨_, rfl⟩).trans worlds,
        frame.trans finalFrame, ?_, finalActualLayout, ?_, finalTyped, ?_, finalState,
        protocol.trans allocationRelated tailRelated,
        ⟨ProtectedStateTransition.ReturnTo.then
          (ProtectedStateTransition.ReturnTo.binding stateBindings scope canonical binder.id payload nextRef)
          tailReturn⟩⟩
      · intro index selectedValue found
        simpa only [List.length_cons, DataMatchCoreAllocation.liftMany, Renaming.lift_comp, Renaming.lift_insertion] using finalSourceLayout found
      · obtain ⟨added, length, canonicalEq, logicalEq⟩ := spine
        exact ⟨added ++ [nextRef], by simp [length], by simpa [List.append_assoc, nextRef, request] using canonicalEq,
          by simpa [List.append_assoc, nextRef, request] using logicalEq⟩
      · simp only [LoopStatements.rename_insert_lift] at agreement
        apply ContinuationSize.trans (a := false) (b := false) ?_ agreement
        simpa only [LanguageResult.bind, Expr.rename, Renaming.lift, LoopRenaming.weakenOne, nextRef, request] using
          ((ContinuationSize.bind initializer).trans (ContinuationSize.letE renamedAllocation)).weak

/-- Compatibility with the original ordinary heap uses the same cell proof. -/
theorem Stateful.prefix_sized {layouts : SourceCoreAllocationLayouts.Prepared}
    {owner : SourceSpecialization.SpecializationKey} {active : TypeSystem.Substitution}
    {layout : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
    {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error}
    {source : TypedSource} {types : List Ty} {output : Ty} {body : Expr}
    {scope : Scope} {start : Nat} {bindings : List Binding} {code : Expr}
    (tree : Tree layouts owner active layout globals onError source types output body scope start bindings code)
    {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection} {nativeDefinitions : DataEnvironment}
    {model : GenericHeap.PayloadModel catalog projects nativeDefinitions}
    {Records : Type v} (protocol : ProtectedStateTransition.Protocol.{u, v} Records)
    (producer : ProtectedStateTransition.MarkedAllocation.Producer protocol layouts layout model)
    (stateBindings : ProtectedStateTransition.Bindings protocol)
    (definitions : layouts.definitions = nativeDefinitions)
    (registered : layout.Registered nativeDefinitions)
    {mapping : LocationMap} {world : StoreTyping} {sources : List Dynamic.Value} {values : List Value}
    (represented : Arguments model mapping world bindings sources values)
    {administrative actualContext : Core.Context} {environment : Dynamic.Environment} {canonical logical actual : Environment}
    {heap : Dynamic.Heap} {store : Store} {ξ : Renaming}
    {allTypes : List Ty} {allValues : List Value} {named : Bool} {contextLocation : Location} {native : NativeFrame}
    (environments : DataHeap.EnvRepresents catalog mapping world administrative scope environment canonical nativeDefinitions)
    (heaps : GenericHeap.HeapRepresents model mapping world heap store)
    (sourceLayout : EnvironmentsAgree (Renaming.comp (Renaming.insertion (start + 1)) (Renaming.insertion start)) canonical logical)
    (actualLayout : EnvironmentsAgree ξ logical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext nativeDefinitions)
    (bundleSlot : logical[start]? = some (DataPatternValues.packValues allValues))
    (types_eq : types = allTypes)
    (bundleLength : allTypes.length = allValues.length)
    (valuesSelected : ∀ {index value}, values[index]? = some value → allValues[start + index]? = some value)
    (kinds : ∀ binding ∈ bindings, source.inputs.any (fun input => decide (input.id = binding.1.id)) = named)
    (reference : canonical[scope.length + (if named then 0 else 1) + globals]? = some (.cellRef layout.type contextLocation))
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode layout native))
    (unmapped : contextLocation ∉ mapping)
    (initial : protocol.State ⟨scope, mapping, world, heap, store, canonical⟩)
    (readyAt : ProtectedStateTransition.OrdinaryAllocation.ReadyAt producer.toOrdinary contextLocation native) :
    ∃ finalEnvironment finalHeap finalCanonical finalLogical finalActual finalStore finalMap finalWorld finalEmbedding,
      Dynamic.BindersAllocate environment heap (bindings.map Prod.fst) sources finalEnvironment finalHeap ∧
      DataHeap.EnvRepresents catalog finalMap finalWorld administrative
        (bindings.foldl (fun scope binding => (binding.1.id, binding.2) :: scope) scope)
        finalEnvironment finalCanonical nativeDefinitions ∧
      GenericHeap.HeapRepresents model finalMap finalWorld finalHeap finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧
      EnvironmentsAgree (DataMatchCoreAllocation.liftMany bindings.length (Renaming.comp (Renaming.insertion (start + 1)) (Renaming.insertion start)))
        finalCanonical finalLogical ∧
      EnvironmentsAgree finalEmbedding finalLogical finalActual ∧
      (∃ added : Environment, added.length = bindings.length ∧
        finalCanonical = added ++ canonical ∧ finalLogical = added ++ logical) ∧
      RuntimeEnvironmentHasTypes finalWorld finalActual (prefixContext bindings actualContext) nativeDefinitions ∧
      ContinuationSize false actual store (code.rename ξ) finalActual finalStore (body.rename finalEmbedding) ∧
      ∃ final : protocol.State
          ⟨bindings.foldl (fun scope binding => (binding.1.id, binding.2) :: scope) scope,
            finalMap, finalWorld, finalHeap, finalStore, finalCanonical⟩,
        protocol.Relates initial final ∧ Nonempty (ProtectedStateTransition.ReturnTo protocol scope canonical
          (bindings.foldl (fun scope binding => (binding.1.id, binding.2) :: scope) scope) finalCanonical) := by
  obtain ⟨finalEnvironment, finalHeap, finalCanonical, finalLogical, finalActual, finalStore, finalMap,
    finalWorld, finalEmbedding, allocated, finalEnvironments, finalHeaps, maps, worlds, preservation,
    finalSourceLayout, finalActualLayout, spine, finalTyped, continuation, finalState, related, restoration⟩ :=
    Stateful.prefix_cells_sized (allocationSource := source) tree (GenericHeap.OrdinaryCells.ordinary model) protocol
      producer.toCells stateBindings definitions registered represented environments (GenericHeap.ordinaryHeap_iff.mpr heaps)
      sourceLayout actualLayout actualTyped bundleSlot types_eq bundleLength valuesSelected kinds reference read unmapped initial readyAt
  exact ⟨finalEnvironment, finalHeap, finalCanonical, finalLogical, finalActual, finalStore, finalMap,
    finalWorld, finalEmbedding, allocated, finalEnvironments, GenericHeap.ordinaryHeap_iff.mp finalHeaps,
    maps, worlds, preservation, finalSourceLayout, finalActualLayout, spine, finalTyped, continuation,
    finalState, related, restoration⟩


/-- The original API erases only the reached witness and future restoration. -/
theorem prefix_sized {layouts : SourceCoreAllocationLayouts.Prepared}
    {owner : SourceSpecialization.SpecializationKey} {active : TypeSystem.Substitution}
    {layout : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
    {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error}
    {source : TypedSource} {types : List Ty} {output : Ty} {body : Expr}
    {scope : Scope} {start : Nat} {bindings : List Binding} {code : Expr}
    (tree : Tree layouts owner active layout globals onError source types output body scope start bindings code)
    {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection} {nativeDefinitions : DataEnvironment}
    {model : GenericHeap.PayloadModel catalog projects nativeDefinitions}
    (definitions : layouts.definitions = nativeDefinitions)
    (registered : layout.Registered nativeDefinitions)
    {mapping : LocationMap} {world : StoreTyping} {sources : List Dynamic.Value} {values : List Value}
    (represented : Arguments model mapping world bindings sources values)
    {administrative actualContext : Core.Context} {environment : Dynamic.Environment} {canonical logical actual : Environment}
    {heap : Dynamic.Heap} {store : Store} {ξ : Renaming}
    {allTypes : List Ty} {allValues : List Value} {named : Bool} {contextLocation : Location} {native : NativeFrame}
    (environments : DataHeap.EnvRepresents catalog mapping world administrative scope environment canonical nativeDefinitions)
    (heaps : GenericHeap.HeapRepresents model mapping world heap store)
    (sourceLayout : EnvironmentsAgree (Renaming.comp (Renaming.insertion (start + 1)) (Renaming.insertion start)) canonical logical)
    (actualLayout : EnvironmentsAgree ξ logical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext nativeDefinitions)
    (bundleSlot : logical[start]? = some (DataPatternValues.packValues allValues))
    (types_eq : types = allTypes)
    (bundleLength : allTypes.length = allValues.length)
    (valuesSelected : ∀ {index value}, values[index]? = some value → allValues[start + index]? = some value)
    (kinds : ∀ binding ∈ bindings, source.inputs.any (fun input => decide (input.id = binding.1.id)) = named)
    (reference : canonical[scope.length + (if named then 0 else 1) + globals]? = some (.cellRef layout.type contextLocation))
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode layout native))
    (unmapped : contextLocation ∉ mapping) :
    ∃ finalEnvironment finalHeap finalCanonical finalLogical finalActual finalStore finalMap finalWorld finalEmbedding,
      Dynamic.BindersAllocate environment heap (bindings.map Prod.fst) sources finalEnvironment finalHeap ∧
      DataHeap.EnvRepresents catalog finalMap finalWorld administrative
        (bindings.foldl (fun scope binding => (binding.1.id, binding.2) :: scope) scope)
        finalEnvironment finalCanonical nativeDefinitions ∧
      GenericHeap.HeapRepresents model finalMap finalWorld finalHeap finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧
      EnvironmentsAgree (DataMatchCoreAllocation.liftMany bindings.length (Renaming.comp (Renaming.insertion (start + 1)) (Renaming.insertion start)))
        finalCanonical finalLogical ∧
      EnvironmentsAgree finalEmbedding finalLogical finalActual ∧
      (∃ added : Environment, added.length = bindings.length ∧
        finalCanonical = added ++ canonical ∧ finalLogical = added ++ logical) ∧
      RuntimeEnvironmentHasTypes finalWorld finalActual (prefixContext bindings actualContext) nativeDefinitions ∧
      ContinuationSize false actual store (code.rename ξ) finalActual finalStore (body.rename finalEmbedding) := by
  obtain ⟨finalEnvironment, finalHeap, finalCanonical, finalLogical, finalActual, finalStore, finalMap, finalWorld,
    finalEmbedding, allocated, finalEnv, finalHeaps, maps, worlds, frame, finalSourceLayout, finalActualLayout,
    spine, finalTyped, agreement, _final, _related, _return⟩ :=
    Stateful.prefix_sized tree ProtectedStateTransition.OrdinaryAllocation.unitProtocol
      (ProtectedStateTransition.MarkedAllocation.unitProducer layouts layout model)
      ProtectedStateTransition.MatchPrefix.unitBindings definitions registered represented environments heaps
      sourceLayout actualLayout actualTyped bundleSlot types_eq bundleLength valuesSelected kinds reference read unmapped
      () (fun _ _ => True.intro)
  exact ⟨finalEnvironment, finalHeap, finalCanonical, finalLogical, finalActual, finalStore, finalMap, finalWorld,
    finalEmbedding, allocated, finalEnv, finalHeaps, maps, worlds, frame, finalSourceLayout, finalActualLayout,
    spine, finalTyped, agreement⟩

theorem prefix_typed {layouts : SourceCoreAllocationLayouts.Prepared}
    {owner : SourceSpecialization.SpecializationKey} {active : TypeSystem.Substitution}
    {layout : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
    {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error}
    {source : TypedSource} {types : List Ty} {output : Ty} {body : Expr}
    {scope : Scope} {start : Nat} {bindings : List Binding} {code : Expr}
    (tree : Tree layouts owner active layout globals onError source types output body scope start bindings code)
    {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection} {nativeDefinitions : DataEnvironment}
    {model : GenericHeap.PayloadModel catalog projects nativeDefinitions}
    (definitions : layouts.definitions = nativeDefinitions)
    (registered : layout.Registered nativeDefinitions)
    {mapping : LocationMap} {world : StoreTyping} {sources : List Dynamic.Value} {values : List Value}
    (represented : Arguments model mapping world bindings sources values)
    {administrative actualContext : Core.Context} {environment : Dynamic.Environment} {canonical logical actual : Environment}
    {heap : Dynamic.Heap} {store : Store} {ξ : Renaming}
    {allTypes : List Ty} {allValues : List Value} {named : Bool} {contextLocation : Location} {native : NativeFrame}
    (environments : DataHeap.EnvRepresents catalog mapping world administrative scope environment canonical nativeDefinitions)
    (heaps : GenericHeap.HeapRepresents model mapping world heap store)
    (sourceLayout : EnvironmentsAgree (Renaming.comp (Renaming.insertion (start + 1)) (Renaming.insertion start)) canonical logical)
    (actualLayout : EnvironmentsAgree ξ logical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext nativeDefinitions)
    (bundleSlot : logical[start]? = some (DataPatternValues.packValues allValues))
    (types_eq : types = allTypes)
    (bundleLength : allTypes.length = allValues.length)
    (valuesSelected : ∀ {index value}, values[index]? = some value → allValues[start + index]? = some value)
    (kinds : ∀ binding ∈ bindings, source.inputs.any (fun input => decide (input.id = binding.1.id)) = named)
    (reference : canonical[scope.length + (if named then 0 else 1) + globals]? = some (.cellRef layout.type contextLocation))
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode layout native))
    (unmapped : contextLocation ∉ mapping) :
    ∃ finalEnvironment finalHeap finalCanonical finalLogical finalActual finalStore finalMap finalWorld finalEmbedding,
      Dynamic.BindersAllocate environment heap (bindings.map Prod.fst) sources finalEnvironment finalHeap ∧
      DataHeap.EnvRepresents catalog finalMap finalWorld administrative
        (bindings.foldl (fun scope binding => (binding.1.id, binding.2) :: scope) scope)
        finalEnvironment finalCanonical nativeDefinitions ∧
      GenericHeap.HeapRepresents model finalMap finalWorld finalHeap finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧
      EnvironmentsAgree (DataMatchCoreAllocation.liftMany bindings.length (Renaming.comp (Renaming.insertion (start + 1)) (Renaming.insertion start)))
        finalCanonical finalLogical ∧
      EnvironmentsAgree finalEmbedding finalLogical finalActual ∧
      (∃ added : Environment, added.length = bindings.length ∧
        finalCanonical = added ++ canonical ∧ finalLogical = added ++ logical) ∧
      RuntimeEnvironmentHasTypes finalWorld finalActual (prefixContext bindings actualContext) nativeDefinitions ∧
      ContinuationAgreement actual store (code.rename ξ) finalActual finalStore (body.rename finalEmbedding) := by
  obtain ⟨finalEnvironment, finalHeap, finalCanonical, finalLogical, finalActual, finalStore, finalMap, finalWorld,
    finalEmbedding, allocated, finalEnv, finalHeaps, maps, worlds, frame, sourceLayout, actualLayout, spine, finalTyped, agreement⟩ :=
    prefix_sized tree definitions registered represented environments heaps sourceLayout actualLayout actualTyped
      bundleSlot types_eq bundleLength valuesSelected kinds reference read unmapped
  exact ⟨finalEnvironment, finalHeap, finalCanonical, finalLogical, finalActual, finalStore, finalMap, finalWorld,
    finalEmbedding, allocated, finalEnv, finalHeaps, maps, worlds, frame, sourceLayout, actualLayout, spine, finalTyped, agreement.agreement⟩


end Solcore.SourceSemantics.CoreLowering.CompatibleMatchTypedArmAllocation
end
