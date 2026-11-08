import Solcore.Frontend.SourceCore.GeneralFunctions
import Solcore.SourceSemantics.Dynamic.Primitive
import Solcore.SourceSemantics.CoreLowering.Internal.Data.Equality
import Solcore.Frontend.SourceCore.Internal.Entries
import Solcore.SourceSemantics.Dynamic.Internal.PatternCompleteness
import Solcore.Core.Correspondence

/-!
# Data: patterns

Pattern certificates, values, leaves, execution and decisions, and the certificates of equality values.
-/

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.DataPatternCertificates
/-! Static certificates extracted from the actual pattern compiler. The tree
records authentic compiler metadata checks and the emitted ordinary Core
syntax. It contains no source or Core evaluation assumptions. -/

set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.DataPatternCertificates
open Frontend Frontend.SourceInference
open SourceCoreDataMatches

abbrev Compilation := SourceCoreDataMatches.Context

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
    (definition : Core.DataDefinition) (children : List Pattern) (types : List Core.Ty) : Pattern :=
  let bindings := children.flatMap (·.bindings)
  let output := bundleType (bindings.map Prod.snd)
  let branches := definition.constructorPayloadTypes.zipIdx.map fun (_, index) =>
    if index = constructor.index then matchChildren output children (childValues types) [] else .inLeft output .unit
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
        (valid : SourceCoreGeneralTypes.lowerBinder compilation.checked source scope binder = .ok type) :
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
    | constructor {expected type instantiation arity constructor definition instructions rest children coreTypes}
        (projection : projected compilation source expected = .ok type)
        (result : instantiation.resultType = expected)
        (count : arity = instantiation.payloadTypes.length)
        (resolved : compilation.checked.catalog.resolveConstructor compilation.signatures instantiation = .ok constructor)
        (coreType : type = .namedData constructor.owner)
        (childrenTyped : Forest compilation source site span scope instantiation.payloadTypes instructions children rest)
        (projectedChildren : instantiation.payloadTypes.mapM (projected compilation source) = .ok coreTypes)
        (registered : compilation.checked.catalog.definitions[constructor.owner.index]? = some definition) :
        Tree compilation source site span scope expected (.constructor instantiation arity :: instructions)
          (constructorPattern type constructor definition children coreTypes) rest

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
            · cases valid : SourceCoreGeneralTypes.lowerBinder compilation.checked source scope binder with
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
              · cases resolved : compilation.checked.catalog.resolveConstructor compilation.signatures instantiation with
                | error error => simp [compileOne, projection, result, count, resolved, Except.mapError, bind, Except.bind] at accepted
                | ok constructor =>
                  by_cases same : type = .namedData constructor.owner
                  · cases compiled : compileMany compilation source site span scope fuel instantiation.payloadTypes instructions with
                    | error error => simp [compileOne, projection, result, count, resolved, Except.mapError, SourceCoreBasic.ensureType, same, compiled, bind, Except.bind] at accepted
                    | ok compiledPair =>
                      obtain ⟨children, after⟩ := compiledPair
                      cases projectedChildren : instantiation.payloadTypes.mapM (projected compilation source) with
                      | error error => simp [compileOne, projection, result, count, resolved, Except.mapError, SourceCoreBasic.ensureType, same, compiled, projectedChildren, bind, Except.bind] at accepted
                      | ok coreTypes =>
                        cases registered : compilation.checked.catalog.definitions[constructor.owner.index]? with
                        | none => simp [compileOne, projection, result, count, resolved, Except.mapError, SourceCoreBasic.ensureType, same, compiled, projectedChildren, registered, bind, Except.bind, pure, Except.pure] at accepted
                        | some definition =>
                          simp [compileOne, projection, result, count, resolved, Except.mapError, SourceCoreBasic.ensureType, same, compiled, projectedChildren, registered, bind, Except.bind, pure, Except.pure] at accepted
                          rcases accepted with ⟨rfl, rfl⟩
                          have tree := Tree.constructor projection result count resolved same
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
    (compiled : CertifiedPattern compilation.checked.catalog.definitions)
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
  | constructor projection result count resolved coreType children projectedChildren registered ih =>
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
  | constructor projection result count resolved coreType children projectedChildren registered ih =>
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

end Solcore.SourceSemantics.CoreLowering.DataPatternCertificates
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.DataPatternValues
/-! Proof-side data representation for matching. A nominal node retains the
entire source instantiation and the catalog constructor lookup; Core type
membership alone does not establish source constructor authenticity. The
initial relation covers finite scalar/product/nominal values. Function,
mapping, and proxy binder inputs need the corresponding general value bridge. -/

set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.DataPatternValues
open Core Frontend Frontend.SourceInference
open SourceCoreDataMatches DataEquality

inductive ListRel {α β : Type} (relation : α → β → Prop) : List α → List β → Prop where
  | nil : ListRel relation [] []
  | cons {head : α} {tail : List α} {value : β} {values : List β}
      (related : relation head value) (rest : ListRel relation tail values) :
      ListRel relation (head :: tail) (value :: values)

def packValues : List Value → Value
  | [] => .unit
  | [value] => value
  | value :: rest => .pair value (packValues rest)

mutual
  inductive ValueRep (catalog : SourceCoreDataCatalog.Catalog) : Dynamic.Value → Value → Prop where
    | unit : ValueRep catalog .unit .unit
    | bool (value : Bool) : ValueRep catalog (.bool value) (.bool value)
    | word (value : Word) : ValueRep catalog (.word value) (.word value)
    | integer (value : Int) : ValueRep catalog (.integer value) (.integer value)
    | product {left right : Dynamic.Value} {a b : Value}
        (leftRep : ValueRep catalog left a) (rightRep : ValueRep catalog right b) :
        ValueRep catalog (.product left right) (.pair a b)
    | constructed {instantiation : DataConstructorInstantiation} {tag : ConstructorId}
        {arguments : List Dynamic.Value} {values : List Value}
        (selected : catalog.constructor? instantiation = some tag)
        (payloads : ValuesRep catalog arguments values) :
        ValueRep catalog (.constructed instantiation arguments) (.constructed tag (packValues values))

  inductive ValuesRep (catalog : SourceCoreDataCatalog.Catalog) : List Dynamic.Value → List Value → Prop where
    | nil : ValuesRep catalog [] []
    | cons {source : Dynamic.Value} {value : Value} {sources : List Dynamic.Value} {values : List Value}
        (head : ValueRep catalog source value) (tail : ValuesRep catalog sources values) :
        ValuesRep catalog (source :: sources) (value :: values)
end

theorem ValuesRep.length {catalog : SourceCoreDataCatalog.Catalog} {sources : List Dynamic.Value} {values : List Value}
    (represented : ValuesRep catalog sources values) : sources.length = values.length := by
  induction sources generalizing values with
  | nil => cases represented; rfl
  | cons head tail ih => cases represented with
    | cons headRep tailRep => simp [ih tailRep]

theorem ValuesRep.pack {catalog : SourceCoreDataCatalog.Catalog} {sources : List Dynamic.Value} {values : List Value}
    (represented : ValuesRep catalog sources values) {source : Dynamic.Value}
    (packed : Dynamic.ValuesPack sources source) : ValueRep catalog source (packValues values) := by
  induction packed generalizing values with
  | nil => cases represented; exact .unit
  | singleton source => cases represented with
    | cons head tail => cases tail; exact head
  | cons packed ih => cases represented with
    | cons head tail =>
      cases tail with
      | cons second rest => exact .product head (ih (.cons second rest))

theorem bundle_evaluates {environment : Environment} {store : Store}
    {expressions : List Expr} {values : List Value}
    (evaluations : ListRel (fun expression value => Evaluates environment store expression value store) expressions values) :
    Evaluates environment store (bundle expressions) (packValues values) store := by
  induction evaluations with
  | nil => exact .unit
  | @cons expression expressions value values head tail ih =>
    cases expressions with
    | nil => cases tail; exact head
    | cons second rest => cases tail with
      | cons secondEval restEval => exact .pair head ih

theorem projectPacked_selects {environment : Environment} {expression : Expr} {types : List Ty} {values : List Value}
    (selected : Selects environment expression (packValues values)) (sameLength : types.length = values.length)
    (index : Nat) {value : Value} (found : values[index]? = some value) :
    Selects environment (SourceCoreDataExpressions.projectPacked index types expression) value := by
  induction types generalizing expression values index with
  | nil =>
    have empty : values = [] := by simpa using sameLength.symm
    subst values; simp at found
  | cons type types ih =>
    cases values with
    | nil => simp at sameLength
    | cons first values =>
      cases types with
      | nil =>
        have empty : values = [] := by simpa using (Nat.succ.inj sameLength).symm
        subst values
        cases index with
        | zero => simp at found; subst value; exact selected
        | succ => simp at found
      | cons second rest =>
        cases values with
        | nil => simp at sameLength
        | cons next values =>
          cases index with
          | zero =>
            simp at found; subst value
            simpa [SourceCoreDataExpressions.projectPacked] using Selects.first selected
          | succ index =>
            have tail := ih (Selects.second selected) (Nat.succ.inj sameLength) index (by simpa using found)
            simpa [SourceCoreDataExpressions.projectPacked] using tail

/-- Pure paths remain valid after introducing the successful child-bundle
binder used by the generated matcher. -/
theorem selects_weaken_list {environment : Environment} {expressions : List Expr} {values : List Value}
    (selected : ListRel (Selects environment) expressions values) (inserted : Value) :
    ListRel (Selects (inserted :: environment)) (expressions.map (·.weakenAt 0)) values := by
  induction selected with
  | nil => exact .nil
  | cons head tail ih => exact .cons (head.weaken inserted) ih

end Solcore.SourceSemantics.CoreLowering.DataPatternValues
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.DataPatternLeaves
/-! End-to-end preservation for the leaf pattern profile. The certificate is
extracted from compilePattern itself; the source evidence ledger has its
independent declarative meaning. No matcher execution premise is supplied by
the caller. Constructor/tuple composition is a subsequent proof layer. -/

set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.DataPatternLeaves
open Core Frontend Frontend.SourceInference
open SourceCoreDataMatches DataPatternCertificates DataPatternValues

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
inductive BindingsRep (catalog : SourceCoreDataCatalog.Catalog) :
    List (TypedBinder × Ty) → List (TypedBinder × Dynamic.Value) → List Value → Prop where
  | nil : BindingsRep catalog [] [] []
  | cons {binder : TypedBinder} {type : Ty} {source : Dynamic.Value} {value : Value}
      {binders : List (TypedBinder × Ty)} {sources : List (TypedBinder × Dynamic.Value)} {values : List Value}
      (head : ValueRep catalog source value) (tail : BindingsRep catalog binders sources values) :
      BindingsRep catalog ((binder, type) :: binders) ((binder, source) :: sources) (value :: values)

inductive OutcomeRep (catalog : SourceCoreDataCatalog.Catalog) (context : Context)
    (pattern : TypedMatchPattern) (compiled : Pattern) (sourceValue : Dynamic.Value) : Value → Prop where
  | matched {bindings : List (TypedBinder × Dynamic.Value)} {values : List Value}
      (meaning : Dynamic.PatternMatches context pattern sourceValue bindings)
      (represented : BindingsRep catalog compiled.bindings bindings values) :
      OutcomeRep catalog context pattern compiled sourceValue (.inRight .unit (packValues values))
  | noMatch (meaning : Dynamic.PatternDoesNotMatch context pattern sourceValue) :
      OutcomeRep catalog context pattern compiled sourceValue (.inLeft (bundleType compiled.bindingTypes) .unit)

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

theorem LiteralCode.constructs_word {compilation : Compilation} {context : Context}
    {literal : Syntax.CoreLiteralValue} {resolution : IntegerLiteralResolution}
    (valid : ContextValid compilation context) (target : resolution.targetType = .word)
    (meaning : NumericLiteralDenotes literal resolution.rawValue)
    (requirement : ∃ solved ∈ compilation.solvedRequirements, solved.id = resolution.requirement ∧
      solved.predicate = ProgramSignatures.builtinIntPredicate .word) :
    Dynamic.ResolvedIntegerLiteralConstructs context literal resolution (.word (Word.ofNatModulo resolution.rawValue)) := by
  cases resolution with
  | mk raw type requirementId =>
    dsimp at target
    subst type
    exact .word meaning (proves valid requirement)

theorem LiteralCode.constructs_integer {compilation : Compilation} {context : Context}
    {literal : Syntax.CoreLiteralValue} {resolution : IntegerLiteralResolution}
    (valid : ContextValid compilation context) (target : resolution.targetType = .integer)
    (meaning : NumericLiteralDenotes literal resolution.rawValue)
    (requirement : ∃ solved ∈ compilation.solvedRequirements, solved.id = resolution.requirement ∧
      solved.predicate = ProgramSignatures.builtinIntPredicate .integer) :
    Dynamic.ResolvedIntegerLiteralConstructs context literal resolution (.integer (Int.ofNat resolution.rawValue)) := by
  cases resolution with
  | mk raw type requirementId =>
    dsimp at target
    subst type
    exact .integer meaning (proves valid requirement)


private theorem projected_word (compilation : Compilation) (source : TypedSource) :
    projected compilation source TypeSystem.Ty.word = .ok .word := rfl
private theorem projected_integer (compilation : Compilation) (source : TypedSource) :
    projected compilation source TypeSystem.Ty.integer = .ok .integer := rfl

/-- Every accepted leaf pattern produces its independent source outcome in
finite Core steps, packs the exact ordered bindings, and preserves the store. -/
theorem leaf_preserves {compilation : Compilation} {context : Context}
    {source : TypedSource} {scope : Scope} {site : StatementId} {span : Syntax.SourceSpan}
    {expected : TypeSystem.Ty} {pattern : TypedMatchPattern} {compiled : Pattern}
    (certificate : Certificate compilation source scope site span expected pattern compiled)
    (valid : ContextValid compilation context) (leaf : LeafResolution pattern.resolution)
    {sourceValue : Dynamic.Value} {value : Value} {world : StoreTyping}
    (represented : ValueRep compilation.checked.catalog sourceValue value)
    (typed : RuntimeValueHasType world value compiled.type compilation.checked.catalog.definitions)
    (environment : Environment) (store : Store) :
    ∃ outcome, OutcomeRep compilation.checked.catalog context pattern compiled sourceValue outcome ∧
      Evaluates (value :: environment) store (.apply compiled.matcher (.var 0)) outcome store := by
  rcases pattern with ⟨spelling, patternType, resolution, requirements⟩
  obtain ⟨instructions, root, tree⟩ := certificate.tree
  obtain ⟨arity, instructionsEq, sourceRep⟩ := rootInstructions_sound compilation context valid.signatures
    spelling resolution instructions root
  subst instructions
  cases leaf with
  | wildcard =>
    cases tree with
    | wildcard projection =>
      refine ⟨.inRight .unit .unit, .matched (bindings := []) (values := []) ?_ .nil, ?_⟩
      · exact .intro sourceRep .wildcard
      exact SourceCoreDataMatches.wildcard_evaluates environment store _ value
  | binder binder =>
    cases tree with
    | binder projection sourceType binderValid =>
      refine ⟨.inRight .unit value, .matched (bindings := [(binder, sourceValue)]) (values := [value]) ?_ (.cons represented .nil), ?_⟩
      · exact .intro sourceRep .binder
      exact SourceCoreDataMatches.binder_evaluates environment store _ value
  | literal literal resolution =>
    cases tree with
    | literal projection validated =>
      have code := literalMatcher_sound compilation site span expected literal resolution _ validated
      cases code with
      | word target meaning retained =>
        have coreType := projection
        rw [projected_word] at coreType
        cases coreType
        cases typed with
        | word =>
          cases represented with
          | word =>
            rename_i actual
            have constructs := LiteralCode.constructs_word valid target meaning retained
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
        cases typed with
        | integer =>
          cases represented with
          | integer =>
            rename_i actual
            have constructs := LiteralCode.constructs_integer valid target meaning retained
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

/-- Public entry consumes actual compiler success; the structural certificate
is obtained internally and is never an extra caller obligation. -/
theorem compilePattern_leaf_preserves (compilation : Compilation) (fuel : Nat)
    (source : TypedSource) (scope : Scope) (site : StatementId) (span : Syntax.SourceSpan)
    (expected : TypeSystem.Ty) (pattern : TypedMatchPattern)
    (compiled : CertifiedPattern compilation.checked.catalog.definitions)
    (accepted : compilePattern compilation fuel source scope site span expected pattern = .ok compiled)
    (context : Context) (valid : ContextValid compilation context) (leaf : LeafResolution pattern.resolution)
    {sourceValue : Dynamic.Value} {value : Value} {world : StoreTyping}
    (represented : ValueRep compilation.checked.catalog sourceValue value)
    (typed : RuntimeValueHasType world value compiled.pattern.type compilation.checked.catalog.definitions)
    (environment : Environment) (store : Store) :
    ∃ outcome, OutcomeRep compilation.checked.catalog context pattern compiled.pattern sourceValue outcome ∧
      Evaluates (value :: environment) store (.apply compiled.pattern.matcher (.var 0)) outcome store :=
  leaf_preserves (certificate_of_compilePattern compilation fuel source scope site span expected pattern compiled accepted)
    valid leaf represented typed environment store

end Solcore.SourceSemantics.CoreLowering.DataPatternLeaves
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.DataPatternExecution
/-! Pure Core execution lemmas for the generated pattern combinators. These
composition facts are discharged structurally by the pattern certificate;
they do not introduce another executable pattern interpreter. -/

set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.DataPatternExecution
open Core Frontend Frontend.SourceInference
open SourceCoreDataMatches DataPatternValues DataPatternLeaves DataEquality

theorem ListRel.append {α β : Type} {relation : α → β → Prop}
    {a c : List α} {b d : List β} (left : ListRel relation a b) (right : ListRel relation c d) :
    ListRel relation (a ++ c) (b ++ d) := by
  induction left with
  | nil => exact right
  | cons head tail ih => exact .cons head ih

theorem ListRel.map {α β : Type} {relation other : α → β → Prop}
    {a : List α} {b : List β} (related : ListRel relation a b)
    (transform : ∀ x y, relation x y → other x y) : ListRel other a b := by
  induction related with
  | nil => exact .nil
  | cons head tail ih => exact .cons (transform _ _ head) ih

theorem ListRel.of_lookup {α β : Type} {relation : α → β → Prop} {a : List α} {b : List β}
    (length : a.length = b.length)
    (related : ∀ (index : Nat) x y, a[index]? = some x → b[index]? = some y → relation x y) :
    ListRel relation a b := by
  induction a generalizing b with
  | nil =>
    have empty : b = [] := by simpa using length.symm
    subst b; exact .nil
  | cons first rest ih =>
    cases b with
    | nil => simp at length
    | cons second tail =>
      refine .cons (related 0 first second rfl rfl) (ih (Nat.succ.inj length) ?_)
      intro index x y left right
      exact related (index + 1) x y left right

theorem projectionList_selects {environment : Environment} {expression : Expr}
    {types : List Ty} {values : List Value}
    (selected : Selects environment expression (packValues values)) (length : types.length = values.length) :
    ListRel (Selects environment)
      (types.zipIdx.map fun (_, index) => SourceCoreDataExpressions.projectPacked index types expression) values := by
  apply ListRel.of_lookup (by simpa using length)
  intro index projected value left right
  simp only [List.getElem?_map, List.getElem?_zipIdx, Nat.zero_add, Option.map_map] at left
  cases found : types[index]? with
  | none => simp [found] at left
  | some type =>
    simp [found] at left
    subst projected
    exact projectPacked_selects selected length index right

theorem BindingsRep.length {catalog : SourceCoreDataCatalog.Catalog}
    {binders : List (TypedBinder × Ty)} {sources : List (TypedBinder × Dynamic.Value)} {values : List Value}
    (represented : BindingsRep catalog binders sources values) : binders.length = values.length := by
  induction represented with
  | nil => rfl
  | cons head tail ih => simp [ih]

theorem BindingsRep.append {catalog : SourceCoreDataCatalog.Catalog}
    {a c : List (TypedBinder × Ty)} {b d : List (TypedBinder × Dynamic.Value)} {v w : List Value}
    (left : BindingsRep catalog a b v) (right : BindingsRep catalog c d w) :
    BindingsRep catalog (a ++ c) (b ++ d) (v ++ w) := by
  induction left with
  | nil => exact right
  | cons head tail ih => exact .cons head ih

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

theorem ValueRep.unpack {catalog : SourceCoreDataCatalog.Catalog}
    {sources : List Dynamic.Value} {source : Dynamic.Value} {value : Value}
    (packing : Dynamic.ValuesPack sources source) (represented : ValueRep catalog source value) :
    ∃ values, ValuesRep catalog sources values ∧ value = packValues values := by
  induction packing generalizing value with
  | nil => cases represented; exact ⟨[], .nil, rfl⟩
  | singleton source => exact ⟨[value], .cons represented .nil, rfl⟩
  | @cons first second rest packed tail ih =>
    cases represented with
    | product left right =>
      obtain ⟨values, represented, same⟩ := ih right
      cases values with
      | nil => have length := represented.length; simp at length
      | cons next values =>
        refine ⟨_ :: next :: values, .cons left represented, ?_⟩
        simp only [packValues]
        rw [same]

end Solcore.SourceSemantics.CoreLowering.DataPatternExecution
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.DataPatternSuccess
/-! Independent successful source matching implies finite execution of the
actual compiled matcher, including arbitrary finite nominal/tuple nesting.
Constructor metadata agreement is supplied by Dynamic.PatternMatches and the
compiler authenticates the selected pattern constructor against its catalog. -/

set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.DataPatternSuccess
open Core Frontend Frontend.SourceInference
open SourceCoreDataMatches DataPatternCertificates DataPatternValues DataPatternLeaves DataPatternExecution DataEquality

theorem projectionList_length {compilation : Compilation} {source : TypedSource}
    {types : List TypeSystem.Ty} {coreTypes : List Ty}
    (projected : types.mapM (SourceCoreDataMatches.projected compilation source) = .ok coreTypes) :
    types.length = coreTypes.length := by
  induction types generalizing coreTypes with
  | nil => simp [List.mapM_nil, pure, Except.pure] at projected; subst coreTypes; rfl
  | cons type types ih =>
    cases first : SourceCoreDataMatches.projected compilation source type with
    | error error => simp [List.mapM_cons, first, bind, Except.bind] at projected
    | ok coreType =>
      cases rest : types.mapM (SourceCoreDataMatches.projected compilation source) with
      | error error => simp [List.mapM_cons, first, rest, bind, Except.bind] at projected
      | ok tail =>
        simp [List.mapM_cons, first, rest, bind, Except.bind, pure, Except.pure] at projected
        subst coreTypes
        simp [ih rest]

private theorem constructorLookup_agrees {catalog : SourceCoreDataCatalog.Catalog}
    {actual expected : DataConstructorInstantiation}
    (agree : Dynamic.ConstructorInstantiationsAgree actual expected) :
    catalog.constructor? actual = catalog.constructor? expected := by
  simp [SourceCoreDataCatalog.Catalog.constructor?, agree.constructor_eq, agree.result_type_eq]

private theorem literal_success {compilation : Compilation} {context : Context}
    {literal : Syntax.CoreLiteralValue} {resolution : IntegerLiteralResolution} {expected : TypeSystem.Ty}
    {matcher : Expr} {source : Dynamic.Value} {value : Value} (type : Ty)
    (code : LiteralCode compilation literal resolution expected matcher)
    (constructed : Dynamic.ResolvedIntegerLiteralConstructs context literal resolution source)
    (represented : ValueRep compilation.checked.catalog source value) :
    MatcherRuns ⟨type, [], [resolution.requirement], matcher⟩ value [] := by
  cases constructed with
  | word meaning evidence =>
    cases code with
    | word target numeric retained =>
      cases represented
      intro environment store expression selected
      exact .apply .lambda (selected.evaluates store)
        (.ifTrue (.binary (.var rfl) .word (by simp [BinaryOp.apply])) (.inRight .unit))
    | integer target => cases target
  | integer meaning evidence =>
    cases code with
    | word target => cases target
    | integer target numeric retained =>
      cases represented
      intro environment store expression selected
      exact .apply .lambda (selected.evaluates store)
        (.ifTrue (.binary (.var rfl) .integer (by simp [BinaryOp.apply])) (.inRight .unit))

/-- A successful source prefix can be consumed only over the same suffix as
the compiler certificate. The binder bundle remains ordered and unmodified. -/
def TreeSuccess (compilation : Compilation) (context : Context)
    (instructions : List MatchPatternInstruction) (pattern : Pattern) (rest : List MatchPatternInstruction) : Prop :=
  ∀ source value bindings sourceRest,
    ValueRep compilation.checked.catalog source value →
    Dynamic.PatternInstructionMatches context source instructions bindings sourceRest →
    ∃ values, sourceRest = rest ∧ BindingsRep compilation.checked.catalog pattern.bindings bindings values ∧
      MatcherRuns pattern value values

def ForestSuccess (compilation : Compilation) (context : Context) (types : List TypeSystem.Ty)
    (instructions : List MatchPatternInstruction) (patterns : List Pattern) (rest : List MatchPatternInstruction) : Prop :=
  ∀ sources values bindings sourceRest,
    ValuesRep compilation.checked.catalog sources values →
    sources.length = types.length →
    Dynamic.PatternInstructionsMatch context sources instructions bindings sourceRest →
    ∃ boundValues, sourceRest = rest ∧
      BindingsRep compilation.checked.catalog (patterns.flatMap (·.bindings)) bindings boundValues ∧
      ChildrenRun patterns values boundValues

theorem Tree.success {compilation : Compilation} {context : Context} {source : TypedSource}
    {site : StatementId} {span : Syntax.SourceSpan} {scope : Scope} {type : TypeSystem.Ty}
    {instructions rest : List MatchPatternInstruction} {pattern : Pattern}
    (tree : Tree compilation source site span scope type instructions pattern rest) :
    TreeSuccess compilation context instructions pattern rest := by
  induction tree using Tree.rec
      (motive_2 := fun types instructions patterns rest _ => ForestSuccess compilation context types instructions patterns rest) with
  | wildcard projection =>
    intro source value bindings sourceRest represented matched
    cases matched
    refine ⟨[], rfl, .nil, ?_⟩
    intro environment store expression selected
    exact .apply .lambda (selected.evaluates store) (.inRight .unit)
  | binder projection sourceType valid =>
    intro source value bindings sourceRest represented matched
    cases matched
    refine ⟨[value], rfl, .cons represented .nil, ?_⟩
    intro environment store expression selected
    exact .apply .lambda (selected.evaluates store) (.inRight (.var rfl))
  | literal projection validated =>
    intro sourceValue value bindings sourceRest represented matched
    cases matched with
    | integerLiteral construction =>
      exact ⟨[], rfl, .nil,
        literal_success _ (literalMatcher_sound compilation site span _ _ _ _ validated) construction represented⟩
  | @tuple expected coreType count types instructions rest children coreTypes projection unpacked childrenTree projectedChildren ih =>
    intro sourceValue value bindings sourceRest represented matched
    cases matched with
    | tuple packed arity matchedChildren =>
      obtain ⟨values, valuesRep, valueEq⟩ := ValueRep.unpack packed represented
      subst value
      obtain ⟨boundValues, restEq, bindingRep, childrenRun⟩ :=
        ih _ _ _ _ valuesRep (arity.trans (unpackTypes_length unpacked).symm) matchedChildren
      refine ⟨boundValues, restEq, bindingRep, ?_⟩
      intro environment store expression selected
      apply Evaluates.apply .lambda (selected.evaluates store)
      have length : coreTypes.length = values.length :=
        (projectionList_length projectedChildren).symm.trans
          ((unpackTypes_length unpacked).trans (arity.symm.trans valuesRep.length))
      have paths := projectionList_selects (environment := packValues values :: environment)
        (expression := .var 0) (.var rfl) length
      simpa [tuplePattern, childValues] using
        childrenRun (packValues values :: environment) store _ [] [] _ paths .nil
  | @constructor expected coreType instantiation count constructor definition instructions rest children coreTypes
      projection result arity resolved sameType childrenTree projectedChildren registered ih =>
    intro sourceValue value bindings sourceRest represented matched
    cases matched with
    | constructor agree countEq matchedChildren =>
      cases represented with
      | @constructed actual tag arguments values selected payloads =>
        have tagEq : _ = some constructor := (constructorLookup_agrees agree).trans
          (SourceCoreDataValues.resolveConstructor_lookup resolved)
        rw [selected] at tagEq
        cases tagEq
        obtain ⟨boundValues, restEq, bindingRep, childrenRun⟩ :=
          ih _ _ _ _ payloads (countEq.trans arity) matchedChildren
        refine ⟨boundValues, restEq, bindingRep, ?_⟩
        intro environment store expression selectedValue
        apply Evaluates.apply .lambda (selectedValue.evaluates store)
        obtain ⟨payloadType, payloadLookup⟩ := SourceCoreDataValues.resolveConstructor_registered resolved
        have lookup : definition.constructorPayloadTypes[constructor.index]? = some payloadType := by
          simpa [DataEnvironment.lookupConstructorPayloadType?, DataEnvironment.lookupDataType?, registered] using payloadLookup
        have branchLookup : (definition.constructorPayloadTypes.zipIdx.map fun (_, index) =>
            if index = constructor.index then matchChildren (bundleType ((children.flatMap (·.bindings)).map Prod.snd)) children (childValues coreTypes) []
            else .inLeft (bundleType ((children.flatMap (·.bindings)).map Prod.snd)) .unit)[constructor.index]? =
            some (matchChildren (bundleType ((children.flatMap (·.bindings)).map Prod.snd)) children (childValues coreTypes) []) := by
          simp [List.getElem?_map, List.getElem?_zipIdx, lookup]
        apply Evaluates.matchData (.var rfl) rfl branchLookup
        have length := (projectionList_length projectedChildren).symm.trans ((countEq.trans arity).symm.trans payloads.length)
        have paths := projectionList_selects
          (environment := packValues values :: .constructed constructor (packValues values) :: environment)
          (expression := .var 0) (Selects.var rfl) length
        simpa [constructorPattern, childValues] using childrenRun _ store _ [] [] _ paths .nil
  | nil =>
    intro sources values bindings sourceRest represented length matched
    have empty : sources = [] := by simpa using length
    subst sources
    cases represented
    cases matched
    exact ⟨[], rfl, .nil, ChildrenRun.nil⟩
  | @cons type types instructions afterHead rest head tail headTree tailTree headIH tailIH =>
    intro sources values bindings sourceRest represented length matched
    cases represented with
    | nil => simp at length
    | cons valueRep valuesRep =>
      cases matched with
      | cons headMatch tailMatch =>
        obtain ⟨headValues, headRestEq, headBindings, headRun⟩ := headIH _ _ _ _ valueRep headMatch
        subst headRestEq
        obtain ⟨tailValues, tailRestEq, tailBindings, tailRun⟩ := tailIH _ _ _ _ valuesRep (Nat.succ.inj length) tailMatch
        exact ⟨headValues ++ tailValues, tailRestEq, BindingsRep.append headBindings tailBindings,
          ChildrenRun.cons (by simpa [Pattern.bindingTypes] using BindingsRep.length headBindings) headRun tailRun⟩


/-- Accepted compilation preserves every independently derived successful
source match in the scalar/product/nominal value profile. No child evaluator
correctness premise is required. -/
theorem compilePattern_success_preserves (compilation : Compilation) (fuel : Nat)
    (source : TypedSource) (scope : Scope) (site : StatementId) (span : Syntax.SourceSpan)
    (expected : TypeSystem.Ty) (pattern : TypedMatchPattern)
    (compiled : CertifiedPattern compilation.checked.catalog.definitions)
    (accepted : compilePattern compilation fuel source scope site span expected pattern = .ok compiled)
    (context : Context) (signatures : context.signatures = compilation.signatures)
    {sourceValue : Dynamic.Value} {value : Value} {bindings : List (TypedBinder × Dynamic.Value)}
    (represented : ValueRep compilation.checked.catalog sourceValue value)
    (matched : Dynamic.PatternMatches context pattern sourceValue bindings) :
    ∃ values, BindingsRep compilation.checked.catalog compiled.pattern.bindings bindings values ∧
      MatcherRuns compiled.pattern value values := by
  have certificate := certificate_of_compilePattern compilation fuel source scope site span expected pattern compiled accepted
  obtain ⟨instructions, root, tree⟩ := certificate.tree
  obtain ⟨arity, instructionsEq, sourceRep⟩ := rootInstructions_sound compilation context signatures _ _ _ root
  cases matched with
  | intro matchedSource instructionMatch =>
    have arityEq := Dynamic.MatchPatternSourceRepresents.rootArity_eq sourceRep matchedSource
    subst arityEq
    subst instructions
    obtain ⟨values, _, bindingsRep, evaluates⟩ := Tree.success tree sourceValue value bindings [] represented instructionMatch
    exact ⟨values, bindingsRep, evaluates⟩

/-- The actual machine eventually returns the ordered successful binder bundle;
any completed run returns that same bundle and the unchanged input store. -/
theorem compilePattern_success_run (compilation : Compilation) (compilationFuel : Nat)
    (source : TypedSource) (scope : Scope) (site : StatementId) (span : Syntax.SourceSpan)
    (expected : TypeSystem.Ty) (pattern : TypedMatchPattern)
    (compiled : CertifiedPattern compilation.checked.catalog.definitions)
    (accepted : compilePattern compilation compilationFuel source scope site span expected pattern = .ok compiled)
    (context : Context) (signatures : context.signatures = compilation.signatures)
    {sourceValue : Dynamic.Value} {value : Value} {bindings : List (TypedBinder × Dynamic.Value)}
    (represented : ValueRep compilation.checked.catalog sourceValue value)
    (matched : Dynamic.PatternMatches context pattern sourceValue bindings)
    (environment : Environment) (store : Store) :
    ∃ values, BindingsRep compilation.checked.catalog compiled.pattern.bindings bindings values ∧
      (∃ required, ∀ fuel, required ≤ fuel →
        runStateful fuel (State.initial (.apply compiled.pattern.matcher (.var 0)) (value :: environment) store) =
          .done (.inRight .unit (packValues values)) store) ∧
      (∀ fuel outcome finalStore,
        runStateful fuel (State.initial (.apply compiled.pattern.matcher (.var 0)) (value :: environment) store) =
          .done outcome finalStore → outcome = .inRight .unit (packValues values) ∧ finalStore = store) := by
  obtain ⟨values, bindingsRep, executes⟩ := compilePattern_success_preserves compilation compilationFuel
    source scope site span expected pattern compiled accepted context signatures represented matched
  have evaluation := executes (value :: environment) store (.var 0) (.var rfl)
  exact ⟨values, bindingsRep, evaluation_runStateful_complete_with_sufficient_fuel evaluation,
    fun _ _ _ ran => evaluation_deterministic (runStateful_evaluation_sound ran) evaluation⟩

end Solcore.SourceSemantics.CoreLowering.DataPatternSuccess
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.DataPatternTypedValues
/-! A closed value profile for complete pattern decisions. Unlike Core typing,
this relation authenticates every nominal constructor's retained source
metadata and recursively checks its payload type list. Function, mapping,
proxy and staged values are outside this proof profile. -/

set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.DataPatternTypedValues
open Core Frontend Frontend.SourceInference
open DataPatternValues

mutual
  inductive TypedValueRep (catalog : SourceCoreDataCatalog.Catalog) (signatures : ProgramSignatures) :
      TypeSystem.Ty → Dynamic.Value → Value → Prop where
    | unit : TypedValueRep catalog signatures .unit .unit .unit
    | bool (value : Bool) : TypedValueRep catalog signatures .bool (.bool value) (.bool value)
    | word (value : Word) : TypedValueRep catalog signatures .word (.word value) (.word value)
    | integer (value : Int) : TypedValueRep catalog signatures .integer (.integer value) (.integer value)
    | product {leftType rightType : TypeSystem.Ty} {left right : Dynamic.Value} {a b : Value}
        (first : TypedValueRep catalog signatures leftType left a)
        (second : TypedValueRep catalog signatures rightType right b) :
        TypedValueRep catalog signatures (.product leftType rightType) (.product left right) (.pair a b)
    | constructed {type : TypeSystem.Ty} {metadata : DataConstructorInstantiation} {tag : ConstructorId}
        {declaration : Resolved.DeclarationId} {typeArguments : List TypeSystem.Ty}
        {arguments : List Dynamic.Value} {values : List Value}
        (nominal : SourceCoreDataCatalog.nominalParts type = some (declaration, typeArguments))
        (result : metadata.resultType = type)
        (authenticated : catalog.resolveConstructor signatures metadata = .ok tag)
        (payloads : TypedValuesRep catalog signatures metadata.payloadTypes arguments values) :
        TypedValueRep catalog signatures type (.constructed metadata arguments) (.constructed tag (packValues values))
  inductive TypedValuesRep (catalog : SourceCoreDataCatalog.Catalog) (signatures : ProgramSignatures) :
      List TypeSystem.Ty → List Dynamic.Value → List Value → Prop where
    | nil : TypedValuesRep catalog signatures [] [] []
    | cons {type : TypeSystem.Ty} {source : Dynamic.Value} {value : Value}
        {types : List TypeSystem.Ty} {sources : List Dynamic.Value} {values : List Value}
        (head : TypedValueRep catalog signatures type source value)
        (tail : TypedValuesRep catalog signatures types sources values) :
        TypedValuesRep catalog signatures (type :: types) (source :: sources) (value :: values)
end

theorem TypedValueRep.erase {catalog : SourceCoreDataCatalog.Catalog} {signatures : ProgramSignatures}
    {type : TypeSystem.Ty} {source : Dynamic.Value} {value : Value}
    (represented : TypedValueRep catalog signatures type source value) : ValueRep catalog source value := by
  induction represented using TypedValueRep.rec
      (motive_2 := fun _ sources values _ => ValuesRep catalog sources values) with
  | unit => exact .unit
  | bool => exact .bool _
  | word => exact .word _
  | integer => exact .integer _
  | product _ _ first second => exact .product first second
  | constructed _ _ authenticated _ ih => exact .constructed (SourceCoreDataValues.resolveConstructor_lookup authenticated) ih
  | nil => exact .nil
  | cons _ _ head tail => exact .cons head tail

theorem TypedValuesRep.erase {catalog : SourceCoreDataCatalog.Catalog} {signatures : ProgramSignatures}
    {types : List TypeSystem.Ty} {sources : List Dynamic.Value} {values : List Value}
    (represented : TypedValuesRep catalog signatures types sources values) : ValuesRep catalog sources values := by
  induction types generalizing sources values with
  | nil => cases represented; exact .nil
  | cons type types ih => cases represented with
    | cons head tail => exact .cons (TypedValueRep.erase head) (ih tail)

theorem TypedValuesRep.length {catalog : SourceCoreDataCatalog.Catalog} {signatures : ProgramSignatures}
    {types : List TypeSystem.Ty} {sources : List Dynamic.Value} {values : List Value}
    (represented : TypedValuesRep catalog signatures types sources values) :
    types.length = sources.length ∧ types.length = values.length := by
  induction types generalizing sources values with
  | nil => cases represented; exact ⟨rfl, rfl⟩
  | cons type types ih => cases represented with
    | cons head tail => have result := ih tail; exact ⟨congrArg Nat.succ result.1, congrArg Nat.succ result.2⟩

theorem TypedValueRep.unpack {catalog : SourceCoreDataCatalog.Catalog} {signatures : ProgramSignatures}
    {type : TypeSystem.Ty} {source : Dynamic.Value} {value : Value} {count : Nat} {types : List TypeSystem.Ty}
    (unpacked : SourceCoreDataMatches.unpackTypes count type = some types)
    (represented : TypedValueRep catalog signatures type source value) :
    ∃ sources values, TypedValuesRep catalog signatures types sources values ∧
      Dynamic.ValuesPack sources source ∧ value = packValues values := by
  induction count using Nat.strongRecOn generalizing type source value types with
  | ind count ih =>
    cases count with
    | zero =>
      simp only [SourceCoreDataMatches.unpackTypes] at unpacked
      split at unpacked
      · rename_i same
        subst type
        cases unpacked
        cases represented with
        | unit => exact ⟨[], [], .nil, .nil, rfl⟩
        | constructed nominal => simp [SourceCoreDataCatalog.nominalParts, TypeSystem.Ty.unit] at nominal
      · contradiction
    | succ count =>
      cases count with
      | zero =>
        cases unpacked
        exact ⟨[source], [value], .cons represented .nil, .singleton _, rfl⟩
      | succ count =>
        cases type <;> simp only [SourceCoreDataMatches.unpackTypes] at unpacked
        all_goals try contradiction
        rename_i leftType rightType
        cases rest : SourceCoreDataMatches.unpackTypes (count + 1) rightType with
        | none => simp [rest] at unpacked
        | some tail =>
          simp [rest] at unpacked
          subst types
          cases represented with
          | constructed nominal => simp [SourceCoreDataCatalog.nominalParts] at nominal
          | product first second =>
            obtain ⟨sources, values, representation, packing, valueEq⟩ := ih (count + 1) (by omega) rest second
            have nonempty : sources ≠ [] := by
              have length := (TypedValuesRep.length representation).1
              have typeLength := DataPatternCertificates.unpackTypes_length rest
              intro empty
              rw [empty] at length
              simp only [List.length_nil] at length
              omega
            cases sources with
            | nil => contradiction
            | cons head sources =>
              cases values with
              | nil =>
                have lengths := TypedValuesRep.length representation
                simp only [List.length_nil, List.length_cons] at lengths
                omega
              | cons value values =>
                exact ⟨_ :: head :: sources, _ :: value :: values, .cons first representation,
                  .cons packing, by simp only [packValues]; rw [valueEq]⟩

end Solcore.SourceSemantics.CoreLowering.DataPatternTypedValues
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.DataPatternAuthenticity
/-! Source metadata facts from the actual catalog authenticator. Equality of a
Core tag alone is insufficient; both source instantiations must be accepted. -/

set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.DataPatternAuthenticity
open Core Frontend Frontend.SourceInference

private theorem bind_ok {α β ε : Type} {first : Except ε α} {next : α → Except ε β} {value : β}
    (accepted : first >>= next = .ok value) : ∃ input, first = .ok input ∧ next input = .ok value := by
  cases first <;> simp_all [bind, Except.bind]

/-- A lookup retains the exact source constructor at the returned index. -/
theorem constructor_lookup {catalog : SourceCoreDataCatalog.Catalog}
    {metadata : DataConstructorInstantiation} {tag : ConstructorId}
    (selected : catalog.constructor? metadata = some tag) :
    ∃ entry, catalog.entries[tag.owner.index]? = some entry ∧
      entry.constructors[tag.index]? = some metadata.constructor := by
  unfold SourceCoreDataCatalog.Catalog.constructor? at selected
  cases identityEq : catalog.identity? metadata.resultType with
  | none => simp [identityEq] at selected
  | some identity =>
    cases entryLookup : catalog.entries[identity.index]? with
    | none => simp [identityEq, entryLookup] at selected
    | some entry =>
      cases constructorLookup : entry.constructors.zipIdx.find? (fun item => decide (item.1 = metadata.constructor)) with
      | none => simp [identityEq, entryLookup, constructorLookup] at selected
      | some item =>
        have found := List.mem_of_find?_eq_some constructorLookup
        have same : item.1 = metadata.constructor := by simpa using List.find?_some constructorLookup
        have found := List.mk_mem_zipIdx_iff_getElem?.mp found
        simp only [identityEq, entryLookup, constructorLookup, bind, Option.bind, pure, Option.some.injEq] at selected
        subst tag
        refine ⟨entry, entryLookup, ?_⟩
        simpa [same] using found

theorem constructor_identity {catalog : SourceCoreDataCatalog.Catalog}
    {metadata : DataConstructorInstantiation} {tag : ConstructorId}
    (selected : catalog.constructor? metadata = some tag) :
    catalog.identity? metadata.resultType = some tag.owner := by
  unfold SourceCoreDataCatalog.Catalog.constructor? at selected
  cases identityEq : catalog.identity? metadata.resultType with
  | none => simp [identityEq] at selected
  | some identity =>
    cases entryLookup : catalog.entries[identity.index]? with
    | none => simp [identityEq, entryLookup] at selected
    | some entry =>
      cases constructorLookup : entry.constructors.zipIdx.find? (fun item => decide (item.1 = metadata.constructor)) with
      | none => simp [identityEq, entryLookup, constructorLookup] at selected
      | some item =>
        simp only [identityEq, entryLookup, constructorLookup, bind, Option.bind, pure, Option.some.injEq] at selected
        subst tag
        rfl

theorem constructor_eq_of_same_tag {catalog : SourceCoreDataCatalog.Catalog}
    {left right : DataConstructorInstantiation} {tag : ConstructorId}
    (leftSelected : catalog.constructor? left = some tag)
    (rightSelected : catalog.constructor? right = some tag) : left.constructor = right.constructor := by
  obtain ⟨leftEntry, leftLookup, leftConstructor⟩ := constructor_lookup leftSelected
  obtain ⟨rightEntry, rightLookup, rightConstructor⟩ := constructor_lookup rightSelected
  have entries := leftLookup.symm.trans rightLookup
  cases entries
  exact Option.some.inj (leftConstructor.symm.trans rightConstructor)

inductive MetadataFacts (signatures : ProgramSignatures) (metadata : DataConstructorInstantiation) : Prop where
  | mk (signature : ProgramDataSignature) (constructor : ProgramDataConstructorSignature)
    (signatureSelected : signatures.dataTypes.filter (fun item => decide (item.id = metadata.constructor.dataType)) = [signature])
    (constructorSelected : signature.constructors.filter (fun item => decide (item.id = metadata.constructor)) = [constructor])
    (parameters : metadata.parameterSubstitution.map Prod.fst = signature.parameters)
    (result : metadata.resultType = TypeSystem.Ty.nominal signature.id (metadata.parameterSubstitution.map Prod.snd))
    (payloads : metadata.payloadTypes = constructor.payloadTypes.map metadata.parameterSubstitution.apply) :
    MetadataFacts signatures metadata

theorem metadataFacts {catalog : SourceCoreDataCatalog.Catalog}
    {signatures : ProgramSignatures} {metadata : DataConstructorInstantiation} {tag : ConstructorId}
    (accepted : catalog.resolveConstructor signatures metadata = .ok tag) : MetadataFacts signatures metadata := by
  unfold SourceCoreDataCatalog.Catalog.resolveConstructor at accepted
  obtain ⟨signature, selected, accepted⟩ := bind_ok accepted
  change (match signatures.dataTypes.filter (fun item => decide (item.id = metadata.constructor.dataType)) with
    | [] => Except.error (SourceCoreDataCatalog.Error.missingData metadata.constructor.dataType)
    | [item] => .ok item
    | _ => .error (SourceCoreDataCatalog.Error.ambiguousData metadata.constructor.dataType)) = .ok signature at selected
  split at selected
  · cases selected
  · rename_i singleton
    cases selected
    simp only [pure, Except.pure, bind, Except.bind, throw] at accepted
    split at accepted
    · rename_i constructor constructorSelected
      split at accepted
      · rename_i parameters
        split at accepted
        · split at accepted
          · rename_i result
            split at accepted
            · rename_i payloads
              exact ⟨_, constructor, singleton, constructorSelected, parameters, result, payloads⟩
            · cases accepted
          · cases accepted
        · cases accepted
      · cases accepted
    · cases accepted
  · cases selected


private theorem nominalParts_applyMany (head : TypeSystem.Ty) (arguments : List TypeSystem.Ty)
    (declaration : Resolved.DeclarationId) (previous : List TypeSystem.Ty)
    (parts : SourceCoreDataCatalog.nominalParts head = some (declaration, previous)) :
    SourceCoreDataCatalog.nominalParts (TypeSystem.Ty.applyMany head arguments) = some (declaration, previous ++ arguments) := by
  unfold TypeSystem.Ty.applyMany
  induction arguments generalizing head previous with
  | nil => simpa using parts
  | cons argument arguments ih =>
    simp only [List.foldl_cons]
    have next : SourceCoreDataCatalog.nominalParts (.application head argument) = some (declaration, previous ++ [argument]) := by
      simp [SourceCoreDataCatalog.nominalParts, parts]
    simpa [List.append_assoc] using ih _ _ next

theorem nominalParts_nominal (declaration : Resolved.DeclarationId) (arguments : List TypeSystem.Ty) :
    SourceCoreDataCatalog.nominalParts (TypeSystem.Ty.nominal declaration arguments) = some (declaration, arguments) := by
  simpa [TypeSystem.Ty.nominal] using nominalParts_applyMany (.constructor (.declaration declaration)) arguments declaration [] rfl

/-- Within one source result type, the same authenticated Core tag denotes the
same source constructor and instantiated payload list. No catalog-wide
injectivity or source typing is inferred from a Core runtime type alone. -/
theorem resolveConstructor_agree {catalog : SourceCoreDataCatalog.Catalog}
    {signatures : ProgramSignatures} {left right : DataConstructorInstantiation} {tag : ConstructorId}
    (leftAccepted : catalog.resolveConstructor signatures left = .ok tag)
    (rightAccepted : catalog.resolveConstructor signatures right = .ok tag)
    (sameResult : left.resultType = right.resultType) :
    Dynamic.ConstructorInstantiationsAgree left right := by
  have constructors := constructor_eq_of_same_tag
    (SourceCoreDataValues.resolveConstructor_lookup leftAccepted)
    (SourceCoreDataValues.resolveConstructor_lookup rightAccepted)
  obtain ⟨leftSignature, leftConstructor, leftSignatureSelected, leftConstructorSelected, leftParameters, leftResult, leftPayloads⟩ := metadataFacts leftAccepted
  obtain ⟨rightSignature, rightConstructor, rightSignatureSelected, rightConstructorSelected, rightParameters, rightResult, rightPayloads⟩ := metadataFacts rightAccepted
  rw [constructors] at leftSignatureSelected leftConstructorSelected
  have signatureSame : leftSignature = rightSignature := (List.singleton_inj.mp (leftSignatureSelected.symm.trans rightSignatureSelected))
  subst rightSignature
  have constructorSame : leftConstructor = rightConstructor := List.singleton_inj.mp (leftConstructorSelected.symm.trans rightConstructorSelected)
  subst rightConstructor
  have arguments : left.parameterSubstitution.map Prod.snd = right.parameterSubstitution.map Prod.snd := by
    have equal := congrArg SourceCoreDataCatalog.nominalParts (leftResult.symm.trans (sameResult.trans rightResult))
    simpa [nominalParts_nominal] using equal
  have substitution : left.parameterSubstitution = right.parameterSubstitution := by
    have first := List.zip_of_prod leftParameters (rfl : left.parameterSubstitution.map Prod.snd = _)
    have second := List.zip_of_prod rightParameters (rfl : right.parameterSubstitution.map Prod.snd = _)
    rw [arguments] at first
    exact first.trans second.symm
  exact ⟨constructors, leftPayloads.trans (by rw [substitution]; exact rightPayloads.symm), sameResult⟩

end Solcore.SourceSemantics.CoreLowering.DataPatternAuthenticity
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.DataValueTyping
/-! Catalog projection and Core runtime typing for the authenticated finite
scalar/product/nominal value relation used by pattern and member proofs. The
proof checks nominal payload types through the actual constructor resolver;
Core typing alone is not used to authenticate source metadata. -/

set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.DataValueTyping
open Core Frontend Frontend.SourceInference DataPatternValues DataPatternTypedValues

private theorem bind_ok {α β ε : Type} {first : Except ε α} {next : α → Except ε β} {value : β}
    (accepted : first >>= next = .ok value) : ∃ input, first = .ok input ∧ next input = .ok value := by
  cases first <;> simp_all [bind, Except.bind]

/-- Constructor authentication includes the exact packed payload type stored
in the Core data environment. -/
theorem resolveConstructor_payload {catalog : SourceCoreDataCatalog.Catalog}
    {signatures : ProgramSignatures} {metadata : DataConstructorInstantiation} {tag : ConstructorId}
    (accepted : catalog.resolveConstructor signatures metadata = .ok tag) :
    ∃ types, metadata.payloadTypes.mapM catalog.project = .ok types ∧
      catalog.definitions.lookupConstructorPayloadType? tag = some (SourceCoreDataMatches.bundleType types) := by
  unfold SourceCoreDataCatalog.Catalog.resolveConstructor at accepted
  obtain ⟨signature, _, accepted⟩ := bind_ok accepted
  simp only [pure, Except.pure, bind, Except.bind, throw] at accepted
  split at accepted
  · split at accepted
    · split at accepted
      · split at accepted
        · split at accepted
          · split at accepted
            · rename_i tag' selected
              cases projected : metadata.payloadTypes.mapM catalog.project with
              | error error => simp [projected] at accepted
              | ok types =>
                simp only [projected] at accepted
                split at accepted
                · rename_i payload
                  cases accepted
                  refine ⟨types, rfl, payload.trans ?_⟩
                  apply congrArg some
                  clear projected payload
                  induction types with
                  | nil => rfl
                  | cons type rest ih =>
                    cases rest with
                    | nil => rfl
                    | cons => exact congrArg (Ty.product type) ih
                · cases accepted
            · cases accepted
          · cases accepted
        · cases accepted
      · cases accepted
    · cases accepted
  · cases accepted

private theorem project_nominal {catalog : SourceCoreDataCatalog.Catalog}
    {type : TypeSystem.Ty} {declaration : Resolved.DeclarationId} {arguments : List TypeSystem.Ty}
    {identity : DataTypeId}
    (nominal : SourceCoreDataCatalog.nominalParts type = some (declaration, arguments))
    (selected : catalog.identity? type = some identity) : catalog.project type = .ok (.namedData identity) := by
  cases type with
  | constructor constructor =>
    cases constructor with
    | declaration declaration => simp [SourceCoreDataCatalog.Catalog.project, selected]
    | builtin builtin => cases builtin <;> simp [SourceCoreDataCatalog.nominalParts] at nominal
  | application function argument => simp [SourceCoreDataCatalog.Catalog.project, selected]
  | _ =>
    simp [SourceCoreDataCatalog.nominalParts] at nominal

/-- A packed list is unit, a singleton, or a right-associated product, exactly
as the data constructor catalog and the pattern compiler require. -/
private theorem pack_typed {world : StoreTyping} {definitions : DataEnvironment}
    {types : List Ty} {values : List Value}
    (typed : ListRel (fun value type => RuntimeValueHasType world value type definitions) values types) :
    RuntimeValueHasType world (packValues values) (SourceCoreDataMatches.bundleType types) definitions := by
  induction typed with
  | nil => exact .unit
  | @cons value type values types head tail ih =>
    cases tail with
    | nil => exact head
    | cons second rest => exact .pair head ih

/-- The finite relation does not contain raw references or closure code. Its
runtime typing therefore holds in every Core world, including worlds with
administrative function cells. -/
theorem TypedValueRep.project_typed {catalog : SourceCoreDataCatalog.Catalog} {signatures : ProgramSignatures}
    {sourceType : TypeSystem.Ty} {source : Dynamic.Value} {value : Value}
    (represented : DataPatternTypedValues.TypedValueRep catalog signatures sourceType source value) :
    ∃ type, catalog.project sourceType = .ok type ∧
      ∀ world, RuntimeValueHasType world value type catalog.definitions := by
  induction represented using DataPatternTypedValues.TypedValueRep.rec
    (motive_2 := fun types _ values _ => ∃ coreTypes, types.mapM catalog.project = .ok coreTypes ∧
      ∀ world, ListRel (fun value type => RuntimeValueHasType world value type catalog.definitions) values coreTypes) with
  | unit => exact ⟨.unit, rfl, fun _ => .unit⟩
  | bool value => exact ⟨.bool, rfl, fun _ => .bool⟩
  | word value => exact ⟨.word, rfl, fun _ => .word⟩
  | integer value => exact ⟨.integer, rfl, fun _ => .integer⟩
  | product left right leftIH rightIH =>
    obtain ⟨a, projectA, typedA⟩ := leftIH
    obtain ⟨b, projectB, typedB⟩ := rightIH
    exact ⟨.product a b, by simp [SourceCoreDataCatalog.Catalog.project, projectA, projectB, bind, Except.bind, pure, Except.pure],
      fun world => .pair (typedA world) (typedB world)⟩
  | constructed nominal result authenticated payloads ih =>
    obtain ⟨types, projected, typed⟩ := ih
    obtain ⟨registered, projectedRegistered, payloadType⟩ := resolveConstructor_payload authenticated
    have same := Except.ok.inj (projected.symm.trans projectedRegistered)
    subst registered
    have identity := DataPatternAuthenticity.constructor_identity
      (SourceCoreDataValues.resolveConstructor_lookup authenticated)
    rw [result] at identity
    exact ⟨_, project_nominal nominal identity, fun world => .constructed payloadType (pack_typed (typed world))⟩
  | nil => exact ⟨[], rfl, fun _ => .nil⟩
  | cons head tail headIH tailIH =>
    obtain ⟨type, projection, typed⟩ := headIH
    obtain ⟨types, projections, restTyped⟩ := tailIH
    exact ⟨type :: types, by simp [List.mapM_cons, projection, projections, bind, Except.bind, pure, Except.pure],
      fun world => .cons (typed world) (restTyped world)⟩

end Solcore.SourceSemantics.CoreLowering.DataValueTyping
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.DataEqualityValues
/-! The finite part of a value observed by source equality. Mapping contents
and closure code are deliberately opaque: equality never evaluates them.
Nominal constructor metadata and proxy identities remain authenticated. This
relation is an equality observation, not a replacement for heap typing or a
general source-value representation relation. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.DataEqualityValues
open Core Frontend SourceInference DataEquality DataPatternValues

theorem identity_entry {catalog : SourceCoreDataCatalog.Catalog} {type : TypeSystem.Ty}
    {id : DataTypeId} (selected : catalog.identity? type = some id) :
    ∃ entry, catalog.entries[id.index]? = some entry ∧ entry.sourceType = SourceCoreDataCatalog.erase type := by
  unfold SourceCoreDataCatalog.Catalog.identity? at selected
  cases found : catalog.entries.zipIdx.find? (fun item => decide (item.1.sourceType = SourceCoreDataCatalog.erase type)) with
  | none => simp [found] at selected
  | some item =>
    have member := List.mk_mem_zipIdx_iff_getElem?.mp (List.mem_of_find?_eq_some found)
    have same : item.1.sourceType = SourceCoreDataCatalog.erase type := by simpa using List.find?_some found
    simp only [found, Option.map_some, Option.some.injEq] at selected
    subst id
    exact ⟨item.1, member, same⟩

theorem erase_nominal {type : TypeSystem.Ty} {declaration : Resolved.DeclarationId}
    {arguments : List TypeSystem.Ty}
    (nominal : SourceCoreDataCatalog.nominalParts type = some (declaration, arguments)) :
    SourceCoreDataCatalog.erase type = type := by
  cases type <;> try rfl
  all_goals simp [SourceCoreDataCatalog.nominalParts] at nominal

/-- Authentication determines the complete instantiation, including its
parameter substitution; equality observes that retained metadata. -/
theorem metadata_eq {catalog : SourceCoreDataCatalog.Catalog} {signatures : ProgramSignatures}
    {left right : DataConstructorInstantiation} {tag : ConstructorId}
    (leftAccepted : catalog.resolveConstructor signatures left = .ok tag)
    (rightAccepted : catalog.resolveConstructor signatures right = .ok tag)
    (sameResult : left.resultType = right.resultType) : left = right := by
  have constructors := DataPatternAuthenticity.constructor_eq_of_same_tag
    (SourceCoreDataValues.resolveConstructor_lookup leftAccepted)
    (SourceCoreDataValues.resolveConstructor_lookup rightAccepted)
  obtain ⟨leftSignature, leftConstructor, leftSelected, leftCtor, leftParameters, leftResult, leftPayloads⟩ :=
    DataPatternAuthenticity.metadataFacts leftAccepted
  obtain ⟨rightSignature, rightConstructor, rightSelected, rightCtor, rightParameters, rightResult, rightPayloads⟩ :=
    DataPatternAuthenticity.metadataFacts rightAccepted
  rw [constructors] at leftSelected leftCtor
  have sameSignature := List.singleton_inj.mp (leftSelected.symm.trans rightSelected)
  subst rightSignature
  have sameConstructor := List.singleton_inj.mp (leftCtor.symm.trans rightCtor)
  subst rightConstructor
  have arguments : left.parameterSubstitution.map Prod.snd = right.parameterSubstitution.map Prod.snd := by
    have same := congrArg SourceCoreDataCatalog.nominalParts (leftResult.symm.trans (sameResult.trans rightResult))
    simpa [DataPatternAuthenticity.nominalParts_nominal] using same
  have substitutions : left.parameterSubstitution = right.parameterSubstitution := by
    have a := List.zip_of_prod leftParameters (rfl : left.parameterSubstitution.map Prod.snd = _)
    have b := List.zip_of_prod rightParameters (rfl : right.parameterSubstitution.map Prod.snd = _)
    rw [arguments] at a
    exact a.trans b.symm
  have payloads : left.payloadTypes = right.payloadTypes := by
    rw [leftPayloads, rightPayloads, substitutions]
  cases left; cases right
  simp_all

inductive Carrier (callableContracts : Bool) : Ty → Prop where
  | unit : Carrier callableContracts .unit
  | bool : Carrier callableContracts .bool
  | word : Carrier callableContracts .word
  | integer : Carrier callableContracts .integer
  | product {left right : Ty} (first : Carrier callableContracts left) (second : Carrier callableContracts right) :
      Carrier callableContracts (.product left right)
  | namedData (id : DataTypeId) : Carrier callableContracts (.namedData id)
  | function (parameter result : Ty) (profile : callableContracts = false) :
      Carrier callableContracts (TaggedFunction.functionType parameter result)
  | contractedFunction (parameter result : Ty) (profile : callableContracts = true) :
      Carrier callableContracts (CallableContract.functionType parameter result)

theorem Carrier.not_sum {profile : Bool} {left right : Ty} : ¬ Carrier profile (.sum left right) := by
  intro impossible
  cases impossible

theorem Carrier.not_tagged_contract {parameter result : Ty} :
    ¬ Carrier true (TaggedFunction.functionType parameter result) := by
  intro impossible
  cases impossible with
  | product first => exact Carrier.not_sum first
  | function _ _ profile => cases profile

theorem Carrier.product_contract_shape {profile : Bool} {left right : Ty}
    (first : Carrier profile left) :
    (profile && SourceCoreDataEquality.isCallableContractType (.product left right)) = false := by
  cases profile with
  | false => rfl
  | true =>
      cases first with
      | unit | bool | word | integer | namedData | contractedFunction => rfl
      | function _ _ impossible => cases impossible
      | product head tail =>
          cases head with
          | unit | bool | word | integer | product | namedData | contractedFunction => rfl
          | function _ _ impossible => cases impossible

inductive Observation (catalog : SourceCoreDataCatalog.Catalog) (signatures : ProgramSignatures)
    (identities : Dynamic.Value → Word → Prop) : Ty → Dynamic.Value → Value → Prop where
  | unit : Observation catalog signatures identities .unit .unit .unit
  | bool (value : Bool) : Observation catalog signatures identities .bool (.bool value) (.bool value)
  | word (value : Word) : Observation catalog signatures identities .word (.word value) (.word value)
  | integer (value : Int) : Observation catalog signatures identities .integer (.integer value) (.integer value)
  | product {leftType rightType : Ty} {left right : Dynamic.Value} {a b : Value}
      (first : Observation catalog signatures identities leftType left a)
      (second : Observation catalog signatures identities rightType right b) :
      Observation catalog signatures identities (.product leftType rightType) (.product left right) (.pair a b)
  | proxy {id : DataTypeId} {entry : SourceCoreDataCatalog.Entry} (inner : TypeSystem.Ty)
      (selected : catalog.entries[id.index]? = some entry) (sourceType : entry.sourceType = .proxy inner) :
      Observation catalog signatures identities (.namedData id) (.proxy inner) (.constructed ⟨id, 0⟩ .unit)
  | mapping {id : DataTypeId} {entry : SourceCoreDataCatalog.Entry} {registeredKey registeredValue : TypeSystem.Ty}
      (selected : catalog.entries[id.index]? = some entry)
      (sourceType : entry.sourceType = .mapping registeredKey registeredValue)
      (key value : TypeSystem.Ty) (entries : List (Dynamic.Value × Dynamic.Value)) (carrier : Value) :
      Observation catalog signatures identities (.namedData id) (.mapping key value entries) carrier
  | identified {source : Dynamic.Value} {identity : Word} (parameter result : Ty) (code : Value)
      (meaning : identities source identity) (profile : catalog.callableContracts = false) :
      Observation catalog signatures identities (TaggedFunction.functionType parameter result)
        source (.pair (.inRight .unit (.word identity)) code)
  | anonymous (source : Dynamic.Closure) (parameter result : Ty) (code : Value)
      (profile : catalog.callableContracts = false) :
      Observation catalog signatures identities (TaggedFunction.functionType parameter result)
        (.closure source) (.pair (.inLeft .word .unit) code)
  | contractedIdentified {source : Dynamic.Value} {identity : Word} (parameter result : Ty)
      (code : Value) (contract : Word) (meaning : identities source identity)
      (profile : catalog.callableContracts = true) :
      Observation catalog signatures identities (CallableContract.functionType parameter result)
        source (.pair (.pair (.inRight .unit (.word identity)) code) (.word contract))
  | contractedAnonymous (source : Dynamic.Closure) (parameter result : Ty)
      (code : Value) (contract : Word) (profile : catalog.callableContracts = true) :
      Observation catalog signatures identities (CallableContract.functionType parameter result)
        (.closure source) (.pair (.pair (.inLeft .word .unit) code) (.word contract))
  | constructed {id : DataTypeId} {index : Nat} {entry : SourceCoreDataCatalog.Entry}
      {metadata : DataConstructorInstantiation} {declaration : Resolved.DeclarationId} {arguments : List TypeSystem.Ty}
      {sources : List Dynamic.Value} {packed : Dynamic.Value} {payloadType : Ty} {payload : Value}
      (selected : catalog.entries[id.index]? = some entry)
      (sourceType : entry.sourceType = metadata.resultType)
      (nominal : SourceCoreDataCatalog.nominalParts metadata.resultType = some (declaration, arguments))
      (authenticated : catalog.resolveConstructor signatures metadata = .ok ⟨id, index⟩)
      (registered : catalog.definitions.lookupConstructorPayloadType? ⟨id, index⟩ = some payloadType)
      (arity : sources.length = metadata.payloadTypes.length)
      (packing : Dynamic.ValuesPack sources packed)
      (representation : Observation catalog signatures identities payloadType packed payload) :
      Observation catalog signatures identities (.namedData id) (.constructed metadata sources)
        (.constructed ⟨id, index⟩ payload)

theorem Observation.carrier {catalog : SourceCoreDataCatalog.Catalog} {signatures : ProgramSignatures}
    {identities : Dynamic.Value → Word → Prop} {type : Ty} {source : Dynamic.Value} {value : Value}
    (observed : Observation catalog signatures identities type source value) :
    Carrier catalog.callableContracts type := by
  induction observed with
  | unit => exact .unit
  | bool => exact .bool
  | word => exact .word
  | integer => exact .integer
  | product _ _ first second => exact .product first second
  | proxy | mapping | constructed => exact .namedData _
  | identified _ _ _ _ profile | anonymous _ _ _ _ profile => exact .function _ _ profile
  | contractedIdentified _ _ _ _ _ profile | contractedAnonymous _ _ _ _ _ profile =>
      exact .contractedFunction _ _ profile

theorem Observation.proxy_of_identity {catalog : SourceCoreDataCatalog.Catalog} {signatures : ProgramSignatures}
    {identities : Dynamic.Value → Word → Prop} {inner : TypeSystem.Ty} {id : DataTypeId}
    (selected : catalog.identity? (.proxy inner) = some id) :
    Observation catalog signatures identities (.namedData id) (.proxy inner) (.constructed ⟨id, 0⟩ .unit) := by
  obtain ⟨entry, found, same⟩ := identity_entry selected
  exact .proxy inner found same

/-- Source equality rejects every mapping pair without examining entries.
Only the actual catalog identity is needed for this observation. -/
theorem Observation.mapping_of_identity {catalog : SourceCoreDataCatalog.Catalog} {signatures : ProgramSignatures}
    {identities : Dynamic.Value → Word → Prop} {key value : TypeSystem.Ty} {id : DataTypeId}
    (selected : catalog.identity? (.mapping key value) = some id)
    (entries : List (Dynamic.Value × Dynamic.Value)) (carrier : Value) :
    Observation catalog signatures identities (.namedData id) (.mapping key value entries) carrier := by
  obtain ⟨entry, found, same⟩ := identity_entry selected
  exact .mapping found same key value entries carrier

/-- The existing authenticated scalar/product/nominal relation supplies the
equality observation automatically, including the exact constructor arity. -/
theorem TypedValueRep.observation {catalog : SourceCoreDataCatalog.Catalog} {signatures : ProgramSignatures}
    {identities : Dynamic.Value → Word → Prop} {sourceType : TypeSystem.Ty}
    {source : Dynamic.Value} {value : Value}
    (represented : DataPatternTypedValues.TypedValueRep catalog signatures sourceType source value) :
    ∃ type, catalog.project sourceType = .ok type ∧ Observation catalog signatures identities type source value := by
  induction represented using DataPatternTypedValues.TypedValueRep.rec
    (motive_2 := fun types sources values _ => ∃ coreTypes packed,
      types.mapM catalog.project = .ok coreTypes ∧ Dynamic.ValuesPack sources packed ∧
        Observation catalog signatures identities (SourceCoreDataMatches.bundleType coreTypes) packed (packValues values)) with
  | unit => exact ⟨_, rfl, .unit⟩
  | bool value => exact ⟨_, rfl, .bool value⟩
  | word value => exact ⟨_, rfl, .word value⟩
  | integer value => exact ⟨_, rfl, .integer value⟩
  | product left right first second =>
    obtain ⟨a, projectA, observedA⟩ := first
    obtain ⟨b, projectB, observedB⟩ := second
    exact ⟨_, by simp [SourceCoreDataCatalog.Catalog.project, projectA, projectB, bind, Except.bind, pure, Except.pure],
      .product observedA observedB⟩
  | @constructed type metadata tag declaration arguments sources values nominal result authenticated payloads ih =>
    obtain ⟨types, packed, projected, packing, observed⟩ := ih
    obtain ⟨registered, projectedRegistered, registeredPayload⟩ := DataValueTyping.resolveConstructor_payload authenticated
    have same := Except.ok.inj (projected.symm.trans projectedRegistered)
    subst registered
    have identity := DataPatternAuthenticity.constructor_identity (SourceCoreDataValues.resolveConstructor_lookup authenticated)
    obtain ⟨entry, selected, sourceType⟩ := identity_entry identity
    have nominalResult : SourceCoreDataCatalog.nominalParts metadata.resultType = some (declaration, arguments) := by
      rw [result]; exact nominal
    rw [erase_nominal nominalResult] at sourceType
    obtain ⟨coreType, projection, typed⟩ := DataValueTyping.TypedValueRep.project_typed
      (.constructed nominal result authenticated payloads)
    have typeEq : coreType = .namedData tag.owner := by
      cases typed []
      rfl
    subst coreType
    exact ⟨_, projection, .constructed selected sourceType nominalResult authenticated registeredPayload
      (DataPatternTypedValues.TypedValuesRep.length payloads).1.symm packing observed⟩
  | nil => exact ⟨[], .unit, rfl, .nil, .unit⟩
  | @cons sourceType source value sourceTypes sources values head tail headIH tailIH =>
    obtain ⟨type, projection, observed⟩ := headIH
    obtain ⟨types, packed, projected, packing, rest⟩ := tailIH
    have generated : (sourceType :: sourceTypes).mapM catalog.project = .ok (type :: types) := by
      simp [List.mapM_cons, projection, projected, bind, Except.bind, pure, Except.pure]
    cases tail with
    | nil =>
      simp only [List.mapM_nil, pure, Except.pure, Except.ok.injEq] at projected
      subst types
      exact ⟨_, _, generated, .singleton _, observed⟩
    | @cons secondType secondSource secondValue remainingSourceTypes remainingSources remainingValues second remaining =>
      have nonempty : types ≠ [] := by
        intro empty
        rw [List.mapM_cons] at projected
        cases first : catalog.project secondType <;> simp [first, bind, Except.bind] at projected
        rename_i firstValue
        cases remainingTypes : List.mapM catalog.project remainingSourceTypes <;> simp [remainingTypes, pure, Except.pure, empty] at projected
      cases types with
      | nil => contradiction
      | cons firstType restTypes => exact ⟨_, _, generated, .cons packing, .product observed rest⟩

end Solcore.SourceSemantics.CoreLowering.DataEqualityValues
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.DataEqualityCertificates
/-! Comparison certificates obtained from accepted code and finite equality
observations. Recursive helper execution follows the finite nominal payload,
not compilation fuel or a source runtime evaluator. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.DataEqualityCertificates
open Core Frontend SourceCoreDataEquality DataEquality DataEqualityValues DataEqualityGeneration

def ReferencesAt (catalog : Catalog) (base depth : Nat) (mapping : Renaming) (environment : Environment) : Prop :=
  ∀ index, index < catalog.entries.length →
    environment[mapping (referenceIndex catalog depth ⟨index⟩)]? =
      some (.cellRef (OptionalCell.cellType (comparatorType (.namedData ⟨index⟩))) (base + index))

theorem ReferencesAt.lift {catalog : Catalog} {base depth : Nat} {mapping : Renaming} {environment : Environment}
    (references : ReferencesAt catalog base depth mapping environment) (value : Value) :
    ReferencesAt catalog base (depth + 1) mapping.lift (value :: environment) := by
  intro index bound
  have next : referenceIndex catalog (depth + 1) ⟨index⟩ = referenceIndex catalog depth ⟨index⟩ + 1 := by
    simp [referenceIndex, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
  simpa [next, Renaming.lift] using references index bound

theorem installedReferences (catalog : Catalog) (base : Nat) (ambient : Environment) (count : Nat) (pair : Value) :
    ReferencesAt catalog base 1 (DataEqualityInstalled.offset count).lift
      (pair :: DataEqualityInstalled.captured count (DataEqualityInstalled.allocatedEnvironment catalog base ambient)) := by
  intro index bound
  have next : referenceIndex catalog 1 ⟨index⟩ = referenceIndex catalog 0 ⟨index⟩ + 1 := by
    simp [referenceIndex, Nat.add_comm]
  simpa only [next, Renaming.lift, DataEqualityInstalled.offset, ← Nat.add_assoc,
    List.getElem?_cons_succ]
    using DataEqualityInstalled.captured_reference catalog base ambient count index bound

theorem tree_of_compareType {catalog : Catalog} {signatures : ProgramSignatures}
    {identities : Dynamic.Value → Word → Prop} {helperFuel : Nat} {bodies : List Expr}
    (generatedHelpers : helperBodies helperFuel catalog = .ok bodies)
    {base : Nat} {ambient : Environment} {store : Store}
    (installed : DataEqualityInstalled.Installed catalog bodies base ambient store)
    {type : Ty} {sourceLeft sourceRight : Dynamic.Value} {leftValue rightValue : Value}
    (leftObserved : Observation catalog signatures identities type sourceLeft leftValue)
    (rightObserved : Observation catalog signatures identities type sourceRight rightValue)
    {fuel depth : Nat} {leftExpression rightExpression compiled : Expr}
    (accepted : compareType fuel catalog depth type leftExpression rightExpression = .ok compiled)
    (environment : Environment) (mapping : Renaming)
    (references : ReferencesAt catalog base depth mapping environment)
    (leftSelected : Selects environment (leftExpression.rename mapping) leftValue)
    (rightSelected : Selects environment (rightExpression.rename mapping) rightValue) :
    ∃ result, Tree identities store environment (compiled.rename mapping) sourceLeft sourceRight result := by
  induction leftObserved generalizing sourceRight rightValue fuel depth leftExpression rightExpression compiled environment mapping with
  | unit | bool | word | integer =>
    cases fuel with
    | zero => simp [compareType] at accepted
    | succ fuel =>
      simp only [compareType, pure, Except.pure, Except.ok.injEq] at accepted
      subst compiled
      cases rightObserved
      first | exact ⟨true, .unit⟩ | exact ⟨_, .bool leftSelected rightSelected⟩ |
        exact ⟨_, .word leftSelected rightSelected⟩ | exact ⟨_, .integer leftSelected rightSelected⟩
  | @product leftType rightType a b x y first second firstIH secondIH =>
    cases rightObserved with
    | identified => exact False.elim (Carrier.not_sum first.carrier)
    | anonymous => exact False.elim (Carrier.not_sum first.carrier)
    | contractedIdentified _ _ _ _ _ profile =>
        exact False.elim (Carrier.not_tagged_contract (by simpa only [profile] using first.carrier))
    | contractedAnonymous _ _ _ _ _ profile =>
        exact False.elim (Carrier.not_tagged_contract (by simpa only [profile] using first.carrier))
    | product otherFirst otherSecond =>
      cases fuel with
      | zero => simp [compareType] at accepted
      | succ fuel =>
        have generated : (show Except Error Expr from do
            let left ← compareType fuel catalog depth leftType (.first leftExpression) (.first rightExpression)
            let right ← compareType fuel catalog depth rightType (.second leftExpression) (.second rightExpression)
            pure (.ifE left right (.bool false))) = .ok compiled := by
          have carrier := first.carrier
          have shape := Carrier.product_contract_shape (right := rightType) carrier
          cases leftType <;> try cases carrier
          all_goals simpa only [compareType, shape, Bool.false_eq_true, ↓reduceIte] using accepted
        obtain ⟨leftCode, leftCompiled, generated⟩ := bind_ok generated
        obtain ⟨rightCode, rightCompiled, generated⟩ := bind_ok generated
        simp only [pure, Except.pure, Except.ok.injEq] at generated
        subst compiled
        obtain ⟨leftResult, leftTree⟩ := firstIH otherFirst leftCompiled environment mapping references (.first leftSelected) (.first rightSelected)
        obtain ⟨rightResult, rightTree⟩ := secondIH otherSecond rightCompiled environment mapping references (.second leftSelected) (.second rightSelected)
        exact ⟨_, .product leftTree rightTree⟩
  | @identified source identity parameter result code meaning profile =>
    cases fuel with
    | zero => simp [compareType] at accepted
    | succ fuel =>
      simp only [TaggedFunction.functionType, TaggedFunction.identityType, LanguageResult.resultType,
        compareType, pure, Except.pure, Except.ok.injEq] at accepted
      subst compiled
      rw [functionEqual_rename]
      cases rightObserved with
      | product first => exact False.elim (Carrier.not_sum first.carrier)
      | identified _ _ _ other _ => exact ⟨_, .identified meaning other leftSelected rightSelected⟩
      | anonymous source => exact ⟨false, .anonymousRight _ source leftSelected rightSelected⟩
  | @anonymous source parameter result code profile =>
    cases fuel with
    | zero => simp [compareType] at accepted
    | succ fuel =>
      simp only [TaggedFunction.functionType, TaggedFunction.identityType, LanguageResult.resultType,
        compareType, pure, Except.pure, Except.ok.injEq] at accepted
      subst compiled
      rw [functionEqual_rename]
      cases rightObserved with
      | product first => exact False.elim (Carrier.not_sum first.carrier)
      | identified | anonymous => exact ⟨false, .anonymousLeft source _ leftSelected rightSelected⟩
  | @contractedIdentified source identity parameter result code contract meaning profile =>
    cases fuel with
    | zero => simp [compareType] at accepted
    | succ fuel =>
      simp only [CallableContract.functionType, TaggedFunction.functionType, TaggedFunction.identityType,
        LanguageResult.resultType, compareType, isCallableContractType, profile,
        Bool.true_and, ↓reduceIte, pure, Except.pure, Except.ok.injEq] at accepted
      subst compiled
      rw [functionEqual_rename]
      cases rightObserved with
      | product first =>
          exact False.elim (Carrier.not_tagged_contract (by simpa only [profile] using first.carrier))
      | contractedIdentified _ _ _ _ other _ =>
          exact ⟨_, .identified meaning other (.first leftSelected) (.first rightSelected)⟩
      | contractedAnonymous source =>
          exact ⟨false, .anonymousRight _ source (.first leftSelected) (.first rightSelected)⟩
  | @contractedAnonymous source parameter result code contract profile =>
    cases fuel with
    | zero => simp [compareType] at accepted
    | succ fuel =>
      simp only [CallableContract.functionType, TaggedFunction.functionType, TaggedFunction.identityType,
        LanguageResult.resultType, compareType, isCallableContractType, profile,
        Bool.true_and, ↓reduceIte, pure, Except.pure, Except.ok.injEq] at accepted
      subst compiled
      rw [functionEqual_rename]
      cases rightObserved with
      | product first =>
          exact False.elim (Carrier.not_tagged_contract (by simpa only [profile] using first.carrier))
      | contractedIdentified | contractedAnonymous =>
          exact ⟨false, .anonymousLeft source _ (.first leftSelected) (.first rightSelected)⟩
  | @proxy id entry inner selected sourceType =>
    cases fuel with
    | zero => simp [compareType] at accepted
    | succ fuel =>
      simp only [compareType, selected, sourceType, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at accepted
      subst compiled
      cases rightObserved with
      | proxy otherInner otherSelected otherType =>
        have entries := Option.some.inj (selected.symm.trans otherSelected)
        subst_vars
        have same := TypeSystem.Ty.proxy.inj (sourceType.symm.trans otherType)
        subst_vars
        exact ⟨true, .proxy _⟩
      | mapping otherSelected otherType =>
        have entries := Option.some.inj (selected.symm.trans otherSelected)
        subst_vars
        rw [sourceType] at otherType
        cases otherType
      | constructed otherSelected otherType nominal =>
        have entries := Option.some.inj (selected.symm.trans otherSelected)
        subst_vars
        rw [← otherType, sourceType] at nominal
        simp [SourceCoreDataCatalog.nominalParts] at nominal
  | @mapping id entry registeredKey registeredValue selected sourceType key value entries carrier =>
    cases fuel with
    | zero => simp [compareType] at accepted
    | succ fuel =>
      simp only [compareType, selected, sourceType, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at accepted
      subst compiled
      cases rightObserved with
      | mapping => exact ⟨false, .mapping _ _ _ _ _ _⟩
      | proxy otherInner otherSelected otherType =>
        have entries := Option.some.inj (selected.symm.trans otherSelected)
        subst_vars
        rw [sourceType] at otherType
        cases otherType
      | constructed otherSelected otherType nominal =>
        have entries := Option.some.inj (selected.symm.trans otherSelected)
        subst_vars
        rw [← otherType, sourceType] at nominal
        simp [SourceCoreDataCatalog.nominalParts] at nominal
  | @constructed id index entry metadata declaration arguments sources packed payloadType payload
      selected sourceType nominal authenticated registered arity packing representation ih =>
    have nominalEntry : SourceCoreDataCatalog.nominalParts entry.sourceType = some (declaration, arguments) := by
      rw [sourceType]; exact nominal
    rw [nominal_compareType selected nominalEntry accepted, invoke_rename]
    cases rightObserved with
    | proxy inner otherSelected otherType =>
      have entries := Option.some.inj (selected.symm.trans otherSelected)
      subst_vars
      rw [otherType] at nominalEntry
      simp [SourceCoreDataCatalog.nominalParts] at nominalEntry
    | mapping otherSelected otherType =>
      have entries := Option.some.inj (selected.symm.trans otherSelected)
      subst_vars
      rw [otherType] at nominalEntry
      simp [SourceCoreDataCatalog.nominalParts] at nominalEntry
    | @constructed _ otherIndex otherEntry otherMetadata otherDeclaration otherArguments otherSources otherPacked otherPayloadType otherPayload
        otherSelected otherType otherNominal otherAuthenticated otherRegistered otherArity otherPacking otherRepresentation =>
      have entries := Option.some.inj (selected.symm.trans otherSelected)
      subst otherEntry
      have bound : id.index < catalog.entries.length := List.getElem?_eq_some_iff.mp selected |>.1
      obtain ⟨body, bodySelected, generatedBody⟩ := helperBodies_lookup generatedHelpers bound
      obtain ⟨definition, definitionSelected, generatedNominal⟩ := nominal_helperBody selected nominalEntry generatedBody
      have leftPayload := registered_payload selected definitionSelected registered
      have rightPayload := registered_payload selected definitionSelected otherRegistered
      obtain ⟨branches, rightBranches, branch, bodyEq, leftBranch, rightBranch, branchGenerated⟩ :=
        nominalBody_branches generatedNominal leftPayload rightPayload
      let captured := DataEqualityInstalled.captured id.index (DataEqualityInstalled.allocatedEnvironment catalog base ambient)
      let pair := Value.pair (.constructed ⟨id, index⟩ payload) (.constructed ⟨id, otherIndex⟩ otherPayload)
      let shift := (DataEqualityInstalled.offset id.index).lift
      have helperReferences : ReferencesAt catalog base 3 shift.lift.lift (otherPayload :: payload :: pair :: captured) :=
        (installedReferences catalog base ambient id.index pair).lift payload |>.lift otherPayload
      have installedBody := installed id.index body bodySelected
      have renamedLeft := renameList_lookup leftBranch shift.lift
      have renamedRight := renameList_lookup rightBranch shift.lift.lift
      by_cases same : index = otherIndex
      · subst otherIndex
        have payloadTypes := Option.some.inj (leftPayload.symm.trans rightPayload)
        subst otherPayloadType
        have metadataSame := metadata_eq authenticated otherAuthenticated (sourceType.symm.trans otherType)
        subst otherMetadata
        simp only [↓reduceIte] at branchGenerated
        obtain ⟨result, payloadTree⟩ := ih otherRepresentation branchGenerated _ shift.lift.lift helperReferences
          (.var rfl) (.var rfl)
        refine ⟨result, .invoke (.var (references id.index bound)) leftSelected rightSelected installedBody ?_⟩
        change Tree identities store (pair :: captured) (body.rename shift) _ _ result
        rw [bodyEq]
        apply Tree.nominalSame metadata (.first (.var rfl)) (.second (.var rfl))
          (by simpa [Expr.rename, Expr.weakenAt, shift, Renaming.lift] using renamedLeft) renamedRight
          packing otherPacking (arity.trans otherArity.symm) payloadTree
      · have branchEq : branch = .bool false := by simpa [same] using branchGenerated.symm
        have distinct : metadata ≠ otherMetadata := by
          intro sameMetadata
          rw [sameMetadata] at authenticated
          have tags := Except.ok.inj (authenticated.symm.trans otherAuthenticated)
          exact same (ConstructorId.mk.inj tags).2
        refine ⟨false, .invoke (.var (references id.index bound)) leftSelected rightSelected installedBody ?_⟩
        change Tree identities store (pair :: captured) (body.rename shift) _ _ false
        rw [bodyEq]
        apply Tree.nominalDifferent metadata otherMetadata sources otherSources distinct
          (.first (.var rfl)) (.second (.var rfl))
          (by simpa [Expr.rename, Expr.weakenAt, shift, Renaming.lift] using renamedLeft)
          (by simpa [branchEq, Expr.rename] using renamedRight)

theorem installed_append {catalog : Catalog} {bodies : List Expr} {base : Nat}
    {environment : Environment} {store : Store}
    (installed : DataEqualityInstalled.Installed catalog bodies base environment store) (suffix : Store) :
    DataEqualityInstalled.Installed catalog bodies base environment (store ++ suffix) := by
  intro index body selected
  have found := installed index body selected
  have bound : base + index < store.length := List.getElem?_eq_some_iff.mp found |>.1
  simpa [Store.read?, List.getElem?_append_left bound] using found

/-- Accepted preparation supplies both generated helper bodies and the main
comparison equation. A later mapping-helper allocation preserves `Installed`. -/
theorem prepared_tree {checked : SourceCoreDataCatalog.Checked} (prepared : Prepared checked)
    {signatures : ProgramSignatures} {identities : Dynamic.Value → Word → Prop}
    {sourceLeft sourceRight : Dynamic.Value} {leftValue rightValue : Value}
    (leftObserved : Observation checked.catalog signatures identities prepared.type sourceLeft leftValue)
    (rightObserved : Observation checked.catalog signatures identities prepared.type sourceRight rightValue)
    (environment : Environment) (initialStore store : Store)
    (installed : DataEqualityInstalled.Installed checked.catalog prepared.bodies initialStore.length environment store) :
    ∃ result, Tree identities store
      (.pair leftValue rightValue :: DataEqualityInstalled.captured prepared.bodies.length
        (DataEqualityInstalled.allocatedEnvironment checked.catalog initialStore.length environment))
      (prepared.body.rename (DataEqualityInstalled.offset prepared.bodies.length).lift) sourceLeft sourceRight result := by
  apply tree_of_compareType prepared.bodiesGenerated installed leftObserved rightObserved prepared.bodyGenerated
  · exact installedReferences _ _ _ _ _
  · exact .first (.var rfl)
  · exact .second (.var rfl)

/-- The exact closure returned by real initialization is a finite, pure
OrderedMapping comparator in any store retaining the installed helper cells. -/
theorem prepared_compares {checked : SourceCoreDataCatalog.Checked} (prepared : Prepared checked)
    (layout : OrderedMapping.Layout) (keyType : layout.keyType = prepared.type)
    {signatures : ProgramSignatures} {identities : Dynamic.Value → Word → Prop}
    (faithful : IdentityFaithful identities)
    {sourceLeft sourceRight : Dynamic.Value} {leftValue rightValue : Value}
    (leftObserved : Observation checked.catalog signatures identities prepared.type sourceLeft leftValue)
    (rightObserved : Observation checked.catalog signatures identities prepared.type sourceRight rightValue)
    (environment : Environment) (initialStore store : Store)
    (installed : DataEqualityInstalled.Installed checked.catalog prepared.bodies initialStore.length environment store) :
    ∃ result, (result = true ↔ Dynamic.ValueEquivalent sourceLeft sourceRight) ∧
      OrderedMapping.Compares layout
        (.closure (.product prepared.type prepared.type) .bool
          (prepared.body.rename (DataEqualityInstalled.offset prepared.bodies.length).lift)
          (DataEqualityInstalled.captured prepared.bodies.length
            (DataEqualityInstalled.allocatedEnvironment checked.catalog initialStore.length environment)))
        leftValue rightValue result store := by
  obtain ⟨result, tree⟩ := prepared_tree prepared leftObserved rightObserved environment initialStore store installed
  exact ⟨result, tree.meaning faithful, by simpa only [keyType] using tree.compares layout⟩

/-- Initializer execution, recursive comparison, and independent source
equality are derived together. No child or helper evaluation is a premise. -/
theorem prepared_compare_preserves {checked : SourceCoreDataCatalog.Checked} (prepared : Prepared checked)
    {signatures : ProgramSignatures} {identities : Dynamic.Value → Word → Prop}
    (faithful : IdentityFaithful identities)
    {sourceLeft sourceRight : Dynamic.Value} {leftValue rightValue : Value}
    (leftObserved : Observation checked.catalog signatures identities prepared.type sourceLeft leftValue)
    (rightObserved : Observation checked.catalog signatures identities prepared.type sourceRight rightValue)
    (environment : Environment) (store : Store) (leftExpression rightExpression : Expr)
    (leftSelected : Selects environment leftExpression leftValue)
    (rightSelected : Selects environment rightExpression rightValue) :
    ∃ result, (result = true ↔ Dynamic.ValueEquivalent sourceLeft sourceRight) ∧
      Evaluates environment store
        (.letE prepared.expression (.apply (.var 0)
          (.pair (leftExpression.weakenAt 0) (rightExpression.weakenAt 0)))) (.bool result)
        (store ++ DataEqualityInstalled.cells
          (DataEqualityInstalled.allocatedEnvironment checked.catalog store.length environment) prepared.bodies) := by
  obtain ⟨result, tree⟩ := prepared_tree prepared leftObserved rightObserved environment store _
    (DataEqualityInstalled.prepared_installed prepared environment store)
  refine ⟨result, tree.meaning faithful, .letE (DataEqualityInstalled.prepared_evaluates_exact prepared environment store) ?_⟩
  exact .apply (.var rfl) (.pair ((leftSelected.weaken _).evaluates _) ((rightSelected.weaken _).evaluates _)) tree.evaluates

/-- Existing authenticated nominal values need no manually constructed
comparison tree, payload certificates, or extra Core typing premises. -/
theorem typed_compare_preserves {checked : SourceCoreDataCatalog.Checked} (prepared : Prepared checked)
    {signatures : ProgramSignatures} {identities : Dynamic.Value → Word → Prop}
    (faithful : IdentityFaithful identities)
    {sourceLeft sourceRight : Dynamic.Value} {leftValue rightValue : Value}
    (leftRepresented : DataPatternTypedValues.TypedValueRep checked.catalog signatures prepared.sourceType sourceLeft leftValue)
    (rightRepresented : DataPatternTypedValues.TypedValueRep checked.catalog signatures prepared.sourceType sourceRight rightValue)
    (environment : Environment) (store : Store) (leftExpression rightExpression : Expr)
    (leftSelected : Selects environment leftExpression leftValue)
    (rightSelected : Selects environment rightExpression rightValue) :
    ∃ result, (result = true ↔ Dynamic.ValueEquivalent sourceLeft sourceRight) ∧
      Evaluates environment store
        (.letE prepared.expression (.apply (.var 0)
          (.pair (leftExpression.weakenAt 0) (rightExpression.weakenAt 0)))) (.bool result)
        (store ++ DataEqualityInstalled.cells
          (DataEqualityInstalled.allocatedEnvironment checked.catalog store.length environment) prepared.bodies) := by
  obtain ⟨leftType, leftProjection, leftObserved⟩ := TypedValueRep.observation (identities := identities) leftRepresented
  obtain ⟨rightType, rightProjection, rightObserved⟩ := TypedValueRep.observation (identities := identities) rightRepresented
  have leftEq := Except.ok.inj (leftProjection.symm.trans prepared.projection)
  have rightEq := Except.ok.inj (rightProjection.symm.trans prepared.projection)
  subst leftType; subst rightType
  exact prepared_compare_preserves prepared faithful leftObserved rightObserved environment store _ _ leftSelected rightSelected

theorem prepared_compare_run {checked : SourceCoreDataCatalog.Checked} (prepared : Prepared checked)
    {signatures : ProgramSignatures} {identities : Dynamic.Value → Word → Prop}
    (faithful : IdentityFaithful identities)
    {sourceLeft sourceRight : Dynamic.Value} {leftValue rightValue : Value}
    (leftObserved : Observation checked.catalog signatures identities prepared.type sourceLeft leftValue)
    (rightObserved : Observation checked.catalog signatures identities prepared.type sourceRight rightValue)
    (environment : Environment) (store : Store) (leftExpression rightExpression : Expr)
    (leftSelected : Selects environment leftExpression leftValue)
    (rightSelected : Selects environment rightExpression rightValue) :
    ∃ result, (result = true ↔ Dynamic.ValueEquivalent sourceLeft sourceRight) ∧
      let expression := Expr.letE prepared.expression (.apply (.var 0)
        (.pair (leftExpression.weakenAt 0) (rightExpression.weakenAt 0)))
      let finalStore := store ++ DataEqualityInstalled.cells
        (DataEqualityInstalled.allocatedEnvironment checked.catalog store.length environment) prepared.bodies
      (∃ required, ∀ fuel, required ≤ fuel →
        runStateful fuel (.initial expression environment store) = .done (.bool result) finalStore) ∧
      (∀ fuel actual actualStore, runStateful fuel (.initial expression environment store) = .done actual actualStore →
        actual = .bool result ∧ actualStore = finalStore) := by
  obtain ⟨result, meaning, evaluated⟩ := prepared_compare_preserves prepared faithful leftObserved rightObserved
    environment store leftExpression rightExpression leftSelected rightSelected
  refine ⟨result, meaning, evaluation_runStateful_complete_with_sufficient_fuel evaluated, ?_⟩
  intro fuel actual actualStore ran
  exact evaluation_deterministic (runStateful_evaluation_sound ran) evaluated

end Solcore.SourceSemantics.CoreLowering.DataEqualityCertificates
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.DataPatternDecision
/-! Every accepted matcher decides the authenticated closed scalar/product/
nominal value profile. Both outcomes execute finitely without changing the
store; nested failures do not require evaluating the remaining children. -/

set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.DataPatternDecision
open Core Frontend Frontend.SourceInference
open SourceCoreDataMatches DataPatternCertificates DataPatternValues DataPatternLeaves
open DataPatternExecution DataPatternSuccess DataPatternTypedValues DataPatternAuthenticity DataEquality

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

def TreeDecision (compilation : Compilation) (context : Context) (type : TypeSystem.Ty)
    (instructions : List MatchPatternInstruction) (pattern : Pattern) (rest : List MatchPatternInstruction) : Prop :=
  ∀ source value, TypedValueRep compilation.checked.catalog compilation.signatures type source value →
    (∃ bindings values, Dynamic.PatternInstructionMatches context source instructions bindings rest ∧
      BindingsRep compilation.checked.catalog pattern.bindings bindings values ∧ MatcherRuns pattern value values) ∨
    MatcherFails pattern value

def ForestDecision (compilation : Compilation) (context : Context) (types : List TypeSystem.Ty)
    (instructions : List MatchPatternInstruction) (patterns : List Pattern) (rest : List MatchPatternInstruction) : Prop :=
  ∀ sources values, TypedValuesRep compilation.checked.catalog compilation.signatures types sources values →
    (∃ bindings boundValues, Dynamic.PatternInstructionsMatch context sources instructions bindings rest ∧
      BindingsRep compilation.checked.catalog (patterns.flatMap (·.bindings)) bindings boundValues ∧
      ChildrenRun patterns values boundValues) ∨ ChildrenFail patterns values

theorem Tree.decides {compilation : Compilation} {context : Context} {source : TypedSource}
    {site : StatementId} {span : Syntax.SourceSpan} {scope : Scope} {type : TypeSystem.Ty}
    {instructions rest : List MatchPatternInstruction} {pattern : Pattern}
    (valid : ContextValid compilation context)
    (tree : Tree compilation source site span scope type instructions pattern rest) :
    TreeDecision compilation context type instructions pattern rest := by
  induction tree using Tree.rec
      (motive_2 := fun types instructions patterns rest _ => ForestDecision compilation context types instructions patterns rest) with
  | wildcard projection =>
    intro source value represented
    exact .inl ⟨[], [], .wildcard, .nil, fun _ store _ path =>
      .apply .lambda (path.evaluates store) (.inRight .unit)⟩
  | binder projection sourceType binderValid =>
    intro source value represented
    exact .inl ⟨[(_, source)], [value], .binder, .cons (TypedValueRep.erase represented) .nil,
      fun _ store _ path => .apply .lambda (path.evaluates store) (.inRight (.var rfl))⟩
  | @literal expected coreType literal resolution matcher rest projection validated =>
    intro sourceValue value represented
    have code := literalMatcher_sound compilation site span _ _ _ _ validated
    cases code with
    | word target meaning retained =>
      cases represented with
      | constructed nominal => simp [SourceCoreDataCatalog.nominalParts, TypeSystem.Ty.word] at nominal
      | word actual =>
        by_cases same : actual = Word.ofNatModulo resolution.rawValue
        · subst actual
          exact .inl ⟨[], [], .integerLiteral (LiteralCode.constructs_word valid target meaning retained), .nil,
            fun _ store _ path => .apply .lambda (path.evaluates store)
              (.ifTrue (.binary (.var rfl) .word (by simp [BinaryOp.apply])) (.inRight .unit))⟩
        · exact .inr (fun _ store _ path => .apply .lambda (path.evaluates store)
            (.ifFalse (.binary (.var rfl) .word (by simp [BinaryOp.apply, same])) (.inLeft .unit)))
    | integer target meaning retained =>
      cases represented with
      | constructed nominal => simp [SourceCoreDataCatalog.nominalParts, TypeSystem.Ty.integer] at nominal
      | integer actual =>
        by_cases same : actual = Int.ofNat resolution.rawValue
        · subst actual
          exact .inl ⟨[], [], .integerLiteral (LiteralCode.constructs_integer valid target meaning retained), .nil,
            fun _ store _ path => .apply .lambda (path.evaluates store)
              (.ifTrue (.binary (.var rfl) .integer (by simp [BinaryOp.apply])) (.inRight .unit))⟩
        · exact .inr (fun _ store _ path => .apply .lambda (path.evaluates store)
            (.ifFalse (.binary (.var rfl) .integer (by
              simp only [BinaryOp.apply, Option.some.injEq, Value.bool.injEq, beq_eq_false_iff_ne]
              exact same)) (.inLeft .unit)))
  | @tuple expected coreType count types instructions rest children coreTypes projection unpacked childrenTree projectedChildren ih =>
    intro sourceValue value represented
    obtain ⟨sources, values, representations, packing, valueEq⟩ := TypedValueRep.unpack unpacked represented
    subst value
    have length := (projectionList_length projectedChildren).symm.trans (TypedValuesRep.length representations).2
    cases ih sources values representations with
    | inl success =>
      obtain ⟨bindings, boundValues, matched, bindingRep, childrenRun⟩ := success
      refine .inl ⟨bindings, boundValues, .tuple packing
        ((TypedValuesRep.length representations).1.symm.trans (unpackTypes_length unpacked)) matched, bindingRep, ?_⟩
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
  | @constructor expected coreType metadata count constructor definition instructions rest children coreTypes
      projection result arity resolved sameType childrenTree projectedChildren registered ih =>
    intro sourceValue value represented
    have nominalExpected : ∃ declaration arguments, SourceCoreDataCatalog.nominalParts expected = some (declaration, arguments) := by
      obtain ⟨signature, _, _, _, _, nominalResult, _⟩ := metadataFacts resolved
      rw [result] at nominalResult
      rw [nominalResult]
      exact ⟨_, _, nominalParts_nominal _ _⟩
    cases represented with
    | unit | bool | word | integer | product =>
      obtain ⟨_, _, impossible⟩ := nominalExpected
      simp [SourceCoreDataCatalog.nominalParts, TypeSystem.Ty.unit, TypeSystem.Ty.bool, TypeSystem.Ty.word, TypeSystem.Ty.integer] at impossible
    | @constructed actualType actual actualTag declaration arguments sourceArguments values nominal actualResult authenticated payloads =>
      have resultEq : actual.resultType = metadata.resultType := actualResult.trans result.symm
      have ownerEq : actualTag.owner = constructor.owner := by
        have first := constructor_identity (SourceCoreDataValues.resolveConstructor_lookup authenticated)
        have second := constructor_identity (SourceCoreDataValues.resolveConstructor_lookup resolved)
        rw [resultEq] at first
        exact Option.some.inj (first.symm.trans second)
      obtain ⟨payloadType, payloadLookup⟩ := SourceCoreDataValues.resolveConstructor_registered authenticated
      have lookup : definition.constructorPayloadTypes[actualTag.index]? = some payloadType := by
        simpa [DataEnvironment.lookupConstructorPayloadType?, DataEnvironment.lookupDataType?, ownerEq, registered] using payloadLookup
      by_cases same : actualTag = constructor
      · subst actualTag
        have agreement := resolveConstructor_agree authenticated resolved resultEq
        have payloads : TypedValuesRep compilation.checked.catalog compilation.signatures metadata.payloadTypes sourceArguments values := agreement.payload_types_eq ▸ payloads
        have length := (projectionList_length projectedChildren).symm.trans (TypedValuesRep.length payloads).2
        have branchLookup : (definition.constructorPayloadTypes.zipIdx.map fun (_, index) =>
            if index = constructor.index then matchChildren (bundleType ((children.flatMap (fun (p : Pattern) => p.bindings)).map Prod.snd)) children (childValues coreTypes) []
            else .inLeft (bundleType ((children.flatMap (fun (p : Pattern) => p.bindings)).map Prod.snd)) .unit)[constructor.index]? =
            some (matchChildren (bundleType ((children.flatMap (fun (p : Pattern) => p.bindings)).map Prod.snd)) children (childValues coreTypes) []) := by
          simp [List.getElem?_map, List.getElem?_zipIdx, lookup]
        cases ih sourceArguments values payloads with
        | inl success =>
          obtain ⟨bindings, boundValues, matched, bindingsRep, childrenRun⟩ := success
          refine .inl ⟨bindings, boundValues, .constructor agreement ((TypedValuesRep.length payloads).1.symm.trans arity.symm) matched, bindingsRep, ?_⟩
          intro environment store expression selected
          apply Evaluates.apply .lambda (selected.evaluates store)
          apply Evaluates.matchData (.var rfl) rfl branchLookup
          have paths := projectionList_selects (environment := packValues values :: .constructed constructor (packValues values) :: environment) (expression := .var 0) (.var rfl) length
          simpa [constructorPattern, Pattern.bindingTypes, childValues] using childrenRun _ store _ [] [] _ paths .nil
        | inr failed =>
          refine .inr ?_
          intro environment store expression selected
          apply Evaluates.apply .lambda (selected.evaluates store)
          apply Evaluates.matchData (.var rfl) rfl branchLookup
          have paths := projectionList_selects (environment := packValues values :: .constructed constructor (packValues values) :: environment) (expression := .var 0) (.var rfl) length
          simpa [constructorPattern, Pattern.bindingTypes, childValues] using failed _ store _ [] [] _ paths .nil
      · have indexDifferent : actualTag.index ≠ constructor.index := by
          intro indices
          apply same
          cases actualTag; cases constructor; cases ownerEq; cases indices; rfl
        have branchLookup : (definition.constructorPayloadTypes.zipIdx.map fun (_, index) =>
            if index = constructor.index then matchChildren (bundleType ((children.flatMap (fun (p : Pattern) => p.bindings)).map Prod.snd)) children (childValues coreTypes) []
            else .inLeft (bundleType ((children.flatMap (fun (p : Pattern) => p.bindings)).map Prod.snd)) .unit)[actualTag.index]? =
            some (.inLeft (bundleType ((children.flatMap (fun (p : Pattern) => p.bindings)).map Prod.snd)) .unit) := by
          simp [List.getElem?_map, List.getElem?_zipIdx, lookup, indexDifferent]
        exact .inr (fun _ store _ selected => .apply .lambda (selected.evaluates store)
          (.matchData (.var rfl) ownerEq branchLookup (.inLeft .unit)))
  | nil =>
    intro sources values represented
    cases represented
    exact .inl ⟨[], [], .nil, .nil, ChildrenRun.nil⟩
  | @cons type types instructions afterHead rest head tail headTree tailTree headIH tailIH =>
    intro sources values represented
    cases represented with
    | cons valueRep valuesRep =>
      cases headIH _ _ valueRep with
      | inr failed => exact .inr (ChildrenFail.head failed)
      | inl success =>
        obtain ⟨headBindings, headValues, headMatch, headBindingRep, headRun⟩ := success
        have length : head.bindingTypes.length = headValues.length := by
          simpa [Pattern.bindingTypes] using BindingsRep.length headBindingRep
        cases tailIH _ _ valuesRep with
        | inr failed => exact .inr (ChildrenFail.tail length headRun failed)
        | inl success =>
          obtain ⟨tailBindings, tailValues, tailMatch, tailBindingRep, tailRun⟩ := success
          exact .inl ⟨headBindings ++ tailBindings, headValues ++ tailValues, .cons headMatch tailMatch,
            BindingsRep.append headBindingRep tailBindingRep, ChildrenRun.cons length headRun tailRun⟩


/-- Actual compiler acceptance yields an independent source success or
non-match and finite execution of the emitted matcher. Nominal input metadata
is authenticated by TypedValueRep, rather than inferred from its Core type. -/
theorem compilePattern_preserves (compilation : Compilation) (compilationFuel : Nat)
    (source : TypedSource) (scope : Scope) (site : StatementId) (span : Syntax.SourceSpan)
    (expected : TypeSystem.Ty) (pattern : TypedMatchPattern)
    (compiled : CertifiedPattern compilation.checked.catalog.definitions)
    (accepted : compilePattern compilation compilationFuel source scope site span expected pattern = .ok compiled)
    (context : Context) (valid : ContextValid compilation context)
    {sourceValue : Dynamic.Value} {value : Value}
    (represented : TypedValueRep compilation.checked.catalog compilation.signatures expected sourceValue value)
    (environment : Environment) (store : Store) :
    ∃ outcome, OutcomeRep compilation.checked.catalog context pattern compiled.pattern sourceValue outcome ∧
      Evaluates (value :: environment) store (.apply compiled.pattern.matcher (.var 0)) outcome store := by
  have certificate := certificate_of_compilePattern compilation compilationFuel source scope site span expected pattern compiled accepted
  obtain ⟨instructions, root, tree⟩ := certificate.tree
  obtain ⟨arity, instructionsEq, sourceRep⟩ := rootInstructions_sound compilation context valid.signatures _ _ _ root
  cases Tree.decides valid tree sourceValue value represented with
  | inl success =>
    obtain ⟨bindings, values, matched, bindingRep, executes⟩ := success
    subst instructions
    exact ⟨.inRight .unit (packValues values), .matched (.intro sourceRep matched) bindingRep,
      executes _ store _ (.var rfl)⟩
  | inr failed =>
    have evaluation := failed (value :: environment) store (.var 0) (.var rfl)
    refine ⟨.inLeft (bundleType compiled.pattern.bindingTypes) .unit, .noMatch (.intro sourceRep ?_), evaluation⟩
    subst instructions
    refine ⟨DataPatternCertificates.Tree.skips tree, ?_⟩
    intro bindings matched
    obtain ⟨values, _, _, executes⟩ := DataPatternSuccess.Tree.success tree sourceValue value bindings []
      (TypedValueRep.erase represented) matched
    have impossible := (evaluation_deterministic evaluation (executes _ store _ (.var rfl))).1
    cases impossible

/-- Sufficient machine fuel returns the independent pattern outcome; every
completed run has that same outcome and exactly the original store. -/
theorem compilePattern_run_preserves (compilation : Compilation) (compilationFuel : Nat)
    (source : TypedSource) (scope : Scope) (site : StatementId) (span : Syntax.SourceSpan)
    (expected : TypeSystem.Ty) (pattern : TypedMatchPattern)
    (compiled : CertifiedPattern compilation.checked.catalog.definitions)
    (accepted : compilePattern compilation compilationFuel source scope site span expected pattern = .ok compiled)
    (context : Context) (valid : ContextValid compilation context)
    {sourceValue : Dynamic.Value} {value : Value}
    (represented : TypedValueRep compilation.checked.catalog compilation.signatures expected sourceValue value)
    (environment : Environment) (store : Store) :
    ∃ outcome, OutcomeRep compilation.checked.catalog context pattern compiled.pattern sourceValue outcome ∧
      (∃ required, ∀ fuel, required ≤ fuel →
        runStateful fuel (State.initial (.apply compiled.pattern.matcher (.var 0)) (value :: environment) store) = .done outcome store) ∧
      (∀ fuel actual finalStore,
        runStateful fuel (State.initial (.apply compiled.pattern.matcher (.var 0)) (value :: environment) store) = .done actual finalStore →
        actual = outcome ∧ finalStore = store) := by
  obtain ⟨outcome, meaning, evaluates⟩ := compilePattern_preserves compilation compilationFuel source scope site span expected pattern compiled
    accepted context valid represented environment store
  exact ⟨outcome, meaning, evaluation_runStateful_complete_with_sufficient_fuel evaluates,
    fun _ _ _ ran => evaluation_deterministic (runStateful_evaluation_sound ran) evaluates⟩


/-- In particular, an independently established source non-match evaluates to
absence. Candidate bindings stay lexical to the matcher until it succeeds. -/
theorem compilePattern_failure_preserves (compilation : Compilation) (compilationFuel : Nat)
    (source : TypedSource) (scope : Scope) (site : StatementId) (span : Syntax.SourceSpan)
    (expected : TypeSystem.Ty) (pattern : TypedMatchPattern)
    (compiled : CertifiedPattern compilation.checked.catalog.definitions)
    (accepted : compilePattern compilation compilationFuel source scope site span expected pattern = .ok compiled)
    (context : Context) (valid : ContextValid compilation context)
    {sourceValue : Dynamic.Value} {value : Value}
    (represented : TypedValueRep compilation.checked.catalog compilation.signatures expected sourceValue value)
    (failed : Dynamic.PatternDoesNotMatch context pattern sourceValue)
    (environment : Environment) (store : Store) :
    Evaluates (value :: environment) store (.apply compiled.pattern.matcher (.var 0))
      (.inLeft (bundleType compiled.pattern.bindingTypes) .unit) store := by
  obtain ⟨outcome, meaning, evaluation⟩ := compilePattern_preserves compilation compilationFuel source scope site span expected pattern
    compiled accepted context valid represented environment store
  cases meaning with
  | matched matched => exact False.elim (failed.excludes matched)
  | noMatch => exact evaluation

end Solcore.SourceSemantics.CoreLowering.DataPatternDecision
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.DataEqualityScalarCertificates
/-! Actual comparison compilation yields a finite comparison certificate for
scalar/product carriers. Nominal recursive payloads, function identities,
mapping keys and proxy metadata require their own authenticated extensions. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.DataEqualityScalarCertificates
open Core Frontend SourceCoreDataEquality DataEquality DataPatternValues

inductive ScalarType : Ty → Prop where
  | unit : ScalarType .unit
  | bool : ScalarType .bool
  | word : ScalarType .word
  | integer : ScalarType .integer
  | product {left right : Ty} (first : ScalarType left) (second : ScalarType right) : ScalarType (.product left right)

private theorem ScalarType.product_contract_shape {left right : Ty}
    (scalar : ScalarType left) (profile : Bool) :
    (profile && isCallableContractType (.product left right)) = false := by
  cases profile with
  | false => rfl
  | true =>
      cases scalar with
      | unit | bool | word | integer => rfl
      | product first => cases first <;> rfl

private theorem bind_ok {α β ε : Type} {computation : Except ε α} {next : α → Except ε β}
    {result : β} (accepted : computation >>= next = .ok result) :
    ∃ value, computation = .ok value ∧ next value = .ok result := by
  cases computation with
  | error => cases accepted
  | ok value => exact ⟨value, rfl, accepted⟩

/-- The certificate is extracted from successful actual compilation and
represented input shapes. It supplies its own finite child comparisons. -/
theorem tree_of_compareType {type : Ty} (scalar : ScalarType type)
    {catalog : Catalog} {fuel depth : Nat} {leftExpression rightExpression compiled : Expr}
    (accepted : compareType fuel catalog depth type leftExpression rightExpression = .ok compiled)
    {definitions : DataEnvironment} {identities : Dynamic.Value → Word → Prop}
    {sourceLeft sourceRight : Dynamic.Value} {leftValue rightValue : Value}
    (leftRepresentation : ValueRep catalog sourceLeft leftValue)
    (rightRepresentation : ValueRep catalog sourceRight rightValue)
    (leftTyped : ValueHasType leftValue type definitions) (rightTyped : ValueHasType rightValue type definitions)
    (environment : Environment) (store : Store) (mapping : Renaming)
    (leftSelected : Selects environment (leftExpression.rename mapping) leftValue)
    (rightSelected : Selects environment (rightExpression.rename mapping) rightValue) :
    ∃ result, Tree identities store environment (compiled.rename mapping) sourceLeft sourceRight result := by
  induction scalar generalizing fuel depth leftExpression rightExpression compiled sourceLeft sourceRight leftValue rightValue with
  | unit =>
    cases fuel with
    | zero => simp [compareType] at accepted
    | succ fuel =>
      simp only [compareType, pure, Except.pure, Except.ok.injEq] at accepted
      subst compiled
      cases leftTyped; cases rightTyped; cases leftRepresentation; cases rightRepresentation
      exact ⟨true, .unit⟩
  | bool =>
    cases fuel with
    | zero => simp [compareType] at accepted
    | succ fuel =>
      simp only [compareType, pure, Except.pure, Except.ok.injEq] at accepted
      subst compiled
      cases leftTyped; cases rightTyped; cases leftRepresentation; cases rightRepresentation
      exact ⟨_, .bool leftSelected rightSelected⟩
  | word =>
    cases fuel with
    | zero => simp [compareType] at accepted
    | succ fuel =>
      simp only [compareType, pure, Except.pure, Except.ok.injEq] at accepted
      subst compiled
      cases leftTyped; cases rightTyped; cases leftRepresentation; cases rightRepresentation
      exact ⟨_, .word leftSelected rightSelected⟩
  | integer =>
    cases fuel with
    | zero => simp [compareType] at accepted
    | succ fuel =>
      simp only [compareType, pure, Except.pure, Except.ok.injEq] at accepted
      subst compiled
      cases leftTyped; cases rightTyped; cases leftRepresentation; cases rightRepresentation
      exact ⟨_, .integer leftSelected rightSelected⟩
  | @product leftType rightType first second firstIH secondIH =>
    cases fuel with
    | zero => simp [compareType] at accepted
    | succ fuel =>
      have generated : (show Except SourceCoreDataEquality.Error Expr from do
          let left ← compareType fuel catalog depth leftType (.first leftExpression) (.first rightExpression)
          let right ← compareType fuel catalog depth rightType (.second leftExpression) (.second rightExpression)
          pure (.ifE left right (.bool false))) = .ok compiled := by
        have shape := first.product_contract_shape (right := rightType) catalog.callableContracts
        cases leftType <;> try cases first
        all_goals simpa only [compareType, shape, Bool.false_eq_true, ↓reduceIte] using accepted
      obtain ⟨leftCode, leftCompiled, generated⟩ := bind_ok generated
      obtain ⟨rightCode, rightCompiled, generated⟩ := bind_ok generated
      simp only [pure, Except.pure, Except.ok.injEq] at generated
      subst compiled
      cases leftTyped with
      | pair firstTyped secondTyped => cases rightTyped with
        | pair otherFirstTyped otherSecondTyped => cases leftRepresentation with
          | product firstRepresentation secondRepresentation => cases rightRepresentation with
            | product otherFirstRepresentation otherSecondRepresentation =>
              obtain ⟨firstResult, firstTree⟩ := firstIH leftCompiled firstRepresentation otherFirstRepresentation
                firstTyped otherFirstTyped (.first leftSelected) (.first rightSelected)
              obtain ⟨secondResult, secondTree⟩ := secondIH rightCompiled secondRepresentation otherSecondRepresentation
                secondTyped otherSecondTyped (.second leftSelected) (.second rightSelected)
              exact ⟨_, .product firstTree secondTree⟩

/-- Scalar comparisons from a prepared initializer work in its real captured
environment and in any later store, including an OrderedMapping helper suffix. -/
theorem prepared_tree {checked : SourceCoreDataCatalog.Checked} (prepared : Prepared checked)
    (scalar : ScalarType prepared.type) {identities : Dynamic.Value → Word → Prop}
    {sourceLeft sourceRight : Dynamic.Value} {leftValue rightValue : Value}
    (leftRepresentation : ValueRep checked.catalog sourceLeft leftValue)
    (rightRepresentation : ValueRep checked.catalog sourceRight rightValue)
    (leftTyped : ValueHasType leftValue prepared.type checked.catalog.definitions)
    (rightTyped : ValueHasType rightValue prepared.type checked.catalog.definitions)
    (environment : Environment) (initialStore store : Store) :
    ∃ result, Tree identities store
      (.pair leftValue rightValue :: DataEqualityInstalled.captured prepared.bodies.length
        (DataEqualityInstalled.allocatedEnvironment checked.catalog initialStore.length environment))
      (prepared.body.rename (DataEqualityInstalled.offset prepared.bodies.length).lift)
      sourceLeft sourceRight result := by
  apply tree_of_compareType scalar prepared.bodyGenerated leftRepresentation rightRepresentation leftTyped rightTyped
  · exact .first (.var rfl)
  · exact .second (.var rfl)

/-- The prepared comparator supplies OrderedMapping's pure comparison law
in the actual later store; scalar/product comparisons perform no heap effects. -/
theorem prepared_compares {checked : SourceCoreDataCatalog.Checked} (prepared : Prepared checked)
    (scalar : ScalarType prepared.type) (layout : OrderedMapping.Layout) (keyType : layout.keyType = prepared.type)
    {identities : Dynamic.Value → Word → Prop} (faithful : IdentityFaithful identities)
    {sourceLeft sourceRight : Dynamic.Value} {leftValue rightValue : Value}
    (leftRepresentation : ValueRep checked.catalog sourceLeft leftValue)
    (rightRepresentation : ValueRep checked.catalog sourceRight rightValue)
    (leftTyped : ValueHasType leftValue prepared.type checked.catalog.definitions)
    (rightTyped : ValueHasType rightValue prepared.type checked.catalog.definitions)
    (environment : Environment) (initialStore store : Store) :
    ∃ result, (result = true ↔ Dynamic.ValueEquivalent sourceLeft sourceRight) ∧
      OrderedMapping.Compares layout
        (.closure (.product prepared.type prepared.type) .bool
          (prepared.body.rename (DataEqualityInstalled.offset prepared.bodies.length).lift)
          (DataEqualityInstalled.captured prepared.bodies.length
            (DataEqualityInstalled.allocatedEnvironment checked.catalog initialStore.length environment)))
        leftValue rightValue result store := by
  obtain ⟨result, tree⟩ := prepared_tree prepared scalar leftRepresentation rightRepresentation
    leftTyped rightTyped environment initialStore store
  exact ⟨result, tree.meaning faithful, by simpa only [keyType] using tree.compares layout⟩

/-- Actual initialization followed by invocation preserves independent source
key equality. Child comparisons and closure installation are both proved,
without an execution-correctness premise supplied by a caller. -/
theorem prepared_compare_preserves {checked : SourceCoreDataCatalog.Checked} (prepared : Prepared checked)
    (scalar : ScalarType prepared.type) {identities : Dynamic.Value → Word → Prop}
    (faithful : IdentityFaithful identities)
    {sourceLeft sourceRight : Dynamic.Value} {leftValue rightValue : Value}
    (leftRepresentation : ValueRep checked.catalog sourceLeft leftValue)
    (rightRepresentation : ValueRep checked.catalog sourceRight rightValue)
    (leftTyped : ValueHasType leftValue prepared.type checked.catalog.definitions)
    (rightTyped : ValueHasType rightValue prepared.type checked.catalog.definitions)
    (environment : Environment) (store : Store) (leftExpression rightExpression : Expr)
    (leftSelected : Selects environment leftExpression leftValue)
    (rightSelected : Selects environment rightExpression rightValue) :
    ∃ result, (result = true ↔ Dynamic.ValueEquivalent sourceLeft sourceRight) ∧
      Evaluates environment store
        (.letE prepared.expression (.apply (.var 0)
          (.pair (leftExpression.weakenAt 0) (rightExpression.weakenAt 0))))
        (.bool result)
        (store ++ DataEqualityInstalled.cells
          (DataEqualityInstalled.allocatedEnvironment checked.catalog store.length environment) prepared.bodies) := by
  obtain ⟨result, tree⟩ := prepared_tree prepared scalar leftRepresentation rightRepresentation leftTyped rightTyped
    environment store (store ++ DataEqualityInstalled.cells
      (DataEqualityInstalled.allocatedEnvironment checked.catalog store.length environment) prepared.bodies)
  refine ⟨result, tree.meaning faithful, .letE (DataEqualityInstalled.prepared_evaluates_exact prepared environment store) ?_⟩
  exact .apply (.var rfl) (.pair ((leftSelected.weaken _).evaluates _) ((rightSelected.weaken _).evaluates _)) tree.evaluates

end Solcore.SourceSemantics.CoreLowering.DataEqualityScalarCertificates
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.DataPatternEncoding
/-! Bridge from the authenticated public data encoder to independent source
values. The profile below only bounds supported forms; actual constructor
metadata and Core payloads come from successful encoding. -/

set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.DataPatternEncoding
open Core Frontend Frontend.SourceInference
open DataPatternValues DataPatternTypedValues DataPatternAuthenticity
abbrev PublicValue := SourceCoreDataValues.Value
abbrev EncodingContext := SourceCoreDataValues.Context

inductive TypeProfile : TypeSystem.Ty → Prop where
  | unit : TypeProfile .unit
  | bool : TypeProfile .bool
  | word : TypeProfile .word
  | integer : TypeProfile .integer
  | product {left right : TypeSystem.Ty} : TypeProfile left → TypeProfile right → TypeProfile (.product left right)
  | nominal {type : TypeSystem.Ty} {declaration : Resolved.DeclarationId} {arguments : List TypeSystem.Ty}
      (parts : SourceCoreDataCatalog.nominalParts type = some (declaration, arguments)) : TypeProfile type

mutual
  inductive CarrierProfile : PublicValue → Prop where
    | unit : CarrierProfile .unit
    | bool (value : Bool) : CarrierProfile (.bool value)
    | word (value : Word) : CarrierProfile (.word value)
    | integer (value : Int) : CarrierProfile (.integer value)
    | product {left right : PublicValue} : CarrierProfile left → CarrierProfile right → CarrierProfile (.product left right)
    | constructed {metadata : DataConstructorInstantiation} {payloads : List PublicValue}
        (types : ∀ type ∈ metadata.payloadTypes, TypeProfile type)
        (values : CarriersProfile payloads) : CarrierProfile (.constructed metadata payloads)
  inductive CarriersProfile : List PublicValue → Prop where
    | nil : CarriersProfile []
    | cons {head : PublicValue} {tail : List PublicValue} : CarrierProfile head → CarriersProfile tail → CarriersProfile (head :: tail)
end

mutual
  /-- Structural public/source identity, retaining all nominal metadata. -/
  inductive Means : PublicValue → Dynamic.Value → Prop where
    | unit : Means .unit .unit
    | bool (value : Bool) : Means (.bool value) (.bool value)
    | word (value : Word) : Means (.word value) (.word value)
    | integer (value : Int) : Means (.integer value) (.integer value)
    | product {left right : PublicValue} {a b : Dynamic.Value} : Means left a → Means right b → Means (.product left right) (.product a b)
    | constructed {metadata : DataConstructorInstantiation} {payloads : List PublicValue} {arguments : List Dynamic.Value} :
        Meanings payloads arguments → Means (.constructed metadata payloads) (.constructed metadata arguments)
  inductive Meanings : List PublicValue → List Dynamic.Value → Prop where
    | nil : Meanings [] []
    | cons {head : PublicValue} {tail : List PublicValue} {source : Dynamic.Value} {sources : List Dynamic.Value} :
        Means head source → Meanings tail sources → Meanings (head :: tail) (source :: sources)
end

theorem Means.functional {value : PublicValue} {left right : Dynamic.Value}
    (first : Means value left) (second : Means value right) : left = right := by
  induction first using Means.rec
      (motive_2 := fun values sources _ => ∀ other, Meanings values other → sources = other) generalizing right with
  | unit => cases second; rfl
  | bool => cases second; rfl
  | word => cases second; rfl
  | integer => cases second; rfl
  | product _ _ leftIH rightIH =>
    cases second with
    | product left right => rw [leftIH left, rightIH right]
  | constructed _ ih => cases second with
    | constructed values => rw [ih _ values]
  | nil => rename_i other relation; cases relation; rfl
  | cons _ _ headIH tailIH =>
    rename_i other relation
    cases relation with
    | cons head tail => rw [headIH head, tailIH _ tail]

private theorem bind_ok {α β ε : Type} {first : Except ε α} {next : α → Except ε β} {value : β}
    (accepted : first >>= next = .ok value) : ∃ input, first = .ok input ∧ next input = .ok value := by
  cases first <;> simp_all [bind, Except.bind]
private theorem mapError_ok {α ε δ : Type} {first : Except ε α} {convert : ε → δ} {value : α}
    (accepted : first.mapError convert = .ok value) : first = .ok value := by
  cases first <;> cases accepted
  rfl

private theorem constructed_encoding {fuel : Nat} {context : EncodingContext} {expected : TypeSystem.Ty}
    {metadata : DataConstructorInstantiation} {payloads : List PublicValue} {core : Value}
    (profile : TypeProfile expected)
    (accepted : SourceCoreDataValues.encodeRaw (fuel + 1) context expected (.constructed metadata payloads) = .ok core) :
    metadata.resultType = expected ∧ ∃ tag payload,
      context.checked.catalog.resolveConstructor context.signatures metadata = .ok tag ∧
      SourceCoreDataValues.encodePayloadsRaw fuel context metadata.payloadTypes payloads 0 = .ok payload ∧
      core = .constructed tag payload := by
  cases expected <;> try (solve | cases profile)
  all_goals try (solve | cases profile with | nominal parts => cases parts)
  all_goals
    simp only [SourceCoreDataValues.encodeRaw] at accepted
    split at accepted
    · rename_i same
      obtain ⟨tag, resolved, accepted⟩ := bind_ok accepted
      obtain ⟨payload, encoded, accepted⟩ := bind_ok accepted
      cases accepted
      exact ⟨same, tag, payload, mapError_ok resolved, encoded, rfl⟩
    · simp_all [pure, Except.pure, bind, Except.bind, throw]

private theorem nominal_result {context : EncodingContext} {metadata : DataConstructorInstantiation} {tag : ConstructorId}
    (accepted : context.checked.catalog.resolveConstructor context.signatures metadata = .ok tag) :
    ∃ declaration arguments, SourceCoreDataCatalog.nominalParts metadata.resultType = some (declaration, arguments) := by
  obtain ⟨signature, _, _, _, _, result, _⟩ := metadataFacts accepted
  rw [result]
  exact ⟨_, _, nominalParts_nominal _ _⟩

private theorem constructed_nonNominal {fuel : Nat} {context : EncodingContext} {expected : TypeSystem.Ty}
    {metadata : DataConstructorInstantiation} {payloads : List PublicValue} {core : Value}
    (profile : TypeProfile expected) (notNominal : SourceCoreDataCatalog.nominalParts expected = none)
    (accepted : SourceCoreDataValues.encodeRaw (fuel + 1) context expected (.constructed metadata payloads) = .ok core) : False := by
  obtain ⟨same, tag, _, resolved, _, _⟩ := constructed_encoding profile accepted
  obtain ⟨_, _, nominal⟩ := nominal_result resolved
  rw [same, notNominal] at nominal
  cases nominal


private def EncodingSound (fuel : Nat) (context : EncodingContext) : Prop :=
  ∀ type value core, TypeProfile type → CarrierProfile value →
    SourceCoreDataValues.encodeRaw fuel context type value = .ok core →
    ∃ source, Means value source ∧ TypedValueRep context.checked.catalog context.signatures type source core

private def PayloadSound (fuel : Nat) (context : EncodingContext) : Prop :=
  ∀ types values index core, (∀ type ∈ types, TypeProfile type) → CarriersProfile values →
    SourceCoreDataValues.encodePayloadsRaw fuel context types values index = .ok core →
    ∃ sources cores, Meanings values sources ∧ TypedValuesRep context.checked.catalog context.signatures types sources cores ∧
      core = packValues cores

private theorem constructed_sound {fuel : Nat} {context : EncodingContext} (induction : PayloadSound fuel context)
    {type : TypeSystem.Ty} {value : Value} {metadata : DataConstructorInstantiation} {payloads : List PublicValue}
    {declaration : Resolved.DeclarationId} {arguments : List TypeSystem.Ty}
    (nominal : SourceCoreDataCatalog.nominalParts type = some (declaration, arguments))
    (types : ∀ type ∈ metadata.payloadTypes, TypeProfile type) (values : CarriersProfile payloads)
    (accepted : SourceCoreDataValues.encodeRaw (fuel + 1) context type (.constructed metadata payloads) = .ok value) :
    ∃ source, Means (.constructed metadata payloads) source ∧ TypedValueRep context.checked.catalog context.signatures type source value := by
  obtain ⟨same, tag, payload, authenticated, encoded, valueEq⟩ := constructed_encoding (.nominal nominal) accepted
  obtain ⟨sources, cores, meanings, representations, packing⟩ := induction _ _ _ _ types values encoded
  subst value
  subst payload
  exact ⟨.constructed metadata sources, .constructed meanings, .constructed nominal same authenticated representations⟩

private theorem raw_sound (fuel : Nat) (context : EncodingContext) : EncodingSound fuel context ∧ PayloadSound fuel context := by
  induction fuel with
  | zero =>
    constructor
    · intro type value core typeProfile valueProfile accepted
      cases accepted
    · intro types values index core typesProfile valuesProfile accepted
      cases types with
      | nil => cases values with
        | nil => simp [SourceCoreDataValues.encodePayloadsRaw] at accepted; subst core; exact ⟨[], [], .nil, .nil, rfl⟩
        | cons => simp [SourceCoreDataValues.encodePayloadsRaw, bind, Except.bind, throw] at accepted
      | cons type types =>
        simp only [SourceCoreDataValues.encodePayloadsRaw] at accepted
        split at accepted <;> cases accepted
  | succ fuel ih =>
    constructor
    · intro type value core typeProfile valueProfile accepted
      cases typeProfile with
      | unit =>
        cases valueProfile <;> try (solve | cases accepted)
        case unit => cases accepted; exact ⟨.unit, .unit, .unit⟩
        case constructed types values => exact False.elim (constructed_nonNominal .unit rfl accepted)
      | bool =>
        cases valueProfile <;> try (solve | cases accepted)
        case bool actual => cases accepted; exact ⟨.bool actual, .bool _, .bool _⟩
        case constructed types values => exact False.elim (constructed_nonNominal .bool rfl accepted)
      | word =>
        cases valueProfile <;> try (solve | cases accepted)
        case word actual => cases accepted; exact ⟨.word actual, .word _, .word _⟩
        case constructed types values => exact False.elim (constructed_nonNominal .word rfl accepted)
      | integer =>
        cases valueProfile <;> try (solve | cases accepted)
        case integer actual => cases accepted; exact ⟨.integer actual, .integer _, .integer _⟩
        case constructed types values => exact False.elim (constructed_nonNominal .integer rfl accepted)
      | product leftTypeProfile rightTypeProfile =>
        cases valueProfile <;> try (solve | cases accepted)
        case constructed types values => exact False.elim (constructed_nonNominal (.product leftTypeProfile rightTypeProfile) rfl accepted)
        case product leftProfile rightProfile =>
          simp only [SourceCoreDataValues.encodeRaw] at accepted
          obtain ⟨leftCore, leftEncoded, accepted⟩ := bind_ok accepted
          obtain ⟨rightCore, rightEncoded, accepted⟩ := bind_ok accepted
          cases accepted
          obtain ⟨leftSource, leftMeaning, leftRepresentation⟩ := ih.1 _ _ _ leftTypeProfile leftProfile (mapError_ok leftEncoded)
          obtain ⟨rightSource, rightMeaning, rightRepresentation⟩ := ih.1 _ _ _ rightTypeProfile rightProfile (mapError_ok rightEncoded)
          exact ⟨.product leftSource rightSource, .product leftMeaning rightMeaning, .product leftRepresentation rightRepresentation⟩
      | nominal nominal =>
        cases type <;> try (solve | cases nominal)
        case constructor constructor =>
          cases constructor <;> try (solve | cases nominal)
          case declaration declaration =>
            cases valueProfile <;> try (solve | cases accepted)
            case constructed types values => exact constructed_sound ih.2 nominal types values accepted
        case application function argument =>
          cases valueProfile <;> try (solve | cases accepted)
          case constructed types values => exact constructed_sound ih.2 nominal types values accepted
    · intro types values index core typesProfile valuesProfile accepted
      by_cases length : types.length = values.length
      · cases types with
        | nil =>
          cases values with
          | nil => simp [SourceCoreDataValues.encodePayloadsRaw] at accepted; subst core; exact ⟨[], [], .nil, .nil, rfl⟩
          | cons => simp at length
        | cons type types =>
          cases values with
          | nil => simp at length
          | cons value values =>
            cases valuesProfile with
            | cons headProfile tailProfile =>
              have headType := typesProfile type (by simp)
              have tailTypes : ∀ type ∈ types, TypeProfile type := fun t member => typesProfile t (by simp [member])
              cases types with
              | nil =>
                have empty : values = [] := by simpa using length.symm
                subst values
                simp only [SourceCoreDataValues.encodePayloadsRaw, length, ne_eq, not_true_eq_false, ↓reduceIte] at accepted
                obtain ⟨source, meaning, representation⟩ := ih.1 _ _ _ headType headProfile (mapError_ok accepted)
                exact ⟨[source], [core], .cons meaning .nil, .cons representation .nil, rfl⟩
              | cons next types =>
                simp only [SourceCoreDataValues.encodePayloadsRaw, length, ne_eq, not_true_eq_false, ↓reduceIte] at accepted
                obtain ⟨headCore, headEncoded, accepted⟩ := bind_ok accepted
                obtain ⟨tailCore, tailEncoded, accepted⟩ := bind_ok accepted
                cases accepted
                obtain ⟨source, meaning, representation⟩ := ih.1 _ _ _ headType headProfile (mapError_ok headEncoded)
                obtain ⟨sources, cores, meanings, representations, packed⟩ := ih.2 _ _ _ _ tailTypes tailProfile tailEncoded
                cases cores with
                | nil => cases representations
                | cons first cores =>
                  refine ⟨source :: sources, headCore :: first :: cores, .cons meaning meanings, .cons representation representations, ?_⟩
                  simp only [packValues]
                  rw [packed]
      · unfold SourceCoreDataValues.encodePayloadsRaw at accepted
        simp [length, bind, Except.bind, throw] at accepted

/-- Successful public encoding automatically supplies the typed independent
value relation inside the stated scalar/product/nominal feature profile. -/
theorem encodes_represents {fuel : Nat} {context : EncodingContext} {type : TypeSystem.Ty}
    {publicValue : PublicValue} {core : Value} (types : TypeProfile type) (values : CarrierProfile publicValue)
    (encoded : SourceCoreDataValues.Encodes fuel context type publicValue core) :
    ∃ source, Means publicValue source ∧ TypedValueRep context.checked.catalog context.signatures type source core :=
  (raw_sound fuel context).1 type publicValue core types values encoded.generated

theorem encode_represents {fuel : Nat} {context : EncodingContext} {type : TypeSystem.Ty}
    {publicValue : PublicValue} {core : Value} (types : TypeProfile type) (values : CarrierProfile publicValue)
    (encoded : SourceCoreDataValues.encode fuel context type publicValue = .ok core) :
    ∃ source, Means publicValue source ∧ TypedValueRep context.checked.catalog context.signatures type source core :=
  encodes_represents types values (SourceCoreDataValues.encodes_of_encode encoded)

theorem decode_represents {fuel : Nat} {context : EncodingContext} {type : TypeSystem.Ty}
    {publicValue : PublicValue} {core : Value} (types : TypeProfile type) (values : CarrierProfile publicValue)
    (decoded : SourceCoreDataValues.decode fuel context type core = .ok publicValue) :
    ∃ source, Means publicValue source ∧ TypedValueRep context.checked.catalog context.signatures type source core :=
  encodes_represents types values (SourceCoreDataValues.encodes_of_decode decoded)


/-- Compose the actual public boundary and actual pattern compiler, producing
both the independent source value and the complete finite matcher outcome. -/
theorem encode_matcher_run_preserves (compilation : SourceCoreDataMatches.Context)
    (compilationFuel encodingFuel : Nat) (source : TypedSource) (scope : SourceCoreDataMatches.Scope)
    (site : StatementId) (span : Syntax.SourceSpan) (expected : TypeSystem.Ty) (pattern : TypedMatchPattern)
    (compiled : SourceCoreDataMatches.CertifiedPattern compilation.checked.catalog.definitions)
    (accepted : SourceCoreDataMatches.compilePattern compilation compilationFuel source scope site span expected pattern = .ok compiled)
    (context : SourceSemantics.Context) (valid : DataPatternLeaves.ContextValid compilation context)
    {publicValue : PublicValue} {core : Value} (types : TypeProfile expected) (values : CarrierProfile publicValue)
    (encoded : SourceCoreDataValues.encode encodingFuel ⟨compilation.checked, compilation.signatures⟩ expected publicValue = .ok core)
    (environment : Environment) (store : Store) :
    ∃ sourceValue outcome, Means publicValue sourceValue ∧
      DataPatternLeaves.OutcomeRep compilation.checked.catalog context pattern compiled.pattern sourceValue outcome ∧
      (∃ required, ∀ fuel, required ≤ fuel →
        runStateful fuel (State.initial (.apply compiled.pattern.matcher (.var 0)) (core :: environment) store) = .done outcome store) ∧
      (∀ fuel actual finalStore,
        runStateful fuel (State.initial (.apply compiled.pattern.matcher (.var 0)) (core :: environment) store) = .done actual finalStore →
        actual = outcome ∧ finalStore = store) := by
  obtain ⟨sourceValue, meaning, represented⟩ := encode_represents types values encoded
  obtain ⟨outcome, outcomeMeaning, finite, reflected⟩ := DataPatternDecision.compilePattern_run_preserves compilation compilationFuel
    source scope site span expected pattern compiled accepted context valid represented environment store
  exact ⟨sourceValue, outcome, meaning, outcomeMeaning, finite, reflected⟩

end Solcore.SourceSemantics.CoreLowering.DataPatternEncoding
end
