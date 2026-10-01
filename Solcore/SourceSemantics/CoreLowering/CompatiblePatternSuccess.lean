import Solcore.SourceSemantics.CoreLowering.CompatiblePatternValues
import Solcore.SourceSemantics.CoreLowering.CompatiblePatternExecution
import Solcore.SourceSemantics.CoreLowering.CompatiblePatternMetadata

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
