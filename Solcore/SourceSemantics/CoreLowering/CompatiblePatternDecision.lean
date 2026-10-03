import Solcore.SourceSemantics.CoreLowering.CompatiblePatternSuccess
import Solcore.SourceSemantics.Dynamic.PatternCompletenessProperties

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
/-- Former generated proof names retain their original types. -/
abbrev Tree.decides._simp_1_1 := @Tree.decides_with_literals._simp_1_1
abbrev Tree.decides.match_1_2 := @Tree.decides_with_literals.match_1_2
end Solcore.SourceSemantics.CoreLowering.CompatiblePatternDecision
