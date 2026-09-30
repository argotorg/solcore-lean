import Solcore.SourceSemantics.CoreLowering.BasicStatementCertificates
import Solcore.SourceSemantics.CoreLowering.BasicStatements
import Solcore.Core.FirstOrderWeakening

/-! Structural certificates for complete basic statement lists. Declarative
binder-context extensions are explicit and no execution result is assumed. -/

set_option autoImplicit false

namespace Solcore.SourceSemantics.CoreLowering.BasicStatements

open Frontend Frontend.SourceInference TypeSystem LocalCell

theorem Metadata.read {source : TypedSource} {id : StatementId}
    {node : StatementNode} {type : Core.Ty}
    (metadata : Metadata source id node type) (unique : NodeOccurrencesUnique source) :
    SourceCoreBasic.readStatement source id = .ok (node, type) :=
  SourceCoreBasic.readStatement_eq metadata.owned
    (lookupStatement?_complete unique metadata.contains) (metadata.types.lower _)

theorem BinderCertificate.lower
    {source : TypedSource} {scope : SourceCoreLocalCell.Scope} {binder : TypedBinder} {type : Core.Ty}
    (certificate : BinderCertificate source scope binder type) :
    SourceCoreBasic.lowerBinder source scope binder = .ok type := by
  simp [SourceCoreBasic.lowerBinder, certificate.owned, certificate.monomorphic,
    certificate.requirements, certificate.runtime, certificate.fresh,
    SourceCoreBasic.projectType, certificate.types.lower _, Except.mapError]

theorem AssignmentCertificate.lower
    {source : TypedSource} {scope : SourceCoreLocalCell.Scope} {assignment : AssignmentResolution}
    {operator : Syntax.ValueAssignOp} {index : Nat} {type : Core.Ty}
    (certificate : AssignmentCertificate source scope assignment operator index type) :
    SourceCoreBasic.lowerAssignment source scope assignment operator = .ok (index, type) := by
  simp [SourceCoreBasic.lowerAssignment, certificate.equal, certificate.owned,
    certificate.requirements, certificate.bare, certificate.slot,
    SourceCoreBasic.projectType, certificate.types.lower _, Except.mapError,
    SourceCoreBasic.ensureType, bind, Except.bind, pure, Pure.pure, Except.pure]

/-- A structural statement certificate additionally carries the declarative
source binder-context extensions. None of its fields assumes compilation or
evaluation. The static context requirement is intentionally not inferred from
the basic compiler's lexical scope checks. -/
inductive Tree (source : TypedSource) (reason : Core.Word) :
    SourceCoreLocalCell.Scope → Context → List StatementId → Core.Ty → Core.Expr → Nat → Prop where
  | nil {scope context} :
      Tree source reason scope context [] .unit (Core.LanguageResult.success .unit) 0
  | letUninitialized
      {scope context middleContext id rest node binder payloadType resultType body depth}
      (metadata : Metadata source id node .unit)
      (form : node.form = .letDecl binder none)
      (binding : BinderCertificate source scope binder payloadType)
      (extension : BinderExtends source.owner context binder middleContext)
      (tail : Tree source reason ((binder.id, payloadType) :: scope) middleContext
        rest resultType body depth) :
      Tree source reason scope context (id :: rest) resultType
        (Core.LocalSequence.letUninitialized payloadType body) (depth + 1)
  | letInitialized
      {scope context middleContext id rest node binder payloadType resultType
        initializer initializerCode body initializerDepth bodyDepth}
      (metadata : Metadata source id node .unit)
      (form : node.form = .letDecl binder (some initializer))
      (binding : BinderCertificate source scope binder payloadType)
      (extension : BinderExtends source.owner context binder middleContext)
      (value : BasicExpressions.Tree source scope reason initializer payloadType initializerCode initializerDepth)
      (tail : Tree source reason ((binder.id, payloadType) :: scope) middleContext
        rest resultType body bodyDepth) :
      Tree source reason scope context (id :: rest) resultType
        (Core.LocalSequence.letInitialized resultType payloadType initializerCode body)
        (max initializerDepth bodyDepth + 1)
  | assign
      {scope context id rest node assignment index payloadType resultType rhs rhsCode body rhsDepth bodyDepth}
      (metadata : Metadata source id node .unit)
      (form : node.form = .assignValue assignment .equal rhs)
      (target : AssignmentCertificate source scope assignment .equal index payloadType)
      (value : BasicExpressions.Tree source scope reason rhs payloadType rhsCode rhsDepth)
      (tail : Tree source reason scope context rest resultType body bodyDepth) :
      Tree source reason scope context (id :: rest) resultType
        (Core.LocalSequence.assign resultType (.var index) rhsCode body) (max rhsDepth bodyDepth + 1)
  | discard
      {scope context id rest node valueId valueType resultType valueCode body valueDepth bodyDepth}
      (metadata : Metadata source id node .unit)
      (form : node.form = .expression valueId true)
      (value : BasicExpressions.Tree source scope reason valueId valueType valueCode valueDepth)
      (tail : Tree source reason scope context rest resultType body bodyDepth) :
      Tree source reason scope context (id :: rest) resultType
        (Core.LocalSequence.discard resultType valueCode body) (max valueDepth bodyDepth + 1)
  | returnValue
      {scope context id node valueId resultType valueCode valueDepth}
      (rest : List StatementId)
      (metadata : Metadata source id node resultType)
      (form : node.form = .returnStmt (some valueId))
      (value : BasicExpressions.Tree source scope reason valueId resultType valueCode valueDepth) :
      Tree source reason scope context (id :: rest) resultType valueCode (valueDepth + 1)
  | returnUnit {scope context id node}
      (rest : List StatementId)
      (metadata : Metadata source id node .unit)
      (form : node.form = .returnStmt none) :
      Tree source reason scope context (id :: rest) .unit (Core.LanguageResult.success .unit) 1
  | tailExpression
      {scope context id node valueId resultType valueCode valueDepth}
      (metadata : Metadata source id node resultType)
      (form : node.form = .expression valueId false)
      (value : BasicExpressions.Tree source scope reason valueId resultType valueCode valueDepth) :
      Tree source reason scope context [id] resultType valueCode (valueDepth + 1)

theorem Tree.cellPayload
    {source : TypedSource} {reason : Core.Word} {scope : SourceCoreLocalCell.Scope}
    {context : Context} {statements : List StatementId} {type : Core.Ty} {code : Core.Expr} {depth : Nat}
    (tree : Tree source reason scope context statements type code depth) : Core.CellPayload type := by
  induction tree with
  | nil | returnUnit => exact .unit
  | returnValue _ _ _ value | tailExpression _ _ value => exact value.cellPayload
  | letUninitialized _ _ _ _ _ ih | letInitialized _ _ _ _ _ _ ih
  | assign _ _ _ _ _ ih | discard _ _ _ _ ih => exact ih

theorem Tree.hasType
    {source : TypedSource} {reason : Core.Word} {scope : SourceCoreLocalCell.Scope}
    {context : Context} {statements : List StatementId} {type : Core.Ty} {code : Core.Expr} {depth : Nat}
    (tree : Tree source reason scope context statements type code depth) :
    Core.HasType (SourceCoreLocalCell.coreContext scope) code (Core.LanguageResult.resultType type) := by
  induction tree with
  | nil | returnUnit => exact Core.LanguageResult.success_hasType .unit
  | returnValue _ _ _ value | tailExpression _ _ value => exact value.hasType
  | letUninitialized _ _ binding _ _ ih =>
      exact Core.LocalSequence.letUninitialized_hasType (binding.types.wellFormed []) ih
  | letInitialized _ _ _ _ value tail ih =>
      exact Core.LocalSequence.letInitialized_hasType tail.cellPayload.wellFormed value.hasType ih
  | assign _ _ target value tail ih =>
      exact Core.LocalSequence.assign_hasType tail.cellPayload.wellFormed
        (.var (SourceCoreLocalCell.lookup?_context target.slot)) value.hasType ih
  | discard _ _ value tail ih =>
      exact Core.LocalSequence.discard_hasType tail.cellPayload.wellFormed value.hasType ih

theorem Tree.lower
    {source : TypedSource} {reason : Core.Word} {scope : SourceCoreLocalCell.Scope}
    {context : Context} {statements : List StatementId} {type : Core.Ty} {code : Core.Expr} {depth : Nat}
    (tree : Tree source reason scope context statements type code depth)
    (unique : NodeOccurrencesUnique source) (fuel : Nat) (enough : depth ≤ fuel) :
    SourceCoreBasic.lowerStatements fuel source scope statements type reason = .ok code := by
  induction tree generalizing fuel with
  | nil => exact SourceCoreBasic.lowerStatements_nil fuel source _ reason
  | letUninitialized metadata form binding _ _ ih =>
      cases fuel with
      | zero => omega
      | succ fuel =>
          exact SourceCoreBasic.lowerStatements_letUninitialized
            (metadata.read unique) form binding.lower (ih fuel (by omega))
  | letInitialized metadata form binding _ value _ ih =>
      cases fuel with
      | zero => omega
      | succ fuel =>
          exact SourceCoreBasic.lowerStatements_letInitialized
            (metadata.read unique) form binding.lower (value.lower unique fuel (by omega)) (ih fuel (by omega))
  | assign metadata form target value _ ih =>
      cases fuel with
      | zero => omega
      | succ fuel =>
          exact SourceCoreBasic.lowerStatements_assign
            (metadata.read unique) form target.lower (value.lower unique fuel (by omega)) (ih fuel (by omega))
  | discard metadata form value _ ih =>
      cases fuel with
      | zero => omega
      | succ fuel =>
          exact SourceCoreBasic.lowerStatements_discard
            (metadata.read unique) form (value.lower unique fuel (by omega)) (ih fuel (by omega))
  | returnValue _ metadata form value =>
      cases fuel with
      | zero => omega
      | succ fuel =>
          exact SourceCoreBasic.lowerStatements_return
            (metadata.read unique) form (value.lower unique fuel (by omega))
  | returnUnit _ metadata form =>
      cases fuel with
      | zero => omega
      | succ fuel =>
          exact SourceCoreBasic.lowerStatements_returnUnit (metadata.read unique) form
  | tailExpression metadata form value =>
      cases fuel with
      | zero => omega
      | succ fuel =>
          exact SourceCoreBasic.lowerStatements_tail
            (metadata.read unique) form (value.lower unique fuel (by omega))


inductive OutcomeRepresents (world : Core.StoreTyping) (reason : Core.Word) :
    Core.Ty → Dynamic.ControlOutcome → Core.Value → Prop where
  | fallthrough {scope environment coreEnvironment}
      (environments : EnvRepresents world scope environment coreEnvironment) :
      OutcomeRepresents world reason .unit (.fallthrough environment) (.inRight .word .unit)
  | returned (value : SourceStagedValue.Value) {type : Core.Ty}
      (typed : SourceStagedValue.coreType value = type) :
      OutcomeRepresents world reason type (.returned (StagedValue.toSource value))
        (.inRight .word (SourceStagedValue.toCore value))
  | uninitialized (location : Dynamic.Location) (type : Core.Ty) :
      OutcomeRepresents world reason type (.fault (.uninitializedLocation location))
        (.inLeft type (.word reason))

private theorem staged_runtime_type (value : SourceStagedValue.Value) (world : Core.StoreTyping) :
    Core.RuntimeValueHasType world (SourceStagedValue.toCore value) (SourceStagedValue.coreType value) := by
  induction value with
  | unit => exact .unit
  | bool => exact .bool
  | word => exact .word
  | product _ _ left right => exact .pair left right

private theorem weaken_three
    {environment : Core.Environment} {context : Core.Context} {store finalStore : Core.Store}
    {world finalWorld : Core.StoreTyping} {expression : Core.Expr} {result : Core.Value}
    {resultType referenceType valueType : Core.Ty} {reference value : Core.Value}
    (evaluation : Core.Evaluates environment store expression result finalStore)
    (typing : Core.HasType context expression (Core.LanguageResult.resultType resultType))
    (payload : Core.CellPayload resultType)
    (environmentTyped : Core.RuntimeEnvironmentHasTypes world environment context)
    (storeTyped : Core.RuntimeStoreHasTypes world store)
    (finalTyped : Core.StoreHasTypes finalWorld finalStore)
    (referenceTyped : Core.RuntimeValueHasType world reference referenceType)
    (valueTyped : Core.RuntimeValueHasType world value valueType) :
    Core.Evaluates (.unit :: value :: reference :: environment) store
      (((expression.weakenAt 0).weakenAt 0).weakenAt 0) result finalStore := by
  have first := evaluation.weakenAt_zero_cellPayload typing (.sum .word payload)
    environmentTyped storeTyped finalTyped reference
  have firstTyped : Core.HasType (referenceType :: context) (expression.weakenAt 0)
      (Core.LanguageResult.resultType resultType) := by
    simpa [Core.Context.insertAt] using typing.weakenAt (inserted := referenceType) 0
  have second := first.weakenAt_zero_cellPayload firstTyped (.sum .word payload)
    (.cons referenceTyped environmentTyped) storeTyped finalTyped value
  have secondTyped : Core.HasType (valueType :: referenceType :: context)
      ((expression.weakenAt 0).weakenAt 0) (Core.LanguageResult.resultType resultType) := by
    simpa [Core.Context.insertAt] using firstTyped.weakenAt (inserted := valueType) 0
  exact second.weakenAt_zero_cellPayload secondTyped (.sum .word payload)
    (.cons valueTyped (.cons referenceTyped environmentTyped)) storeTyped finalTyped .unit

/-- Whole-list preservation for the structural basic fragment. Child evaluation
and final-store typing are derived recursively. The only heap premise is the
initial scalar/product optional-cell representation. -/
theorem Tree.preserves
    {source : TypedSource} {reason : Core.Word} {scope : SourceCoreLocalCell.Scope}
    {context : Context} {statements : List StatementId} {type : Core.Ty} {code : Core.Expr} {depth : Nat}
    (tree : Tree source reason scope context statements type code depth)
    (unique : NodeOccurrencesUnique source) (program : Program) (evidence : Dynamic.EvidenceEnvironment)
    {environment : Dynamic.Environment} {heap : Dynamic.Heap}
    {coreEnvironment : Core.Environment} {store : Core.Store} {world : Core.StoreTyping}
    (environments : EnvRepresents world scope environment coreEnvironment)
    (heaps : HeapRepresents heap.cells store world) :
    ∃ finalContext outcome after result finalStore finalWorld,
      Dynamic.FunctionStatementsExecuteOutcome program context evidence source environment heap
        statements finalContext outcome after ∧
      OutcomeRepresents finalWorld reason type outcome result ∧
      Core.Evaluates coreEnvironment store code result finalStore ∧
      HeapRepresents after.cells finalStore finalWorld ∧ Core.WorldExtends world finalWorld := by
  induction tree generalizing environment heap coreEnvironment store world with
  | nil =>
      exact ⟨_, _, _, _, _, _, .control .nil, .fallthrough environments,
        .inRight .unit, heaps, .refl _⟩
  | @returnUnit scope context id node rest metadata form =>
      obtain ⟨_, sourceExecution, coreExecution⟩ := returnUnit_prefix (fuel := 0)
        (scope := scope) (reason := reason) metadata.contains (metadata.read unique) form
      exact ⟨_, _, _, _, _, _, sourceExecution, .returned .unit rfl, coreExecution, heaps, .refl _⟩
  | @returnValue scope context id node valueId resultType valueCode valueDepth rest metadata form value =>
      obtain ⟨sourceOutcome, result, sourceEvaluation, related, coreEvaluation⟩ :=
        value.preserves program context evidence environments heaps
      cases related with
      | value staged typed =>
          cases sourceEvaluation with
          | value sourceEvaluation =>
              obtain ⟨_, sourceExecution, coreExecution⟩ := return_prefix staged metadata.contains
                (metadata.read unique) form (value.lower unique valueDepth (Nat.le_refl _))
                sourceEvaluation coreEvaluation
              exact ⟨_, _, _, _, _, _, sourceExecution, .returned staged typed, coreExecution, heaps, .refl _⟩
      | uninitialized location =>
          cases sourceEvaluation with
          | fault sourceFault =>
              obtain ⟨_, sourceExecution, coreExecution⟩ := return_fault metadata.contains
                (metadata.read unique) form (value.lower unique valueDepth (Nat.le_refl _))
                sourceFault coreEvaluation
              exact ⟨_, _, _, _, _, _, sourceExecution, .uninitialized location _, coreExecution, heaps, .refl _⟩
  | @tailExpression scope context id node valueId resultType valueCode valueDepth metadata form value =>
      obtain ⟨sourceOutcome, result, sourceEvaluation, related, coreEvaluation⟩ :=
        value.preserves program context evidence environments heaps
      cases related with
      | value staged typed =>
          cases sourceEvaluation with
          | value sourceEvaluation =>
              obtain ⟨_, sourceExecution, coreExecution⟩ := Solcore.SourceSemantics.CoreLowering.BasicStatements.tailExpression staged metadata.contains
                (metadata.read unique) form (value.lower unique valueDepth (Nat.le_refl _))
                sourceEvaluation coreEvaluation
              exact ⟨_, _, _, _, _, _, sourceExecution, .returned staged typed, coreExecution, heaps, .refl _⟩
      | uninitialized location =>
          cases sourceEvaluation with
          | fault sourceFault =>
              obtain ⟨_, sourceExecution, coreExecution⟩ := tailExpression_fault metadata.contains
                (metadata.read unique) form (value.lower unique valueDepth (Nat.le_refl _))
                sourceFault coreEvaluation
              exact ⟨_, _, _, _, _, _, sourceExecution, .uninitialized location _, coreExecution, heaps, .refl _⟩
  | @letUninitialized scope context middleContext id rest node binder payloadType resultType body bodyDepth
      metadata form binding extension tail ih =>
      have allocated : Dynamic.Heap.Allocates heap binder.scheme.body none
          ⟨heap.cells.length⟩ ⟨heap.cells ++ [{ type := binder.scheme.body, value := none }]⟩ := .append
      obtain ⟨nextEnvironments, nextHeaps⟩ := environments.bind heaps (.uninitialized binding.types) allocated
      obtain ⟨finalContext, outcome, after, result, finalStore, finalWorld,
        tailSource, tailRelated, tailCore, finalHeaps, extended⟩ := ih nextEnvironments nextHeaps
      obtain ⟨_, sourceExecution, coreExecution⟩ := letUninitialized_prefix metadata.contains
        (metadata.read unique) form binding.lower binding.monomorphic extension binding.types heaps allocated
        (tail.lower unique bodyDepth (Nat.le_refl _)) tailSource tailCore
      exact ⟨_, _, _, _, _, _, sourceExecution, tailRelated, coreExecution, finalHeaps,
        (Core.WorldExtends.trans ⟨_, rfl⟩ extended)⟩
  | @letInitialized scope context middleContext id rest node binder payloadType resultType
      initializer initializerCode body initializerDepth bodyDepth metadata form binding extension value tail ih =>
      let fuel := max initializerDepth bodyDepth
      have valueLowered := value.lower unique fuel (Nat.le_max_left _ _)
      have tailLowered := tail.lower unique fuel (Nat.le_max_right _ _)
      obtain ⟨sourceOutcome, result, sourceEvaluation, related, coreEvaluation⟩ :=
        value.preserves program context evidence environments heaps
      cases related with
      | value staged typed =>
          cases sourceEvaluation with
          | value sourceEvaluation =>
              have binderType : binder.scheme.body = SourceStagedValue.sourceType staged :=
                binding.types.source_unique (typed ▸ stagedTypes staged)
              have allocated : Dynamic.Heap.Allocates heap binder.scheme.body (some (StagedValue.toSource staged))
                  ⟨heap.cells.length⟩
                  ⟨heap.cells ++ [{ type := binder.scheme.body, value := some (StagedValue.toSource staged) }]⟩ := .append
              have cell : CellRepresents
                  { type := binder.scheme.body, value := some (StagedValue.toSource staged) }
                  (.inRight .unit (SourceStagedValue.toCore staged)) payloadType := by
                rw [binderType, ← typed]
                exact .initialized staged
              obtain ⟨nextEnvironments, nextHeaps⟩ := environments.bind heaps cell allocated
              obtain ⟨finalContext, outcome, after, result, finalStore, finalWorld,
                tailSource, tailRelated, tailCore, finalHeaps, extended⟩ := ih nextEnvironments nextHeaps
              have shifted := tailCore.weakenAt_cellPayload tail.hasType (.sum .word tail.cellPayload)
                (nextEnvironments.runtime_hasTypes []) (nextHeaps.runtime_hasTypes [])
                finalHeaps.firstOrder_hasTypes 1 (SourceStagedValue.toCore staged)
              simp only [Core.Environment.insertAt] at shifted
              obtain ⟨_, sourceExecution, coreExecution⟩ := letInitialized_prefix staged metadata.contains
                (metadata.read unique) form (typed ▸ binding.lower) binding.monomorphic extension binderType
                (typed ▸ valueLowered) sourceEvaluation coreEvaluation heaps allocated
                (typed ▸ tailLowered) tailSource (typed ▸ shifted)
              exact ⟨_, _, _, _, _, _, sourceExecution, tailRelated, typed ▸ coreExecution, finalHeaps,
                (Core.WorldExtends.trans ⟨_, rfl⟩ extended)⟩
      | uninitialized location =>
          cases sourceEvaluation with
          | fault sourceFault =>
              obtain ⟨_, sourceExecution, coreExecution⟩ := letInitialized_fault metadata.contains
                (metadata.read unique) form binding.lower binding.monomorphic valueLowered tailLowered
                sourceFault coreEvaluation
              exact ⟨_, _, _, _, _, _, sourceExecution, .uninitialized location _, coreExecution, heaps, .refl _⟩
  | @discard scope context id rest node valueId valueType resultType valueCode body valueDepth bodyDepth
      metadata form value tail ih =>
      let fuel := max valueDepth bodyDepth
      have valueLowered := value.lower unique fuel (Nat.le_max_left _ _)
      have tailLowered := tail.lower unique fuel (Nat.le_max_right _ _)
      obtain ⟨sourceOutcome, result, sourceEvaluation, related, coreEvaluation⟩ :=
        value.preserves program context evidence environments heaps
      cases related with
      | value staged typed =>
          cases sourceEvaluation with
          | value sourceEvaluation =>
              obtain ⟨finalContext, outcome, after, result, finalStore, finalWorld,
                tailSource, tailRelated, tailCore, finalHeaps, extended⟩ := ih environments heaps
              have shifted := tailCore.weakenAt_zero_cellPayload tail.hasType (.sum .word tail.cellPayload)
                (environments.runtime_hasTypes []) (heaps.runtime_hasTypes [])
                finalHeaps.firstOrder_hasTypes (SourceStagedValue.toCore staged)
              obtain ⟨_, sourceExecution, coreExecution⟩ := discard_prefix staged metadata.contains
                (metadata.read unique) form valueLowered sourceEvaluation coreEvaluation tailLowered tailSource shifted
              exact ⟨_, _, _, _, _, _, sourceExecution, tailRelated, coreExecution, finalHeaps, extended⟩
      | uninitialized location =>
          cases sourceEvaluation with
          | fault sourceFault =>
              obtain ⟨_, sourceExecution, coreExecution⟩ := discard_fault metadata.contains
                (metadata.read unique) form valueLowered tailLowered sourceFault coreEvaluation
              exact ⟨_, _, _, _, _, _, sourceExecution, .uninitialized location _, coreExecution, heaps, .refl _⟩
  | @assign scope context id rest node assignment index payloadType resultType rhs rhsCode body rhsDepth bodyDepth
      metadata form target value tail ih =>
      let fuel := max rhsDepth bodyDepth
      have valueLowered := value.lower unique fuel (Nat.le_max_left _ _)
      have tailLowered := tail.lower unique fuel (Nat.le_max_right _ _)
      obtain ⟨sourceOutcome, result, sourceEvaluation, related, coreEvaluation⟩ :=
        value.preserves program context evidence environments heaps
      cases related with
      | value staged typed =>
          cases sourceEvaluation with
          | value sourceEvaluation =>
              obtain ⟨location, updatedHeap, updatedStore, assignmentSource, lookup, ⟨oldValue, readable⟩,
                written, updatedHeaps, updatedEnvironments⟩ := equal_assignment environments heaps (.refl _) heaps
                  target.slot target.bare staged typed sourceEvaluation
              obtain ⟨finalContext, outcome, after, result, finalStore, finalWorld,
                tailSource, tailRelated, tailCore, finalHeaps, extended⟩ := ih updatedEnvironments updatedHeaps
              have rhsShifted := coreEvaluation.weakenAt_zero_cellPayload value.hasType
                (.sum .word value.cellPayload) (environments.runtime_hasTypes [])
                (heaps.runtime_hasTypes []) heaps.firstOrder_hasTypes
                (.cellRef (Core.OptionalCell.cellType payloadType) location.index)
              have referenceTyped : Core.RuntimeValueHasType world
                  (.cellRef (Core.OptionalCell.cellType payloadType) location.index)
                  (Core.OptionalCell.referenceType payloadType) := by
                obtain ⟨reference, found, referenceTyping⟩ :=
                  (environments.runtime_hasTypes []).lookup (SourceCoreLocalCell.lookup?_context target.slot)
                rw [lookup] at found
                cases found
                exact referenceTyping
              have shifted := weaken_three tailCore tail.hasType tail.cellPayload
                (updatedEnvironments.runtime_hasTypes []) (updatedHeaps.runtime_hasTypes [])
                finalHeaps.firstOrder_hasTypes referenceTyped (staged_runtime_type staged world)
              obtain ⟨_, sourceExecution, coreExecution⟩ := assign_prefix metadata.contains
                (metadata.read unique) form target.lower valueLowered tailLowered assignmentSource
                lookup rhsShifted readable written tailSource shifted
              exact ⟨_, _, _, _, _, _, sourceExecution, tailRelated, coreExecution, finalHeaps, extended⟩
      | uninitialized location =>
          cases sourceEvaluation with
          | fault sourceFault =>
              obtain ⟨targetLocation, cell, current, sourceLookup, coreLookup, _, read, _, cellRelated⟩ :=
                environments.lookup_heap heaps target.slot
              let captured : Dynamic.ResolvedPlace := {
                location := targetLocation, rootType := cell.type, valueType := assignment.target.type,
                projections := [], selected := cell.value
              }
              have resolved : Dynamic.SourcePlaceResolves program context evidence source environment
                  heap assignment.target captured heap := by
                apply Dynamic.SourcePlaceResolves.intro sourceLookup read
                · rw [target.bare]; exact .nil
                · exact read
                · exact cellRelated.rootInitialValue
                · exact .nil
              have rhsShifted := coreEvaluation.weakenAt_zero_cellPayload value.hasType
                (.sum .word value.cellPayload) (environments.runtime_hasTypes [])
                (heaps.runtime_hasTypes []) heaps.firstOrder_hasTypes
                (.cellRef (Core.OptionalCell.cellType payloadType) targetLocation.index)
              obtain ⟨_, sourceExecution, coreExecution⟩ := assign_fault metadata.contains
                (metadata.read unique) form target.lower valueLowered tailLowered
                (.rhs resolved sourceFault) coreLookup rhsShifted
              exact ⟨_, _, _, _, _, _, sourceExecution, .uninitialized location _, coreExecution, heaps, .refl _⟩

/-- The finite basic grammar supplies its evaluation witness structurally.
Successful Core runs agree on the result and complete final store. This does
not assert determinism or completeness of every source fault rule. -/
theorem Tree.lower_run_preserves
    {source : TypedSource} {reason : Core.Word} {scope : SourceCoreLocalCell.Scope}
    {context : Context} {statements : List StatementId} {type : Core.Ty} {code : Core.Expr} {depth : Nat}
    (tree : Tree source reason scope context statements type code depth)
    (unique : NodeOccurrencesUnique source) (compilationFuel : Nat) (enough : depth ≤ compilationFuel)
    (program : Program) (evidence : Dynamic.EvidenceEnvironment)
    {environment : Dynamic.Environment} {heap : Dynamic.Heap}
    {coreEnvironment : Core.Environment} {store : Core.Store} {world : Core.StoreTyping}
    (environments : EnvRepresents world scope environment coreEnvironment)
    (heaps : HeapRepresents heap.cells store world) :
    SourceCoreBasic.lowerStatements compilationFuel source scope statements type reason = .ok code ∧
    Core.infer? (SourceCoreLocalCell.coreContext scope) code = some (Core.LanguageResult.resultType type) ∧
    ∃ finalContext outcome after result finalStore finalWorld required,
      Dynamic.FunctionStatementsExecuteOutcome program context evidence source environment heap
        statements finalContext outcome after ∧
      OutcomeRepresents finalWorld reason type outcome result ∧
      HeapRepresents after.cells finalStore finalWorld ∧ Core.WorldExtends world finalWorld ∧
      EnvRepresents finalWorld scope environment coreEnvironment ∧
      (∀ fuel, required ≤ fuel → Core.runStateful fuel (.initial code coreEnvironment store) =
        .done result finalStore) ∧
      (∀ fuel actual actualStore, Core.runStateful fuel (.initial code coreEnvironment store) =
        .done actual actualStore → actual = result ∧ actualStore = finalStore) := by
  obtain ⟨finalContext, outcome, after, result, finalStore, finalWorld,
    sourceExecution, related, coreExecution, finalHeaps, extended⟩ :=
    tree.preserves unique program evidence environments heaps
  obtain ⟨required, completes⟩ := Core.evaluation_runStateful_complete_with_sufficient_fuel coreExecution
  refine ⟨tree.lower unique compilationFuel enough, Core.infer_complete tree.hasType,
    finalContext, outcome, after, result, finalStore, finalWorld, required,
    sourceExecution, related, finalHeaps, extended, environments.extend extended, completes, ?_⟩
  intro fuel actual actualStore completed
  exact Core.evaluation_deterministic (Core.runStateful_evaluation_sound completed) coreExecution

end Solcore.SourceSemantics.CoreLowering.BasicStatements
