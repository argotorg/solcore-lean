import Solcore.SourceSemantics.CoreLowering.CellAwareStagedProjectedBitNotCommit
import Solcore.SourceSemantics.CoreLowering.CompatiblePlacePrefixReflection
import Solcore.SourceSemantics.CoreLowering.CoreEvaluationSize
import Solcore.SourceSemantics.CoreLowering.CoreContinuationAgreement

/-! Exact Unit-RHS sequencing for the absent source RHS branch. These laws
compose or invert a commit constructed from independent source semantics. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CellAwareStagedProjectedBitNotCommit
open Core Frontend SourceInference GeneralHeap DataPatternValues CompatiblePayload CompatibleHeap
open SourceCoreCompatibleDataPlaces DataPlaceExecution CoreProof

variable {checked : Checked} {registry : SourceCoreRawMetadata.Registry}
  {ambient : AmbientDefinitions checked.catalog.definitions}
    {functions : FunctionModel checked.catalog ambient}
  {cells : GenericHeap.CellModel ambient.definitions}
  {instances : GeneralizedLocalDescriptorHeap.InstanceModel ambient.definitions} {prepared : Prepared} {codes : List SourceCoreBasic.LoweredExpr}
  {environment : Environment} {store : Store} {mapping : LocationMap} {world : StoreTyping}
  {target : Location} {keys : List Value} {snapshot : Value} {before after : Dynamic.Heap}
  {updated : Dynamic.Value} {operator : Option BinaryOp} {invalid : Word}

private theorem unit_rhs (environment : Environment) (store : Store) :
    Evaluates environment store (shift 3 (LanguageResult.success .unit)) (.inRight .word .unit) store := by
  simpa only [shift, List.range, List.range.loop, List.foldl, Expr.weakenAt, LanguageResult.success] using
    (Evaluates.inRight (leftType := .word) (environment := environment) (initialStore := store) Evaluates.unit)

theorem Execution.plug (execution : Execution checked registry functions cells instances prepared codes environment store mapping world
    target keys snapshot before after updated operator invalid)
    {next : Expr} {outputType : Ty} {result : Value} {finalStore : Store}
    (continuation : Evaluates (writtenEnvironment prepared.route.rootType target (packValues keys)
      (.inRight .unit snapshot) .unit execution.replacement execution.value environment)
      execution.finalStore (shift 7 next) result finalStore) :
    Evaluates (snapshotEnvironment prepared.route.rootType target (packValues keys) (.inRight .unit snapshot) environment)
      store (CompatiblePlacePrefixReflection.remainder prepared (SourceCoreCalls.packArguments codes).type
        (LanguageResult.success .unit) next outputType operator true invalid) result finalStore := by
  obtain ⟨optional, read⟩ := execution.read
  exact LanguageResult.bind_success _ (unit_rhs _ _) (LanguageResult.bind_success _ execution.modified
    (LanguageResult.bind_success _ execution.setter
      (.letE (.storeCell (.var rfl) read (.inRight (.var rfl)) execution.written) continuation)))

/-- A completed absent-RHS tail must reach the exact generated mapped commit.
The remaining seven-slot continuation is recovered as an output witness. -/
theorem Execution.reflects (execution : Execution checked registry functions cells instances prepared codes environment store mapping world
    target keys snapshot before after updated operator invalid)
    {next : Expr} {outputType : Ty} {result : Value} {finalStore : Store}
    (completed : Evaluates (snapshotEnvironment prepared.route.rootType target (packValues keys) (.inRight .unit snapshot) environment)
      store (CompatiblePlacePrefixReflection.remainder prepared (SourceCoreCalls.packArguments codes).type
        (LanguageResult.success .unit) next outputType operator true invalid) result finalStore) :
    Evaluates (writtenEnvironment prepared.route.rootType target (packValues keys)
      (.inRight .unit snapshot) .unit execution.replacement execution.value environment)
      execution.finalStore (shift 7 next) result finalStore := by
  cases completed with
  | caseLeft rhsEvaluated failed =>
    have impossible := (evaluation_deterministic rhsEvaluated (unit_rhs _ _)).1
    cases impossible
  | caseRight rhsEvaluated remaining =>
    obtain ⟨same, stores⟩ := evaluation_deterministic rhsEvaluated (unit_rhs _ _)
    cases same
    subst_vars
    cases remaining with
    | caseLeft modifiedEvaluated failed =>
      have impossible := (evaluation_deterministic modifiedEvaluated execution.modified).1
      cases impossible
    | caseRight modifiedEvaluated remaining =>
      obtain ⟨same, stores⟩ := evaluation_deterministic modifiedEvaluated execution.modified
      cases same
      subst_vars
      cases remaining with
      | caseLeft setterEvaluated failed =>
        have impossible := (evaluation_deterministic setterEvaluated execution.setter).1
        cases impossible
      | caseRight setterEvaluated remaining =>
        obtain ⟨same, stores⟩ := evaluation_deterministic setterEvaluated execution.setter
        cases same
        subst_vars
        cases remaining with
        | letE written continuation =>
          obtain ⟨optional, read⟩ := execution.read
          have actual : Evaluates
              (execution.value :: modifiedEnvironment prepared.route.rootType target (packValues keys)
                (.inRight .unit snapshot) .unit execution.replacement environment) execution.helperStore
              (.storeCell (.var 5) (.inRight .unit (.var 0))) .unit execution.finalStore :=
            .storeCell (.var rfl) read (.inRight (.var rfl)) execution.written
          obtain ⟨same, stores⟩ := evaluation_deterministic written actual
          subst_vars
          exact continuation

theorem Execution.reflects_size (execution : Execution checked registry functions cells instances prepared codes environment store mapping world
    target keys snapshot before after updated operator invalid)
    {next : Expr} {outputType : Ty} {result : Value} {finalStore : Store} {size : Nat}
    (completed : CoreProof.EvaluationSize size (snapshotEnvironment prepared.route.rootType target (packValues keys) (.inRight .unit snapshot) environment)
      store (CompatiblePlacePrefixReflection.remainder prepared (SourceCoreCalls.packArguments codes).type
        (LanguageResult.success .unit) next outputType operator true invalid) result finalStore) :
    ∃ remainingSize, remainingSize < size ∧ CoreProof.EvaluationSize remainingSize (writtenEnvironment prepared.route.rootType target (packValues keys)
      (.inRight .unit snapshot) .unit execution.replacement execution.value environment)
      execution.finalStore (shift 7 next) result finalStore := by
  cases completed with
  | caseLeft rhsEvaluated failed =>
    have impossible := (evaluation_deterministic rhsEvaluated.sound (unit_rhs _ _)).1
    cases impossible
  | caseRight rhsEvaluated remaining =>
    obtain ⟨same, stores⟩ := evaluation_deterministic rhsEvaluated.sound (unit_rhs _ _)
    cases same
    subst_vars
    cases remaining with
    | caseLeft modifiedEvaluated failed =>
      have impossible := (evaluation_deterministic modifiedEvaluated.sound execution.modified).1
      cases impossible
    | caseRight modifiedEvaluated remaining =>
      obtain ⟨same, stores⟩ := evaluation_deterministic modifiedEvaluated.sound execution.modified
      cases same
      subst_vars
      cases remaining with
      | caseLeft setterEvaluated failed =>
        have impossible := (evaluation_deterministic setterEvaluated.sound execution.setter).1
        cases impossible
      | caseRight setterEvaluated remaining =>
        obtain ⟨same, stores⟩ := evaluation_deterministic setterEvaluated.sound execution.setter
        cases same
        subst_vars
        cases remaining with
        | letE written continuation =>
          obtain ⟨optional, read⟩ := execution.read
          have actual : Evaluates
              (execution.value :: modifiedEnvironment prepared.route.rootType target (packValues keys)
                (.inRight .unit snapshot) .unit execution.replacement environment) execution.helperStore
              (.storeCell (.var 5) (.inRight .unit (.var 0))) .unit execution.finalStore :=
            .storeCell (.var rfl) read (.inRight (.var rfl)) execution.written
          obtain ⟨same, stores⟩ := evaluation_deterministic written.sound actual
          subst_vars
          exact ⟨_, by omega, continuation⟩

/-- Prefix composition uses only the actual key, getter and unary executions. -/
theorem Execution.prefix_agreement
    {sourceTypes : List TypeSystem.Ty} {place : PlaceResolution} {leaf : TypeSystem.Ty}
    {before selectedHeap : Dynamic.Heap} {initialStore : Store} {initialMap : LocationMap} {initialWorld : StoreTyping}
    {sourceTarget : Dynamic.ResolvedPlace}
    (resolution : CompatibleCellPlaceResolution.Execution checked registry functions cells instances prepared codes sourceTypes place leaf sourceTarget
      environment initialStore initialMap initialWorld before selectedHeap)
    (execution : Execution checked registry functions cells instances prepared codes environment resolution.store resolution.mapping resolution.world
      resolution.target resolution.values resolution.snapshot selectedHeap after updated operator invalid)
    {index : Nat}
    (lookup : environment[index]? = some (.cellRef (OptionalCell.cellType prepared.route.rootType) resolution.target))
    (next : Expr) (output : Ty) :
    ContinuationAgreement environment initialStore
      (execute prepared (.var index) (SourceCoreCalls.packArguments codes) (LanguageResult.success .unit) next output operator true invalid)
      (writtenEnvironment prepared.route.rootType resolution.target (packValues resolution.values)
        (.inRight .unit resolution.snapshot) .unit execution.replacement execution.value environment)
      execution.finalStore (shift 7 next) := by
  obtain ⟨optional, read⟩ := execution.read
  exact (ContinuationAgreement.letE (.var lookup)).trans
    ((ContinuationAgreement.bind resolution.keysEvaluated).trans
      ((ContinuationAgreement.bind resolution.snapshotEvaluated).trans
        ((ContinuationAgreement.bind (unit_rhs _ _)).trans
          ((ContinuationAgreement.bind execution.modified).trans
            ((ContinuationAgreement.bind execution.setter).trans
              (ContinuationAgreement.letE (.storeCell (.var rfl) read (.inRight (.var rfl)) execution.written)))))))

end Solcore.SourceSemantics.CoreLowering.CellAwareStagedProjectedBitNotCommit
