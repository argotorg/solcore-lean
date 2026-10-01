import Solcore.SourceSemantics.CoreLowering.CompatiblePlaceBitNotCommit
import Solcore.SourceSemantics.CoreLowering.CompatiblePlacePrefixReflection

/-! Exact Unit-RHS sequencing for the absent source RHS branch. These laws
compose or invert a commit constructed from independent source semantics. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatiblePlaceBitNotCommit
open Core Frontend SourceInference GeneralHeap DataPatternValues CompatiblePayload CompatibleHeap
open SourceCoreCompatibleDataPlaces DataPlaceExecution

variable {checked : Checked} {registry : SourceCoreRawMetadata.Registry}
  {functions : FunctionModel checked.catalog} {prepared : Prepared} {codes : List SourceCoreBasic.LoweredExpr}
  {environment : Environment} {store : Store} {mapping : LocationMap} {world : StoreTyping}
  {target : Location} {keys : List Value} {snapshot : Value} {before after : Dynamic.Heap}
  {updated : Dynamic.Value} {operator : Option BinaryOp} {invalid : Word}

private theorem unit_rhs (environment : Environment) (store : Store) :
    Evaluates environment store (shift 3 (LanguageResult.success .unit)) (.inRight .word .unit) store := by
  simpa only [shift, List.range, List.range.loop, List.foldl, Expr.weakenAt, LanguageResult.success] using
    (Evaluates.inRight (leftType := .word) (environment := environment) (initialStore := store) Evaluates.unit)

theorem Execution.plug (execution : Execution checked registry functions prepared codes environment store mapping world
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
theorem Execution.reflects (execution : Execution checked registry functions prepared codes environment store mapping world
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

end Solcore.SourceSemantics.CoreLowering.CompatiblePlaceBitNotCommit
