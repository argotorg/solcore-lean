import Solcore.SourceSemantics.CoreLowering.DataPlacePathHelpers

/-! Exact administrative contexts for the emitted assignment sequence.
These are composition laws, not a whole source-compilation theorem. Child
compiler certificates must establish their own execution in the displayed
expanded environments; unrestricted exact-value weakening is not assumed.
Getter/setter certificates above supply their semantic executions separately. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.DataPlaceExecution
open Core Frontend SourceCoreDataPlaces

def referenceEnvironment (type : Ty) (location : Location) (environment : Environment) : Environment :=
  .cellRef (OptionalCell.cellType type) location :: environment

def keysEnvironment (type : Ty) (location : Location) (keys : Value) (environment : Environment) : Environment :=
  keys :: referenceEnvironment type location environment

def snapshotEnvironment (type : Ty) (location : Location) (keys snapshot : Value) (environment : Environment) : Environment :=
  snapshot :: keysEnvironment type location keys environment

def rhsEnvironment (type : Ty) (location : Location) (keys snapshot rhs : Value) (environment : Environment) : Environment :=
  rhs :: snapshotEnvironment type location keys snapshot environment

def modifiedEnvironment (type : Ty) (location : Location) (keys snapshot rhs changed : Value) (environment : Environment) : Environment :=
  changed :: rhsEnvironment type location keys snapshot rhs environment

def writtenEnvironment (type : Ty) (location : Location) (keys snapshot rhs changed updated : Value) (environment : Environment) : Environment :=
  .unit :: updated :: modifiedEnvironment type location keys snapshot rhs changed environment

/-- Exact success sequencing. The getter's store is the RHS input; the
setter sees the RHS store, and the write follows all setter administrative
allocations. No source-expression phase is repeated. -/
theorem execute_success {prepared : Prepared} {reference rhs next : Expr} {keys : SourceCoreBasic.LoweredExpr}
    {outputType : Ty} {operator : Option BinaryOp} {bitNot : Bool} {invalidOperand : Word}
    {environment : Environment} {before keyStore snapshotStore rhsStore modifiedStore setterStore written finalStore : Store}
    {location : Location} {keyValue snapshot right changed updated old result : Value}
    (referenceSelected : DataEquality.Selects environment reference (.cellRef (OptionalCell.cellType prepared.route.rootType) location))
    (keysEvaluated : Evaluates (referenceEnvironment prepared.route.rootType location environment) before
      (shift 1 keys.expression) (.inRight .word keyValue) keyStore)
    (snapshotEvaluated : Evaluates (keysEnvironment prepared.route.rootType location keyValue environment) keyStore
      (.apply (getter prepared keys.type) (.pair (.loadCell (.var 1)) (.var 0))) (.inRight .word snapshot) snapshotStore)
    (rhsEvaluated : Evaluates (snapshotEnvironment prepared.route.rootType location keyValue snapshot environment) snapshotStore
      (shift 3 rhs) (.inRight .word right) rhsStore)
    (modifiedEvaluated : Evaluates (rhsEnvironment prepared.route.rootType location keyValue snapshot right environment) rhsStore
      (modified prepared.route.leafType operator bitNot (.var 1) (.var 0) invalidOperand) (.inRight .word changed) modifiedStore)
    (setterEvaluated : Evaluates (modifiedEnvironment prepared.route.rootType location keyValue snapshot right changed environment) modifiedStore
      (.apply (setter prepared keys.type) (.pair (.loadCell (.var 4)) (.pair (.var 3) (.var 0)))) (.inRight .word updated) setterStore)
    (read : setterStore.read? location = some old)
    (write : setterStore.write? location (.inRight .unit updated) = some written)
    (nextEvaluated : Evaluates (writtenEnvironment prepared.route.rootType location keyValue snapshot right changed updated environment)
      written (shift 7 next) result finalStore) :
    Evaluates environment before (execute prepared reference keys rhs next outputType operator bitNot invalidOperand) result finalStore := by
  exact .letE (referenceSelected.evaluates before)
    (LanguageResult.bind_success _ keysEvaluated
      (LanguageResult.bind_success _ snapshotEvaluated
        (LanguageResult.bind_success _ rhsEvaluated
          (LanguageResult.bind_success _ modifiedEvaluated
            (LanguageResult.bind_success _ setterEvaluated
              (.letE (.storeCell (.var rfl) read (.inRight (.var rfl)) write) nextEvaluated))))))

/-- Failure in an index suppresses the getter, RHS, modifier, setter and
continuation. Each premise is for the actual shifted key code. -/
theorem execute_keys_failure {prepared : Prepared} {reference rhs next : Expr} {keys : SourceCoreBasic.LoweredExpr}
    {outputType : Ty} {operator : Option BinaryOp} {bitNot : Bool} {invalidOperand reason : Word}
    {environment : Environment} {before after : Store} {location : Location}
    (referenceSelected : DataEquality.Selects environment reference (.cellRef (OptionalCell.cellType prepared.route.rootType) location))
    (keysEvaluated : Evaluates (referenceEnvironment prepared.route.rootType location environment) before
      (shift 1 keys.expression) (.inLeft keys.type (.word reason)) after) :
    Evaluates environment before (execute prepared reference keys rhs next outputType operator bitNot invalidOperand)
      (.inLeft outputType (.word reason)) after :=
  .letE (referenceSelected.evaluates before) (LanguageResult.bind_failure _ keysEvaluated)

theorem execute_snapshot_failure {prepared : Prepared} {reference rhs next : Expr} {keys : SourceCoreBasic.LoweredExpr}
    {outputType : Ty} {operator : Option BinaryOp} {bitNot : Bool} {invalidOperand reason : Word}
    {environment : Environment} {before keyStore after : Store} {location : Location} {keyValue : Value}
    (referenceSelected : DataEquality.Selects environment reference (.cellRef (OptionalCell.cellType prepared.route.rootType) location))
    (keysEvaluated : Evaluates (referenceEnvironment prepared.route.rootType location environment) before
      (shift 1 keys.expression) (.inRight .word keyValue) keyStore)
    (snapshotEvaluated : Evaluates (keysEnvironment prepared.route.rootType location keyValue environment) keyStore
      (.apply (getter prepared keys.type) (.pair (.loadCell (.var 1)) (.var 0)))
      (.inLeft prepared.optionalLeaf (.word reason)) after) :
    Evaluates environment before (execute prepared reference keys rhs next outputType operator bitNot invalidOperand)
      (.inLeft outputType (.word reason)) after :=
  .letE (referenceSelected.evaluates before)
    (LanguageResult.bind_success _ keysEvaluated (LanguageResult.bind_failure _ snapshotEvaluated))

theorem execute_rhs_failure {prepared : Prepared} {reference rhs next : Expr} {keys : SourceCoreBasic.LoweredExpr}
    {outputType rightType : Ty} {operator : Option BinaryOp} {bitNot : Bool} {invalidOperand reason : Word}
    {environment : Environment} {before keyStore snapshotStore after : Store}
    {location : Location} {keyValue snapshot : Value}
    (referenceSelected : DataEquality.Selects environment reference (.cellRef (OptionalCell.cellType prepared.route.rootType) location))
    (keysEvaluated : Evaluates (referenceEnvironment prepared.route.rootType location environment) before
      (shift 1 keys.expression) (.inRight .word keyValue) keyStore)
    (snapshotEvaluated : Evaluates (keysEnvironment prepared.route.rootType location keyValue environment) keyStore
      (.apply (getter prepared keys.type) (.pair (.loadCell (.var 1)) (.var 0))) (.inRight .word snapshot) snapshotStore)
    (rhsEvaluated : Evaluates (snapshotEnvironment prepared.route.rootType location keyValue snapshot environment) snapshotStore
      (shift 3 rhs) (.inLeft rightType (.word reason)) after) :
    Evaluates environment before (execute prepared reference keys rhs next outputType operator bitNot invalidOperand)
      (.inLeft outputType (.word reason)) after :=
  .letE (referenceSelected.evaluates before)
    (LanguageResult.bind_success _ keysEvaluated
      (LanguageResult.bind_success _ snapshotEvaluated (LanguageResult.bind_failure _ rhsEvaluated)))

theorem execute_modified_failure {prepared : Prepared} {reference rhs next : Expr} {keys : SourceCoreBasic.LoweredExpr}
    {outputType : Ty} {operator : Option BinaryOp} {bitNot : Bool} {invalidOperand reason : Word}
    {environment : Environment} {before keyStore snapshotStore rhsStore after : Store}
    {location : Location} {keyValue snapshot right : Value}
    (referenceSelected : DataEquality.Selects environment reference (.cellRef (OptionalCell.cellType prepared.route.rootType) location))
    (keysEvaluated : Evaluates (referenceEnvironment prepared.route.rootType location environment) before
      (shift 1 keys.expression) (.inRight .word keyValue) keyStore)
    (snapshotEvaluated : Evaluates (keysEnvironment prepared.route.rootType location keyValue environment) keyStore
      (.apply (getter prepared keys.type) (.pair (.loadCell (.var 1)) (.var 0))) (.inRight .word snapshot) snapshotStore)
    (rhsEvaluated : Evaluates (snapshotEnvironment prepared.route.rootType location keyValue snapshot environment) snapshotStore
      (shift 3 rhs) (.inRight .word right) rhsStore)
    (modifiedEvaluated : Evaluates (rhsEnvironment prepared.route.rootType location keyValue snapshot right environment) rhsStore
      (modified prepared.route.leafType operator bitNot (.var 1) (.var 0) invalidOperand)
      (.inLeft prepared.route.leafType (.word reason)) after) :
    Evaluates environment before (execute prepared reference keys rhs next outputType operator bitNot invalidOperand)
      (.inLeft outputType (.word reason)) after :=
  .letE (referenceSelected.evaluates before)
    (LanguageResult.bind_success _ keysEvaluated
      (LanguageResult.bind_success _ snapshotEvaluated
        (LanguageResult.bind_success _ rhsEvaluated (LanguageResult.bind_failure _ modifiedEvaluated))))

theorem execute_setter_failure {prepared : Prepared} {reference rhs next : Expr} {keys : SourceCoreBasic.LoweredExpr}
    {outputType : Ty} {operator : Option BinaryOp} {bitNot : Bool} {invalidOperand reason : Word}
    {environment : Environment} {before keyStore snapshotStore rhsStore modifiedStore after : Store}
    {location : Location} {keyValue snapshot right changed : Value}
    (referenceSelected : DataEquality.Selects environment reference (.cellRef (OptionalCell.cellType prepared.route.rootType) location))
    (keysEvaluated : Evaluates (referenceEnvironment prepared.route.rootType location environment) before
      (shift 1 keys.expression) (.inRight .word keyValue) keyStore)
    (snapshotEvaluated : Evaluates (keysEnvironment prepared.route.rootType location keyValue environment) keyStore
      (.apply (getter prepared keys.type) (.pair (.loadCell (.var 1)) (.var 0))) (.inRight .word snapshot) snapshotStore)
    (rhsEvaluated : Evaluates (snapshotEnvironment prepared.route.rootType location keyValue snapshot environment) snapshotStore
      (shift 3 rhs) (.inRight .word right) rhsStore)
    (modifiedEvaluated : Evaluates (rhsEnvironment prepared.route.rootType location keyValue snapshot right environment) rhsStore
      (modified prepared.route.leafType operator bitNot (.var 1) (.var 0) invalidOperand) (.inRight .word changed) modifiedStore)
    (setterEvaluated : Evaluates (modifiedEnvironment prepared.route.rootType location keyValue snapshot right changed environment) modifiedStore
      (.apply (setter prepared keys.type) (.pair (.loadCell (.var 4)) (.pair (.var 3) (.var 0))))
      (.inLeft prepared.route.rootType (.word reason)) after) :
    Evaluates environment before (execute prepared reference keys rhs next outputType operator bitNot invalidOperand)
      (.inLeft outputType (.word reason)) after :=
  .letE (referenceSelected.evaluates before)
    (LanguageResult.bind_success _ keysEvaluated
      (LanguageResult.bind_success _ snapshotEvaluated
        (LanguageResult.bind_success _ rhsEvaluated
          (LanguageResult.bind_success _ modifiedEvaluated (LanguageResult.bind_failure _ setterEvaluated)))))

end Solcore.SourceSemantics.CoreLowering.DataPlaceExecution
