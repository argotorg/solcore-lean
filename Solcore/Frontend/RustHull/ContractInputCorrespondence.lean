import Solcore.Frontend.RustHull.ContractExecutionCorrespondence
import Solcore.Frontend.RustHull.StorageCorrespondence

/-! Actual public contract instantiation supplies its normalized context,
linked account records and concrete runtime argument. Literal construction
leaves the store unchanged and introduces no execution assumptions. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.Correspondence
open ScalarExecution

def optionalWordValue : Option Core.Word → Core.Value
  | none => .inLeft .word .unit
  | some value => .inRight .unit (.word value)

def optionalHashesValue : Option Core.WordMapping.Entries → Core.Value
  | none => .inLeft Core.WordMapping.type .unit
  | some entries => .inRight .unit (Core.WordMapping.encode entries)

theorem ambientWord_evaluates (word : Option Core.Word) (environment : Core.Environment) (store : Core.Store) :
    Core.Evaluates environment store (Ambient.wordLiteral word) (optionalWordValue word) store := by
  cases word with
  | none => exact .inLeft .unit
  | some word => exact .inRight .word

theorem ambientHashes_evaluates (hashes : Option Core.WordMapping.Entries)
    (environment : Core.Environment) (store : Core.Store) :
    Core.Evaluates environment store (Ambient.hashesLiteral hashes) (optionalHashesValue hashes) store := by
  cases hashes with
  | none => exact .inLeft .unit
  | some entries => exact .inRight (Core.WordMapping.literal_evaluates entries environment store)

def ambientValues (context : Ambient.Context) : List Core.Value :=
  [optionalWordValue context.origin, optionalWordValue context.gasprice,
   optionalWordValue context.coinbase, optionalWordValue context.timestamp,
   optionalWordValue context.number, optionalWordValue context.prevrandao,
   optionalWordValue context.gaslimit, optionalWordValue context.chainid,
   optionalWordValue context.basefee, optionalWordValue context.blobbasefee,
   optionalHashesValue context.blockHashes, optionalHashesValue (context.blobHashes.map Ambient.blobEntries)]

theorem ambientContext_evaluates (context : Ambient.Context) (environment : Core.Environment) (store : Core.Store) :
    Core.Evaluates environment store (Ambient.contextExpression context) (bundleValues (ambientValues context)) store :=
  .pair (ambientWord_evaluates _ _ _) (.pair (ambientWord_evaluates _ _ _)
    (.pair (ambientWord_evaluates _ _ _) (.pair (ambientWord_evaluates _ _ _)
    (.pair (ambientWord_evaluates _ _ _) (.pair (ambientWord_evaluates _ _ _)
    (.pair (ambientWord_evaluates _ _ _) (.pair (ambientWord_evaluates _ _ _)
    (.pair (ambientWord_evaluates _ _ _) (.pair (ambientWord_evaluates _ _ _)
    (.pair (ambientHashes_evaluates _ _ _) (ambientHashes_evaluates _ _ _)))))))))))

def contextValues (compiled : Contract.CompiledObject) (context : Contract.Context) : List Core.Value :=
  [Core.WordMapping.encode (Contract.calldataEntries context.calldata),
   .word (Core.Word.ofNatModulo context.calldata.length),
   .word context.value, .word context.caller, .word context.address, optionalWordValue context.availableGas,
   Core.WordMapping.encode (Core.WordMapping.insertEntries context.address context.balance context.accounts),
   StorageCorrespondence.world (StorageCorrespondence.canonical (compiled.initialWorld context)),
   .bool context.isStatic, .bool context.completeWorld,
   bundleValues (ambientValues context.ambient), .bool context.deploying]

theorem contextArgument_evaluates (compiled : Contract.CompiledObject) (context : Contract.Context)
    (environment : Core.Environment) (store : Core.Store) :
    Core.Evaluates environment store (compiled.contextArgument context)
      (bundleValues (contextValues compiled context)) store := by
  have gas : Core.Evaluates environment store
      (match context.availableGas with | none => .inLeft .word .unit | some value => .inRight .unit (.word value))
      (optionalWordValue context.availableGas) store := by
    cases context.availableGas with
    | none => exact .inLeft .unit
    | some value => exact .inRight .word
  exact .pair (Core.WordMapping.literal_evaluates _ _ _) (.pair .word (.pair .word (.pair .word
    (.pair .word (.pair gas (.pair (Core.WordMapping.literal_evaluates _ _ _)
    (.pair (StorageCorrespondence.literal_evaluates _ _ _) (.pair .bool (.pair .bool
    (.pair (ambientContext_evaluates _ _ _) .bool))))))))))

/-- The public constructor evaluates the actual context literal before entering
the compiled lambda. The source state can therefore be based on these exact
normalized inputs instead of an assumed argument representation. -/
theorem instantiate_evaluates {compiled : Contract.CompiledObject} (context : Contract.Context)
    {parameter resultType : Core.Ty} {body : Core.Expr}
    (expression : compiled.expression = .lambda parameter resultType body)
    {value : Core.Value} {store : Core.Store}
    (executed : Core.Evaluates [bundleValues (contextValues compiled (Contract.normalizeContext context))]
      [] body value store) :
    Core.Evaluates [] [] (compiled.instantiate context).expression value store := by
  change Core.Evaluates [] []
    (.apply compiled.expression (compiled.contextArgument (Contract.normalizeContext context))) value store
  rw [expression]
  exact .apply .lambda (contextArgument_evaluates compiled (Contract.normalizeContext context) [] []) executed

/-- Every genuine public resumption chain reaches exactly the receipt exported
from the instantiated lambda, at the cumulative transition count. -/
theorem instantiate_resumes_exact {compiled : Contract.CompiledObject} (context : Contract.Context)
    {parameter resultType : Core.Ty} {body : Core.Expr}
    (expression : compiled.expression = .lambda parameter resultType body)
    {value : Core.Value} {store : Core.Store}
    (executed : Core.Evaluates [bundleValues (contextValues compiled (Contract.normalizeContext context))]
      [] body value store) :
    ∃ required, ∀ fuel additional limit last,
      Contract.ReceiptResumes limit (Contract.runWithReceipt (compiled.instantiate context) fuel limit) additional last →
      (last = Contract.finish limit value ↔ required ≤ fuel + additional) ∧
      ((∃ checkpoint, last.outcome = .outOfFuel checkpoint) ↔ fuel + additional < required) :=
  Contract.evaluation_resumes_exact (instantiate_evaluates context expression executed)

end Solcore.Frontend.RustHull.Correspondence
