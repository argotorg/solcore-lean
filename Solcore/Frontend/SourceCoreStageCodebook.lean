import Solcore.Frontend.SourceCoreStageContracts

/-! Finite artifact-owned callable contracts. Contract IDs are ordinary Core
words and are independent of source named-function identity. The enclosing
artifact authenticates the prepared plan; sealed callable receipts authenticate
the retained source flags and cumulative contexts. This module evaluates no
source expressions. Its IDs need only existing Core word comparisons to dispatch.

The inventory covers compiled plan origins and discovered local instances.
External closure importing and declarative source staging-guard rules are
separate boundaries. Extra closed lambda origins in a retained source table
are harmless: the compiler emits a descriptor only for the exact origin it
actually compiles. -/

set_option autoImplicit false

namespace Solcore.Frontend.SourceCoreStageCodebook

open SourceInference
abbrev Key := SourceCoreStageContracts.Key
abbrev Plan := SourceCoreStageContracts.Plan
abbrev Contract := SourceCoreStageContracts.Contract
abbrev Sidecar := SourceCoreStageContracts.Sidecar
abbrev Guard := SourceCoreStageContracts.Guard
abbrev RuntimeError := SourceCoreStageContracts.RuntimeError

inductive Origin where
  | named (key : Key)
  | lambda (owner : Key) (id : ExpressionId) (context : TypeSystem.Substitution)
  | builtin (function : BuiltinFunctionId)
  deriving Repr, DecidableEq

structure Limits where
  maxContracts : Nat := 4096
  maxDecisions : Nat := 65536
  deriving Repr

inductive Error where
  | contracts (error : SourceCoreStageContracts.Error)
  | localInstances (error : SourceCoreLocalPolymorphism.Error)
  | localEvidence (error : SourceCoreLocalEvidence.Error)
  | contractBudgetExhausted (limit : Nat)
  | decisionBudgetExhausted (limit : Nat)
  | contractIdSpaceExhausted (next : Nat)
  | zeroFirstId
  | ambiguousOrigin (origin : Origin)
  | duplicateId
  | duplicateDecision
  | missingCallsite (caller : Key) (id : ExpressionId)
  deriving Repr

structure Entry where private mk ::
  id : Core.Word
  origin : Origin
  parameterCount : Nat
  /-- Builtins bypass the old indirect staging validator. Their ordinary
  callable application still owns parameter-count/type checks. -/
  contract : Option Contract

structure Decision where private mk ::
  caller : Key
  call : ExpressionId
  entry : Entry
  argumentCount : Nat
  guard : Option Guard

namespace Decision

def answer (row : Decision) : Except RuntimeError Unit :=
  match row.guard with | some guard => guard.decision | none => .ok ()

def beforeArguments (row : Decision) : Except RuntimeError Unit := row.answer

/-- Unlike the stage guard, callable application checks full arity even for
an effectful-staging caller. This runs after arguments/coercions and before
parameter cells are allocated. -/
def afterArguments (row : Decision) : Except RuntimeError Unit :=
  if row.entry.parameterCount = row.argumentCount then .ok ()
  else .error (.argumentArityMismatch row.entry.parameterCount row.argumentCount)

theorem afterArguments_ok (row : Decision) (same : row.entry.parameterCount = row.argumentCount) :
    row.afterArguments = .ok () := by simp [afterArguments, same]

theorem afterArguments_mismatch (row : Decision) (different : row.entry.parameterCount ≠ row.argumentCount) :
    row.afterArguments = .error (.argumentArityMismatch row.entry.parameterCount row.argumentCount) := by
  simp [afterArguments, different]

def key (row : Decision) : Key × ExpressionId × Core.Word := (row.caller, row.call, row.entry.id)

theorem exact_guard (row : Decision) (guard : Guard) (same : row.guard = some guard) :
    row.answer = SourceCompilationPlan.validateStagedCallableContract guard.sidecar.caller guard.node guard.arguments
      guard.contract.parameters guard.contract.stagedResult guard.contract.owner := by
  simp only [answer, same]
  exact guard.decision_exact.symm

end Decision

structure Table where private mk ::
  entries : List Entry
  decisions : List Decision
  idsUnique : (entries.map (·.id)).Nodup
  originsUnique : (entries.map (·.origin)).Nodup
  decisionsUnique : (decisions.map Decision.key).Nodup

namespace Table

def idAt? (table : Table) (origin : Origin) : Option Core.Word :=
  (table.entries.find? (fun entry => decide (entry.origin = origin))).map (·.id)

def entryAt? (table : Table) (id : Core.Word) : Option Entry :=
  table.entries.find? (fun entry => decide (entry.id = id))

def decisionAt? (table : Table) (caller : Key) (call : ExpressionId) (id : Core.Word) : Option Decision :=
  table.decisions.find? (fun row => decide (row.key = (caller, call, id)))

def casesAt (table : Table) (caller : Key) (call : ExpressionId) : List Decision :=
  table.decisions.filter (fun row => decide (row.caller = caller ∧ row.call = call))

def contractCount (table : Table) : Nat := table.entries.length
def decisionCount (table : Table) : Nat := table.decisions.length

end Table

private def insert (limits : Limits) (firstId : Nat) (entries : List Entry)
    (origin : Origin) (count : Nat) (contract : Option Contract) : Except Error (List Entry) := do
  if entries.any (fun entry => decide (entry.origin = origin)) then return entries
  if entries.length ≥ limits.maxContracts then throw (.contractBudgetExhausted limits.maxContracts)
  let id ← match Core.Word.ofNat? (firstId + entries.length) with
    | some id => pure id
    | none => throw (.contractIdSpaceExhausted (firstId + entries.length))
  pure (entries ++ [.mk id origin count contract])

private def lambdaIds (sidecar : Sidecar) : List ExpressionId :=
  sidecar.source.nodes.filterMap fun
    | .expression { id, form := .lambda _ _ _, .. } => some id
    | _ => none

private def collectLambdas (limits : Limits) (firstId : Nat) (sidecar : Sidecar)
    (prepared : Option SourceCoreLocalEvidence.Prepared) (entries : List Entry) : Except Error (List Entry) := do
  let mut entries := entries
  let context := prepared.map (·.substitution) |>.getD []
  for id in lambdaIds sidecar do
    let answer := match prepared with
      | none => SourceCoreStageContracts.Contract.lambda sidecar id
      | some prepared => SourceCoreStageContracts.Contract.contextualLambda sidecar prepared id
    match answer with
    | .error (.openLambda _) => pure ()
    | .error error => throw (.contracts error)
    | .ok contract =>
        entries ← insert limits firstId entries (.lambda sidecar.caller.key id context)
          contract.parameters.length (some contract)
  pure entries

/-- Existing local discovery orders enclosing contexts before nested contexts.
Try the original caller and already authenticated contexts; every accepted
receipt checks the exact full cumulative instance and its evidence chain. -/
private def contextualReceipt (program : CheckedProgram) (plan : Plan)
    (parents : List SourceCoreLocalEvidence.Prepared) (candidate : SourceCoreLocalPolymorphism.Instance) :
    Except Error SourceCoreLocalEvidence.Prepared := do
  match SourceCoreLocalEvidence.prepare program plan candidate with
  | .ok prepared => pure prepared
  | .error originalError =>
      let mut found := none
      for parent in parents do
        if found.isNone then
          match SourceCoreLocalEvidence.prepare program plan candidate (some parent) with
          | .ok prepared => found := some prepared
          | .error _ => pure ()
      match found with
      | some prepared => pure prepared
      | none => throw (.localEvidence originalError)

/-- Storage order of source nodes need not be lexical parent order. Revisit
pending instances after each progress pass; every pass authenticates at least
one instance, so the instance count bounds this static dependency traversal. -/
private def contextualReceipts (program : CheckedProgram) (plan : Plan) : Nat →
    List SourceCoreLocalEvidence.Prepared → List SourceCoreLocalPolymorphism.Instance →
    Except Error (List SourceCoreLocalEvidence.Prepared)
  | _, parents, [] => pure parents
  | 0, _, _ :: _ => throw (.contractBudgetExhausted 0)
  | fuel + 1, parents, pending => do
      let mut parents := parents
      let mut remaining := []
      let mut firstError := none
      for candidate in pending do
        match contextualReceipt program plan parents candidate with
        | .ok prepared => parents := parents ++ [prepared]
        | .error error =>
            remaining := remaining ++ [candidate]
            if firstError.isNone then firstError := some error
      if remaining.length = pending.length then
        match firstError with
        | some error => throw error
        | none => throw (.contractBudgetExhausted 0)
      contextualReceipts program plan fuel parents remaining

private def collectDecisions (limits : Limits) (sidecars : List Sidecar) (entries : List Entry) :
    Except Error (List Decision) := do
  let mut rows := []
  for sidecar in sidecars do
    for node in sidecar.source.nodes do
      match node with
      | .expression { id, form := .call _ arguments (.indirect _), .. } =>
          for entry in entries do
            if rows.length ≥ limits.maxDecisions then throw (.decisionBudgetExhausted limits.maxDecisions)
            let guard ← match entry.contract with
              | none => pure none
              | some contract =>
                  (SourceCoreStageContracts.prepareGuard sidecar id contract).map some |>.mapError Error.contracts
            rows := rows ++ [.mk sidecar.caller.key id entry arguments.length guard]
      | _ => pure ()
  pure rows

/-- Construct once during artifact preparation. The IDs are positive words,
never wrapping; the immutable table certifies unique origins, IDs, and lookup
keys. The limits bound accepted origins and callsite/contract combinations. -/
def prepare (program : CheckedProgram) (plan : Plan) (checked : SourceCoreDataCatalog.Checked)
    (limits : Limits := {}) (firstId : Nat := 1) : Except Error Table := do
  if firstId = 0 then throw .zeroFirstId
  let mut entries := []
  let mut sidecars := []
  for specialized in plan.specializations do
    let sidecar ← (SourceCoreStageContracts.prepareSidecar plan specialized.key).mapError Error.contracts
    sidecars := sidecars ++ [sidecar]
    let contract ← (SourceCoreStageContracts.Contract.named plan specialized.key).mapError Error.contracts
    entries ← insert limits firstId entries (.named specialized.key) contract.parameters.length (some contract)
    entries ← collectLambdas limits firstId sidecar none entries
  for function in BuiltinFunctionId.all do
    entries ← insert limits firstId entries (.builtin function) function.parameterTypes.length none
  let locals ← (SourceCoreLocalPolymorphism.prepare checked plan).mapError Error.localInstances
  let candidates := locals.bindings.flatMap (·.instances)
  if candidates.length > limits.maxContracts then throw (.contractBudgetExhausted limits.maxContracts)
  let contexts ← contextualReceipts program plan candidates.length [] candidates
  for prepared in contexts do
    let sidecar ← (SourceCoreStageContracts.prepareSidecar plan prepared.caller.key).mapError Error.contracts
    entries ← collectLambdas limits firstId sidecar (some prepared) entries
  let rows ← collectDecisions limits sidecars entries
  if ids : (entries.map (·.id)).Nodup then
    if origins : (entries.map (·.origin)).Nodup then
      if unique : (rows.map Decision.key).Nodup then
        pure (.mk entries rows ids origins unique)
      else throw .duplicateDecision
    else throw (.ambiguousOrigin (entries.head?.map (·.origin) |>.getD (.builtin .integerAdd)))
  else throw .duplicateId


end Solcore.Frontend.SourceCoreStageCodebook
