import Solcore.Abi.StaticWordContract
import Solcore.Core.Wire.V3.Host
import Solcore.Oracle.V5.Input

/-! Deterministic admission of Oracle v5 contract definitions. -/

set_option autoImplicit false

namespace Solcore.Oracle.V5

open Solcore.Core.Wire
open Solcore.Semantics

/-- The exact location of a Core checker failure inside a contract package. -/
inductive ContractProgramSite where
  | checkedCore (contract : ContractId)
  | staticMethod (contract : ContractId) (methodName : String)
  deriving Repr, BEq, DecidableEq

/-- Closed semantic failures selected while admitting a v5 contract package. -/
inductive ContractAdmissionError where
  | invalidContractId (actual : String)
  | duplicateContractId (id : ContractId)
  | coreCheckFailed
      (site : ContractProgramSite)
      (error : Solcore.Core.CheckError)
  | unsupportedEntryResultType
      (contract : ContractId)
      (actual : Solcore.Core.Ty)
  | invalidMethodName
      (contract : ContractId)
      (actual : String)
  | methodDataDefinitionsNonempty
      (contract : ContractId)
      (methodName : String)
      (count : Nat)
  | methodResultTypeMismatch
      (contract : ContractId)
      (methodName : String)
      (actual : Solcore.Core.Ty)
  | emptyMethodTable (contract : ContractId)
  | duplicateSignature
      (contract : ContractId)
      (firstMethod secondMethod signature : String)
  | selectorCollision
      (contract : ContractId)
      (firstSignature secondSignature : String)
      (selector : Solcore.Abi.V1.Selector)
  | duplicateCode (firstId secondId : ContractId)

namespace ContractAdmission

private structure IdentifiedInput where
  id : ContractId
  spec : ContractSpec

private def rawIdLE (left right : ContractInput) : Bool :=
  (compare left.id right.id).isLE

/-- Canonical contract ordering is byte-exact ordering of the raw ID strings. -/
def canonicalInputs (contracts : List ContractInput) : List ContractInput :=
  contracts.mergeSort rawIdLE

private def validateIds :
    List ContractInput → Except ContractAdmissionError (List IdentifiedInput)
  | [] => .ok []
  | input :: rest => do
      let id ← match ContractId.ofString? input.id with
        | some id => .ok id
        | none => .error (.invalidContractId input.id)
      let tail ← validateIds rest
      .ok ({ id, spec := input.spec } :: tail)

private def firstDuplicateId? :
    List IdentifiedInput → Option ContractId
  | [] => none
  | first :: rest =>
      match rest.find? (fun later => decide (later.id = first.id)) with
      | some _ => some first.id
      | none => firstDuplicateId? rest

private theorem checkDetailed_ok_result
    {program : V3.Program}
    {actual : Solcore.Core.Ty}
    (accepted : program.checkDetailed = .ok actual) :
    actual = program.resultType.toCore := by
  unfold V3.Program.checkDetailed V3.Host.checkDetailed at accepted
  unfold Solcore.Core.Program.checkDetailedIn at accepted
  split at accepted
  · split at accepted
    · split at accepted
      · simp_all
      · split at accepted
        · exact (Except.ok.inj accepted).symm
        · simp_all
    · simp_all
  · simp_all

private structure CheckedWireProgram (wire : V3.Program) where
  code : CheckedHostCoreProgram
  program_eq : code.program = wire.toCore

private def checkedHost
    (program : V3.Program) :
    Except Solcore.Core.CheckError (CheckedWireProgram program) :=
  match detailed : program.checkDetailed with
  | .error error => .error error
  | .ok _actual =>
      have resultEq := checkDetailed_ok_result detailed
      have accepted :
          program.checkDetailed = .ok program.resultType.toCore :=
        detailed.trans (congrArg Except.ok resultEq)
      if checked : program.check = true then
        .ok ⟨⟨program.toCore, program.check_promotes_current checked⟩, rfl⟩
      else
        False.elim <| checked <| V3.Program.checkDetailed_iff_check.mp accepted

/-- Admit only the two entry profiles frozen by Oracle v5. -/
private def checkedCore
    (id : ContractId)
    (program : V3.Program) :
    Except ContractAdmissionError CheckedCoreContract := do
  let checked ← (checkedHost program).mapError
    (ContractAdmissionError.coreCheckFailed (.checkedCore id))
  match resultTypeEq : program.resultType with
  | .word =>
      let wordCode : CheckedHostCoreWordProgram :=
        ⟨checked.code, by
          rw [checked.program_eq]
          simp [V3.Program.toCore, V3.Ty.toCore, resultTypeEq]⟩
      .ok (CheckedCoreContract.returnWord wordCode)
  | .sum .word (.sum .word .word) =>
      .ok (CheckedCoreContract.wordOutcomeV1 checked.code (by
        rw [checked.program_eq]
        simp [V3.Program.toCore, V3.Ty.toCore, resultTypeEq,
          CoreContractEntryProfile.resultType]))
  | _ => .error (.unsupportedEntryResultType id checked.code.program.resultType)

private structure NamedMethodInput where
  name : Solcore.Abi.V1.MethodName
  implementation : V3.Program

private def rawMethodSignature (method : StaticMethodInput) : String :=
  method.name ++ "(uint256)"

private def rawMethodLE
    (left right : StaticMethodInput) : Bool :=
  (compare (rawMethodSignature left) (rawMethodSignature right)).isLE

/-- Method input is canonicalized by its derived Static Word signature. -/
def canonicalMethods
    (methods : List StaticMethodInput) : List StaticMethodInput :=
  methods.mergeSort rawMethodLE

private def validateMethodNames
    (id : ContractId) :
    List StaticMethodInput →
      Except ContractAdmissionError (List NamedMethodInput)
  | [] => .ok []
  | method :: rest => do
      let name ← match Solcore.Abi.V1.validateMethodName? method.name with
        | some name => .ok name
        | none => .error (.invalidMethodName id method.name)
      let tail ← validateMethodNames id rest
      .ok ({ name, implementation := method.implementation } :: tail)

private def firstDuplicateMethod? :
    List NamedMethodInput → Option (String × String × String)
  | [] => none
  | first :: rest =>
      match rest.find? (fun later => later.name.text == first.name.text) with
      | some later =>
          some (first.name.text, later.name.text,
            first.name.text ++ "(uint256)")
      | none => firstDuplicateMethod? rest

private def admitMethod
    (id : ContractId)
    (method : NamedMethodInput) :
    Except ContractAdmissionError Solcore.Abi.V1.Method := do
  let checked ← (checkedHost method.implementation).mapError
    (ContractAdmissionError.coreCheckFailed
      (.staticMethod id method.name.text))
  let code := checked.code
  if _definitionsEq : code.program.dataDefinitions = [] then
    if _resultTypeEq :
        code.program.resultType = .function .word .word then
      match Solcore.Abi.V1.WordImplementation.ofCode? code with
      | some implementation => .ok {
          metadata := .staticWord method.name
          implementation
        }
      | none => .error (.methodResultTypeMismatch id method.name.text
          code.program.resultType)
    else
      .error (.methodResultTypeMismatch id method.name.text
        code.program.resultType)
  else
    .error (.methodDataDefinitionsNonempty id method.name.text
      code.program.dataDefinitions.length)

private def admitMethods
    (id : ContractId) :
    List NamedMethodInput →
      Except ContractAdmissionError (List Solcore.Abi.V1.Method)
  | [] => .ok []
  | method :: rest => do
      let admitted ← admitMethod id method
      let tail ← admitMethods id rest
      .ok (admitted :: tail)

private def mapTableError
    (id : ContractId) :
    Solcore.Abi.V1.MethodTableError → ContractAdmissionError
  | .empty => .emptyMethodTable id
  | .duplicateSignature first second signature =>
      .duplicateSignature id first.name.text second.name.text signature
  | .selectorCollision _ _ firstSignature secondSignature selector =>
      .selectorCollision id firstSignature secondSignature selector

/-- One admitted contract retains either raw or generated ABI provenance. -/
inductive AdmittedContract where
  | checkedCore (contract : CheckedCoreContract)
  | staticWordAbi
      (methods : List Solcore.Abi.V1.Method)
      (contract : Solcore.Abi.V1.StaticWordContract methods)

namespace AdmittedContract

def contract : AdmittedContract → CheckedCoreContract
  | .checkedCore contract => contract
  | .staticWordAbi _ contract => contract.checkedCore

end AdmittedContract

private def admitStaticWordAbi
    (id : ContractId)
    (rawMethods : List StaticMethodInput) :
    Except ContractAdmissionError AdmittedContract := do
  let methods ← validateMethodNames id (canonicalMethods rawMethods)
  match firstDuplicateMethod? methods with
  | some (first, second, signature) =>
      .error (.duplicateSignature id first second signature)
  | none =>
      let admitted ← admitMethods id methods
      match Solcore.Abi.V1.StaticWordContract.admit admitted with
      | .error failure => .error (mapTableError id failure)
      | .ok contract => .ok (.staticWordAbi admitted contract)

structure AdmittedEntry where
  id : ContractId
  admitted : AdmittedContract

namespace AdmittedEntry

def contract (entry : AdmittedEntry) : CheckedCoreContract :=
  entry.admitted.contract

def program (entry : AdmittedEntry) : Solcore.Core.Program :=
  entry.contract.code.program

end AdmittedEntry

private def admitOne
    (input : IdentifiedInput) :
    Except ContractAdmissionError AdmittedEntry := do
  let admittedResult : Except ContractAdmissionError AdmittedContract :=
    match input.spec with
    | .checkedCore program =>
        (checkedCore input.id program).map AdmittedContract.checkedCore
    | .staticWordAbi methods => admitStaticWordAbi input.id methods
  let admitted ← admittedResult
  .ok { id := input.id, admitted }

private def admitAll :
    List IdentifiedInput →
      Except ContractAdmissionError (List AdmittedEntry)
  | [] => .ok []
  | input :: rest => do
      let admitted ← admitOne input
      let tail ← admitAll rest
      .ok (admitted :: tail)

/-- Select the first duplicate identifier pair in canonical package order. -/
def firstDuplicateEntryId? :
    List AdmittedEntry → Option ContractId
  | [] => none
  | first :: rest =>
      match rest.find? (fun later => decide (later.id = first.id)) with
      | some _ => some first.id
      | none => firstDuplicateEntryId? rest

/-- Select the first equal checked Program pair in canonical package order. -/
def firstDuplicateProgram? :
    List AdmittedEntry → Option (ContractId × ContractId)
  | [] => none
  | first :: rest =>
      match rest.find? (fun later => decide (later.program = first.program)) with
      | some later => some (first.id, later.id)
      | none => firstDuplicateProgram? rest

/--
A finite, canonically ordered package whose identifier and underlying checked
Program uniqueness checks both succeeded. The private constructor keeps raw
input from bypassing admission.
-/
structure ContractPackage where
  private mk ::
  entries : List AdmittedEntry
  identifiersUnique : firstDuplicateEntryId? entries = none
  programsUnique : firstDuplicateProgram? entries = none

namespace ContractPackage

/-- Find one admitted entry by its validated, byte-exact identifier. -/
def lookupEntry?
    (package : ContractPackage)
    (id : ContractId) : Option AdmittedEntry :=
  package.entries.find? (fun entry => decide (entry.id = id))

/-- Resolve one validated identifier to its runnable checked contract. -/
def lookup?
    (package : ContractPackage)
    (id : ContractId) : Option CheckedCoreContract :=
  (package.lookupEntry? id).map AdmittedEntry.contract

/-- Reject invalid raw identifiers before attempting package resolution. -/
def lookupRaw?
    (package : ContractPackage)
    (rawId : String) : Option CheckedCoreContract := do
  let id ← ContractId.ofString? rawId
  package.lookup? id

/-- Map installed checked code back to its unique canonical package ID. -/
def idByProgram?
    (package : ContractPackage)
    (program : Solcore.Core.Program) : Option ContractId :=
  (package.entries.find? (fun entry => decide (entry.program = program))).map
    (fun entry => entry.id)

/-- Checked-code view of `idByProgram?`, suitable for world-state probes. -/
def idByCode?
    (package : ContractPackage)
    (code : CheckedHostCoreProgram) : Option ContractId :=
  package.idByProgram? code.program

theorem mem_of_lookupEntry?_eq_some
    {package : ContractPackage}
    {id : ContractId}
    {entry : AdmittedEntry}
    (found : package.lookupEntry? id = some entry) :
    entry ∈ package.entries := by
  exact List.mem_of_find?_eq_some found

theorem id_eq_of_lookupEntry?_eq_some
    {package : ContractPackage}
    {id : ContractId}
    {entry : AdmittedEntry}
    (found : package.lookupEntry? id = some entry) :
    entry.id = id := by
  unfold lookupEntry? at found
  have accepted : decide (entry.id = id) :=
    @List.find?_some AdmittedEntry
      (fun candidate => decide (candidate.id = id)) entry _ found
  exact of_decide_eq_true accepted

theorem program_eq_of_idByProgram?_eq_some
    {package : ContractPackage}
    {program : Solcore.Core.Program}
    {id : ContractId}
    (found : package.idByProgram? program = some id) :
    ∃ entry ∈ package.entries,
      entry.id = id ∧ entry.program = program := by
  unfold idByProgram? at found
  rcases Option.map_eq_some_iff.mp found with ⟨entry, selected, idEq⟩
  refine ⟨entry, List.mem_of_find?_eq_some selected, idEq, ?_⟩
  have accepted : decide (entry.program = program) :=
    @List.find?_some AdmittedEntry
      (fun candidate => decide (candidate.program = program)) entry _ selected
  exact of_decide_eq_true accepted

end ContractPackage

/--
Canonicalize, validate, check, refine, and de-alias a complete contract package.
Identifier duplicates are rejected before either duplicate entry is checked.
-/
def admit
    (contracts : List ContractInput) :
    Except ContractAdmissionError ContractPackage := do
  let identified ← validateIds (canonicalInputs contracts)
  match firstDuplicateId? identified with
  | some duplicate => .error (.duplicateContractId duplicate)
  | none =>
      let entries ← admitAll identified
      match idCheck : firstDuplicateEntryId? entries with
      | some duplicate => .error (.duplicateContractId duplicate)
      | none =>
          match codeCheck : firstDuplicateProgram? entries with
          | some duplicate =>
              .error (.duplicateCode duplicate.1 duplicate.2)
          | none => .ok {
              entries
              identifiersUnique := idCheck
              programsUnique := codeCheck
            }

end ContractAdmission

end Solcore.Oracle.V5
