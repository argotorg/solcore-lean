import Solcore.Abi.StaticWord
import Solcore.Core.Wire.V3.Host
import Solcore.Oracle.V5.Input
import Solcore.Oracle.V5.CheckDiagnostic
import Solcore.ContractRuntime.RuntimeScalars.TextProperties

/-! Deterministic admission of Oracle v5 contract definitions. -/

set_option autoImplicit false

namespace Solcore.Oracle.V5

open Solcore.Core.Wire
open Solcore.ContractRuntime

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
  if _resultTypeEq :
      code.program.resultType = .function .word .word then
    if _definitionsEq : code.program.dataDefinitions = [] then
      match Solcore.Abi.V1.WordImplementation.ofCode? code with
      | some implementation => .ok {
          metadata := .staticWord method.name
          implementation
        }
      | none => .error (.methodResultTypeMismatch id method.name.text
          code.program.resultType)
    else
      .error (.methodDataDefinitionsNonempty id method.name.text
        code.program.dataDefinitions.length)
  else
    .error (.methodResultTypeMismatch id method.name.text
      code.program.resultType)

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

/-!
## Consolidated module: `Solcore.Oracle.V5.ContractAdmissionDiagnostic`
-/

/-! Canonical Oracle v5 diagnostics for contract-package admission. -/

set_option autoImplicit false

namespace Solcore.Oracle.V5.ContractAdmissionDiagnostic

open Solcore.Core.Wire

private def diagnostic
    (code : String)
    (path : List String)
    (arguments : Lean.Json) : Diagnostic := {
  code
  phase := .contractAdmission
  path
  arguments
}

private def encodeCoreType
    (type : Solcore.Core.Ty) : Except InternalError Lean.Json :=
  match V3.Ty.ofCore? type with
  | some wire => .ok (V3.encodeType wire)
  | none => .error .coreWireProjectionFailed

private def selectorText (selector : Solcore.Abi.V1.Selector) : String :=
  ((Solcore.ContractRuntime.encodeBytesText selector.encode).drop 2).toString

private def programPrefix : ContractProgramSite → List String
  | .checkedCore contract => ["contracts", contract.value, "program"]
  | .staticMethod contract methodName =>
      ["contracts", contract.value, "methods", methodName, "implementation"]

/-- Project every closed admission failure into its exact diagnostic shape. -/
def ofError :
    ContractAdmissionError → Except InternalError Diagnostic
  | .invalidContractId actual => .ok <| diagnostic
      "oracle.v5.contract.invalid-id"
      ["contracts", actual, "id"]
      (.mkObj [("actual", actual)])
  | .duplicateContractId id => .ok <| diagnostic
      "oracle.v5.contract.duplicate-id"
      ["contracts", id.value, "id"]
      (.mkObj [("id", id.value)])
  | .coreCheckFailed site error =>
      CheckDiagnostic.ofError .contractAdmission (programPrefix site) error
  | .unsupportedEntryResultType contract actual => do
      .ok <| diagnostic
        "oracle.v5.contract.unsupported-entry-result-type"
        ["contracts", contract.value, "program", "resultType"]
        (.mkObj [("actual", ← encodeCoreType actual)])
  | .invalidMethodName contract actual => .ok <| diagnostic
      "oracle.v5.method.invalid-name"
      ["contracts", contract.value, "methods", actual, "name"]
      (.mkObj [("actual", actual)])
  | .methodDataDefinitionsNonempty contract methodName count => .ok <|
      diagnostic
        "oracle.v5.method.nonempty-data-definitions"
        ["contracts", contract.value, "methods", methodName,
          "implementation", "dataDefinitions"]
        (.mkObj [("count", Lean.toJson count)])
  | .methodResultTypeMismatch contract methodName actual => do
      .ok <| diagnostic
        "oracle.v5.method.result-type-mismatch"
        ["contracts", contract.value, "methods", methodName,
          "implementation", "resultType"]
        (.mkObj [("actual", ← encodeCoreType actual)])
  | .emptyMethodTable contract => .ok <| diagnostic
      "oracle.v5.abi.empty-method-table"
      ["contracts", contract.value, "methods"]
      (.mkObj [])
  | .duplicateSignature contract firstMethod secondMethod signature =>
      .ok <| diagnostic
        "oracle.v5.abi.duplicate-signature"
        ["contracts", contract.value, "methods"]
        (.mkObj [
          ("signature", signature),
          ("firstMethod", firstMethod),
          ("secondMethod", secondMethod)
        ])
  | .selectorCollision contract firstSignature secondSignature selector =>
      .ok <| diagnostic
        "oracle.v5.abi.selector-collision"
        ["contracts", contract.value, "methods"]
        (.mkObj [
          ("selector", selectorText selector),
          ("firstSignature", firstSignature),
          ("secondSignature", secondSignature)
        ])
  | .duplicateCode firstId secondId => .ok <| diagnostic
      "oracle.v5.contract.duplicate-code"
      ["contracts", secondId.value]
      (.mkObj [
        ("firstId", firstId.value),
        ("secondId", secondId.value)
      ])

end Solcore.Oracle.V5.ContractAdmissionDiagnostic

/-!
## Consolidated module: `Solcore.Oracle.V5.ContractAdmissionProperties`
-/

/-! Exact uniqueness and lookup laws for admitted Oracle v5 packages. -/

set_option autoImplicit false

namespace Solcore.Oracle.V5.ContractAdmission

/-- Identifier scan success is exactly pairwise identifier uniqueness. -/
theorem firstDuplicateEntryId?_eq_none_iff (entries : List AdmittedEntry) :
    firstDuplicateEntryId? entries = none ↔
      entries.Pairwise fun left right => left.id ≠ right.id := by
  induction entries with
  | nil => simp [firstDuplicateEntryId?]
  | cons first rest inductionHypothesis =>
      cases found : rest.find? (fun later => decide (later.id = first.id)) with
      | none =>
          have headDistinct : ∀ later ∈ rest, first.id ≠ later.id := by
            intro later member equal
            have rejected := (List.find?_eq_none.mp found) later member
            exact rejected (by simp [equal])
          rw [firstDuplicateEntryId?, found, inductionHypothesis,
            List.pairwise_cons]
          exact ⟨fun tail => ⟨headDistinct, tail⟩, fun all => all.2⟩
      | some later =>
          have laterMember : later ∈ rest :=
            List.mem_of_find?_eq_some found
          have equal : later.id = first.id := by
            simpa using List.find?_some found
          simp only [firstDuplicateEntryId?, found, reduceCtorEq,
            false_iff, List.pairwise_cons]
          intro pairwise
          exact pairwise.1 later laterMember equal.symm

/-- Program scan success is exactly pairwise checked-Program uniqueness. -/
theorem firstDuplicateProgram?_eq_none_iff (entries : List AdmittedEntry) :
    firstDuplicateProgram? entries = none ↔
      entries.Pairwise fun left right => left.program ≠ right.program := by
  induction entries with
  | nil => simp [firstDuplicateProgram?]
  | cons first rest inductionHypothesis =>
      cases found : rest.find? (fun later =>
          decide (later.program = first.program)) with
      | none =>
          have headDistinct : ∀ later ∈ rest,
              first.program ≠ later.program := by
            intro later member equal
            have rejected := (List.find?_eq_none.mp found) later member
            exact rejected (by simp [equal])
          rw [firstDuplicateProgram?, found, inductionHypothesis,
            List.pairwise_cons]
          exact ⟨fun tail => ⟨headDistinct, tail⟩, fun all => all.2⟩
      | some later =>
          have laterMember : later ∈ rest :=
            List.mem_of_find?_eq_some found
          have equal : later.program = first.program := by
            simpa using List.find?_some found
          simp only [firstDuplicateProgram?, found, reduceCtorEq,
            false_iff, List.pairwise_cons]
          intro pairwise
          exact pairwise.1 later laterMember equal.symm

namespace ContractPackage

/-- Every sealed package has pairwise distinct validated identifiers. -/
theorem identifiersPairwise (package : ContractPackage) :
    package.entries.Pairwise fun left right => left.id ≠ right.id :=
  (firstDuplicateEntryId?_eq_none_iff package.entries).mp
    package.identifiersUnique

/-- Every sealed package has one canonical ID for each checked Program. -/
theorem programsPairwise (package : ContractPackage) :
    package.entries.Pairwise fun left right =>
      left.program ≠ right.program :=
  (firstDuplicateProgram?_eq_none_iff package.entries).mp
    package.programsUnique

private theorem findId?_of_mem
    {entries : List AdmittedEntry}
    (unique : entries.Pairwise fun left right => left.id ≠ right.id)
    {entry : AdmittedEntry}
    (member : entry ∈ entries) :
    entries.find? (fun candidate => decide (candidate.id = entry.id)) =
      some entry := by
  induction entries with
  | nil => simp at member
  | cons first rest inductionHypothesis =>
      rw [List.pairwise_cons] at unique
      have memberCases : entry = first ∨ entry ∈ rest := by
        simpa using member
      rcases memberCases with equal | member
      · simp [equal]
      · have different : first.id ≠ entry.id :=
          unique.1 entry member
        rw [List.find?_cons]
        simp [different, inductionHypothesis unique.2 member]

private theorem findProgram?_of_mem
    {entries : List AdmittedEntry}
    (unique : entries.Pairwise fun left right =>
      left.program ≠ right.program)
    {entry : AdmittedEntry}
    (member : entry ∈ entries) :
    entries.find? (fun candidate =>
      decide (candidate.program = entry.program)) = some entry := by
  induction entries with
  | nil => simp at member
  | cons first rest inductionHypothesis =>
      rw [List.pairwise_cons] at unique
      have memberCases : entry = first ∨ entry ∈ rest := by
        simpa using member
      rcases memberCases with equal | member
      · simp [equal]
      · have different : first.program ≠ entry.program :=
          unique.1 entry member
        rw [List.find?_cons]
        simp [different, inductionHypothesis unique.2 member]

/-- Lookup is complete for every entry carried by the finite package. -/
@[simp] theorem lookupEntry?_of_mem
    (package : ContractPackage)
    {entry : AdmittedEntry}
    (member : entry ∈ package.entries) :
    package.lookupEntry? entry.id = some entry := by
  exact findId?_of_mem package.identifiersPairwise member

/-- Runnable lookup returns the exact checked contract of every package entry. -/
@[simp] theorem lookup?_of_mem
    (package : ContractPackage)
    {entry : AdmittedEntry}
    (member : entry ∈ package.entries) :
    package.lookup? entry.id = some entry.contract := by
  simp [lookup?, lookupEntry?_of_mem package member]

/-- Raw validated-ID lookup has the same exact completeness law. -/
@[simp] theorem lookupRaw?_of_mem
    (package : ContractPackage)
    {entry : AdmittedEntry}
    (member : entry ∈ package.entries) :
    package.lookupRaw? entry.id.value = some entry.contract := by
  simp [lookupRaw?, lookup?_of_mem package member]

/-- Program reverse lookup returns the unique package identifier. -/
@[simp] theorem idByProgram?_of_mem
    (package : ContractPackage)
    {entry : AdmittedEntry}
    (member : entry ∈ package.entries) :
    package.idByProgram? entry.program = some entry.id := by
  simp [idByProgram?, findProgram?_of_mem package.programsPairwise member]

/-- Checked-code reverse lookup returns the unique package identifier. -/
@[simp] theorem idByCode?_of_mem
    (package : ContractPackage)
    {entry : AdmittedEntry}
    (member : entry ∈ package.entries) :
    package.idByCode? entry.contract.code = some entry.id := by
  exact idByProgram?_of_mem package member

/-- A successful forward lookup always round-trips through checked code. -/
theorem idByCode?_of_lookupEntry?_eq_some
    {package : ContractPackage}
    {id : ContractId}
    {entry : AdmittedEntry}
    (found : package.lookupEntry? id = some entry) :
    package.idByCode? entry.contract.code = some id := by
  rw [idByCode?_of_mem package
    (mem_of_lookupEntry?_eq_some found),
    id_eq_of_lookupEntry?_eq_some found]

/-- Runnable lookup always round-trips through the canonical checked-code ID. -/
theorem idByCode?_of_lookup?_eq_some
    {package : ContractPackage}
    {id : ContractId}
    {contract : Solcore.ContractRuntime.CheckedCoreContract}
    (found : package.lookup? id = some contract) :
    package.idByCode? contract.code = some id := by
  unfold lookup? at found
  rcases Option.map_eq_some_iff.mp found with
    ⟨entry, entryFound, contractEq⟩
  subst contract
  exact idByCode?_of_lookupEntry?_eq_some entryFound

/-- Forward and reverse package resolution identify the same exact Program. -/
theorem program_eq_of_idByProgram?_and_lookupEntry?
    {package : ContractPackage}
    {program : Solcore.Core.Program}
    {id : ContractId}
    {entry : AdmittedEntry}
    (reverse : package.idByProgram? program = some id)
    (forward : package.lookupEntry? id = some entry) :
    program = entry.program := by
  rcases program_eq_of_idByProgram?_eq_some reverse with
    ⟨candidate, candidateMember, candidateId, candidateProgram⟩
  have candidateLookup :=
    lookupEntry?_of_mem package candidateMember
  rw [candidateId] at candidateLookup
  have sameEntry : candidate = entry :=
    Option.some.inj (candidateLookup.symm.trans forward)
  subst entry
  exact candidateProgram.symm

end ContractPackage

end Solcore.Oracle.V5.ContractAdmission
