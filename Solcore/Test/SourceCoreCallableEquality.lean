import Solcore.SourceSemantics.CoreLowering.DataEqualityCertificates

/-! Contract descriptors govern calls; source equality observes the retained
function identity. The same compiler certificates cover both catalog profiles. -/
set_option autoImplicit false
namespace Tests.SourceCoreCallableEquality
open Solcore Solcore.Core Solcore.Frontend SourceInference
open Solcore.SourceSemantics Solcore.SourceSemantics.CoreLowering
open SourceCoreDataEquality DataEquality DataEqualityValues DataEqualityCertificates

private def word (value : Nat) : Word := Word.ofNatModulo value
private def catalog : SourceCoreDataCatalog.Catalog := { callableContracts := true }
private def checked : SourceCoreDataCatalog.Checked :=
  ⟨catalog, DataEnvironment.isWellFormed_sound (by decide)⟩
private def signatures : ProgramSignatures := ⟨[], [], [], [], [], []⟩

private def oneIdentity (function : Dynamic.GlobalFunction) (source : Dynamic.Value) (id : Word) : Prop :=
  source = .global function ∧ id = Word.zero
private theorem oneFaithful (function : Dynamic.GlobalFunction) : IdentityFaithful (oneIdentity function) := by
  constructor
  · intro source id represented
    rw [represented.1]
    exact .global _
  · intro left right leftId rightId leftRep rightRep
    simp [leftRep.1, rightRep.1, leftRep.2, rightRep.2]

/-- A legacy tagged function cannot masquerade as a product component in the
contracted profile's equality relation. Core typing alone is not that relation. -/
example {source : Dynamic.Value} {value : Value} {parameter result : Ty}
    (observed : Observation catalog signatures (fun _ _ => False)
      (TaggedFunction.functionType parameter result) source value) : False :=
  Carrier.not_tagged_contract observed.carrier

/-- Descriptor words and closure code can differ while the named source
identity remains equal. Actual generated initialization and invocation follow. -/
example (prepared : Prepared checked)
    (type : prepared.type = CallableContract.functionType .word .word)
    (function : Dynamic.GlobalFunction) (leftCode rightCode : Value) (store : Store) :
    ∃ required, ∀ fuel, required ≤ fuel →
      runStateful fuel (.initial (.letE prepared.expression
        (.apply (.var 0) (.pair (.var 1) (.var 2))))
        [.pair (.pair (.inRight .unit (.word Word.zero)) leftCode) (.word (word 7)),
         .pair (.pair (.inRight .unit (.word Word.zero)) rightCode) (.word (word 9))] store) =
        .done (.bool true) store := by
  have left : Observation catalog signatures (oneIdentity function) prepared.type (.global function)
      (.pair (.pair (.inRight .unit (.word Word.zero)) leftCode) (.word (word 7))) :=
    type ▸ .contractedIdentified _ _ _ _ ⟨rfl, rfl⟩ rfl
  have right : Observation catalog signatures (oneIdentity function) prepared.type (.global function)
      (.pair (.pair (.inRight .unit (.word Word.zero)) rightCode) (.word (word 9))) :=
    type ▸ .contractedIdentified _ _ _ _ ⟨rfl, rfl⟩ rfl
  obtain ⟨result, meaning, evaluated⟩ := prepared_compare_preserves prepared (oneFaithful function) left right
    [.pair (.pair (.inRight .unit (.word Word.zero)) leftCode) (.word (word 7)),
      .pair (.pair (.inRight .unit (.word Word.zero)) rightCode) (.word (word 9))]
    store (.var 0) (.var 1) (.var rfl) (.var rfl)
  have same : result = true := meaning.mpr ⟨rfl, .global _⟩
  subst result
  have noBodies : prepared.bodies = [] := by
    have generated := prepared.bodiesGenerated
    simpa [helperBodies, checked, catalog, pure, Except.pure] using generated.symm
  simpa [checked, catalog, noBodies, DataEqualityInstalled.cells, Expr.weakenAt]
    using evaluation_runStateful_complete_with_sufficient_fuel evaluated

private def assertTrue (condition : Bool) (message : String) : IO Unit := do
  unless condition do throw (IO.userError message)

private def raw : Expr :=
  .lambda .word (LanguageResult.resultType .word) (LanguageResult.success (.var 0))
private def effectful : Expr :=
  .lambda .word (LanguageResult.resultType .word)
    (.letE (.newCell .word (.var 0)) (LanguageResult.success (.loadCell (.var 0))))
private def named (contract : Nat) (code : Expr := raw) : Expr :=
  CallableContract.wrap (word contract) (TaggedFunction.identified Word.zero code)
private def anonymous (contract : Nat) : Expr :=
  CallableContract.wrap (word contract) (TaggedFunction.anonymous raw)

private def compare (checked : SourceCoreDataCatalog.Checked) (type : TypeSystem.Ty)
    (left right : Expr) (expected : Bool) : IO Unit := do
  let prepared ← match SourceCoreDataEquality.prepare 64 checked type with
    | .ok prepared => pure prepared
    | .error error => throw (IO.userError s!"callable equality compilation failed: {reprStr error}")
  let expression := Expr.letE prepared.expression
    (.pair (.apply (.var 0) (.pair left right)) (.apply (.var 0) (.pair right left)))
  let program : Core.Program := ⟨.product .bool .bool, expression, checked.catalog.definitions⟩
  assertTrue program.check "callable equality program failed checking"
  match program.runStateful 10000 with
  | .done value store =>
      assertTrue (value == .pair (.bool expected) (.bool expected)) "callable equality changed source identity"
      assertTrue (store.length == checked.catalog.entries.length) "equality invoked closure effects or reinstalled helpers"
  | other => throw (IO.userError s!"callable equality failed: {reprStr other}")
  match program.runStateful 4 with
  | .outOfFuel checkpoint =>
      assertTrue (Core.runStateful 9996 checkpoint == program.runStateful 10000)
        "callable equality resume changed result or store"
  | _ => throw (IO.userError "callable equality did not suspend at fuel four")

private def workspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := []
  mainSources := [{path := "main.solc", content :=
    "enum Tree<T> { Leaf(T), Pair(Tree<T>, Tree<T>) }\nfunction identity(value: Word) returns (Word) { return value; }"}]
}

def run : IO Unit := do
  let functionType := TypeSystem.Ty.function .word .word
  compare checked functionType (named 7) (named 9 effectful) true
  compare checked functionType (anonymous 7) (anonymous 7) false
  compare checked functionType (anonymous 7) (named 7) false
  compare checked (.product functionType .word)
    (.pair (named 7) (.word (word 1))) (.pair (named 9) (.word (word 2))) false
  compare checked (.product functionType .word)
    (.pair (named 7) (.word (word 1))) (.pair (named 9) (.word (word 1))) true
  let legacy : SourceCoreDataCatalog.Checked :=
    ⟨{}, DataEnvironment.isWellFormed_sound (by decide)⟩
  compare legacy (.product functionType .word)
    (.pair (TaggedFunction.identified Word.zero raw) (.word (word 7)))
    (.pair (TaggedFunction.identified Word.zero raw) (.word (word 9))) false
  let program ← match checkProgram workspace with
    | .ok program => pure program
    | .error error => throw (IO.userError s!"callable equality source failed: {reprStr error}")
  let declaration ← match program.signatures.dataTypes.find? (·.name == "Tree") with
    | some declaration => pure declaration
    | none => throw (IO.userError "callable equality Tree signature missing")
  let treeType := TypeSystem.Ty.nominal declaration.id [functionType]
  let recursive ← match SourceCoreDataCatalog.prepare program.signatures 64 [treeType] true with
    | .ok checked => pure checked
    | .error error => throw (IO.userError s!"callable recursive catalog failed: {reprStr error}")
  let id ← match recursive.catalog.identity? treeType with
    | some id => pure id
    | none => throw (IO.userError "callable recursive identity missing")
  let leaf := fun code => Expr.construct ⟨id, 0⟩ code
  let node := fun a b => Expr.construct ⟨id, 1⟩ (.pair a b)
  compare recursive treeType
    (node (leaf (named 7)) (leaf (named 7)))
    (node (leaf (named 9 effectful)) (leaf (named 9))) true
  compare recursive treeType
    (node (leaf (named 7)) (leaf (anonymous 7)))
    (node (leaf (named 9)) (leaf (anonymous 7))) false
  IO.println "callable equality profiles, generated certificates and recursive payloads GREEN"

end Tests.SourceCoreCallableEquality
