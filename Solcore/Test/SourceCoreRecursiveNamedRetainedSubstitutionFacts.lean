import Solcore.SourceSemantics.CoreLowering.RecursiveNamedRetainedSubstitutionFacts
import Solcore.SourceSemantics.SubstitutionCorrespondence
import Solcore.Test.SourceCoreUnifiedCorpusSupport

/-! Reversal retains the same structural body without equating the ordered
instantiation records. Duplicate keys expose the first-match boundary. -/
#check_failure Solcore.Frontend.SourceTypedRuntime.run
set_option autoImplicit false
namespace Tests.SourceCoreRecursiveNamedRetainedSubstitutionFacts
open Solcore Frontend SourceInference TypeSystem SourceSemantics SourceSemantics.CoreLowering
open StructuralSubstitution RecursiveNamedRetainedSubstitutionFacts

theorem exact_source {substitution : TypeSystem.ParameterSubstitution} {parameters : List TypeParameterId}
    (exact : SourceSemantics.ParameterSubstitution.Exact substitution parameters) (source : TypedSource) :
    applyTypedSource substitution.reverse source = applyTypedSource substitution source :=
  typedSource_reverse exact.domain_nodup source

theorem exact_full_ledger {substitution : TypeSystem.ParameterSubstitution} {parameters : List TypeParameterId}
    (exact : SourceSemantics.ParameterSubstitution.Exact substitution parameters) (rows : List SolvedRequirement) :
    rows.map (applySolvedRequirement substitution.reverse) = rows.map (applySolvedRequirement substitution) :=
  ledger_reverse exact.domain_nodup rows

theorem full_valid {context : SourceSemantics.Context} {instantiation : DeclarationInstantiation}
    (valid : SourceSemantics.DeclarationInstantiation.Valid context instantiation) :
    SourceSemantics.DeclarationInstantiation.Valid context (CallableNamedReversal.instantiation instantiation) :=
  valid_reverse valid

theorem same_body {program : SourceSemantics.Program} {instantiation : DeclarationInstantiation} {body : Dynamic.BodyInstance}
    (actual : Dynamic.FunctionInstantiates program instantiation body) :
    Dynamic.FunctionInstantiates program (CallableNamedReversal.instantiation instantiation) body :=
  instantiates_reverse actual

theorem retained_body {program : SourceSemantics.Program} {specialized : SourceSpecialization.SpecializedFunction}
    {body : Dynamic.BodyInstance}
    (actual : Dynamic.FunctionInstantiates program (CallableNamedMetadata.instantiation specialized) body) :
    Dynamic.FunctionInstantiates program (CallableNamedCanonicalOrder.retainedInstantiation specialized) body :=
  retained_instantiates actual

/-- A range row is retained even if its parameter does not occur in the body. -/
theorem unused_range_retained {context : SourceSemantics.Context} {substitution : TypeSystem.ParameterSubstitution}
    (range : SourceSemantics.ParameterSubstitution.RangeWellFormed context substitution)
    {parameter : TypeParameterId} {replacement : TypeSystem.Ty}
    (member : (parameter, replacement) ∈ substitution) :
    (parameter, replacement) ∈ substitution.reverse ∧ TypeWellFormed context replacement :=
  ⟨List.mem_reverse.mpr member, range parameter replacement member⟩

theorem duplicate_key_changes_raw_result (parameter : TypeParameterId) :
    TypeSystem.ParameterSubstitution.apply [(parameter, .word), (parameter, .bool)] (.parameter parameter) ≠
      TypeSystem.ParameterSubstitution.apply ([(parameter, .word), (parameter, .bool)].reverse) (.parameter parameter) := by
  simp [TypeSystem.ParameterSubstitution.apply, TypeSystem.ParameterSubstitution.lookup?, TypeSystem.Ty.word, TypeSystem.Ty.bool]

theorem records_keep_their_order (first second : TypeParameterId) (different : first ≠ second) :
    ([(first, .word), (second, .bool)] : TypeSystem.ParameterSubstitution) ≠
      [(first, .word), (second, .bool)].reverse := by
  intro same
  have head := congrArg (fun rows : TypeSystem.ParameterSubstitution => rows.head?) same
  simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append,
    List.head?_cons, Option.some.injEq, Prod.mk.injEq] at head
  exact different head.1

theorem raw_staging_preserved (parameter : TypeParameterId) :
    TypeSystem.ParameterSubstitution.apply [(parameter, .comptime .word)] (.parameter parameter) = .comptime .word ∧
      TypeSystem.ParameterSubstitution.apply [(parameter, .comptime .word)] (.parameter parameter) ≠ .word := by
  simp [TypeSystem.ParameterSubstitution.apply, TypeSystem.ParameterSubstitution.lookup?, TypeSystem.Ty.word]

private def content : String := String.intercalate "\n" [
  "enum Box<T> { Box(T) }",
  "function choose<A, B>(first: A, second: B) returns (A) { let saved = first; return saved; }",
  "function pair<A, B>(first: A, second: B) returns ((A, B)) { return (first, second); }",
  "function wrap<T>(value: T) returns (Box<T>) { return Box(value); }",
  "function wordRoot() returns (Word) { return choose(9, false); }",
  "function boolRoot() returns (Bool) { return choose(true, 8); }",
  "function pairRoot() returns ((Word, Bool)) { return pair(7, true); }",
  "function boxRoot() returns (Box<Word>) { return wrap(5); }"
]
private def require := SourceCoreUnifiedCorpusSupport.assertTrue
private def get {α ε : Type} [Repr ε] := @SourceCoreUnifiedCorpusSupport.get α ε _

private def recursive_ledger (parameter : TypeParameterId) : List SolvedRequirement :=
  let goal := ProgramSignatures.builtinIntPredicate (.parameter parameter)
  let nested := ProgramSignatures.builtinIntPredicate (.proxy (.parameter parameter))
  let staged := ProgramSignatures.builtinIntPredicate (.comptime (.parameter parameter))
  [{id := ⟨77⟩, predicate := goal, evidence := .assumption goal},
   {id := ⟨79⟩, predicate := nested, evidence := .implementation
      (.byImpl nested (.builtin .intWord)
        [.byImpl staged (.builtin .intInteger) [.byImpl goal (.builtin .intWord) []]])},
   {id := ⟨77⟩, predicate := goal, evidence := .assumption goal}]

/-- Real specialization rows exercise the structural equations. Synthetic
unused rows and nested evidence exercise full raw retention separately. -/
private def inspect (compiled : SourceCoreUnifiedCompilation.Compiled) : IO Unit := do
  let mut selectedCount := 0
  let mut reversedCount := 0
  let mut ledgerCount := 0
  for specialized in compiled.compatible.prepared.plan.specializations do
    let generic ← match compiled.sourceProgram.functions.find? (fun f => f.declaration == specialized.declaration) with
      | some generic => pure generic
      | none => throw (IO.userError "retained substitution original function missing")
    let signature ← match compiled.sourceProgram.signatures.functions.find? (fun s => s.id == specialized.declaration) with
      | some signature => pure signature
      | none => throw (IO.userError "retained substitution original signature missing")
    let actual ← get "retained actual specialization"
      (SourceSpecialization.specializeFunction signature generic specialized.parameterSubstitution)
    require (reprStr actual == reprStr specialized) "retained full actual specialization changed"
    let substitution := specialized.parameterSubstitution
    require (decide ((substitution.map Prod.fst).Nodup)) "retained actual substitution has duplicate keys"
    let original := applyTypedSource substitution generic.typedBody
    let reversed := applyTypedSource substitution.reverse generic.typedBody
    require (reprStr original == reprStr specialized.function.typedBody && reprStr reversed == reprStr original)
      "retained full source application changed"
    require (substitution.apply generic.inferredBodyType == specialized.function.inferredBodyType &&
        TypeSystem.ParameterSubstitution.apply substitution.reverse generic.inferredBodyType == specialized.function.inferredBodyType)
      "retained full raw result changed"
    let originalLedger := generic.solvedRequirements.map (applySolvedRequirement substitution)
    require (reprStr originalLedger == reprStr specialized.function.solvedRequirements &&
        reprStr (generic.solvedRequirements.map (applySolvedRequirement substitution.reverse)) == reprStr originalLedger)
      "retained actual full requirement ledger changed"
    let retained := CallableNamedCanonicalOrder.retainedInstantiation specialized
    require (retained.parameterSubstitution == substitution.reverse && retained.type == specialized.function.type &&
        reprStr retained.predicates == reprStr specialized.assumptions)
      "retained record order or non-substitution metadata changed"
    if substitution.length > 1 then
      require (retained.parameterSubstitution != substitution) "retained ordered records were collapsed"
      reversedCount := reversedCount + 1
    if let some (parameter, _) := substitution.head? then
      let extra : TypeParameterId := ⟨parameter.owner, 10000⟩
      require (!(substitution.map Prod.fst).contains extra) "retained synthetic unused key is not fresh"
      let extended := substitution ++ [(extra, .comptime (.proxy .bool))]
      let rows := recursive_ledger parameter
      let full := rows.map (applySolvedRequirement extended)
      require (reprStr full == reprStr (rows.map (applySolvedRequirement extended.reverse)))
        "retained recursive evidence/staging changed"
      require (full.map (·.id.index) == [77, 79, 77]) "retained duplicate requirement IDs/order changed"
      require (extended.reverse.head? == some (extra, .comptime (.proxy .bool))) "retained unused raw row was dropped"
      require (reprStr (applyTypedSource extended generic.typedBody) == reprStr original)
        "retained synthetic unused replacement affected original source"
      require (TypeSystem.ParameterSubstitution.lookup? [(parameter, .word), (parameter, .bool)] parameter !=
          TypeSystem.ParameterSubstitution.lookup? [(parameter, .bool), (parameter, .word)] parameter)
        "retained duplicate-key first-match boundary missing"
      ledgerCount := ledgerCount + 1
    selectedCount := selectedCount + 1
  require (selectedCount == 8 && reversedCount == 3 && ledgerCount == 4)
    s!"retained actual specialization coverage changed {selectedCount}/{reversedCount}/{ledgerCount}"

def run : IO Unit := do
  let compiled ← SourceCoreUnifiedCorpusSupport.prepare "recursive named retained substitutions" content
    ["wordRoot", "boolRoot", "pairRoot", "boxRoot"]
  inspect compiled
  IO.println "recursive named retained substitutions: actual full source/results/ledgers, reverse record order, unused raw rows and nested evidence GREEN"

end Tests.SourceCoreRecursiveNamedRetainedSubstitutionFacts
