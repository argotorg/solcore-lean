import Solcore.SourceSemantics.CoreLowering.CompatibleSourceInstantiationClosure
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedSourceContextFacts
import Solcore.SourceSemantics.CoreLowering.CallableIndexedNamedGeneration
import Solcore.SourceSemantics.CoreLowering.CallableNamedCanonicalOrder
import Solcore.Test.SourceCoreUnifiedCorpusSupport

/-! Closedness bridges independent source admission to validity without
changing the real residual context. Unused and reordered substitution rows
remain visible. Runtime checks inspect actual retained compiler metadata;
they do not supply source typing or well-formedness proofs. -/
set_option autoImplicit false
namespace Tests.SourceCoreCompatibleSourceInstantiationClosure
open Solcore Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open CompatibleSourceInstantiationClosure

private def signatures : ProgramSignatures := ⟨[], [], [], [], [], []⟩
private def residual : SourceSemantics.Context :=
  (SourceSemantics.Context.ofSignatures signatures).withResidualTypeVariables

private theorem binders : TypeParameterBindersWellFormed residual := by
  simp [TypeParameterBindersWellFormed, residual, Context.ofSignatures,
    Context.withResidualTypeVariables]

/-- Closed composite types retain staging wrappers and the exact source scope. -/
theorem composite_in_residual :
    TypeWellFormed residual (.comptime (.function (.proxy .bool) (.mapping .bool (.product .word .integer)))) ∧
    residual.residualTypeVariables = true := by
  refine ⟨well_formed ⟨binders, .comptime (.function (.proxy (.builtin .bool))
    (.mapping (.builtin .bool) (.product (.builtin .word) (.builtin .integer))))⟩ rfl rfl, rfl⟩

/-- Full range checking is independent of declaration parameter order. -/
theorem reordered_range (first second : TypeSystem.TypeParameterId) :
    ParameterSubstitution.RangeWellFormed residual [(second, .bool), (first, .comptime .word)] := by
  apply range_well_formed (lexical := rfl)
  · intro parameter replacement member
    rcases List.mem_cons.mp member with same | member
    · cases same; exact ⟨binders, .builtin .bool⟩
    · cases List.mem_singleton.mp member; exact ⟨binders, .comptime (.builtin .word)⟩
  · intro parameter replacement member
    rcases List.mem_cons.mp member with same | member
    · cases same; rfl
    · cases List.mem_singleton.mp member; rfl

/-- An unused residual replacement remains admissible but cannot be hidden by
the fact that applying the substitution leaves a closed result unchanged. -/
theorem unused_open_row (parameter : TypeSystem.TypeParameterId) :
    ParameterSubstitution.RangeAdmissible residual [(parameter, .variable ⟨17⟩)] ∧
    TypeSystem.ParameterSubstitution.apply [(parameter, .variable ⟨17⟩)] .word = .word ∧
    ¬ ClosedParameterRange [(parameter, .variable ⟨17⟩)] ∧
    ¬ ParameterSubstitution.RangeWellFormed residual [(parameter, .variable ⟨17⟩)] := by
  refine ⟨?_, rfl, ?_, ?_⟩
  · intro other replacement member
    simp only [List.mem_singleton] at member
    cases member
    exact TypeAdmissible.variableOfResidual binders rfl ⟨17⟩
  · intro closed
    have impossible := closed parameter (.variable ⟨17⟩) (by simp)
    cases impossible
  · intro valid
    have impossible := TypeWellScoped.variable_iff.mp
      (valid parameter (.variable ⟨17⟩) (by simp)).typeWellScoped
    cases impossible

variable {checked : CallableAncestryPairedLookup.Checked} {base : CallableAncestryPairedLookup.Base checked}
  {prepared : SourceCoreCallableIndexedAncestry.Prepared base}
  {values : SourceCoreCompatibleValues.Context} {definitions : Core.DataEnvironment} {program : SourceSemantics.Program}

/-- The actual named header supplies lexical emptiness, without a false
residual assumption. All declaration metadata is retained by the conclusion. -/
theorem actual_header_declaration (header : RecursiveNamedCatalog.Header prepared values definitions program)
    {instantiation : SourceInference.DeclarationInstantiation}
    (admissible : SourceSemantics.DeclarationInstantiation.Admissible header.context instantiation)
    (closed : ClosedParameterRange instantiation.parameterSubstitution) :
    SourceSemantics.DeclarationInstantiation.Valid header.context instantiation :=
  declaration_valid admissible (RecursiveNamedSourceContextFacts.header_typeVariables header) closed

theorem actual_header_constructor (header : RecursiveNamedCatalog.Header prepared values definitions program)
    {instantiation : SourceInference.DataConstructorInstantiation}
    (admissible : SourceSemantics.DataConstructorInstantiation.Admissible header.context instantiation)
    (closed : ClosedParameterRange instantiation.parameterSubstitution) :
    SourceSemantics.DataConstructorInstantiation.Valid header.context instantiation :=
  constructor_valid admissible (RecursiveNamedSourceContextFacts.header_typeVariables header) closed

private def content : String := String.intercalate "\n" [
  "enum Pair<A, B> { Pair(A, B) }",
  "function choose<A, B>(first: A, second: B) returns (A) { return first; }",
  "function wordRoot() returns (Word) { return choose(7, true); }",
  "function boolRoot() returns (Bool) { return choose(false, 9); }",
  "function dataRoot() returns (Pair<Word, Bool>) { return Pair(choose(11, false), true); }"
]
private def require := SourceCoreUnifiedCorpusSupport.assertTrue

def run : IO Unit := do
  let compiled ← SourceCoreUnifiedCorpusSupport.prepare "source instantiation closure" content
    ["wordRoot", "boolRoot", "dataRoot"]
  let mut functions := 0
  let mut constructors := 0
  for named in compiled.indexed.base.functions do
    let source := CallableIndexedNamedGeneration.source named
    for item in source.nodes do
      match item with
      | .expression node =>
        match node.form with
        | .call _ _ (.declaration instantiation) =>
          let key ← SourceCoreUnifiedCorpusSupport.get "closure exact source key"
            (SourceCompilationPlan.exactInstantiationKey compiled.indexed.base.plan instantiation)
          let selected ← SourceCoreUnifiedCorpusSupport.get "closure full specialization"
            (SourceCompilationPlan.exactSpecialization compiled.indexed.base.plan key)
          require (decide (instantiation = CallableNamedCanonicalOrder.retainedInstantiation selected))
            "closure full source instantiation changed"
          require (instantiation.parameterSubstitution.length == 2)
            "closure lost generic source parameter rows"
          require (instantiation.parameterSubstitution.all (fun row => SourceCoreDataCatalog.closed row.2))
            "closure retained open source replacement"
          functions := functions + 1
        | .constructor instantiation _ =>
          require (instantiation.parameterSubstitution.length == 2)
            "closure lost generic constructor parameter rows"
          require (instantiation.parameterSubstitution.all (fun row => SourceCoreDataCatalog.closed row.2))
            "closure constructor range retained open replacement"
          constructors := constructors + 1
        | _ => pure ()
      | _ => pure ()
  require (functions == 3 && constructors == 1)
    s!"closure actual metadata coverage changed: functions={functions}, constructors={constructors}"
  IO.println "source instantiation closure: true residual scope, complete ranges, generic source metadata GREEN"

end Tests.SourceCoreCompatibleSourceInstantiationClosure
