import Solcore.SourceSemantics.CoreLowering.CallableIndexedNamedValues
import Solcore.SourceSemantics.CoreLowering.CompatibleEqualityMeaning
import Solcore.Test.SourceCompilerFeatureSupport

#check_failure Solcore.Frontend.SourceTypedRuntime.run
set_option autoImplicit false
namespace Tests.SourceCoreCallableIndexedNamedValues
open Solcore Core Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open CallableIndexedNamedValues CompatiblePayload GeneralHeap

/-- Actual validator and canonical resolver success imply equality of complete
source values, with domain order retained as an explicit occurrence receipt. -/
theorem metadata_from_checks {program : CheckedProgram} {plan : SourceCompilationPlan.Plan}
    {key : SourceCompilationPlan.Key} {metadata : DeclarationInstantiation} {specialized : Specialized}
    {actual canonical : Evidence}
    (target : SourceCompilationPlan.exactInstantiationKey plan metadata = .ok key)
    (record : SourceCompilationPlan.exactSpecialization plan key = .ok specialized)
    (domain : specialized.parameterSubstitution.map Prod.fst = metadata.parameterSubstitution.map Prod.fst)
    (authenticated : SourceCompilationPlan.validateAuthenticatedRuntimeEvidence program.signatures key specialized.assumptions actual = .ok ())
    (resolved : SourceCompilationPlan.resolveRuntimeEvidenceEnvironment program key specialized.assumptions = .ok canonical) :
    (⟨metadata, CallableNamedMetadata.environment actual⟩ : Dynamic.GlobalFunction) = CallableNamedMetadata.global specialized canonical :=
  CallableNamedMetadata.global_eq target record domain authenticated resolved

theorem distinct_dictionary_trees_rejected {program : CheckedProgram} {key : SourceCompilationPlan.Key}
    {predicates : List ProgramPredicate} {actual canonical : Evidence}
    (resolved : SourceCompilationPlan.resolveRuntimeEvidenceEnvironment program key predicates = .ok canonical)
    (different : actual ≠ canonical) :
    SourceCompilationPlan.validateAuthenticatedRuntimeEvidence program.signatures key predicates actual ≠ .ok () := by
  intro accepted
  exact different (CallableNamedMetadata.authenticated_evidence_eq accepted resolved)

/-- Both named and builtin leaves discharge the comparator's identity and
observation laws, with no invocation or child-evaluation hypothesis. -/
theorem comparison_from_receipts {checked : SourceCoreCompatibleCatalog.Checked} (prepared : Prepared checked)
    (profile : checked.catalog.callableContracts = true) (comparator : SourceCoreCompatibleDataEquality.Prepared checked)
    {registry : SourceCoreRawMetadata.Registry} {world : StoreTyping} {mapping : LocationMap}
    {leftType rightType : TypeSystem.Ty} {left right : Dynamic.Value} {a b : Value}
    (first : (model prepared profile).Represents registry mapping world leftType left a comparator.type)
    (second : (model prepared profile).Represents registry mapping world rightType right b comparator.type)
    (store : Store) :
    ∃ result, (result = true ↔ Dynamic.ValueEquivalent left right) ∧
      Evaluates [a, b] store (CompatibleEquality.comparison comparator (.var 0) (.var 1)) (.bool result)
        (CompatibleEquality.preparedStore comparator [a, b] store) :=
  CompatibleEquality.prepared_compare_preserves comparator (identity_faithful prepared)
    (observations prepared profile first) (observations prepared profile second) [a, b] store _ _ (.var rfl) (.var rfl)

theorem runtime_view_from_receipts {checked : SourceCoreCompatibleCatalog.Checked} (prepared : Prepared checked)
    (profile : checked.catalog.callableContracts = true)
    {registry : SourceCoreRawMetadata.Registry} {mapping : LocationMap} {world : StoreTyping}
    {parameter result : TypeSystem.Ty} {source : Dynamic.Value} {value : Value} {type : Ty}
    (related : (model prepared profile).Represents registry mapping world (.function parameter result) source value type) :
    Dynamic.ValueRuntimeTypeMatches source (.function parameter result) :=
  runtime_views prepared profile related

private def workspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := [], mainSources := [{path := "main.solc", content := String.intercalate "\n" [
    "trait Eq<T> {}", "impl Eq<Word> {}", "trait Mark<T> {}", "impl Mark<Word> {}",
    "function first() returns (Bool) { return true; }",
    "function second() returns (Bool) { return false; }",
    "function firstRef() returns (function() returns (Bool)) { return first; }",
    "function secondRef() returns (function() returns (Bool)) { return second; }",
    "function keep<T>(value: T) returns (T) where T: Eq, T: Mark { return value; }",
    "function keepRef() returns (function(Word) returns (Word)) { return keep; }",
    "function pair<A, B>(a: A, b: B) returns (A) { return a; }",
    "function pairRef() returns (function(Word, Bool) returns (Word)) { return pair; }",
    "function nativeAdd(a: integer, b: integer) returns (integer) { return integerAdd(a, b); }",
    "function namedAddRef() returns (function(integer, integer) returns (integer)) { return nativeAdd; }",
    "function builtinAddRef() returns (function(integer, integer) returns (integer)) { return integerAdd; }"
  ]}] }

private def compare {checked : SourceCoreCompatibleCatalog.Checked} (prepared : Prepared checked)
    (sourceType : TypeSystem.Ty) (a b : Value) (expected : Bool) : IO Unit := do
  let comparator ← SourceCompilerFeatureSupport.get "named comparator" (SourceCoreCompatibleDataEquality.prepare 500 checked sourceType)
  let code := CompatibleEquality.comparison comparator (.var 0) (.var 1)
  SourceCompilerFeatureSupport.require (infer? [comparator.type, comparator.type] code prepared.layouts.definitions == some .bool) "named comparator rejected ambient definitions"
  let before : Store := [.word (Word.ofNatModulo 94)]
  let done := runStateful 100000 (.initial code [a,b] before)
  SourceCompilerFeatureSupport.require (done == .done (.bool expected) (CompatibleEquality.preparedStore comparator [a,b] before))
    "named/builtin equality did not preserve full source identity"
  for fuel in [0, 1, 13] do
    match runStateful fuel (.initial code [a,b] before) with
    | .outOfFuel suspended => SourceCompilerFeatureSupport.require (runStateful 100000 suspended == done) "named comparison resume changed result"
    | other => SourceCompilerFeatureSupport.require (other == done) "named comparison prefix changed result"

private def key (program : CheckedProgram) (name : String) : IO SourceSpecialization.SpecializationKey := do
  let found ← match program.signatures.functions.find? (·.name == name) with
    | some found => pure found
    | none => throw (IO.userError s!"missing named fixture {name}")
  pure ⟨found.id, []⟩

private def returned {checked : SourceCoreCompatibleCatalog.Checked} (prepared : Prepared checked)
    (name : String) : IO Value := do
  let target ← key prepared.base.sourceProgram name
  let initial ← SourceCompilerFeatureSupport.get "actual indexed reference return" (prepared.runSource target [] 0)
  let done := initial.resume 300000
  match done.result.native.observation with
  | .succeeded value _ =>
    let direct ← SourceCompilerFeatureSupport.get "direct indexed reference return" (prepared.runSource target [] 300000)
    match direct.result.native.observation with
    | .succeeded expected _ => SourceCompilerFeatureSupport.require (value == expected) "native named output resume changed captures"; pure value
    | other => throw (IO.userError s!"direct reference result {reprStr other}")
  | other => throw (IO.userError s!"named reference result {reprStr other}")

def run : IO Unit := do
  let sourceProgram ← SourceCompilerFeatureSupport.get "named leaf checked source" (checkProgram workspace)
  let seeds := (sourceProgram.signatures.functions.filter (·.scheme.parameters.isEmpty)).map fun signature =>
    (⟨signature.id, []⟩ : SourceSpecializationWorklist.Request)
  let plan ← match SourceSpecializationWorklist.run sourceProgram seeds 256 with
    | .ok (.complete plan) => pure plan
    | other => throw (IO.userError s!"named leaf worklist {reprStr other}")
  let automatic ← SourceCompilerFeatureSupport.get "named leaf compatible artifact" (SourceCoreCompatibleFunctions.prepare sourceProgram plan 500)
  let prepared ← SourceCompilerFeatureSupport.get "named leaf indexed artifact" (SourceCoreCallableIndexedPrograms.prepare automatic.prepared 500)
  let mut observed : List (String × Value) := []
  let mut evidenceCount := 0
  let mut permutedCount := 0
  for name in ["firstRef", "secondRef", "keepRef", "pairRef", "namedAddRef"] do
    let value ← returned prepared name
    observed := observed ++ [(name, value)]
    match value with
    | .pair (.pair (.inRight .unit (.word identity)) (.closure parameter result body captured)) (.word contract) =>
      SourceCompilerFeatureSupport.require (identity.val > 0) "zero named identity"
      let index := identity.val - 1
      let signature ← match prepared.base.globals[index]? with
        | some signature => pure signature | none => throw (IO.userError "named identity outside actual globals")
      let record ← SourceCompilerFeatureSupport.get "canonical named record" (SourceCompilationPlan.exactSpecialization prepared.base.plan signature.key)
      let header := CallableNamedMetadata.instantiation record
      let selected ← SourceCompilerFeatureSupport.get "canonical named target" (SourceCompilationPlan.exactInstantiationKey prepared.base.plan header)
      SourceCompilerFeatureSupport.require (decide (selected = signature.key)) "canonical metadata selected different target"
      let evidence ← SourceCompilerFeatureSupport.get "canonical full dictionary" (SourceCompilationPlan.resolveRuntimeEvidenceEnvironment sourceProgram signature.key record.assumptions)
      let _ ← SourceCompilerFeatureSupport.get "authenticate full dictionary" (SourceCompilationPlan.validateAuthenticatedRuntimeEvidence sourceProgram.signatures signature.key record.assumptions evidence)
      if !evidence.isEmpty then
        evidenceCount := evidenceCount + 1
        let changed := evidence.map fun | .byImpl goal _ premises => TraitResolution.Evidence.byImpl goal (.builtin .intWord) premises
        SourceCompilerFeatureSupport.require (match SourceCompilationPlan.validateAuthenticatedRuntimeEvidence sourceProgram.signatures signature.key record.assumptions changed with | .error _ => true | .ok _ => false)
          "same goals with changed evidence trees were accepted"
      if header.parameterSubstitution.length > 1 then
        permutedCount := permutedCount + 1
        let changed := {header with parameterSubstitution := header.parameterSubstitution.reverse}
        SourceCompilerFeatureSupport.require (decide (header ≠ changed)) "two-parameter fixture did not change retained order"
        let keyAgain ← SourceCompilerFeatureSupport.get "order-insensitive actual target" (SourceCompilationPlan.exactInstantiationKey prepared.base.plan changed)
        SourceCompilerFeatureSupport.require (decide (keyAgain = selected)) "actual matcher unexpectedly demands canonical list order"
      let descriptor ← SourceCompilerFeatureSupport.get "named owned descriptor" (SourceCoreCallableContracts.descriptor prepared.ancestry.graph.inputs.callable.table (.named signature.key))
      SourceCompilerFeatureSupport.require (contract == descriptor.id) "named carrier descriptor changed"
      let template ← match prepared.secondPass.closures[index]? with
        | some template => pure template | none => throw (IO.userError "missing cached named body")
      SourceCompilerFeatureSupport.require (SourceCoreCompatibleOutputs.installedTemplate index template == .lambda parameter result body)
        "actual named body differs from installed cached code"
      SourceCompilerFeatureSupport.require (!captured.isEmpty) "indexed named closure lost actual administrative captures"
      compare prepared header.type value value true
    | other => throw (IO.userError s!"unexpected named carrier {reprStr other}")
  SourceCompilerFeatureSupport.require (evidenceCount == 1 && permutedCount == 1) "qualified/multi-parameter fixture coverage changed"
  let first := (observed.find? (·.1 == "firstRef")).getD ("", .unit) |>.2
  let second := (observed.find? (·.1 == "secondRef")).getD ("", .unit) |>.2
  compare prepared (.function .unit .bool) first second false
  let namedAdd := (observed.find? (·.1 == "namedAddRef")).getD ("", .unit) |>.2
  let builtinAdd ← returned prepared "builtinAddRef"
  compare prepared BuiltinFunctionId.integerAdd.type namedAdd builtinAdd false
  IO.println "indexed named leaves: full metadata/evidence, permutation boundary, installed captures, mixed identities and resume GREEN"
end Tests.SourceCoreCallableIndexedNamedValues
