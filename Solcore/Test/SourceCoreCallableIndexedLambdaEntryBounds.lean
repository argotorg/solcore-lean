import Solcore.SourceSemantics.CoreLowering.CallableIndexedLambdaEntryBounds
import Solcore.Test.SourceCoreCallableIndexedLambdaViewCalls
import Solcore.Test.SourceCoreCallableIndexedLambdaValues

/-! Original indexed lambda completions expose a strict body witness and the
actual typed allocation state, including complete captures and frame restore.
The empty argument case keeps the frame/manifest boundary. Runtime regressions
reuse real ordered-parameter, capture, fault and resume fixtures. No old Entry
identity or source body meaning is inferred from the reached prefix. -/
#check_failure Solcore.Frontend.SourceTypedRuntime.run
set_option autoImplicit false
namespace Tests.SourceCoreCallableIndexedLambdaEntryBounds
open Solcore Core Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open GeneralHeap ReadOnly CoreProof CompatiblePayload
open CallableIndexedHistory CallableIndexedLambdaValues
open CallableIndexedParameterCertificates CallableIndexedParameterMeaning
open SourceCoreCallableIndexedFrames SourceCoreLambdaTemplates CallableIndexedLambdaEntryBounds

section Entry
variable {values : SourceCoreCompatibleValues.Context} {prepared : Prepared values.checked}
  {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope} {mapping : LocationMap} {world : StoreTyping}
  {capturedActual : Environment}
  (captured : CallableIndexedLambdaValues.Captures prepared mapping world scope function.captured capturedActual)
  (code : Code prepared function scope captured.administrative) (history : History code)
  (inputs : CallableIndexedLambdaEntryPrefix.Context code) (profile : values.checked.catalog.callableContracts = true)
  {registry : SourceCoreRawMetadata.Registry} {arguments : List Dynamic.Value} {nativeArguments : List Value}
  (represented : Arguments (CompatibleAmbientHeap.payloadModel values.checked registry (model prepared profile))
    mapping world code.receipt.loweredParameters arguments nativeArguments)
  {before : Dynamic.Heap} {store : Store} {location : Location}
  {current : NativeFrame} {currentGhost : GhostFrame} {currentMetadata : Option MetadataState}
  (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry (model prepared profile) mapping world before store)
  (locals : Dynamic.EnvironmentAgrees before function.context.locals function.captured)
  (reference : captured.canonical[code.referenceIndex]? = some (.cellRef prepared.ancestry.layout.frame.type location))
  (read : store.read? location = some (encode prepared.ancestry.layout.frame current))
  (currentCarried : Carries prepared.ancestry.graph.inputs prepared.ancestry.graph.table current currentGhost currentMetadata)
  (unmapped : location ∉ mapping)
  (allowed : SourceCoreCallableAncestryPairedPreparation.lambdaAllowed prepared.ancestry.graph.inputs history.metadata code.descriptor.id = true)

include captured code history inputs profile represented heaps locals reference read currentCarried unmapped allowed in
/-- The consumer keeps the body subderivation of the supplied application,
and reads the ordered lexical prefix from its reached state. -/
theorem original_application {size : Nat} {result : Value} {finalStore : Store}
    (completed : EvaluationSize size
      [CallableIndexedLambdaValues.value code captured.embedding history.native capturedActual,
        DataPatternValues.packValues nativeArguments]
      store CallableIndexedLambdaCalls.applyPayload result finalStore) :
    ∃ reached : Prefix captured code history inputs profile registry arguments before store location current,
      ∃ child bodyStore,
        child < size ∧ EvaluationSize child reached.actual reached.store
          (code.receipt.body.rename reached.embedding) result bodyStore ∧
        finalStore = bodyStore.set location (encode prepared.ancestry.layout.frame current) ∧
        ∃ added : Environment, added.length = code.receipt.loweredParameters.length ∧
          reached.canonical = added ++ captured.canonical := by
  obtain ⟨reached, child, bodyStore, smaller, evaluated, restored⟩ :=
    application_prefix captured code history inputs profile represented heaps locals reference read currentCarried unmapped allowed completed
  exact ⟨reached, child, bodyStore, smaller, evaluated, restored, reached.spine⟩

include captured code history inputs profile represented heaps locals reference read currentCarried unmapped allowed in
/-- Zero arguments retain the original strict body edge; the canonical
lexical spine has no added parameter values. Administrative values remain. -/
theorem empty_arguments_strict {size : Nat} {result : Value} {finalStore : Store}
    (empty : nativeArguments = [])
    (completed : EvaluationSize size
      [CallableIndexedLambdaValues.value code captured.embedding history.native capturedActual,
        DataPatternValues.packValues nativeArguments]
      store CallableIndexedLambdaCalls.applyPayload result finalStore) :
    ∃ reached : Prefix captured code history inputs profile registry arguments before store location current,
      ∃ child bodyStore,
        child < size ∧ EvaluationSize child reached.actual reached.store
          (code.receipt.body.rename reached.embedding) result bodyStore ∧
        finalStore = bodyStore.set location (encode prepared.ancestry.layout.frame current) ∧
        reached.canonical = captured.canonical := by
  obtain ⟨reached, child, bodyStore, smaller, evaluated, restored⟩ :=
    application_prefix captured code history inputs profile represented heaps locals reference read currentCarried unmapped allowed completed
  obtain ⟨added, length, spine⟩ := reached.spine
  have parameters : code.receipt.loweredParameters.length = 0 := by
    simpa [empty] using represented.length.2
  have noValues : added = [] := List.eq_nil_of_length_eq_zero (length.trans parameters)
  rw [noValues] at spine
  exact ⟨reached, child, bodyStore, smaller, evaluated, restored, by simpa using spine⟩

include captured code history inputs profile represented heaps locals reference read currentCarried unmapped allowed in
/-- This consumer erases only the extracted child witness. It never chooses a
new grade for the original completion. -/
theorem original_body {size : Nat} {result : Value} {finalStore : Store}
    (completed : EvaluationSize size
      (DataPatternValues.packValues nativeArguments :: encode prepared.ancestry.layout.frame history.native :: capturedActual)
      store (code.body.rename captured.embedding.lift.lift) result finalStore) :
    ∃ reached : Prefix captured code history inputs profile registry arguments before store location current,
      ∃ child bodyStore,
        child < size ∧ EvaluationSize child reached.actual reached.store
          (code.receipt.body.rename reached.embedding) result bodyStore ∧
        Evaluates reached.actual reached.store (code.receipt.body.rename reached.embedding) result bodyStore ∧
        finalStore = bodyStore.set location (encode prepared.ancestry.layout.frame current) := by
  obtain ⟨reached, child, bodyStore, smaller, evaluated, restored⟩ :=
    body_prefix captured code history inputs profile represented heaps locals reference read currentCarried unmapped allowed completed
  exact ⟨reached, child, bodyStore, smaller, evaluated, evaluated.sound, restored⟩
end Entry

/-- Actual manifest captures and their type survive stripping the original
let witness, even if the marked parameter prefix is empty. -/
theorem original_manifest {catalog : SourceCoreDataCatalog.Catalog} {definitions : DataEnvironment}
    {mapping : LocationMap} {world : StoreTyping} {administrative : Core.Context}
    {scope : SourceCoreLocalCell.Scope} {source : Dynamic.Environment} {canonical actual : Environment}
    {argument : Value} {ξ : Renaming}
    (related : DataHeap.EnvRepresents catalog mapping world administrative scope source canonical definitions)
    (agrees : EnvironmentsAgree ξ (argument :: canonical) actual)
    (descriptor : Word) (fields : List (Word × Ty)) (body : Expr) (store : Store)
    {size : Nat} {result : Value} {finalStore : Store}
    (completed : EvaluationSize size actual store
      ((manifestBody descriptor fields (SourceCoreSourceCells.captures id scope) body).rename ξ) result finalStore) :
    ∃ manifest child,
      RuntimeValueHasType world manifest
        (.product .word (.product (scopeManifestType fields) (SourceCoreSourceCells.captureType scope))) definitions ∧
      child < size ∧ EvaluationSize child (manifest :: actual) store
        (body.rename (Renaming.comp (Renaming.insertion 0) ξ)) result finalStore := by
  obtain ⟨manifest, typed, sized⟩ := manifest_prefix related agrees descriptor fields body store
  obtain ⟨child, smaller, evaluated⟩ := sized.remaining completed
  exact ⟨manifest, child, typed, smaller, evaluated⟩

theorem empty_prefix_same_size {size : Nat} {environment : Environment} {store after : Store}
    {code : Expr} {value : Value} (original : EvaluationSize size environment store code value after) :
    ∃ child, child = size ∧ EvaluationSize child environment store code value after :=
  ⟨size, rfl, original⟩

theorem agreement_does_not_force_strict :
    ContinuationAgreement [] [] .unit [] [] .unit ∧ ¬ ContinuationSize true [] [] .unit [] [] .unit := by
  refine ⟨.refl _ _ _, ?_⟩
  intro strict
  obtain ⟨child, smaller, original⟩ := strict.remaining EvaluationSize.unit
  cases original
  simp at smaller

/-- This is the actual empty capture/field manifest initializer. Its let
is strict while the remaining unit body keeps its own size one witness. -/
theorem empty_manifest_actual :
    ∃ child, child < 7 ∧ EvaluationSize child
      [.pair (.word Word.zero) (.pair .unit .unit)] [] .unit .unit [] := by
  have initializer : EvaluationSize 5 [] []
      (.pair (.word Word.zero) (.pair .unit .unit))
      (.pair (.word Word.zero) (.pair .unit .unit)) [] :=
    .pair EvaluationSize.word (.pair EvaluationSize.unit EvaluationSize.unit)
  have original : EvaluationSize 7 [] []
      (manifestBody Word.zero [] (SourceCoreSourceCells.captures id []) .unit) .unit [] := by
    simpa [manifestBody, scopeManifest, SourceCoreSourceCells.captures, Expr.weakenAt, Expr.rename]
      using EvaluationSize.letE initializer (EvaluationSize.unit (environment :=
        [.pair (.word Word.zero) (.pair .unit .unit)]) (store := []))
  have lowered : manifestBody Word.zero [] (SourceCoreSourceCells.captures id []) .unit =
      .letE (.pair (.word Word.zero) (.pair .unit .unit)) .unit := by
    simp [manifestBody, scopeManifest, SourceCoreSourceCells.captures, Expr.weakenAt]
  rw [lowered] at original
  exact (ContinuationSize.letE initializer.sound).remaining original

def run : IO Unit := do
  Tests.SourceCoreCallableIndexedLambdaViewCalls.run
  Tests.SourceCoreCallableIndexedLambdaValues.run
  IO.println "indexed lambda sized entry: original frame/manifest/parameter children, empty arity and complete typed captures GREEN"
end Tests.SourceCoreCallableIndexedLambdaEntryBounds
