import Solcore.SourceSemantics.SourceCompiledProvenanceStatementContracts
import Solcore.SourceSemantics.SourceCompiledGeneralizedAssemblyContracts

/-! The original APIs are exactly the unrestricted instance of call provenance.
The conversion does not construct provenance for any actual selected run. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceCompiledGeneralizedSoundness
open Frontend SourceInference TypeSystem SourceInferenceSoundness
open SourceCompiledLocalFinalization SourceInferenceExecution

variable {compiled : SourceCoreCompiler.Compiled}
    {row : SourceSpecialization.SpecializedFunction} {fuel childFuel : Nat}
    {selected : BodySelection compiled row fuel}

theorem statementRootedSoundnessFor_true
    (sound : StatementRootedSoundness selected childFuel) :
    StatementRootedSoundnessFor (fun _ => True) selected childFuel :=
  fun _ safe admissible boundary => sound safe admissible boundary

theorem statementRootedSoundness_of_true
    (sound : StatementRootedSoundnessFor (fun _ => True) selected childFuel) :
    StatementRootedSoundness selected childFuel :=
  fun safe admissible boundary => sound trivial safe admissible boundary

theorem statementsRootedSoundnessFor_true
    (sound : StatementsRootedSoundness selected childFuel) :
    StatementsRootedSoundnessFor (fun _ => True) selected childFuel :=
  fun _ safe admissible boundary => sound safe admissible boundary

theorem statementsRootedSoundness_of_true
    (sound : StatementsRootedSoundnessFor (fun _ => True) selected childFuel) :
    StatementsRootedSoundness selected childFuel :=
  fun safe admissible boundary => sound trivial safe admissible boundary

theorem forItemRootedSoundnessFor_true
    (sound : ForItemRootedSoundness selected childFuel) :
    ForItemRootedSoundnessFor (fun _ => True) selected childFuel :=
  fun _ boundary => sound boundary

theorem forItemRootedSoundness_of_true
    (sound : ForItemRootedSoundnessFor (fun _ => True) selected childFuel) :
    ForItemRootedSoundness selected childFuel :=
  fun boundary => sound trivial boundary

theorem forItemsRootedSoundnessFor_true
    (sound : ForItemsRootedSoundness selected childFuel) :
    ForItemsRootedSoundnessFor (fun _ => True) selected childFuel :=
  fun _ boundary => sound boundary

theorem forItemsRootedSoundness_of_true
    (sound : ForItemsRootedSoundnessFor (fun _ => True) selected childFuel) :
    ForItemsRootedSoundness selected childFuel :=
  fun boundary => sound trivial boundary

theorem placeRootedSoundnessFor_true
    (sound : PlaceRootedSoundness selected childFuel) :
    PlaceRootedSoundnessFor (fun _ => True) selected childFuel :=
  fun _ boundary => sound boundary

theorem placeRootedSoundness_of_true
    (sound : PlaceRootedSoundnessFor (fun _ => True) selected childFuel) :
    PlaceRootedSoundness selected childFuel :=
  fun boundary => sound trivial boundary

theorem BodyInitializerBarriers.with_true (barriers : BodyInitializerBarriers selected) :
    BodyInitializerBarriersFor (fun _ => True) selected where
  statement occurrence _ boundary := barriers.statement occurrence boundary
  header _ boundary receipt := barriers.header boundary receipt

theorem BodyInitializerBarriersFor.of_true
    (barriers : BodyInitializerBarriersFor (fun _ => True) selected) :
    BodyInitializerBarriers selected where
  statement occurrence boundary := barriers.statement occurrence trivial boundary
  header boundary receipt := barriers.header trivial boundary receipt

end Solcore.SourceSemantics.SourceCompiledGeneralizedSoundness
