import Solcore.SourceSemantics.Dynamic.Program
import Solcore.SourceSemantics.Dynamic.WholeLanguagePreservation

/-!
Whole-program preservation for the declarative resolved-source semantics.

The core mutual preservation proof is packaged as
`WholeLanguagePreservation`.  This module connects that package to the
observable `ProgramEvaluates` boundary: the entry-point instantiation supplies
the exact static body certificate, and its source binders determine the
argument types consumed by the invocation theorem.
-/

set_option autoImplicit false

namespace Solcore.SourceSemantics.Dynamic

namespace ProgramEvaluates

/-- A successful, admitted program execution preserves the instantiated entry
body whenever the whole-language preservation package is supplied.  The body
instance is retained existentially because it is intentionally hidden by the
public program-evaluation judgment. -/
theorem preservesWith
    {program : Program} {entry : ProgramEntry}
    {initial final : Heap} {result : Value}
    (preservation : WholeLanguagePreservation program)
    (evaluates : ProgramEvaluates program entry initial result final) :
    exists bodyInstance,
      ProgramEntryValid program entry initial bodyInstance /\
        BodyInvocationPreserved bodyInstance initial final result := by
  cases evaluates with
  | run admitted entryValid invokes =>
      obtain ⟨inputTypes, lexicalContext, facts, certificate⟩ :=
        entryValid.instantiates.certificate preservation.program_well_formed
      refine ⟨_, entryValid, preservation.invoke (bodyInstance := _)
        (evidence := entry.evidence) (before := initial) (after := final)
        (arguments := entry.arguments) (result := result)
        (inputTypes := inputTypes) (lexicalContext := lexicalContext)
        (facts := facts) certificate.toBodyInstanceTypingCertificate
        entryValid.evidence_covers
        entryValid.heap_typed ?_ invokes⟩
      rw [← Solcore.SourceSemantics.Dynamic.MonoBindersExtend.bodyTypes_eq
        certificate.toBodyInstanceTypingCertificate.typing.inputs_extend]
      exact entryValid.arguments_typed

/-- Successful whole-program execution preserves the exact instantiated entry
body.  Unlike `preservesWith`, this theorem constructs the whole-language
preservation package directly from the static admission carried by the
program-evaluation derivation. -/
theorem preserves
    {program : Program} {entry : ProgramEntry}
    {initial final : Heap} {result : Value}
    (evaluates : ProgramEvaluates program entry initial result final) :
    exists bodyInstance,
      ProgramEntryValid program entry initial bodyInstance /\
        BodyInvocationPreserved bodyInstance initial final result :=
  evaluates.preservesWith
    evaluates.program_well_formed.wholeLanguagePreservation

end ProgramEvaluates

end Solcore.SourceSemantics.Dynamic
