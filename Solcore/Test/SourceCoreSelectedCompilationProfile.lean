import Solcore.Test.SourceCoreCompilationScope
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationCompilerStaticProfile

/-! The actual compiler profile accepts the selected identity cache even when
an unrelated checked conversion has no executable coercion method. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreSelectedCompilationProfile
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open SourceCoreCompilationScope (workspace options)

def run : IO Unit := do
  match checked : checkProgram workspace options.checkingFuel with
  | .error errors => throw (IO.userError s!"scope profile checking: {reprStr errors}")
  | .ok program =>
    let some identity := program.signatures.functions.find? (·.name == "identity")
      | throw (IO.userError "scope profile identity missing")
    match generated : SourceCoreCompiler.compileChecked program [.declaration identity.id] options with
    | .error error => throw (IO.userError s!"scope profile compilation: {reprStr error}")
    | .ok source =>
      match present : source.artifact? with
      | none => throw (IO.userError "scope profile cached artifact missing")
      | some cached =>
        have sameProgram : cached.sourceProgram = program :=
          (source.artifact_fields present).1.trans
            (SourceCoreCompiler.compileChecked_program generated)
        have accepted : checkProgram workspace options.checkingFuel = .ok cached.sourceProgram := by
          rw [sameProgram]
          exact checked
        let some profile := SelectedCompilationCompilerStaticProfile.validateCheckedProfile cached accepted
          | throw (IO.userError "scope profile rejected the selected identity")
        unless cached.sourceProgram.functions.length == 2 &&
            cached.indexed.base.functions.length == 1 && profile.table.rows.length == 1 do
          throw (IO.userError "scope profile changed original declarations or selected cache")
        IO.println "SELECTED_COMPILATION_PROFILE_PASS: checker-derived signatures; original functions2; selected cache1/table1; unrelated missing coercion method retained"

end Tests.SourceCoreSelectedCompilationProfile
