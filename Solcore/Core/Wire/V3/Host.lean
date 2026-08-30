import Solcore.Core.Check
import Solcore.Core.Host
import Solcore.Core.Wire.V3.Conversions

/-! The frozen host boundary used to check Semantic Core Wire v3 programs. -/

set_option autoImplicit false

namespace Solcore.Core.Wire.V3.Host

abbrev CoreProgram := Solcore.Core.Program
abbrev CoreHostFunction := Solcore.Core.HostFunction

/-- The exact host functions exposed by Semantic Core Wire v3.

This list is deliberately written out instead of referring to the evolving
internal `Core.HostFunction.all` table. -/
def functions : List CoreHostFunction :=
  [.storageRead, .storageWrite, .storageAddress, .codeAddress,
    .callValue, .callerAddress, .inputDataByte?, .inputDataSize,
    .inputDataWordBE?, .currentAddress, .callContractWord,
    .callContractWordWithValue, .createContractWord, .emitLogWord]

/-- The exact root typing context published by Semantic Core Wire v3. -/
def context : Solcore.Core.Context :=
  functions.map Solcore.Core.HostFunction.functionType

/-- The runtime values corresponding positionally to `context`. -/
def environment : Solcore.Core.Environment :=
  functions.map fun function => .hostFunction function

@[simp] theorem functions_length : functions.length = 14 :=
  rfl

@[simp] theorem context_length : context.length = 14 := by
  simp [context]

@[simp] theorem environment_length : environment.length = 14 := by
  simp [environment]

@[simp] theorem functions_lookup (function : CoreHostFunction) :
    functions[function.index]? = some function := by
  cases function <;> rfl

@[simp] theorem context_lookup (function : CoreHostFunction) :
    context[function.index]? = some function.functionType := by
  cases function <;> rfl

@[simp] theorem environment_lookup (function : CoreHostFunction) :
    environment[function.index]? = some (.hostFunction function) := by
  cases function <;> rfl

@[simp] theorem functions_firstUnbound : functions[14]? = none :=
  rfl

@[simp] theorem context_firstUnbound : context[14]? = none :=
  rfl

@[simp] theorem environment_firstUnbound : environment[14]? = none :=
  rfl

/-- The frozen table currently occupies the exact internal host table. -/
theorem functions_eq_current :
    functions = Solcore.Core.HostFunction.all :=
  rfl

/-- Append-only internal evolution must retain the entire v3 table as a prefix. -/
theorem functions_prefix_current :
    functions <+: Solcore.Core.HostFunction.all := by
  rw [functions_eq_current]
  exact ⟨[], by simp⟩

theorem context_eq_current :
    context = Solcore.Core.hostContext := by
  rw [context, Solcore.Core.hostContext, functions_eq_current]

theorem context_prefix_current :
    context <+: Solcore.Core.hostContext := by
  rw [context_eq_current]
  exact ⟨[], by simp⟩

/-- Identity renaming preserves every frozen binding in the current context. -/
theorem context_respects_current :
    Solcore.Core.Renaming.Respects Solcore.Core.Renaming.id
      context Solcore.Core.hostContext := by
  intro index type found
  rcases context_prefix_current with ⟨suffix, equation⟩
  rw [← equation]
  have bound : index < context.length :=
    (List.getElem?_eq_some_iff.mp found).1
  have bound14 : index < 14 := by simpa using bound
  simpa [Solcore.Core.Renaming.id, List.getElem?_append, bound14] using found

theorem environment_eq_current :
    environment = Solcore.Core.hostEnvironment := by
  rw [environment, Solcore.Core.hostEnvironment, functions_eq_current]

theorem environment_prefix_current :
    environment <+: Solcore.Core.hostEnvironment := by
  rw [environment_eq_current]
  exact ⟨[], by simp⟩

/-- Declarative validity under the frozen v3 host context. -/
abbrev WellTyped (program : CoreProgram) : Prop :=
  program.WellTypedIn context

/-- Boolean Core checking under exactly the v3 host context. -/
def check (program : CoreProgram) : Bool :=
  program.checkIn context

/-- Diagnostic Core checking under exactly the v3 host context. -/
def checkDetailed (program : CoreProgram) : Except Solcore.Core.CheckError Solcore.Core.Ty :=
  program.checkDetailedIn context

theorem check_full_sound
    {program : CoreProgram}
    (checked : check program = true) :
    WellTyped program :=
  Solcore.Core.Program.checkIn_full_sound checked

theorem check_sound
    {program : CoreProgram}
    (checked : check program = true) :
    Solcore.Core.HasType context program.body program.resultType
      program.dataDefinitions :=
  Solcore.Core.Program.checkIn_sound checked

theorem check_complete
    {program : CoreProgram}
    (wellTyped : WellTyped program) :
    check program = true :=
  Solcore.Core.Program.checkIn_complete wellTyped

theorem check_iff_wellTyped {program : CoreProgram} :
    check program = true ↔ WellTyped program :=
  Solcore.Core.Program.checkIn_iff_wellTyped

theorem checkDetailed_iff_check {program : CoreProgram} :
    checkDetailed program = .ok program.resultType ↔ check program = true :=
  Solcore.Core.Program.checkDetailedIn_iff_checkIn

theorem checkDetailed_iff_wellTyped {program : CoreProgram} :
    checkDetailed program = .ok program.resultType ↔ WellTyped program :=
  Solcore.Core.Program.checkDetailedIn_iff_wellTyped

theorem checkDetailed_full_sound
    {program : CoreProgram}
    (checked : checkDetailed program = .ok program.resultType) :
    WellTyped program :=
  Solcore.Core.Program.checkDetailedIn_full_sound checked

theorem checkDetailed_sound
    {program : CoreProgram}
    (checked : checkDetailed program = .ok program.resultType) :
    Solcore.Core.HasType context program.body program.resultType
      program.dataDefinitions :=
  Solcore.Core.Program.checkDetailedIn_sound checked

theorem checkDetailed_complete
    {program : CoreProgram}
    (wellTyped : WellTyped program) :
    checkDetailed program = .ok program.resultType :=
  Solcore.Core.Program.checkDetailedIn_complete wellTyped

/-- Frozen v3 acceptance promotes to the current internal host checker. -/
theorem check_promotes_current
    {program : CoreProgram}
    (checked : check program = true) :
    program.checkHost = true := by
  have wellTyped := check_full_sound checked
  apply Solcore.Core.Program.checkHost_complete
  refine ⟨wellTyped.dataDefinitionsWellFormed,
    wellTyped.resultTypeWellFormed, ?_⟩
  simpa using wellTyped.bodyHasType.rename context_respects_current

end Solcore.Core.Wire.V3.Host

namespace Solcore.Core.Wire.V3.Program

/-- Check a Wire v3 program under the frozen v3 host context. -/
def check (program : Program) : Bool :=
  Host.check program.toCore

/-- Check a Wire v3 program with Core diagnostics under the frozen context. -/
def checkDetailed (program : Program) :
    Except Solcore.Core.CheckError Solcore.Core.Ty :=
  Host.checkDetailed program.toCore

/-- Declarative validity of the projected program under the frozen context. -/
abbrev WellTyped (program : Program) : Prop :=
  Host.WellTyped program.toCore

theorem check_full_sound
    {program : Program}
    (checked : program.check = true) :
    program.WellTyped :=
  Host.check_full_sound checked

theorem check_sound
    {program : Program}
    (checked : program.check = true) :
    Solcore.Core.HasType Host.context program.toCore.body
      program.resultType.toCore program.toCore.dataDefinitions :=
  Host.check_sound checked

theorem check_complete
    {program : Program}
    (wellTyped : program.WellTyped) :
    program.check = true :=
  Host.check_complete wellTyped

theorem check_iff_wellTyped {program : Program} :
    program.check = true ↔ program.WellTyped :=
  Host.check_iff_wellTyped

theorem checkDetailed_iff_check {program : Program} :
    program.checkDetailed = .ok program.resultType.toCore ↔
      program.check = true :=
  Host.checkDetailed_iff_check

theorem checkDetailed_iff_wellTyped {program : Program} :
    program.checkDetailed = .ok program.resultType.toCore ↔
      program.WellTyped :=
  Host.checkDetailed_iff_wellTyped

theorem checkDetailed_full_sound
    {program : Program}
    (checked : program.checkDetailed = .ok program.resultType.toCore) :
    program.WellTyped :=
  Host.checkDetailed_full_sound checked

theorem checkDetailed_sound
    {program : Program}
    (checked : program.checkDetailed = .ok program.resultType.toCore) :
    Solcore.Core.HasType Host.context program.toCore.body
      program.resultType.toCore program.toCore.dataDefinitions :=
  Host.checkDetailed_sound checked

theorem checkDetailed_complete
    {program : Program}
    (wellTyped : program.WellTyped) :
    program.checkDetailed = .ok program.resultType.toCore :=
  Host.checkDetailed_complete wellTyped

/-- Wire acceptance is sufficient for current checked-host admission. -/
theorem check_promotes_current
    {program : Program}
    (checked : program.check = true) :
    program.toCore.checkHost = true :=
  Host.check_promotes_current checked

end Solcore.Core.Wire.V3.Program
