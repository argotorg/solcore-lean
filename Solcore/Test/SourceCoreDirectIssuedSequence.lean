import Solcore.Test.SourceCoreDirectIssuedCommon

/-! Genuine named and builtin issuances are interleaved with direct public
calls. Each next operation uses the exact completion of its predecessor. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreDirectIssued
open Solcore Frontend SourceInference SourceSemantics
open Tests.SourceCoreCapturedReuse

def issuanceFuel : Nat := 1024
def builtinArgument : Int := 37
def builtinResult : Core.Word := Core.Word.ofNatModulo 37

structure ObservedNamed {artifact : SourceCoreExecution.Artifact}
    (session : SourceCoreExecution.Session artifact) (key : SourceCoreIndexedSession.Key) where
  completion : SourceCoreExecution.Completion artifact
  issued : session.NamedIssuedAt key issuanceFuel completion
  handle : SourceCorePublicValues.Handle
  returned : completion.value = .function handle

structure ObservedBuiltin {artifact : SourceCoreExecution.Artifact}
    (session : SourceCoreExecution.Session artifact) where
  completion : SourceCoreExecution.Completion artifact
  issued : session.BuiltinIssuedAt .wordFromInteger issuanceFuel completion
  handle : SourceCorePublicValues.Handle
  returned : completion.value = .function handle

structure ObservedInvocation {artifact : SourceCoreExecution.Artifact}
    (session : SourceCoreExecution.Session artifact) (handle : SourceCorePublicValues.Handle)
    (argument : SourceCorePublicValues.Value) where
  completion : SourceCoreExecution.Completion artifact
  executed : session.InvokeAt handle argument runOptions (.ok (.succeeded completion))

def observeNamed {artifact : SourceCoreExecution.Artifact}
    (session : SourceCoreExecution.Session artifact) (key : SourceCoreIndexedSession.Key) :
    IO (ObservedNamed session key) := do
  match ← session.namedWithReceipt key issuanceFuel with
  | .error error => throw (IO.userError (reprStr error))
  | .ok result =>
    match returned : result.val.value with
    | .function handle => pure ⟨result.val, result.property, handle, returned⟩
    | _ => throw (IO.userError "named issuance did not return a function")

def observeBuiltin {artifact : SourceCoreExecution.Artifact}
    (session : SourceCoreExecution.Session artifact) : IO (ObservedBuiltin session) := do
  match ← session.builtinWithReceipt .wordFromInteger issuanceFuel with
  | .error error => throw (IO.userError (reprStr error))
  | .ok result =>
    match returned : result.val.value with
    | .function handle => pure ⟨result.val, result.property, handle, returned⟩
    | _ => throw (IO.userError "builtin issuance did not return a function")

def observeInvocation {artifact : SourceCoreExecution.Artifact}
    (session : SourceCoreExecution.Session artifact) (handle : SourceCorePublicValues.Handle)
    (argument : SourceCorePublicValues.Value) : IO (ObservedInvocation session handle argument) := do
  let executed ← session.invokePackedWithReceipt handle argument runOptions
  match result : executed.val with
  | .error error => throw (IO.userError (reprStr error))
  | .ok (.failed _ _) => throw (IO.userError "direct issued call failed")
  | .ok (.exportError error _) => throw (IO.userError (reprStr error))
  | .ok (.outOfFuel _) => throw (IO.userError "direct issued call exhausted")
  | .ok (.succeeded completion) => pure ⟨completion, result ▸ executed.property⟩

structure ObservedSequence (fixture : CompiledFixture) (observed : ObservedProgram fixture) where
  first : ObservedPublicRun fixture observed.makeRow
  named : ObservedNamed first.completion.session observed.readRow.row.key
  read : ObservedInvocation named.completion.session named.handle (.function first.handle)
  readValue : read.completion.value = .word seed
  builtin : ObservedBuiltin read.completion.session
  converted : ObservedInvocation builtin.completion.session builtin.handle (.integer builtinArgument)
  convertedValue : converted.completion.value = .word builtinResult

private def confirm (proposition : Prop) [Decidable proposition] (label : String) : IO (PLift proposition) :=
  if accepted : proposition then pure ⟨accepted⟩ else throw (IO.userError label)

def observeSequence (fixture : CompiledFixture) (observed : ObservedProgram fixture) :
    IO (ObservedSequence fixture observed) := do
  let first ← observePublicRun fixture observed.makeRow
  let named ← observeNamed first.completion.session observed.readRow.row.key
  let read ← observeInvocation named.completion.session named.handle (.function first.handle)
  let ⟨readValue⟩ ← confirm (read.completion.value = .word seed) "direct named read did not return 10"
  let builtin ← observeBuiltin read.completion.session
  let converted ← observeInvocation builtin.completion.session builtin.handle (.integer builtinArgument)
  let ⟨convertedValue⟩ ← confirm (converted.completion.value = .word builtinResult)
    "direct builtin conversion did not return 37"
  pure ⟨first, named, read, readValue, builtin, converted, convertedValue⟩

end Tests.SourceCoreDirectIssued
