import Solcore.Test.SourceCoreConstructorCallsFixture

/-! Actual public calls reuse distinct closure exports through the returned
sessions. Every step retains its original startup and run receipts. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreConstructorCalls
open Solcore Frontend SourceInference SourceSemantics

def secondSeed : Core.Word := Core.Word.ofNatModulo 20
def interveningSeed : Core.Word := Core.Word.ofNatModulo 30

structure ObservedCall {artifact : SourceCoreExecution.Artifact}
    (session : SourceCoreExecution.Session artifact) (key : SourceCoreIndexedSession.Key)
    (arguments : List SourceCorePublicValues.Value) where
  checkpoint : SourceCoreExecution.Checkpoint artifact
  started : session.start key arguments runOptions.inputValidationFuel = .ok checkpoint
  completion : SourceCoreExecution.Completion artifact
  executed : session.RunAt key arguments runOptions (.ok (.succeeded completion))

def observeCall {artifact : SourceCoreExecution.Artifact}
    (session : SourceCoreExecution.Session artifact) (key : SourceCoreIndexedSession.Key)
    (arguments : List SourceCorePublicValues.Value) : IO (ObservedCall session key arguments) := do
  match started : session.start key arguments runOptions.inputValidationFuel with
  | .error error => throw (IO.userError (reprStr error))
  | .ok checkpoint =>
    let executed ← session.runWithReceipt key arguments runOptions
    match result : executed.val with
    | .error error => throw (IO.userError (reprStr error))
    | .ok (.failed _ _) => throw (IO.userError "captured reuse public call failed")
    | .ok (.exportError error _) => throw (IO.userError (reprStr error))
    | .ok (.outOfFuel _) => throw (IO.userError "captured reuse public call exhausted")
    | .ok (.succeeded completion) =>
      return ⟨checkpoint, started, completion, result ▸ executed.property⟩

structure ObservedFunctionCall {artifact : SourceCoreExecution.Artifact}
    (session : SourceCoreExecution.Session artifact) (key : SourceCoreIndexedSession.Key)
    (arguments : List SourceCorePublicValues.Value) extends ObservedCall session key arguments where
  handle : SourceCorePublicValues.Handle
  returned : completion.value = .function handle

def observeFunctionCall {artifact : SourceCoreExecution.Artifact}
    (session : SourceCoreExecution.Session artifact) (key : SourceCoreIndexedSession.Key)
    (arguments : List SourceCorePublicValues.Value) : IO (ObservedFunctionCall session key arguments) := do
  let call ← observeCall session key arguments
  match returned : call.completion.value with
  | .function handle => return ⟨call, handle, returned⟩
  | _ => throw (IO.userError "captured reuse expected a function export")

def issuanceFuel : Nat := 1024

structure ObservedNamed {artifact : SourceCoreExecution.Artifact}
    (session : SourceCoreExecution.Session artifact) (key : SourceCoreIndexedSession.Key) where
  completion : SourceCoreExecution.Completion artifact
  issued : session.NamedIssuedAt key issuanceFuel completion
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


structure ObservedBuiltin {artifact : SourceCoreExecution.Artifact}
    (session : SourceCoreExecution.Session artifact) where
  completion : SourceCoreExecution.Completion artifact
  issued : session.BuiltinIssuedAt .wordFromInteger issuanceFuel completion
  handle : SourceCorePublicValues.Handle
  returned : completion.value = .function handle

def observeBuiltin {artifact : SourceCoreExecution.Artifact}
    (session : SourceCoreExecution.Session artifact) : IO (ObservedBuiltin session) := do
  match ← session.builtinWithReceipt .wordFromInteger issuanceFuel with
  | .error error => throw (IO.userError (reprStr error))
  | .ok result =>
    match returned : result.val.value with
    | .function handle => pure ⟨result.val, result.property, handle, returned⟩
    | _ => throw (IO.userError "builtin issuance did not return a function")


def packedArgument (factory prior convert : SourceCorePublicValues.Handle) : SourceCorePublicValues.Value :=
  .product (.function factory) (.product (.word secondSeed) (.product (.function prior) (.function convert)))

structure ObservedConstruction {artifact : SourceCoreExecution.Artifact}
    (session : SourceCoreExecution.Session artifact) (handle factory prior convert : SourceCorePublicValues.Handle)
    (instantiation : DataConstructorInstantiation)
    extends ObservedInvocation session handle (packedArgument factory prior convert) where
  newOutput : SourceCorePublicValues.Handle
  priorOutput : SourceCorePublicValues.Handle
  factoryOutput : SourceCorePublicValues.Handle
  builtinOutput : SourceCorePublicValues.Handle
  returned : completion.value = .constructed instantiation
    [.function newOutput, .function priorOutput, .function factoryOutput, .function builtinOutput]
  priorSame : priorOutput = prior
  factorySame : factoryOutput = factory
  builtinSame : builtinOutput = convert
  distinct : newOutput ≠ priorOutput
  newType : newOutput.sourceType = closureType
  priorType : priorOutput.sourceType = closureType
  factoryType : factoryOutput.sourceType = makerType
  builtinType : builtinOutput.sourceType = convertType

def observeConstruction {artifact : SourceCoreExecution.Artifact}
    (session : SourceCoreExecution.Session artifact) (handle factory prior convert : SourceCorePublicValues.Handle)
    (instantiation : DataConstructorInstantiation) :
    IO (ObservedConstruction session handle factory prior convert instantiation) := do
  let call ← observeInvocation session handle (packedArgument factory prior convert)
  match call.completion.value with
  | .constructed _ [.function newOutput, .function priorOutput, .function factoryOutput, .function builtinOutput] =>
    if returned : call.completion.value = .constructed instantiation
        [.function newOutput, .function priorOutput, .function factoryOutput, .function builtinOutput] then
      if priorSame : priorOutput = prior then
        if factorySame : factoryOutput = factory then
          if builtinSame : builtinOutput = convert then
            if distinct : newOutput ≠ priorOutput then
              if newType : newOutput.sourceType = closureType then
                if priorType : priorOutput.sourceType = closureType then
                  if factoryType : factoryOutput.sourceType = makerType then
                    if builtinType : builtinOutput.sourceType = convertType then
                      return ⟨call, newOutput, priorOutput, factoryOutput, builtinOutput, returned,
                        priorSame, factorySame, builtinSame, distinct, newType, priorType, factoryType, builtinType⟩
                    else throw (IO.userError "constructor builtin raw signature")
                  else throw (IO.userError "constructor factory raw signature")
                else throw (IO.userError "constructor prior raw signature")
              else throw (IO.userError "constructor new raw signature")
            else throw (IO.userError "constructor lost distinct captures")
          else throw (IO.userError "constructor changed builtin handle")
        else throw (IO.userError "constructor changed factory handle")
      else throw (IO.userError "constructor changed prior handle")
    else throw (IO.userError "constructor changed payload metadata or order")
  | _ => throw (IO.userError "constructor output expected four handles")

structure ObservedSequence (fixture : CompiledFixture) (observed : ObservedProgram fixture) where
  first : ObservedPublicRun fixture observed.makeRow
  factory : ObservedNamed first.completion.session observed.makeRow.row.key
  builtin : ObservedBuiltin factory.completion.session
  named : ObservedNamed builtin.completion.session observed.readRow.row.key
  construction : ObservedConstruction named.completion.session named.handle factory.handle first.handle builtin.handle
    observed.readShape.instantiation
  newRead : ObservedInvocation construction.completion.session construction.newOutput .unit
  newValue : newRead.completion.value = .word secondSeed
  intervening : ObservedInvocation newRead.completion.session construction.factoryOutput (.word interveningSeed)
  interveningHandle : SourceCorePublicValues.Handle
  interveningReturned : intervening.completion.value = .function interveningHandle
  priorRead : ObservedInvocation intervening.completion.session construction.priorOutput .unit
  priorValue : priorRead.completion.value = .word seed
  builtinRead : ObservedInvocation priorRead.completion.session construction.builtinOutput (.integer 37)
  builtinValue : builtinRead.completion.value = .word (Core.Word.ofNatModulo 37)

def observeSequence (fixture : CompiledFixture) (observed : ObservedProgram fixture) :
    IO (ObservedSequence fixture observed) := do
  let first ← observePublicRun fixture observed.makeRow
  let factory ← observeNamed first.completion.session observed.makeRow.row.key
  let builtin ← observeBuiltin factory.completion.session
  let named ← observeNamed builtin.completion.session observed.readRow.row.key
  let construction ← observeConstruction named.completion.session named.handle factory.handle first.handle builtin.handle
    observed.readShape.instantiation
  let newRead ← observeInvocation construction.completion.session construction.newOutput .unit
  if newValue : newRead.completion.value = .word secondSeed then
    let intervening ← observeInvocation newRead.completion.session construction.factoryOutput (.word interveningSeed)
    match interveningReturned : intervening.completion.value with
    | .function interveningHandle =>
      let priorRead ← observeInvocation intervening.completion.session construction.priorOutput .unit
      if priorValue : priorRead.completion.value = .word seed then
        let builtinRead ← observeInvocation priorRead.completion.session construction.builtinOutput (.integer 37)
        if builtinValue : builtinRead.completion.value = .word (Core.Word.ofNatModulo 37) then
          pure ⟨first, factory, builtin, named, construction, newRead, newValue, intervening, interveningHandle,
            interveningReturned, priorRead, priorValue, builtinRead, builtinValue⟩
        else throw (IO.userError "collected builtin did not return 37")
      else throw (IO.userError "collected prior capture did not return 10")
    | _ => throw (IO.userError "collected factory did not export a closure")
  else throw (IO.userError "indirect constructor child did not capture 20")

end Tests.SourceCoreConstructorCalls
