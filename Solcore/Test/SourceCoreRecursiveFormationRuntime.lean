import Solcore.Test.SourceCoreRecursiveFormationFixture

/-! Actual public calls reuse distinct closure exports through the returned
sessions. Every step retains its original startup and run receipts. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreRecursiveFormation
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

structure ObservedPairCall {artifact : SourceCoreExecution.Artifact}
    (session : SourceCoreExecution.Session artifact) (key : SourceCoreIndexedSession.Key)
    (arguments : List SourceCorePublicValues.Value) extends ObservedCall session key arguments where
  left : SourceCorePublicValues.Handle
  right : SourceCorePublicValues.Handle
  returned : completion.value = .product (.function left) (.function right)
  leftType : left.sourceType = closureType
  rightType : right.sourceType = closureType

def observePairCall {artifact : SourceCoreExecution.Artifact}
    (session : SourceCoreExecution.Session artifact) (key : SourceCoreIndexedSession.Key)
    (arguments : List SourceCorePublicValues.Value) : IO (ObservedPairCall session key arguments) := do
  let call ← observeCall session key arguments
  match returned : call.completion.value with
  | .product (.function left) (.function right) =>
    if leftType : left.sourceType = closureType then
      if rightType : right.sourceType = closureType then return ⟨call, left, right, returned, leftType, rightType⟩
      else throw (IO.userError "second exported closure raw type")
    else throw (IO.userError "first exported closure raw type")
  | _ => throw (IO.userError "expected two function exports")

structure ObservedInvocation {artifact : SourceCoreExecution.Artifact}
    (session : SourceCoreExecution.Session artifact) (handle : SourceCorePublicValues.Handle)
    (argument : SourceCorePublicValues.Value) where
  completion : SourceCoreExecution.Completion artifact
  executed : session.InvokeAt handle argument runOptions (.ok (.succeeded completion))

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
  firstLeftType : first.left.sourceType = closureType
  firstRightType : first.right.sourceType = closureType
  firstRead : ObservedInvocation first.completion.session first.left .unit
  firstValue : firstRead.completion.value = .word seed
  second : ObservedPairCall firstRead.completion.session observed.makeRow.row.key [.word secondSeed]
  firstDistinct : first.left ≠ first.right
  secondDistinct : second.left ≠ second.right
  distinct : first.left ≠ second.left
  secondRead : ObservedInvocation second.completion.session first.right .unit
  secondValue : secondRead.completion.value = .word seed
  thirdRead : ObservedInvocation secondRead.completion.session second.left .unit
  thirdValue : thirdRead.completion.value = .word secondSeed
  repeatedRead : ObservedInvocation thirdRead.completion.session first.left .unit
  repeatedValue : repeatedRead.completion.value = .word seed

def observeSequence (fixture : CompiledFixture) (observed : ObservedProgram fixture) :
    IO (ObservedSequence fixture observed) := do
  let first ← observePublicRun fixture observed.makeRow
  let ⟨firstLeftType⟩ ← if actual : first.left.sourceType = closureType then
    pure (PLift.up actual) else throw (IO.userError "first left closure type")
  let ⟨firstRightType⟩ ← if actual : first.right.sourceType = closureType then
    pure (PLift.up actual) else throw (IO.userError "first right closure type")
  let firstRead ← observeInvocation first.completion.session first.left .unit
  if firstValue : firstRead.completion.value = .word seed then
    let second ← observePairCall firstRead.completion.session observed.makeRow.row.key [.word secondSeed]
    if firstDistinct : first.left ≠ first.right then
      if secondDistinct : second.left ≠ second.right then
        if distinct : first.left ≠ second.left then
          let secondRead ← observeInvocation second.completion.session first.right .unit
          if secondValue : secondRead.completion.value = .word seed then
            let thirdRead ← observeInvocation secondRead.completion.session second.left .unit
            if thirdValue : thirdRead.completion.value = .word secondSeed then
              let repeatedRead ← observeInvocation thirdRead.completion.session first.left .unit
              if repeatedValue : repeatedRead.completion.value = .word seed then
                return {first, firstLeftType, firstRightType, firstRead, firstValue, second, firstDistinct, secondDistinct, distinct, secondRead, secondValue, thirdRead, thirdValue, repeatedRead, repeatedValue}
              else throw (IO.userError "first captured cell changed")
            else throw (IO.userError "second factory capture changed")
          else throw (IO.userError "second output of first factory capture changed")
        else throw (IO.userError "factory calls reused one handle")
      else throw (IO.userError "second factory returned equal handles")
    else throw (IO.userError "first factory returned equal handles")
  else throw (IO.userError "first factory capture changed")

end Tests.SourceCoreRecursiveFormation
