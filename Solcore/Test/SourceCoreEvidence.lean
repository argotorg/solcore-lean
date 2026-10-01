import Solcore.Test.SourceCompilerFeatureSupport

/-! Closed evidence and retained coercions run through ordinary cached Core
functions. The checker keeps its existing admission rules. -/
set_option autoImplicit false

namespace Tests.SourceCoreEvidence
open Solcore Solcore.Frontend SourceCoreExecution

private def assertTrue (condition : Bool) (message : String) : IO Unit := do
  unless condition do throw (IO.userError message)
private def w (value : Nat) : Core.Word := Core.Word.ofNatModulo value

private def workspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := [],
  mainSources := [{path := "main.solc", content := String.intercalate "\n" [
    "trait Marker<T> {}", "impl Marker<Word> {}",
    "function keep<T>(value: T) returns (T) where T: Marker { return value; }",
    "function relay<T>(value: T) returns (T) where T: Marker { return keep(value); }",
    "function constrained(value: Word) returns (Word) where Word: Marker { let table: mapping(Word => Word); table[0] = relay(value); return table[0]; }",
    "trait Coerce<From, To> { function coerce(value: From) returns (To); }",
    "impl Coerce<Bool, Word> { function coerce(value: Bool) returns (Word) { let table: mapping(Word => Word); table[0] = value ? 40 : 6; table[0] += 2; return table[0]; } }",
    "function converted(flag: Bool) returns (Word) { let table: mapping(Word => Word); table[0] = flag; return table[0]; }",
    "function indirect(flag: Bool) returns (Word) { let f: function(Word) returns (Word) = lam(value: Word) -> Word { return value + 5; }; return f(flag); }",
    "function identity(value: Word) returns (Word) { return value; }",
    "type WordFunction = function(Word) returns (Word);",
    "impl Coerce<Word, WordFunction> { function coerce(value: Word) returns (WordFunction) { return identity; } }",
    "function convertedFunction(value: Word) returns (WordFunction) { return value; }",
    "function useFunction(f: WordFunction, value: Word) returns (Word) { return f(value); }",
    "enum Token { A, B, C }",
    "trait Add<T> { function add(left: T, right: T) returns (T) where T: Marker; }",
    "trait BitNot<T> { function bnot(value: T) returns (T) where T: Marker; }",
    "impl Marker<Token> {}",
    "impl Add<Token> { function add(left: Token, right: Token) returns (Token) where Token: Marker { match (left) { case .A { return right; } case .B { return .C; } default { return .A; } } } }",
    "impl BitNot<Token> { function bnot(value: Token) returns (Token) where Token: Marker { match (value) { case .A { return .B; } case .B { return .C; } default { return .A; } } } }",
    "function operatorResult() returns (Token) { return ~(Token.A + Token.B); }",
    "function operatorEffects() returns (Word) { let count: Word = 0; let left = lam() -> Token { count = count * 10 + 1; return .A; }; let right = lam() -> Token { count = count * 10 + 2; return .B; }; let token: Token = left() + right(); return count; }"
  ]}]
}

private def compile (program : CheckedProgram) (name : String) : IO SourceCompilerFeatureSupport.Entry :=
  SourceCompilerFeatureSupport.compileNamed program name []
    {specializationBudget := 256, compilationFuel := 1000}

private def testWord (program : CheckedProgram) (name : String) (arguments : List Value)
    (expected : Nat) : IO Unit := do
  let compiled ← compile program name
  for _ in [0, 1] do
    assertTrue ((← compiled.run arguments) == .word (w expected)) s!"{name} Core evidence result changed"
  compiled.checkResume arguments (.word (w expected)) 0

def run : IO Unit := do
  let program ← match checkProgram workspace 4096 with
    | .ok program => pure program
    | .error error => throw (IO.userError s!"evidence source rejected: {reprStr error}")
  testWord program "constrained" [.word (w 7)] 7
  for (flag, expected) in [(true, 42), (false, 8)] do
    testWord program "converted" [.bool flag] expected
    testWord program "indirect" [.bool flag] (expected + 5)
  testWord program "operatorEffects" [] 12
  let token ← match program.signatures.dataTypes.filter (·.name == "Token") with
    | [token] => pure token
    | _ => throw (IO.userError "Token missing")
  let tokenType := TypeSystem.Ty.nominal token.id []
  let expected : Value := .constructed ⟨⟨token.id, 2⟩, [], [], tokenType⟩ []
  let compiled ← compile program "operatorResult"
  assertTrue ((← compiled.run []) == expected) "evidence-selected nominal operators changed"
  compiled.checkResume [] expected 0
  let seeds ← ["convertedFunction", "useFunction"].mapM fun name => do
    match program.signatures.functions.filter (·.name == name) with
    | [signature] => pure (SourceCoreCompiler.Seed.declaration signature.id)
    | _ => throw (IO.userError "function coercion root missing")
  let shared ← match SourceCoreExecution.compileChecked program seeds {compilationFuel := 256, specializationBudget := 256} with
    | .ok shared => pure shared
    | .error error => throw (IO.userError s!"function coercion session failed: {reprStr error}")
  let artifact ← shared.open
  let session ← SourceCompilerFeatureSupport.boot artifact
  let producer ← match shared.keys[0]? with | some key => pure key | none => throw (IO.userError "producer missing")
  let consumer ← match shared.keys[1]? with | some key => pure key | none => throw (IO.userError "consumer missing")
  let made ← session.run producer [.word (w 1)] {executionFuel := 300000}
  match made with
  | .ok (.succeeded completion) =>
      match ← completion.session.run consumer [completion.value, .word (w 9)] {executionFuel := 300000} with
      | .ok (.succeeded applied) => match applied.value with
          | .word actual => assertTrue (actual == w 9) "coerced function lost original global"
          | _ => throw (IO.userError "coerced function returned the wrong value")
      | _ => throw (IO.userError "coerced function invocation failed")
  | _ => throw (IO.userError "function coercion did not complete")
  IO.println "source Core closed evidence and coercions GREEN"

end Tests.SourceCoreEvidence
