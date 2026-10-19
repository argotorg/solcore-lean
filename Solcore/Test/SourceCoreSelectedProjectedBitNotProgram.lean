import Solcore.Frontend.SourceCompiler

set_option autoImplicit false
namespace Tests.SourceCoreSelectedProjectedBitNot
open Solcore Frontend

/-- One unchanged original program for two explicit compilation scopes. The
complete runtime companion configures every declaration as a seed. -/
def workspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := [], mainSources := [{path := "main.solc", content := String.intercalate "\n" [
    "function key(value: Word) returns (Word) { let copy: Word = value; return copy; }",
    "function failedKey(value: Word) returns (Word) { let copy: Word = value; let absent: Word; return absent; }",
    "function invert(table: mapping(Word => Word), index: Word) returns (mapping(Word => Word)) { table[index] ~=; return table; }",
    "function nested(table: mapping(Word => mapping(Word => Word)), first: Word, second: Word) returns (Word) { table[first][second] ~=; return table[first][second]; }",
    "function effects(table: mapping(Word => Word), index: Word) returns (mapping(Word => Word)) { table[key(index)] ~=; return table; }",
    "function keyFailure(table: mapping(Word => Word), index: Word) returns (mapping(Word => Word)) { let absent: Word; table[absent] ~=; return table; }",
    "function calledKeyFailure(table: mapping(Word => Word), index: Word) returns (mapping(Word => Word)) { table[failedKey(index)] ~=; return table; }",
    "function nestedFailure(table: mapping(Word => mapping(Word => Word)), first: Word, second: Word) returns (Word) { table[key(first)][failedKey(second)] ~=; return 0; }",
    "function initialize(table: mapping(Word => Word), index: Word) returns (mapping(Word => Word)) { for (table[index] ~=; false; table[index] ~=) { } return table; }",
    "function post(table: mapping(Word => Word)) returns (mapping(Word => Word)) { for (let i: Word = 0; i < 1; table[i] ~=, i += 1) { continue; } return table; }",
    "function stop(table: mapping(Word => Word)) returns (mapping(Word => Word)) { for (let i: Word = 0; true; table[i] ~=) { break; } return table; }",
    "function make(table: mapping(Word => Word)) returns (function(Word) returns (Word)) { return lam(index: Word) -> Word { table[index] ~=; return table[index]; }; }",
    "function defaultLocal() returns (Word) { let table: mapping(Word => Word); table[1] ~=; return table[1]; }"
  ]}] }

def options : SourceCompiler.Options :=
  {checkingFuel := 1000, compilationFuel := 1000, specializationBudget := 128}
def runOptions : SourceCoreExecution.RunOptions :=
  {executionFuel := 100000, outputValidationFuel := 1000}

end Tests.SourceCoreSelectedProjectedBitNot
