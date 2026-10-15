import Solcore.Frontend.SourceCompiler

set_option autoImplicit false
namespace Tests.SourceCoreSelectedProjectedAssignment
open Solcore Frontend

def workspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := [], mainSources := [{path := "main.solc", content := String.intercalate "\n" [
    "function replace(table: mapping(Word => Word), key: Word, right: Word) returns (mapping(Word => Word)) { table[key] = right; return table; }",
    "function add(table: mapping(Word => Word), key: Word, right: Word) returns (mapping(Word => Word)) { table[key] += right; return table; }",
    "function divide(table: mapping(Word => Word), key: Word, right: Word) returns (mapping(Word => Word)) { table[key] /= right; return table; }",
    "function ordered(table: mapping(Word => Word)) returns (mapping(Word => Word)) { table[7] = 80; table[9] = 90; return table; }",
    "function nested(table: mapping(Word => mapping(Word => Word)), first: Word, second: Word, right: Word) returns (Word) { table[first][second] += right; return table[first][second]; }",
    "function key(value: Word) returns (Word) { let copy: Word = value; return copy; }",
    "function failedKey(value: Word) returns (Word) { let copy: Word = value; let absent: Word; return absent; }",
    "function effects(table: mapping(Word => Word), index: Word, right: Word) returns (mapping(Word => Word)) { table[key(index)] += key(right); return table; }",
    "function keyFailure(table: mapping(Word => Word), index: Word, right: Word) returns (mapping(Word => Word)) { table[failedKey(index)] += key(right); return table; }",
    "function rhsFailure(table: mapping(Word => Word), index: Word, right: Word) returns (mapping(Word => Word)) { table[key(index)] += failedKey(right); return table; }",
    "function missing(table: mapping(Word => Word), index: Word) returns (mapping(Word => Word)) { let absent: Word; table[index] += absent; return table; }",
    "function initialize(table: mapping(Word => Word), index: Word, right: Word) returns (mapping(Word => Word)) { for (table[index] = right; false; table[index] += 1) { } return table; }",
    "function post(table: mapping(Word => Word)) returns (mapping(Word => Word)) { for (let i: Word = 0; i < 1; table[i] += 2, i += 1) { continue; } return table; }",
    "function stop(table: mapping(Word => Word)) returns (mapping(Word => Word)) { for (let i: Word = 0; true; table[i] += 2) { break; } return table; }",
    "function make(table: mapping(Word => Word)) returns (function(Word) returns (Word)) { return lam(index: Word) -> Word { table[index] += 1; return table[index]; }; }"
  ]}] }

def options : SourceCompiler.Options :=
  {checkingFuel := 1000, compilationFuel := 1000, specializationBudget := 128}
def runOptions : SourceCoreExecution.RunOptions :=
  {executionFuel := 100000, outputValidationFuel := 1000}

end Tests.SourceCoreSelectedProjectedAssignment
