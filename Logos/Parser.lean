module

/-
The shared proof parser. `Core` implements the grammar; `Datatypes` handles
parser-local datatype templates and provides the `parseProof` entry point.
-/

public import Logos.Parser.Datatypes
import all Logos.Parser.Datatypes
