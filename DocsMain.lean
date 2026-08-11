/-
Triptych documentation site — entry point (Verso manual/book genre).

Build:   lake build docs
Render:  lake exe docs --output _site
-/
import VersoManual
import Docs

open Verso.Genre.Manual

def main := manualMain (%doc Docs)
  (config := {
    sourceLink := some "https://github.com/cruisesong7/triptych",
    issueLink := some "https://github.com/cruisesong7/triptych/issues"
  })
