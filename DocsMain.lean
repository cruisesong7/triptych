/-
Triptych documentation site — entry point (Verso manual/book genre).

From cedar-examples/:
Build:   lake build docs
Render:  lake exe docs --output ../_site
-/
import VersoManual
import Docs

open Verso.Genre.Manual

def main := manualMain (%doc Docs)
  (config := {
    sourceLink := some "https://github.com/cruisesong7/triptych",
    issueLink := some "https://github.com/cruisesong7/triptych/issues",
    extraJs := {
      JS.mk r#"
document.addEventListener("DOMContentLoaded", () => {
  document
    .querySelectorAll('.hl.lean .keyword.token[data-binding^="kw-occ-Lean.Parser.Command.eval-"]')
    .forEach((token) => token.removeAttribute("data-verso-hover"));

  document.querySelectorAll(".hl.lean.block").forEach((block) => {
    if (block.querySelector(".keyword.token")?.textContent !== "triptych") return;

    block.classList.add("triptych-source");
    [...block.querySelectorAll(".has-info")].reverse().forEach((annotation) => {
      annotation.querySelectorAll(":scope > .hover-container").forEach((hover) => hover.remove());
      annotation.replaceWith(...annotation.childNodes);
    });
  });
});
"#
    },
    extraCss := {
      CSS.mk r#"
code.hl.lean.block.triptych-source .keyword.token {
  color: #005cc5;
}

code.hl.lean.block.triptych-source .const.token {
  color: #8250df;
}

.triptych-source .literal.string.token {
  color: #a31515;
}

.triptych-source .literal.number.token {
  color: #087f5b;
}

.triptych-source .punctuation.operator.token {
  color: #57606a;
}
"#
    }
  })
