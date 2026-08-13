/-
Triptych documentation site — entry point (Verso manual/book genre).

From cedar-examples/:
Build:   lake build docs
Render:  lake exe docs --output ../_site
-/
import VersoManual
import Docs

open Verso.Genre.Manual

def demoSources : Lean.Json := Lean.Json.mkObj [
  ("Inputs/Decimal.lean", Lean.Json.str (include_str "cedar-examples/Inputs/Decimal.lean")),
  ("Inputs/Duration.lean", Lean.Json.str (include_str "cedar-examples/Inputs/Duration.lean")),
  ("Inputs/Datetime.lean", Lean.Json.str (include_str "cedar-examples/Inputs/Datetime.lean")),
  ("Inputs/IPv4.lean", Lean.Json.str (include_str "cedar-examples/Inputs/IPv4.lean")),
  ("Inputs/IPv6.lean", Lean.Json.str (include_str "cedar-examples/Inputs/IPv6.lean")),
  ("LeanWeb/Starter.lean", Lean.Json.str (include_str "cedar-examples/LeanWeb/Starter.lean"))
]

-- The docs executable embeds the Demo client and its editable grammar sources.
def demoJs : JsFile := {
  filename := "demo.js"
  contents := JS.mk s!"window.TRIPTYCH_DEMO_SOURCES = {Lean.Json.compress demoSources};\n\
    {include_str "Docs/demo.js"}"
  sourceMap? := none
  defer := true
}

def demoCss : CssFile := {
  filename := "demo.css"
  contents := CSS.mk (include_str "Docs/demo.css")
}

def main := manualMain (%doc Docs)
  (config := {
    extraFilesHtml := [
      ("../Docs/triptych-logo.svg", "triptych-logo.svg"),
      ("../Docs/triptych-mark.svg", "triptych-mark.svg")
    ],
    logo := some "triptych-mark.svg",
    sourceLink := some "https://github.com/cruisesong7/triptych",
    issueLink := some "https://github.com/cruisesong7/triptych/issues",
    extraJsFiles := {demoJs},
    extraCssFiles := {demoCss},
    extraJs := {
      JS.mk r#"
document.addEventListener("DOMContentLoaded", () => {
  const logo = document.querySelector('#logo img');
  if (logo) logo.alt = "Triptych";

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

.header-logo-wrapper {
  display: flex;
  align-items: center;
  height: 100%;
}

#logo {
  display: inline-flex;
  align-items: center;
}

#logo img {
  display: block;
  width: 11rem;
  height: 2.5rem;
}

main .titlepage:has(img[src$="triptych-logo.svg"]) > h1 {
  position: absolute;
  width: 1px;
  height: 1px;
  padding: 0;
  margin: -1px;
  overflow: hidden;
  clip: rect(0, 0, 0, 0);
  white-space: nowrap;
  border: 0;
}

main .titlepage p:has(> img[src$="triptych-logo.svg"]) {
  margin: 0.5rem 0 2rem;
}

main .titlepage img[src$="triptych-logo.svg"] {
  display: block;
  width: min(100%, 25rem);
  height: auto;
  margin: 0 auto;
}

@media screen and (max-width: 700px) {
  .header-logo-wrapper {
    display: none;
  }
}

table.tabular {
  width: 100%;
  margin: 1rem 0 1.5rem;
  table-layout: fixed;
  border-collapse: collapse;
  border: 1px solid #d0d7de;
  font-size: 0.95rem;
  line-height: 1.35;
}

table.tabular th,
table.tabular td {
  padding: 0.65rem 0.75rem;
  border-bottom: 1px solid #d0d7de;
  border-right: 1px solid #d8dee4;
}

table.tabular thead th {
  background: #eef2f6;
  color: #24292f;
  font-weight: 600;
}

table.tabular tr:nth-child(even) td {
  background: #f8fafc;
}

table.tabular th:first-child,
table.tabular td:first-child {
  width: 22%;
  font-weight: 600;
}

table.tabular th:last-child,
table.tabular td:last-child {
  width: 5.5rem;
  text-align: right;
  white-space: nowrap;
  border-right: 0;
  font-variant-numeric: tabular-nums;
}

body table.tabular.left-align {
  margin: 1rem 0 1.5rem;
}

@media (max-width: 700px) {
  table.tabular {
    display: block;
    width: calc(100vw - 2rem);
    max-width: 100%;
    font-size: 0.875rem;
  }

  table.tabular thead,
  table.tabular tbody {
    display: block;
    width: 100%;
  }

  table.tabular tr {
    display: grid;
    grid-template-columns: 5.5rem minmax(0, 1fr) 3.75rem;
    width: 100%;
  }

  table.tabular th,
  table.tabular td {
    box-sizing: border-box;
    width: auto !important;
    min-width: 0;
    padding: 0.5rem;
    overflow-wrap: anywhere;
  }
}
"#
    }
  })
