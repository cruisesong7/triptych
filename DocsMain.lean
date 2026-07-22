/-
FormatSpec documentation site — entry point.

Build:   lake build docs
Render:  lake exe docs --output _site
-/
import VersoBlog
import Docs

open Verso Genre Blog Site Syntax
open Output Html Template Theme in

def theme : Theme := { Theme.default with
  primaryTemplate := do
    let postList :=
      match (← param? "posts") with
      | none => Html.empty
      | some html => {{ <h2> "Posts" </h2> }} ++ html
    return {{
      <html>
        <head>
          <meta charset="utf-8"/>
          <meta name="viewport" content="width=device-width, initial-scale=1"/>
          <meta name="color-scheme" content="light dark"/>
          <link rel="stylesheet" href="https://cdn.jsdelivr.net/npm/sakura.css/css/sakura.css" type="text/css"/>
          <title>{{ (← param (α := String) "title") }} " — FormatSpec"</title>
          {{← builtinHeader }}
        </head>
        <body>
          <header>
            <div class="inner-wrap">
              <a class="logo" href="."><h1>"FormatSpec"</h1></a>
              {{ ← topNav }}
            </div>
          </header>
          <main>
            <div class="wrap">
              {{ (← param "content") }}
              {{ postList }}
            </div>
          </main>
        </body>
      </html>
    }}
  }

def formatSpecSite : Site := site Docs.Front /
  "blog" Docs.Blog with
    Docs.Blog.Intro

def main := blogMain theme formatSpecSite
