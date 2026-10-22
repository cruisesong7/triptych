/-
 Copyright Cedar Contributors

 Licensed under the Apache License, Version 2.0 (the "License");
 you may not use this file except in compliance with the License.
 You may obtain a copy of the License at

      https://www.apache.org/licenses/LICENSE-2.0

 Unless required by applicable law or agreed to in writing, software
 distributed under the License is distributed on an "AS IS" BASIS,
 WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 See the License for the specific language governing permissions and
 limitations under the License.
-/

import Triptych.Architecture.Syntax
import Triptych.Backend.Verus.Drift
import Triptych.Backend.Verus.VermilionRoundtrip

open System

namespace Triptych.Cli

private def usage : String :=
  "Triptych command-line tools\n\
  \n\
  Usage:\n\
  \x20 lake exe triptych -- check-verus [--syntax|--exact] <source.lean>...\n\
  \x20 lake exe triptych -- check-verus-roundtrip [options] <source.lean>...\n\
  \n\
  check-verus regenerates each `verus` clause in memory and compares spec.rs, parser.rs,\n\
  and contract.rs (when generated) with the checked-in snapshots. It never writes generated\n\
  files. The default --syntax mode ignores whitespace and comments outside literals; --exact\n\
  requires byte-for-byte equality.\n\
  \n\
  check-verus-roundtrip first requires exact snapshot equality, exports deterministic temporary\n\
  Lean obligations, runs the exact generated spec through Vermilion, and kernel-checks each\n\
  developer-maintained theorem. A missing <Format>.lean proof file is scaffolded with `sorry`. Options:\n\
  \x20 --vermilion-root DIR   Vermilion checkout (or set VERMILION_ROOT)\n\
  \x20 --proof-root DIR       directory containing <Format>.lean proof modules\n\
  \x20 --runner FILE          integration runner (default scripts/check-vermilion-roundtrip.sh)\n\
  \x20 --keep-artifacts       retain successful temporary artifacts\n"

private structure CheckOptions where
  mode : Verus.Drift.CompareMode := .syntax
  sources : List String := []

private def parseCheckOptions :
    List String → Verus.Drift.CompareMode → List String → Except String CheckOptions
  | [], mode, sources =>
      if sources.isEmpty then
        .error "check-verus requires at least one Triptych Lean source file"
      else
        .ok { mode, sources := sources.reverse }
  | "--syntax" :: rest, _, sources => parseCheckOptions rest .syntax sources
  | "--exact" :: rest, _, sources => parseCheckOptions rest .exact sources
  | argument :: rest, mode, sources =>
      if argument.startsWith "-" then
        .error s!"unknown check-verus option: {argument}"
      else
        parseCheckOptions rest mode (argument :: sources)

private def hasLakefile (directory : FilePath) : IO Bool := do
  return (← (directory / "lakefile.lean").pathExists) ||
    (← (directory / "lakefile.toml").pathExists)

private partial def findLakeProject (directory : FilePath) : IO (Option FilePath) := do
  if ← hasLakefile directory then
    return some directory
  match directory.parent with
  | some parent =>
      if parent == directory then
        return none
      findLakeProject parent
  | none => return none

private def emitProcessOutput (output : IO.Process.Output) : IO Unit := do
  unless output.stdout.isEmpty do
    IO.print output.stdout
  unless output.stderr.isEmpty do
    IO.eprint output.stderr

private def checkSource (mode : Verus.Drift.CompareMode) (sourceArgument : String) :
    IO Bool := do
  try
    let source ← IO.FS.realPath (FilePath.mk sourceArgument)
    let startDirectory ← match source.parent with
      | some parent => pure parent
      | none => IO.currentDir
    let some projectDirectory ← findLakeProject startDirectory
      | IO.eprintln s!"Triptych: no lakefile found above {source}"
        return false
    IO.println s!"Triptych: checking generated Verus snapshots from {source}"
    let output ← IO.Process.output {
      cmd := "lake"
      args := #["env", "lean", source.toString]
      cwd := some projectDirectory
      env := #[(Verus.Drift.checkEnvironmentVariable, some mode.description)]
    }
    emitProcessOutput output
    if output.exitCode == 0 then
      let processText := output.stdout ++ output.stderr
      if (processText.splitOn Verus.Drift.snapshotCurrentMessagePrefix).length > 1 then
        return true
      IO.eprintln s!"Triptych: {source} did not elaborate any `verus` clause"
      return false
    IO.eprintln s!"Triptych: Verus drift check failed for {source}"
    return false
  catch error =>
    IO.eprintln s!"Triptych: unable to check {sourceArgument}: {error}"
    return false

private def runCheck (options : CheckOptions) : IO UInt32 := do
  let mut succeeded := true
  for source in options.sources do
    unless ← checkSource options.mode source do
      succeeded := false
  if succeeded then
    IO.println s!"Triptych: all generated Verus snapshots match ({options.mode.description})"
    return 0
  return 1

private structure RoundtripOptions where
  vermilionRoot : Option String := none
  proofRoot : String := "verus-experiments/vermilion-roundtrip/proofs/TriptychVermilionProofs"
  runner : String := "scripts/check-vermilion-roundtrip.sh"
  keepArtifacts : Bool := false
  sources : List String := []

private def parseRoundtripOptions :
    List String → RoundtripOptions → Except String RoundtripOptions
  | [], options =>
      if options.sources.isEmpty then
        .error "check-verus-roundtrip requires at least one Triptych Lean source file"
      else
        .ok { options with sources := options.sources.reverse }
  | "--vermilion-root" :: argument :: rest, options =>
      parseRoundtripOptions rest { options with vermilionRoot := some argument }
  | "--proof-root" :: argument :: rest, options =>
      parseRoundtripOptions rest { options with proofRoot := argument }
  | "--runner" :: argument :: rest, options =>
      parseRoundtripOptions rest { options with runner := argument }
  | "--keep-artifacts" :: rest, options =>
      parseRoundtripOptions rest { options with keepArtifacts := true }
  | argument :: rest, options =>
      if argument == "--vermilion-root" || argument == "--proof-root" ||
          argument == "--runner" then
        .error s!"missing value for {argument}"
      else if argument.startsWith "-" then
        .error s!"unknown check-verus-roundtrip option: {argument}"
      else
        parseRoundtripOptions rest { options with sources := argument :: options.sources }

private def makeTemporaryDirectory : IO (Except String FilePath) := do
  let output ← IO.Process.output {
    cmd := "mktemp"
    args := #["-d", "/tmp/triptych-vermilion-roundtrip.XXXXXX"]
  }
  if output.exitCode != 0 then
    return .error ("unable to create temporary directory: " ++ output.stderr.trimAscii.toString)
  let path := output.stdout.trimAscii.toString
  if path.isEmpty then
    return .error "mktemp returned an empty path"
  return .ok (FilePath.mk path)

private def manifestValue (manifest key : String) : Option String :=
  manifest.splitOn "\n" |>.findSome? fun line =>
    let keyPrefix := key ++ "="
    if line.startsWith keyPrefix then some (line.drop keyPrefix.length).toString else none

private def runRoundtripArtifact (vermilionRoot proofRoot runner
    projectDirectory artifactDirectory : FilePath) : IO Bool := do
  let manifestPath := artifactDirectory / "manifest.txt"
  unless ← manifestPath.pathExists do
    IO.eprintln s!"Triptych: generated roundtrip manifest is missing: {manifestPath}"
    return false
  let manifest ← IO.FS.readFile manifestPath
  let some formatName := manifestValue manifest "format"
    | IO.eprintln s!"Triptych: generated manifest has no format: {manifestPath}"
      return false
  let proofFile := proofRoot / s!"{formatName}.lean"
  unless ← proofFile.pathExists do
    let scaffold := artifactDirectory / s!"{formatName}.proof-scaffold.lean"
    unless ← scaffold.pathExists do
      IO.eprintln s!"Triptych: generated Vermilion proof scaffold is missing: {scaffold}"
      return false
    IO.FS.writeFile proofFile (← IO.FS.readFile scaffold)
    IO.eprintln s!"Triptych: created Vermilion proof scaffold: {proofFile}"
    IO.eprintln "Triptych: replace each `sorry`, then rerun the roundtrip check"
    return false
  IO.println s!"Triptych: checking Vermilion semantic roundtrip for {formatName}"
  let output ← IO.Process.output {
    cmd := "bash"
    args := #[
      runner.toString,
      "--vermilion-root", vermilionRoot.toString,
      "--artifact-dir", artifactDirectory.toString,
      "--proof-file", proofFile.toString,
      "--source-project", projectDirectory.toString
    ]
  }
  emitProcessOutput output
  return output.exitCode == 0

private def checkRoundtripSource (options : RoundtripOptions)
    (vermilionRoot proofRoot runner : FilePath) (sourceArgument : String) : IO Bool := do
  let temporary ← match ← makeTemporaryDirectory with
    | .ok path => pure path
    | .error message =>
        IO.eprintln s!"Triptych: {message}"
        return false
  let source ← try
      IO.FS.realPath (FilePath.mk sourceArgument)
    catch error =>
      IO.eprintln s!"Triptych: unable to resolve {sourceArgument}: {error}"
      return false
  let startDirectory ← match source.parent with
    | some parent => pure parent
    | none => IO.currentDir
  let some projectDirectory ← findLakeProject startDirectory
    | IO.eprintln s!"Triptych: no lakefile found above {source}"
      return false
  let exportRoot := temporary / "export"
  IO.FS.createDirAll exportRoot
  IO.println s!"Triptych: exporting deterministic Vermilion obligations from {source}"
  let output ← IO.Process.output {
    cmd := "lake"
    args := #["env", "lean", source.toString]
    cwd := some projectDirectory
    env := #[
      (Verus.Drift.checkEnvironmentVariable, some "exact"),
      (Backend.Verus.VermilionRoundtrip.exportEnvironmentVariable,
        some exportRoot.toString)
    ]
  }
  emitProcessOutput output
  if output.exitCode != 0 then
    IO.eprintln s!"Triptych: failed to export Vermilion obligations; artifacts retained at \
      {temporary}"
    return false
  let artifacts ← exportRoot.readDir
  if artifacts.isEmpty then
    IO.eprintln s!"Triptych: {source} did not elaborate any `verus` clause"
    return false
  let mut succeeded := true
  for artifact in artifacts do
    if ← artifact.path.isDir then
      unless ← runRoundtripArtifact vermilionRoot proofRoot runner projectDirectory
          artifact.path do
        succeeded := false
  if succeeded && !options.keepArtifacts then
    try
      IO.FS.removeDirAll temporary
    catch error =>
      IO.eprintln s!"Triptych: warning: unable to remove temporary artifacts {temporary}: {error}"
  else
    IO.println s!"Triptych: Vermilion roundtrip artifacts retained at {temporary}"
  return succeeded

private def runRoundtrip (options : RoundtripOptions) : IO UInt32 := do
  let vermilionRootString ← match options.vermilionRoot with
    | some root => pure root
    | none =>
        match ← IO.getEnv "VERMILION_ROOT" with
        | some root => pure root
        | none =>
            IO.eprintln "Triptych: provide --vermilion-root or set VERMILION_ROOT"
            return 2
  let vermilionRoot ← IO.FS.realPath (FilePath.mk vermilionRootString)
  let proofRoot ← IO.FS.realPath (FilePath.mk options.proofRoot)
  let runner ← IO.FS.realPath (FilePath.mk options.runner)
  let mut succeeded := true
  for source in options.sources do
    unless ← checkRoundtripSource options vermilionRoot proofRoot runner source do
      succeeded := false
  if succeeded then
    IO.println "Triptych: all Vermilion semantic roundtrips verified"
    return 0
  return 1

def run (arguments : List String) : IO UInt32 := do
  let arguments := match arguments with
    | "--" :: rest => rest
    | _ => arguments
  match arguments with
  | [] | ["--help"] | ["-h"] =>
      IO.println usage
      return 0
  | "check-verus" :: rest =>
      match parseCheckOptions rest .syntax [] with
      | .ok options => runCheck options
      | .error message =>
          IO.eprintln s!"Triptych: {message}\n\n{usage}"
          return 2
  | "check-verus-roundtrip" :: rest =>
      match parseRoundtripOptions rest {} with
      | .ok options => runRoundtrip options
      | .error message =>
          IO.eprintln s!"Triptych: {message}\n\n{usage}"
          return 2
  | command :: _ =>
      IO.eprintln s!"Triptych: unknown command: {command}\n\n{usage}"
      return 2

end Triptych.Cli

def main (arguments : List String) : IO UInt32 :=
  Triptych.Cli.run arguments
