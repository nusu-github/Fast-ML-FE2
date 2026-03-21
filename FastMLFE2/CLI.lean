import FastMLFE2.Runtime.CliArgs
import FastMLFE2.Runtime.Solver

open System

namespace FastMLFE2.CLI

def runCli (args : List String) : IO PUnit := do
  let invocation ← Runtime.parseCliInvocation args
  Runtime.runCliInvocation invocation

def main (args : List String) : IO UInt32 := do
  try
    runCli args
    pure 0
  catch e =>
    IO.eprintln e.toString
    pure 1

end FastMLFE2.CLI
