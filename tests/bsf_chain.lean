import LeanAV.PlanIR

open LeanAV.PlanIR

-- Runtime regression assertions on production pure functions.
-- These are tests, not a universal parser/codec-correctness theorem.
-- Run after lake build: lake env lean --run tests/bsf_chain.lean

private def gateVectors : List (String × Bool) :=
  [
    ("null", true),
    (" null \t", true),
    ("null,null", true),
    ("null,", true),
    ("'null'", true),
    ("n'ul'l", true),
    ("nu\\ll", true),
    ("'null", true),
    ("=null", true),
    ("===null=", true),
    ("null=", true),
    ("null=ignored", true),
    ("null=\\", true),
    ("", false),
    (" \t", false),
    ("''", false),
    (",null", false),
    ("null,,", false),
    ("null, ", false),
    ("null,\t", false),
    ("null\\", false),
    ("\"null\"", false),
    ("NULL", false),
    ("null =ignored", false),
    ("'null '", false),
    ("null\\ ", false),
    ("null\\,null", false),
    ("null\\\\,null", false),
    ("'null,null", false),
    ("setts=ts=if(eq(N\\,0)\\,PTS\\,DTS)", true),
    ("setts=ts='if(eq(N,0),PTS,DTS)'", true),
    ("setts=ts=if(eq(N\\\\,0)\\\\,PTS\\\\,DTS)", false),
    ("trim", true),
    ("jpegapp", true),
    ("apv_metadata", true),
    ("dv_error_marker", true),
    ("remove_extra", true),
    ("setts=duration=if(eq(NEXT_PTS\\,NOPTS)\\,PREV_OUTDURATION\\,(NEXT_PTS-PTS)/2):ts=PTS/2", true),
    ("setts=duration=if(eq(N\\,0)\\,18063360\\,DURATION):pts=PTS+if(gte(N\\,1)\\,16257024\\,0),trim=end=9031680", true),
    ("setts=duration=if(eq(N\\,0)\\,18063360\\,DURATION):pts=PTS+if(gte(N\\,1)\\,16257024\\,0),trim=start=9031680", true),
    ("setts=duration=if(eq(N\\,0)\\,10000\\,DURATION):pts=PTS+if(gte(N\\,1)\\,9040\\,0),trim=end=9188", true),
    ("setts=duration=if(eq(N\\,0)\\,10000\\,DURATION):pts=PTS+if(gte(N\\,1)\\,9040\\,0),trim=start=9188", true),
    ("setts=pts=PTS+if(gte(N\\,1)\\,10000\\,0),trim=start=1:start_type=pkt_index", true),
    ("setts=duration=if(eq(N\\,0)\\,11024\\,DURATION):pts=PTS+if(gte(N\\,1)\\,10000\\,0),trim=start=1:start_type=pkt_index", true),
    ("setts=pts=if(gte(N\\,1)\\,NOPTS\\,PTS),trim=start=1:start_type=pkt_index", true),
    ("setts=pts=if(eq(N\\,0)\\,NOPTS\\,PTS),trim=end=100:end_type=dur_ts", true),
    ("setts=pts=if(eq(N\\,0)\\,NOPTS\\,PTS),trim=start=120:start_rel=1:end=600", true)
  ]

private def tokenVectors : List (String × List String) :=
  [
    ("", [""]),
    ("null,", ["null"]),
    ("null,,", ["null", ""]),
    ("null, ", ["null", ""]),
    (" null \t", ["null"]),
    ("'null '", ["null "]),
    ("null  '' ,trim", ["null  ", "trim"]),
    ("'null ", ["null"]),
    ("null\\ ", ["null "]),
    ("setts=ts=if(eq(N\\,0)\\,PTS\\,DTS),trim=end=5", ["setts=ts=if(eq(N,0),PTS,DTS)", "trim=end=5"]),
    ("null\\\\,trim", ["null\\", "trim"]),
    ("null\\", ["null\\"]),
    ("'null\\,trim'", ["null\\,trim"])
  ]

private def nameVectors : List (String × Bool) :=
  [("===trim=start=5", true), ("===", false), ("trim =start=5", false), ("TRIM", false)]

def main : IO Unit := do
  for (value, expected) in gateVectors do
    unless supportedBsfChain value == expected do
      throw (IO.userError s!"BSF gate mismatch: {repr value}, expected {expected}")
  for (value, expected) in tokenVectors do
    unless splitBsfChain value == expected do
      throw (IO.userError s!"BSF token mismatch: {repr value}, expected {repr expected}")
  for (value, expected) in nameVectors do
    unless supportedBsf value == expected do
      throw (IO.userError s!"BSF name mismatch: {repr value}, expected {expected}")
  IO.println s!"BSF pure regressions passed: {gateVectors.length + tokenVectors.length + nameVectors.length}"
