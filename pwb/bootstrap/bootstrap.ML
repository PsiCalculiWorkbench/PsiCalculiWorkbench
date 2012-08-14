
structure PwbSml =
struct
end;

val pwbHomeEnv = OS.Process.getEnv "PSI_WORKBENCH_HOME";

case pwbHomeEnv of
     NONE => raise (Fail "The environment variable PSI_WORKBENCH_HOME is not set!")
   | SOME _ => ();

val SOME pwbHome = pwbHomeEnv;


fun pwbPlatformiseFiles files =
let
  val {arcs,isAbs,vol} = OS.Path.fromString pwbHome
  val fls = map (String.fields (fn c => c = #"/")) files
in
  map (fn farcs =>
    OS.Path.toString {arcs=arcs@farcs, isAbs=isAbs, vol=vol}) fls
end;


fun pwbPlatformisedUse str =
  use (List.hd (pwbPlatformiseFiles [str]));


fun pwbIsPolyML () = String.isSubstring "poly" (CommandLine.name ());

if pwbIsPolyML () 
    then pwbPlatformisedUse "pwb/bootstrap/bootstrap-poly.ML"
    else ();


PwbSml.supressOutput ();

pwbPlatformisedUse "pwb/bootstrap/bootstrap-uses.ML";

