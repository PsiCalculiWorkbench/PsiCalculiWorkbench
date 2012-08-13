
(*PolyML.print_depth 0;*)


val pwbHomeEnv = OS.Process.getEnv "PSI_WORKBENCH_HOME";

case pwbHomeEnv of
     NONE => raise (Fail "The environment variable PSI_WORKBENCH_HOME is not set!")
   | SOME _ => ();

val SOME pwbHome = pwbHomeEnv;

val pwbUsesRequiredFiles =
  map (String.fields (fn c => c = #"/"))
  [
  "pwb/missing.ML",
  "pwb/missing-io.ML",
  "pwb/pwb-logging.ML",
  "pwb/parser.ML",
  "pwb/contrib/md5-sig.ML",
  "pwb/contrib/md5.ML",
  "pwb/bootstrap/uses.ML"
  ];


fun pwbPlatformiseFiles files =
let
  val {arcs,isAbs,vol} = OS.Path.fromString pwbHome
in
  map (fn farcs =>
    OS.Path.toString {arcs=arcs@farcs, isAbs=isAbs, vol=vol}) files
end;


val pwbUsesRequiredFiles = pwbPlatformiseFiles pwbUsesRequiredFiles;
val () = List.app use pwbUsesRequiredFiles;


Uses.prependToPath pwbHome;

(* Mark the required files as already loaded in order to prevent
 * the same files being loaded via Uses.uses, thus shadowing previous
 * definitions *)
val () = List.app Uses.markAsLoadedFile pwbUsesRequiredFiles;

val uses = Uses.uses;


(*PolyML.print_depth 100;*)

