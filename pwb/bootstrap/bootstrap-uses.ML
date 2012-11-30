
val pwbUsesRequiredFiles =
  [
  "pwb/missing.ML",
  "pwb/missing-io.ML",
  "pwb/pwb-logger.ML",
  (*"pwb/pwb-config.ML",*)
  "pwb/parser.ML",
  "pwb/contrib/md5-sig.ML",
  "pwb/contrib/md5.ML",
  "pwb/bootstrap/uses.ML"
  ];


val pwbUsesRequiredFiles = pwbPlatformiseFiles pwbUsesRequiredFiles;
val () = List.app use pwbUsesRequiredFiles;


Uses.prependToPath pwbHome;

(* Mark the required files as already loaded in order to prevent
 * the same files being loaded via Uses.uses, thus shadowing previous
 * definitions *)
val () = List.app Uses.markAsLoadedFile pwbUsesRequiredFiles;

val uses = Uses.uses;

PwbLog.pushLoggerStdErr "Pwb Uses";

