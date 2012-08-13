

fun pwbIsPolyML () = String.isSubstring "poly" (CommandLine.name ());

if pwbIsPolyML () then use "bootstrap-poly.ML"
else ();
