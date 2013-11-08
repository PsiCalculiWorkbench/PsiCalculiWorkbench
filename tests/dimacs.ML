(* uses pwb/missing,
        pwb/constraint-solvers/dimacs
 *)

(* The example of CNF format from DIMACS specification *)

structure Dimacs = DIMACSParser(StringParser);


val t1 = PwbTestRunner.testTrue "Example CNF DIMACS" 
(fn () => 
let
  val s = "c Example CNF format file\nc\np cnf 4 3\n1 3 -4 0\n4 0 2\n-3"
in
  case (StringParser.parseString (Dimacs.dimacs ())) s of
       Missing.LEFT x => false
     | Missing.RIGHT (res,_) =>
         res = (4, 3, [[1, 3, ~4], [4], [2, ~3]])
end
);

PwbTestRunner.registerTests [t1];

