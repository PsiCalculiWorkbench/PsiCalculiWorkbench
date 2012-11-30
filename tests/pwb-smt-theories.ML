(* uses pwb/missing,
        pwb/constraint-solvers/pwb-smt-theories,
        pwb/pwb-test
 *)

val tLEM = PwbTestRunner.testSome "Propostitional Law of Excluded Middle" (fn () =>
  PwbSATSolver.sat [[1, ~1]]
);

val tC = PwbTestRunner.testNone "Propostitional Contradiction" (fn () =>
  PwbSATSolver.sat [[1],[~1]]
);

val t1 = PwbTestRunner.testSome "Propostitional sat 1" (fn () =>
  PwbSATSolver.sat [[~1,~2], [2,3], [~1,~3,4], [2,~3,~4], [1,4]]
);

val t2 = PwbTestRunner.testSome "Propostitional sat 2" (fn () =>
  PwbSATSolver.sat [[1,2,3],[~1,4],[~4,1]]
);

val t3 = PwbTestRunner.testSome "Propostitional sat 3" (fn () =>
  PwbSATSolver.sat [[1,2],[~1,3],[~1,~3]]
);

val t4 = PwbTestRunner.testSome "Propostitional sat 4" (fn () =>
  PwbSATSolver.sat (map (fn x => [x,x]) (Lst.enum 1 10))
);

val t5 = PwbTestRunner.testSome "Propostitional sat 5 (edge case)" (fn () =>
  PwbSATSolver.sat ([~1,~2,~3,~4,~5,~6] :: (map (fn x => [x,x]) (Lst.enum 1 5)))
);


val t6 = PwbTestRunner.testSome "Theory of equality over vars 1" (fn () =>
  PwbEqSMTSolver.sat ( [
    [PwbEqTheory.Eq ("a", "b"), PwbEqTheory.Eq("c","c")],
    [PwbEqTheory.Eq ("b", "c")],
    [PwbEqTheory.InEq ("a", "c")]
    ])
);

local
  structure PwbEqSMTSolver2 = PwbSMTNoForget(PwbEqTheory);
in
val t7 = PwbTestRunner.testSome "Theory of equality over vars 1 (NoForget)" (fn () =>
  PwbEqSMTSolver2.sat ( [
    [PwbEqTheory.Eq ("a", "b"), PwbEqTheory.Eq("c","c")],
    [PwbEqTheory.Eq ("b", "c")],
    [PwbEqTheory.InEq ("a", "c")]
    ])
)
end;


PwbTestRunner.registerTests [tLEM, tC, t1, t2, t3, t4, t5, t6, t7];

