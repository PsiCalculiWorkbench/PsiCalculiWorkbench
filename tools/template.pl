#!/usr/bin/perl

use warnings;
use strict;
use Getopt::Std;


sub usage {
    print "Usage: $ENV{COMMANDEXEC} [-h] [-o <filename>] <instance name>\n";
}

my %opts;
getopts('o:h', \%opts);

if ($opts{h}) {
    usage;
    exit 0;
}

my $outfile;
if (exists $opts{o}) {
    if (defined $opts{o}) {
        $outfile = $opts{o};
    } else {
        print "output file not specified!\n";
        usage;
        exit 1;
    }
} else {
    $outfile = '-';
}

my $instance_name = $ARGV[0];
if (not defined $instance_name) {
    print "The instance name not given!\n";
    usage;
    exit 1;
}

my $tmpl = <<"END";
structure ${instance_name}InstanceRequisites =
struct
  type name      = unit
  type term      = unit
  type condition = unit
  type assertion = unit

  type atom = name

  fun chaneq  (a,b)       = Err.undefined ()
  fun compose (psi1,psi2) = Err.undefined ()
  val unit                = ()
  fun entails (psi, phi)  = Err.undefined ()

  (* Could use the structure StringName.swap_name (a,b) n *)
  fun swap_name (a,b) n = Err.undefined ()

  (* StringName.generateDistinct xvec *)
  fun new n xvec = Err.undefined ()

  fun supportT m   = Err.undefined ()
  fun supportC phi = Err.undefined ()
  fun supportA psi = Err.undefined ()

  fun swapT pi m   = Err.undefined ()
  fun swapC pi phi = Err.undefined ()
  fun swapA pi psi = Err.undefined ()

  fun eqT _ (a,b) = Err.undefined ()
  fun eqC _ (a,b) = Err.undefined ()
  fun eqA _ (a,b) = Err.undefined ()

  fun substT sigma m   = Err.undefined ()
  fun substC sigma psi = Err.undefined ()
  fun substA sigma phi = Err.undefined ()

  fun brTransmit (m,n) = Err.undefined ()
  fun brReceive (m,n) = Err.undefined ()

  (* Unsorted *)
  structure Sort = Unsorted

  fun isNameSort _ = true
  fun canRecv _ _  = true
  fun canSend _ _  = true
  fun canSubs _ _  = true
  fun nameSort _   = Unsorted.SORT
  fun sortT _      = Unsorted.SORT
  fun sortC _      = Unsorted.SORT
  fun sortA _      = Unsorted.SORT

  structure Term = Nominal(struct
    structure AtomSort = Sort
    structure DataSort = Sort
    type atom    = name
    type data    = term
    val atomSort = nameSort
    val dataSort = sortT
    val swap     = swapT
    val support  = supportT
    val eq       = eqT
    val new      = new
  end)

  structure Cond = Nominal(struct
    structure AtomSort = Sort
    structure DataSort = Sort
    type atom    = name
    type data    = condition
    val atomSort = nameSort
    val dataSort = sortC
    val swap     = swapC
    val support  = supportC
    val eq       = eqC
    val new      = new
  end)

  structure Assr = Nominal(struct
    structure AtomSort = Sort
    structure DataSort = Sort
    type atom    = name
    type data    = assertion
    val atomSort = nameSort
    val dataSort = sortA
    val swap     = swapA
    val support  = supportA
    val eq       = eqA
    val new      = new
  end)

end;


structure ${instance_name}PsiInstance = Psi(${instance_name}InstanceRequisites)


structure ${instance_name}SymbolicInstanceRequisites =
struct
  open ${instance_name}InstanceRequisites

  structure Constraint      = SymbolicOSConstraint(${instance_name}PsiInstance.Inst)
  structure BisimConstraint = SymBisimConstraint(${instance_name}PsiInstance)

  fun var n               = Err.undefined ()
  fun solve cs            = Err.undefined ()
  fun solveBisim cs       = Err.undefined ()
  fun nameOfConstrSort () = Err.undefined ()
end;


structure ${instance_name}SymbolicInstance : SYMBOLIC_PSI = struct
  structure Psi         = ${instance_name}PsiInstance
  structure Clause      = PsiClause(Psi)
  structure ClEnv       = PsiClauseEnvironment(Clause)
  structure PsiInstance = ${instance_name}PsiInstance.Inst
  structure Constraint  = ${instance_name}SymbolicInstanceRequisites.Constraint
  val var               = ${instance_name}SymbolicInstanceRequisites.var
  val nameOfConstrSort  = ${instance_name}SymbolicInstanceRequisites.nameOfConstrSort
end


structure ${instance_name}SymbolicConstraintSolver : SYMBOLIC_CONSTRAINT_SOLVER =
struct
  structure Inst       = ${instance_name}PsiInstance.Inst
  structure Constraint = ${instance_name}SymbolicInstanceRequisites.Constraint
  val solve            = ${instance_name}SymbolicInstanceRequisites.solve
end;

structure ${instance_name}SymbolicBisimConstraintSolver : SYMBOLIC_BISIM_CONSTRAINT_SOLVER =
struct
  structure Psi = ${instance_name}PsiInstance
  structure Constraint = ${instance_name}SymbolicInstanceRequisites.BisimConstraint
  val solve = ${instance_name}SymbolicInstanceRequisites.solveBisim
end;

structure ${instance_name}ParserPrinterRequisites =
struct
  open ${instance_name}InstanceRequisites

  structure Parser = Parser(StringStream)
  structure Lex    = PsiLexerParserComb(Parser)

  fun printN n   = Err.undefined ()
  fun printT m   = Err.undefined ()
  fun printC phi = Err.undefined ()
  fun printA psi = Err.undefined ()

  fun name () = Err.undefined ()
  fun term () = Err.undefined ()
  fun cond () = Err.undefined ()
  fun assr () = Err.undefined ()

  fun parseResult p s =
    case Parser.parse (p ()) (StringStream.make s) of
         Either.RIGHT [(r,s)] => Either.RIGHT r
       | Either.RIGHT _ => Err.undefined ()
       | Either.LEFT  _ => Either.LEFT "Error parsing"

  fun parseName s = parseResult name s
  fun parseTerm s = parseResult term s
  fun parseCond s = parseResult cond s
  fun parseAssr s = parseResult assr s

end;

structure ${instance_name}ParserRequisites : PSI_PARSER_REQ =
struct
  structure Psi = ${instance_name}PsiInstance
  open ${instance_name}ParserPrinterRequisites
  val var = SOME ${instance_name}SymbolicInstanceRequisites.var
end;

structure ${instance_name}PrinterRequisites : PSI_PP_REQ =
struct
  structure Inst = ${instance_name}PsiInstance.Inst
  open ${instance_name}ParserPrinterRequisites
  val var = SOME ${instance_name}SymbolicInstanceRequisites.var
end;

structure ${instance_name}Command = CommandParser(struct
  structure SI           = ${instance_name}SymbolicInstance
  structure SCS          = ${instance_name}SymbolicConstraintSolver
  structure SBCS         = ${instance_name}SymbolicBisimConstraintSolver
  structure PsiParserReq = ${instance_name}ParserRequisites
  structure PPInst       = ${instance_name}PrinterRequisites
  val useBisim           = false (* true if bisimulation constraint solver is
                                    implemented *)
end);

structure ${instance_name} = ${instance_name}Command;
structure PsiInstance = ${instance_name};
END


my $out;
if ($outfile eq '-') {
    $out = \*STDOUT;
} else {
    open $out, '>', $outfile;
}

print $out $tmpl;


if (not $outfile eq '-') {
    close $out;
}

