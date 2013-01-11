#!/usr/bin/perl

use File::Find;
use File::Basename;
use Getopt::Long;
use Sys::Hostname;
use File::NCopy;
use File::Path 'rmtree';
use Cwd;
use lib '/usr/local/share/perl/5.10.0';
use Spreadsheet::ParseExcel;
use Spreadsheet::ParseExcel::SaveParser;

GetOptions( 
	"stop"  => \$stop,
	"help" => \$help,
	"root=s" => \$root,
	"tp=s" => \$prover,
	"flags=s" => \$flags,
	"copy-to-home21" => \$home21,
	"log-string=s" => \$str_log,
	"bags" => \$bags,
	"term" => \$term,
  "lists" => \$lists
);

@param_list = @ARGV;
if(($help) || (@param_list == ""))
{
	print "./run-fast-tests.pl [-help] [-root path_to_sleek] [-tp name_of_prover] [-log-string string_to_be_added_to_the_log] [-copy-to-home21] hip_tr|hip|imm|sleek|hip_vperm|sleek_vperm [-flags \"arguments to be transmited to hip/sleek \"]\n";
	exit(0);
}

if($root) {
	$exempl_path = "$root/examples";
	$exec_path = "$root";
}
else {
	$exempl_path = ".";
	$exec_path = '../../..';
}

if($prover) {
	%provers = ('cvcl' => 'cvcl', 'cvc3' => 'cvc3', 'oc' => 'oc','oc-2.1.6' => 'oc-2.1.6', 
		'co' => 'co', 'isabelle' => 'isabelle', 'coq' => 'coq', 'mona' => 'mona', 'om' => 'om', 
		'oi' => 'oi', 'set' => 'set', 'cm' => 'cm', 'redlog' => 'redlog', 'rm' => 'rm', 'prm' => 'prm', 
		'z3' => 'z3', 'z3-2.19' => 'z3-2.19', 'zm' => 'zm', 'log' => 'log');
	if (!exists($provers{$prover})) {
		print "./run-fast-tests.pl [-help] [-root path_to_sleek] [-tp name_of_prover] [-log-timings]  [-log-string string_to_be_added_to_the_log] [-copy-to-home21] hip_tr|hip|sleek|hip_vperm|sleek_vperm [-flags \"arguments to be transmited to hip/sleek \"]\n";
		print "\twhere name_of_prover should be one of the followings: 'cvcl', 'cvc3', 'omega', 'co', 'isabelle', 'coq', 'mona', 'om', 'oi', 'set', 'cm', 'redlog', 'rm', 'prm', 'z3' or 'zm'\n";
		exit(0);
	}
}
else {
	if("$flags" =~ m/-tp (\w+)\b/ ) {
		$prover = "$1";
  }
  else {
		$prover = "oc";
  }
}

if("$flags"){
	$script_arguments = "$flags";
	if (!($script_arguments =~ "-tp ")){
		$script_arguments = $script_arguments." -tp ".$prover;
	}
}
else{
	$script_arguments = " -tp ".$prover;
}

@excl_files = ();
$error_count = 0;
$error_files = "";
$hip = "$exec_path/hip ";
# please use make native
$sleek = "$exec_path/sleek ";
$output_file = "log";
# list of file, nr of functions, function name, output, function name, output......
# files are searched in the subdirectory with the same name as the list name, in examples/working/hip directory (ex. hip/array for "array" list)
%hip_files=(
	"Aprove" => [
		#(23)
		["Aprove_09/DivMinus2.ss", 3, "", "main", "SUCCESS", "div", "SUCCESS", "minus", "SUCCESS"],
		["Aprove_09/DivMinus.ss", 2, "", "main", "SUCCESS", "div", "SUCCESS"],
		["Aprove_09/DivWithoutMinus.ss", 1, "", "main", "SUCCESS"],
		["Aprove_09/Duplicate.ss", 2, "", "main", "SUCCESS", "round", "SUCCESS"],
		["Aprove_09/GCD2.ss", 2, "-tp redlog", "main", "SUCCESS", "gcd", "SUCCESS"],
		["Aprove_09/GCD3.ss", 3, "", "main", "SUCCESS", "gcd", "SUCCESS", "mod", "SUCCESS"],
		["Aprove_09/GCD4.ss", 3, "", "main", "SUCCESS", "gcd", "SUCCESS", "mod", "SUCCESS"],
		["Aprove_09/GCD5.ss", 2, "-tp redlog", "main", "SUCCESS", "gcd", "SUCCESS"],
		["Aprove_09/GCD.ss", 2, "-tp redlog", "main", "SUCCESS", "gcd", "SUCCESS"],
		["Aprove_09/LogAG.ss", 3, "", "main", "SUCCESS", "half", "SUCCESS", "log", "SUCCESS"],
		["Aprove_09/LogBuiltIn.ss", 2, "", "main", "SUCCESS", "log", "SUCCESS"],
		["Aprove_09/LogIterative.ss", 2, "-tp redlog", "main", "SUCCESS", "log", "SUCCESS"],
		["Aprove_09/LogMult.ss", 2, "-tp redlog", "main", "SUCCESS", "log", "SUCCESS"],
		["Aprove_09/Log.ss", 3, "", "main", "SUCCESS", "half", "SUCCESS", "log", "SUCCESS"],
		["Aprove_09/McCarthyIterative-may.ss", 1, "", "mcCarthy", "SUCCESS"],
		["Aprove_09/McCarthyIterative.ss", 1, "", "mcCarthy", "SUCCESS"],
		["Aprove_09/McCarthyRec.ss", 1, "", "mcCarthy", "SUCCESS"],
		["Aprove_09/MinusBuiltIn.ss", 1, "", "main", "SUCCESS"],
		["Aprove_09/MinusMin.ss", 2, "", "main", "SUCCESS", "mn", "SUCCESS"],
		["Aprove_09/MinusUserDefined.ss", 2, "", "main", "SUCCESS", "gt", "SUCCESS"],
		["Aprove_09/Mod.ss", 3, "", "main", "SUCCESS", "mod", "SUCCESS", "minus", "SUCCESS"],
		["Aprove_09/PlusSwap.ss", 2, "", "main", "SUCCESS", "loop", "SUCCESS"],
		["Aprove_09/Round3.ss", 1, "", "main", "SUCCESS"],
		#(1)
		["AProVE_10/AG313.ss", 2, "", "main", "SUCCESS", "quot", "SUCCESS"],
		#(2)
		["AProVE_11_iterative/RetValRec.ss", 3, "", "main", "SUCCESS", "ret", "SUCCESS", "test", "SUCCESS"],
		["AProVE_11_iterative/RetVal.ss", 3, "", "main", "SUCCESS", "ret", "SUCCESS", "test", "SUCCESS"],
		#(2)
		["AProVE11NO/LoopingNonTerm.ss", 2, "", "main", "SUCCESS", "loop", "SUCCESS"],
		["AProVE11NO/NonPeriodicNonTerm2.ss", 2, "", "main", "SUCCESS", "loop", "SUCCESS"],
		#(13)
		["BOG_RTA_11/Avg.ss", 1, "", "avg", "SUCCESS"],
		["BOG_RTA_11/EqUserDefRec.ss", 2, "", "main", "SUCCESS", "eq", "SUCCESS"],
		["BOG_RTA_11/Fibonacci.ss", 2, "", "main", "SUCCESS", "fib", "SUCCESS"],
		["BOG_RTA_11/LeUserDefRec.ss", 2, "", "main", "SUCCESS", "le", "SUCCESS"],
		["BOG_RTA_11/LogRecursive.ss", 2, "-tp redlog", "main", "SUCCESS", "log", "SUCCESS"],
		["BOG_RTA_11/Nest.ss", 2, "", "main", "SUCCESS", "nest", "SUCCESS"],
		["BOG_RTA_11/TerminatiorRec01.ss", 3, "", "main", "SUCCESS", "f", "SUCCESS", "loop", "SUCCESS"],
		["BOG_RTA_11/TerminatiorRec02.ss", 1, "-tp redlog", "fact", "SUCCESS"],
		["BOG_RTA_11/TerminatiorRec03.ss", 1, "", "f", "SUCCESS"],
		["BOG_RTA_11/TerminatiorRec04-modified.ss", 3, "", "main", "SUCCESS", "f", "SUCCESS", "loop", "SUCCESS"],
		["BOG_RTA_11/TerminatiorRec04.ss", 3, "", "main", "SUCCESS", "f", "SUCCESS", "loop", "SUCCESS"],
		["BOG_RTA_11/TimesPlusUserDef.ss", 3, "", "main", "SUCCESS", "times", "SUCCESS", "plus", "SUCCESS"],
		["BOG_RTA_11/TwoWay.ss", 1, "-tp redlog", "twoWay", "SUCCESS"],
		#(34)
		["Costa_Julia_09/Break.ss", 1, "", "main", "SUCCESS"],
		["Costa_Julia_09/Continue1.ss", 1, "", "main", "SUCCESS"],
		["Costa_Julia_09/Continue.ss", 1, "", "main", "SUCCESS"],
		["Costa_Julia_09/costa09-example_1.ss", 6, "", "incr", "SUCCESS", "add", "SUCCESS", 
			"incr2", "SUCCESS", "add2", "SUCCESS", "incr3", "SUCCESS", "add3", "SUCCESS"],
		["Costa_Julia_09/costa09-example_2.ss", 2, "-tp redlog", "main", "SUCCESS", "divBy", "SUCCESS"],
		["Costa_Julia_09/costa09-example_3.ss", 2, "", "main", "SUCCESS", "m", "SUCCESS"],
		["Costa_Julia_09/Exc1-exc.ss", 2, "", "main", "SUCCESS", "rec_f", "SUCCESS"],
		["Costa_Julia_09/Exc1.ss", 1, "", "main", "SUCCESS"],
		["Costa_Julia_09/Exc2-exc.ss", 2, "", "main", "SUCCESS", "rec_f", "SUCCESS"],
		["Costa_Julia_09/Exc3-exc.ss", 2, "", "main", "SUCCESS", "rec_f", "SUCCESS"],
		["Costa_Julia_09/Exc4-exc.ss", 2, "", "main", "SUCCESS", "rec_f", "SUCCESS"],
		["Costa_Julia_09/Exc4.ss", 1, "", "main", "SUCCESS"],
		["Costa_Julia_09/Exc5-exc.ss", 2, "", "main", "SUCCESS", "rec_f", "SUCCESS"],
		["Costa_Julia_09/Exc-exc.ss", 2, "", "main", "SUCCESS", "rec_f", "SUCCESS"],
		["Costa_Julia_09/Exc1-no.ss", 1, "", "main", "SUCCESS"],
		["Costa_Julia_09/Exc2-no.ss", 1, "", "main", "SUCCESS"],
		["Costa_Julia_09/Exc3-no.ss", 1, "", "main", "SUCCESS"],
		["Costa_Julia_09/Exc4-no.ss", 2, "", "main", "SUCCESS", "loop", "SUCCESS"],
		["Costa_Julia_09/Exc5-no.ss", 1, "", "main", "SUCCESS"],
		["Costa_Julia_09/Exc-no.ss", 1, "", "main", "SUCCESS"],
		["Costa_Julia_09/Loop1.ss", 1, "", "main", "SUCCESS"],
		["Costa_Julia_09/Nested.ss", 1, "", "main", "SUCCESS"],
		["Costa_Julia_09/Sequence.ss", 1, "", "main", "SUCCESS"],
		["Costa_Julia_09/TestJulia4.ss", 1, "-tp redlog", "main", "SUCCESS"],
		["Costa_Julia_09/costa09-example_4.ss", 3, "", "getF", "SUCCESS", "setF", "SUCCESS", "exampleMethods", "SUCCESS"],
		["Costa_Julia_09/costa09-example_4-1.ss", 4, "", "getF", "SUCCESS", "setF", "SUCCESS", 
			"exampleMethods", "SUCCESS", "loop", "SUCCESS"],
		["Costa_Julia_09/costa09-example_5.ss", 1, "", "m", "SUCCESS"],
		["Costa_Julia_09/costa09-example_5-1.ss", 2, "", "m", "SUCCESS", "loop", "SUCCESS"],
		["Costa_Julia_09/julia-09-iterative-exc.ss", 2, "", "main", "SUCCESS", "rec_f", "SUCCESS"],
		["Costa_Julia_09/julia-09-iterative-exc1.ss", 2, "", "main", "SUCCESS", "rec_f", "SUCCESS"],
		["Costa_Julia_09/julia-09-iterative-exc2.ss", 2, "", "main", "SUCCESS", "rec_f", "SUCCESS"],
		["Costa_Julia_09/julia-09-iterative-exc3.ss", 2, "", "main", "SUCCESS", "rec_f", "SUCCESS"],
		["Costa_Julia_09/julia-09-iterative-exc4.ss", 2, "", "main", "SUCCESS", "rec_f", "SUCCESS"],
		["Costa_Julia_09/julia-09-iterative-exc5.ss", 2, "", "main", "SUCCESS", "rec_f", "SUCCESS"],
		#(11)
		["Costa_Julia_09-recursive/Ackermann.ss", 2, "", "main", "SUCCESS", "ack", "SUCCESS"],
		["Costa_Julia_09-recursive/Double-1.ss", 2, "-tp redlog", "test", "SUCCESS", "loop", "SUCCESS"],
		["Costa_Julia_09-recursive/Double2-1.ss", 3, "", "main", "SUCCESS", "test", "SUCCESS", "loop", "SUCCESS"],
		["Costa_Julia_09-recursive/Double2.ss", 2, "", "main", "SUCCESS", "test", "SUCCESS"],
		["Costa_Julia_09-recursive/Double3-1.ss", 3, "", "main", "SUCCESS", "test", "SUCCESS", "loop", "SUCCESS"],
		["Costa_Julia_09-recursive/Double3.ss", 2, "", "main", "SUCCESS", "test", "SUCCESS"],
		["Costa_Julia_09-recursive/Double.ss", 2, "-tp redlog", "main", "SUCCESS", "test", "SUCCESS"],
		["Costa_Julia_09-recursive/Factorial.ss", 2, "-tp redlog", "main", "SUCCESS", "fact", "SUCCESS"],
		["Costa_Julia_09-recursive/FactSumList.ss", 2, "-tp redlog", "doSum", "SUCCESS", "fact", "SUCCESS"],
		["Costa_Julia_09-recursive/FactSum.ss", 2, "-tp redlog", "doSum", "SUCCESS", "fact", "SUCCESS", "main", "SUCCESS"],
		["Costa_Julia_09-recursive/Hanoi.ss", 2, "", "main", "SUCCESS", "sol", "SUCCESS"],
		#(3)
		["Julia_10_Iterative/NonPeriodic.ss", 1, "", "main", "SUCCESS"],
		["Julia_10_Iterative/Test11.ss", 1, "-tp redlog", "main", "SUCCESS"],
		["Julia_10_Iterative/Test2.ss", 3, "", "main", "SUCCESS", "iter", "SUCCESS", "add", "SUCCESS"],
		#(8)
		["Julia_10_Recursive/AckR.ss", 2, "", "main", "SUCCESS", "ack", "SUCCESS"],
		["Julia_10_Recursive/FibSLR.ss", 4, "-tp redlog", 
				"main", "SUCCESS", "fib", "SUCCESS", "doSum", "SUCCESS", "create", "SUCCESS"],
		["Julia_10_Recursive/HanR.ss", 2, "", "main", "SUCCESS", "sol", "SUCCESS"],
		["Julia_10_Recursive/Power.ss", 3, "-tp redlog", "power", "SUCCESS", "even", "SUCCESS", "odd", "SUCCESS"],
		["Julia_10_Recursive/Recursions.ss", 6, "", "main", "SUCCESS", "rec0", "SUCCESS", "rec1", "SUCCESS",
			"rec2", "SUCCESS", "rec3", "SUCCESS", "rec4", "SUCCESS"],
		["Julia_10_Recursive/Test10.ss", 4, "", "main", "SUCCESS", "rec", "SUCCESS", 
			"test", "SUCCESS", "descend", "SUCCESS"],
		["Julia_10_Recursive/Test12.ss", 2, "-tp redlog", "main", "SUCCESS", "rec", "SUCCESS"],
		["Julia_10_Recursive/Test1.ss", 2, "", "main", "SUCCESS", "rec", "SUCCESS"],
		#(24)
		["Julia_11_iterative/ChooseLife.ss", 2, "", "main", "SUCCESS", "loop", "SUCCESS"],
		["Julia_11_iterative/Choose.ss", 2, "", "main", "SUCCESS", "loop", "SUCCESS"],
		["Julia_11_iterative/Continue.ss", 2, "", "main", "SUCCESS", "loop", "SUCCESS"],
		["Julia_11_iterative/Loop.ss", 2, "-tp redlog", "main", "SUCCESS", "test", "SUCCESS"],
		["Julia_11_iterative/NO_00.ss", 1, "", "main", "SUCCESS"],
		["Julia_11_iterative/NO_01.ss", 1, "", "main", "SUCCESS"],
		["Julia_11_iterative/NO_02.ss", 1, "", "main", "SUCCESS"],
		["Julia_11_iterative/NO_03.ss", 1, "", "main", "SUCCESS"],
		["Julia_11_iterative/NO_04.ss", 6, "", "main", "SUCCESS", "for_1", "SUCCESS", "for_2", "SUCCESS", 
				"for_3", "SUCCESS", "for_4", "SUCCESS", "for_5", "SUCCESS"],
		["Julia_11_iterative/NO_04-1.ss", 1, "", "main", "SUCCESS"],
		["Julia_11_iterative/NO_05.ss", 1, "", "main", "SUCCESS"],
		["Julia_11_iterative/NO_06.ss", 1, "", "main", "SUCCESS"],
		["Julia_11_iterative/NO_10.ss", 1, "", "main", "SUCCESS"],
		["Julia_11_iterative/NO_11.ss", 1, "", "main", "SUCCESS"],
		["Julia_11_iterative/NO_12.ss", 1, "", "main", "SUCCESS"],
		["Julia_11_iterative/NO_13.ss", 1, "", "main", "SUCCESS"],
		["Julia_11_iterative/NO_13-gen.ss", 3, "", "main", "SUCCESS", "loop", "SUCCESS", "loop2", "SUCCESS"],
		["Julia_11_iterative/NO_20.ss", 1, "", "main", "SUCCESS"],
		["Julia_11_iterative/NO_21.ss", 1, "", "main", "SUCCESS"],
		["Julia_11_iterative/NO_22.ss", 1, "", "main", "SUCCESS"],
		["Julia_11_iterative/NO_23.ss", 1, "", "main", "SUCCESS"],
		["Julia_11_iterative/NO_24.ss", 1, "", "main", "SUCCESS"],
		["Julia_11_iterative/Parts.ss", 6, "", "parts", "SUCCESS", "main", "SUCCESS", "for_1", "SUCCESS",
				"loop_1", "SUCCESS", "for_2", "SUCCESS", "loop_2", "SUCCESS"],
		["Julia_11_iterative/Swingers.ss", 2, "", "main", "SUCCESS", "loop", "SUCCESS"]
	],
	"Invel" => [
		["AlternatingIncr.ss", 1, "", "increase", "SUCCESS"],
		["AlternDiv-invalid-1.ss", 1, "-tp redlog", "loop", "SUCCESS"],
		["AlternDiv.ss", 1, "-tp redlog", "loop", "SUCCESS"],
		["AlternDivWidening.ss", 2, "-tp redlog", "loop", "SUCCESS", "loop_aux", "SUCCESS"],
		["AlternDivWide.ss", 2, "", "loop", "SUCCESS", "loop_aux", "SUCCESS"],
		["AlternKonv.ss", 1, "", "loop", "SUCCESS"],
		["Collatz.ss", 1, "", "collatz", "SUCCESS"],
		["ComplInterv2.ss", 1, "", "loop", "SUCCESS"],
		["ComplInterv3.ss", 1, "", "loop", "SUCCESS"],
		["ComplInterv.ss", 1, "-tp z3", "loop", "SUCCESS"],
		["ComplxStruc1.ss", 2, "", "loop", "SUCCESS", "complxStruc", "SUCCESS"], 
		["ComplxStruc2.ss", 2, "", "loop", "SUCCESS", "complxStruc", "SUCCESS"],
		["ComplxStruc-rec.ss", 2, "", "loop", "SUCCESS", "complxStruc", "SUCCESS"],
		["ConvLower.ss", 1, "", "loop", "SUCCESS"],
		["Cousot.ss", 1, "", "loop", "SUCCESS"],
		["DoubleNeg.ss", 1, "-tp redlog", "loop", "SUCCESS"],
		["Even.ss", 2, "", "even", "SUCCESS", "loop", "SUCCESS"],
		["Ex01.ss", 1, "", "loop", "SUCCESS"],
		["Ex02.ss", 1, "", "loop", "SUCCESS"],
		["Ex03.ss", 1, "", "loop", "SUCCESS"],
		["Ex04.ss", 1, "", "loop", "SUCCESS"],
		["Ex05.ss", 1, "", "loop", "SUCCESS"],
		["Ex06.ss", 1, "", "loop", "SUCCESS"],
		["Ex07.ss", 1, "", "loop", "SUCCESS"],
		["Ex08.ss", 2, "", "main", "SUCCESS", "loop", "SUCCESS"],
		["Ex09.ss", 2, "", "half", "SUCCESS", "loop", "SUCCESS"],
		["Fibonacci.ss", 2, "", "fib", "SUCCESS", "loop", "SUCCESS"],
		["Flip2.ss", 1, "", "flip", "SUCCESS"],
		["Flip3.ss", 1, "", "flip", "SUCCESS"],
		["Flip.ss", 1, "", "flip", "SUCCESS"],
		["Gauss.ss", 2, "", "sum", "SUCCESS", "loop", "SUCCESS"],
		["Gcd.ss", 1, "", "gcd", "SUCCESS"],
		["Lcm.ss", 2, "", "lcm", "SUCCESS", "loop", "SUCCESS"],
		["Marbie1.ss", 1, "", "loop", "SUCCESS"],
		["Marbie2.ss", 1, "", "loop", "SUCCESS"],
		["Middle.ss", 1, "", "middle", "SUCCESS"],
		["MirrorIntervSim.ss", 1, "", "loop", "SUCCESS"],
		["MirrorInterv.ss", 2, "", "mirrorInterv", "SUCCESS", "loop", "SUCCESS"],
		["ModuloLower.ss", 1, "", "loop", "SUCCESS"],
		["ModuloUp.ss", 2, "-tp redlog", "up", "SUCCESS", "loop", "SUCCESS"],
		["Narrowing.ss", 2, "", "narrowing", "SUCCESS", "loop", "SUCCESS"],
		["NarrowKonv.ss", 2, "", "narrowKonv", "SUCCESS", "loop", "SUCCESS"],
		["NegPos.ss", 1, "-tp redlog", "loop", "SUCCESS"],
		["Plait-rec.ss", 1, "", "plait", "SUCCESS"],
		["Sunset.ss", 1, "", "loop", "SUCCESS"],
		["TrueDiv.ss", 1, "", "loop", "SUCCESS"],
		["TwoFloatInterv.ss", 1, "", "loop", "SUCCESS"],
		["UpAndDownIneq.ss", 2, "", "upAndDown", "SUCCESS", "loop", "SUCCESS"],
		["UpAndDown.ss", 2, "", "upAndDown", "SUCCESS", "loop", "SUCCESS"],
		["WhileBreak.ss", 1, "", "loop", "SUCCESS"],
		["WhileDecr.ss", 1, "", "decrease", "SUCCESS"],
		["WhileIncrPart.ss", 1, "", "increase", "SUCCESS"],
		["WhileIncr.ss", 1, "", "increase", "SUCCESS"],
		["WhileNestedOffset.ss", 3, "", "increase", "SUCCESS", "loop_1", "SUCCESS", "loop_2", "SUCCESS"],
		["WhileNested.ss", 3, "", "increase", "SUCCESS", "loop_1", "SUCCESS", "loop_2", "SUCCESS"],
		["WhilePart.ss", 1, "", "increase", "SUCCESS"],
		["WhileSingle.ss", 1, "", "increase", "SUCCESS"],
		["WhileSum.ss", 1, "", "increase", "SUCCESS"],
		["WhileTrue.ss", 1, "", "endless", "SUCCESS"]
	],
	"Pasta" => [
		["PastaA10.ss", 2, "", "main", "SUCCESS", "loop", "SUCCESS"],
		["PastaA1.ss", 3, "", "main", "SUCCESS", "loop_1", "SUCCESS", "loop_2", "SUCCESS"],
		["PastaA4.ss", 1, "", "main", "SUCCESS"],
		["PastaA5.ss", 1, "", "main", "SUCCESS"],
		["PastaA6.ss", 1, "", "main", "SUCCESS"],
		["PastaA7.ss", 1, "", "main", "SUCCESS"],
		["PastaA8.ss", 2, "", "main", "SUCCESS", "loop", "SUCCESS"],
		["PastaA9.ss", 2, "", "main", "SUCCESS", "loop", "SUCCESS"],
		["PastaB10.ss", 2, "", "main", "SUCCESS", "loop", "SUCCESS"],
		["PastaB11.ss", 2, "", "main", "SUCCESS", "loop", "SUCCESS"],
		["PastaB12.ss", 2, "", "main", "SUCCESS", "loop", "SUCCESS"],
		["PastaB13.ss", 2, "", "main", "SUCCESS", "loop", "SUCCESS"],
		["PastaB14.ss", 3, "", "main", "SUCCESS", "loop_1", "SUCCESS", "loop_2", "SUCCESS"],
		["PastaB15.ss", 3, "", "main", "SUCCESS", "loop_1", "SUCCESS", "loop_2", "SUCCESS"],
		["PastaB16-loop.ss", 3, "", "main", "SUCCESS", "loop_1", "SUCCESS", "loop_2", "SUCCESS"],
		["PastaB16.ss", 3, "", "main", "SUCCESS", "loop_1", "SUCCESS", "loop_2", "SUCCESS"],
		["PastaB17.ss", 3, "", "main", "SUCCESS", "loop_1", "SUCCESS", "loop_2", "SUCCESS"],
		["PastaB18.ss", 3, "", "main", "SUCCESS", "loop", "SUCCESS", "decrease", "SUCCESS"],
		["PastaB1.ss", 1, "", "main", "SUCCESS"],
		["PastaB2.ss", 1, "", "main", "SUCCESS"],
		["PastaB3.ss", 1, "", "main", "SUCCESS"],
		["PastaB4.ss", 1, "", "main", "SUCCESS"],
		["PastaB4-loop.ss", 1, "", "main", "SUCCESS"],
		["PastaB5.ss", 1, "", "main", "SUCCESS"],
		["PastaB6.ss", 1, "", "main", "SUCCESS"],
		["PastaB7.ss", 1, "", "main", "SUCCESS"],
		["PastaB8.ss", 1, "", "main", "SUCCESS"],
		["PastaC10-while.ss", 1, "", "main", "SUCCESS"],
		["PastaC11.ss", 2, "", "main", "SUCCESS", "loop", "SUCCESS"],
		["PastaC11-while.ss", 1, "", "main", "SUCCESS"],
		["PastaC1.ss", 3, "", "main", "SUCCESS", "loop_1", "SUCCESS", "loop_2", "SUCCESS"],
		["PastaC1-while.ss", 1, "", "main", "SUCCESS"],
		["PastaC2-while.ss", 1, "", "main", "SUCCESS"],
		["PastaC3.ss", 2, "", "main", "SUCCESS", "loop", "SUCCESS"],
		["PastaC3-while.ss", 1, "", "main", "SUCCESS"],
		["PastaC4-while.ss", 1, "", "main", "SUCCESS"],
		["PastaC5-while.ss", 1, "", "main", "SUCCESS"],
		["PastaC7-simpl-1.ss", 1, "", "loop", "SUCCESS"],
		["PastaC7-simpl-2.ss", 1, "", "loop", "SUCCESS"],
		["PastaC7-simpl.ss", 1, "", "loop", "SUCCESS"],
		["PastaC7.ss", 2, "", "main", "SUCCESS", "loop", "SUCCESS"],
		["PastaC7-while.ss", 1, "", "main", "SUCCESS"],
		["PastaC8-while.ss", 1, "", "main", "SUCCESS"],
		["PastaC9-while.ss", 1, "", "main", "SUCCESS"]
	],
	"Others" => [
		["ex1.ss", 2, "", "length", "SUCCESS", "app2", "SUCCESS"],
    ["ex2.ss", 1, "", "loop", "SUCCESS"],
    ["ex3.ss", 1, "", "loop", "SUCCESS"],
    ["ex4.ss", 1, "", "inc_loop", "SUCCESS"],
    ["ex5.ss", 1, "", "foo", "SUCCESS"],
    ["ex6.ss", 1, "", "Ack", "SUCCESS"],
    ["ex7.ss", 1, "", "loop", "SUCCESS"],
    ["ex8.ss", 2, "", "loop2", "SUCCESS", "loop", "SUCCESS"],
    ["ex9.ss", 1, "", "loop", "SUCCESS"],
		["ex10.ss", 1, "", "loop", "SUCCESS"],
    ["ex11.ss", 1, "", "bsearch", "SUCCESS"],
    ["ex12.ss", 2, "", "loop", "SUCCESS", "f", "SUCCESS"],
    ["ex13.ss", 1, "", "loop", "SUCCESS"],
		["ex14.ss", 1, "", "loop", "SUCCESS"],
		["mutual.ss", 2, "", "g", "SUCCESS", "f", "SUCCESS"],
		["lit/ase09-1.ss", 1, "", "find", "SUCCESS"],
		["lit/ase09-2.ss", 2, "", "find", "SUCCESS", "find_r", "SUCCESS"],
		["lit/cav08-1.ss", 1, "", "loop", "SUCCESS"],
		["lit/cav08-2.ss", 1, "", "loop", "SUCCESS"],
		["lit/cav08-3.ss", 1, "", "loop", "SUCCESS"],
		["lit/cav08-4.ss", 1, "", "loop", "SUCCESS"],
		["lit/cav08-5.ss", 2, "", "loop", "SUCCESS", "f", "SUCCESS"],
		["lit/cav08-6.ss", 1, "", "gcd", "SUCCESS"],
		["lit/dijkstra76-1.ss", 1, "", "loop", "SUCCESS"],
		["lit/dijkstra76-2.ss", 1, "", "loop", "SUCCESS"],
		["lit/dijkstra76-3.ss", 1, "", "loop", "SUCCESS"],
		["lit/pldi06-1.ss", 1, "", "loop", "SUCCESS"],
		["lit/pldi06-2.ss", 3, "", "main", "SUCCESS", "loop_1", "SUCCESS", "loop_2", "SUCCESS"],
		["lit/pldi06-3.ss", 2, "", "main", "SUCCESS", "loop", "SUCCESS"],
		["lit/pldi06-4.ss", 3, "", "main", "SUCCESS", "loop", "SUCCESS", "loop_aux", "SUCCESS"],
		["lit/pldi06-5.ss", 1, "", "Ack", "SUCCESS"],
		["lit/popl07-1.ss", 3, "", "loop_1", "SUCCESS", "loop_2", "SUCCESS", "loop_3", "SUCCESS"],
		["lit/popl07-2.ss", 1, "", "loop", "SUCCESS"],
		["lit/sas05.ss", 2, "", "loop_1", "SUCCESS", "loop_2", "SUCCESS"],
		["lit/sas10-1.ss", 3, "", "f", "SUCCESS", "loop_1", "SUCCESS", "loop_2", "SUCCESS"],
		["lit/sas10-2.ss", 2, "", "foo", "SUCCESS", "loop", "SUCCESS"],
		["lit/sas10-2a.ss", 2, "", "foo", "SUCCESS", "loop", "SUCCESS"],
		["lit/sas10-3.ss", 3, "", "main", "SUCCESS", "foo", "SUCCESS", "loop", "SUCCESS"],
		["lit/vcc-1.ss", 2, "", "f", "SUCCESS", "g", "SUCCESS"],
		["lit/vmcai05-1a.ss", 1, "", "loop", "SUCCESS"],
		["lit/vmcai05-1b.ss", 1, "-tp redlog", "loop", "SUCCESS"],
		["lit/leap-year-bug-zune-loop.ss", 3, "", "ConvertDays", "SUCCESS", "loop", "SUCCESS", "IsLeapYear", "SUCCESS"]
	],
	"SIR" => [
		["print_tokens.c", 23, "-tp z3",  
			"gat_loop1", "SUCCESS",
			"gat_loop2", "SUCCESS",
			"check_delimiter", "SUCCESS",
			"numeric_case_loop", "SUCCESS",
			"next_state", "SUCCESS",
			"get_char", "SUCCESS",
			"is_end_of_character_stream", "SUCCESS",
			"skip_loop", "SUCCESS",
			"unget_char", "SUCCESS",
			"get_actual_token", "SUCCESS",
			"special", "SUCCESS",
			"skip","SUCCESS",
			"numeric_case","SUCCESS",
			"keyword","SUCCESS",
			"error_or_eof_case","SUCCESS",
			"constant","SUCCESS",
			"open_character_stream","SUCCESS",
			"get_token_loop","SUCCESS",
			"print_token","SUCCESS",
			"open_token_stream","SUCCESS",
			"main","SUCCESS",
			"is_eof_token","SUCCESS",
			"get_token","SUCCESS"
		],
		["print_tokens2.c", 22, "-tp z3", 
			"is_str_constant_loop", "SUCCESS",
			"get_token_loop21", "SUCCESS",
			"is_identifier_loop", "SUCCESS",
			"get_char", "SUCCESS",
			"is_spec_symbol", "SUCCESS",
			"is_eof_token", "SUCCESS",
			"is_token_end", "SUCCESS",
			"is_num_constant_loop", "SUCCESS",
			"is_str_constant", "SUCCESS",
			"is_num_constant", "SUCCESS",
			"is_keyword", "SUCCESS",
			"is_identifier", "SUCCESS",
			"is_comment", "SUCCESS",
			"is_char_constant", "SUCCESS",
			"token_type", "SUCCESS",
			"open_character_stream", "SUCCESS",
			"unget_char", "SUCCESS",
			"print_token", "SUCCESS",
			"print_spec_symbol", "SUCCESS",
			"open_token_stream", "SUCCESS",
			"main", "SUCCESS",
			"get_token", "SUCCESS"			
		],
		["replace.c", 25, "-tp z3", 
			"makesub_loop", "SUCCESS",
			"addstr", "SUCCESS",
			"stclose_loop", "SUCCESS",
			"esc", "SUCCESS",
			"dodash_loop1", "SUCCESS",
			"dodash", "SUCCESS",
			"locate_loop", "SUCCESS",
			"putsub", "SUCCESS",
			"subline_loop", "SUCCESS",
			"stclose", "SUCCESS",
			"in_set_2", "SUCCESS",
			"getccl", "SUCCESS",
			"makepat_loop", "SUCCESS",
			"in_pat_set", "SUCCESS",
			"makesub", "SUCCESS",
			"makepat", "SUCCESS",
			"subline", "SUCCESS",
			"getline", "SUCCESS",
			"patsize", "SUCCESS",
			"omatch", "SUCCESS",
			"main", "SUCCESS",
			"getsub", "SUCCESS",
			"getpat", "SUCCESS",
			"change", "SUCCESS",
			"Caseerror", "SUCCESS"			
		],
		["tcas.c", 9, "-tp z3", 
			"Own_Below_Threat", "SUCCESS",
			"Own_Above_Threat", "SUCCESS",
			"Inhibit_Biased_Climb", "SUCCESS",
			"ALIM", "SUCCESS",
			"Non_Crossing_Biased_Descend", "SUCCESS",
			"Non_Crossing_Biased_Climb", "SUCCESS",
			"initialize", "SUCCESS",
			"alt_sep_test", "SUCCESS",
			"main", "SUCCESS"
		],
		["schedule.c", 20, "", 
			"init_prio_queue_helper", "SUCCESS",
			"init_prio_queue", "SUCCESS",
			"main_helper", "SUCCESS",
			"new_ele", "SUCCESS",
			"new_process", "SUCCESS",
			"find_nth_helper", "SUCCESS",
			"get_first_seg", "SUCCESS",
			"find_nth", "SUCCESS",
			"do_upgrade_process_prio", "SUCCESS",
			"schedule", "SUCCESS",
			"initialize", "SUCCESS",
			"free_ele", "SUCCESS",
			"upgrade_process_prio", "SUCCESS",
			"unblock_process", "SUCCESS",
			"quantum_expire", "SUCCESS",
			"main", "SUCCESS",
			"get_first", "SUCCESS",
			"finish_process", "SUCCESS",
			"block_process", "SUCCESS",
			"add_process", "SUCCESS"
		],
		["schedule2.c", 16, "", 
			"lput_end", "SUCCESS",
			# "flush", "SUCCESS",
			"get_current", "SUCCESS",
			"finish", "SUCCESS",
			"do_get_process", "SUCCESS",
			"put_end", "SUCCESS",
			"reschedule", "SUCCESS",
			"get_process", "SUCCESS",
			"enqueue", "SUCCESS",
			"upgrade_prio", "SUCCESS",
			"unblock", "SUCCESS",
			"quantum_expire", "SUCCESS",
			"new_job", "SUCCESS",
			"block", "SUCCESS",
			"schedule", "SUCCESS",
			"get_command", "SUCCESS",
			"main", "SUCCESS"
		]	
	],
	"SV-COMP" => [
		["alternating_list.ss", 2, "-tp om", 
			"create", "SUCCESS",
			"main", "SUCCESS"
		],
		["create.ss", 1, "-tp om", "create", "SUCCESS"],
		["list_flag.ss", 2, "-tp om", 
			"create", "SUCCESS",
			"main", "SUCCESS"
		],
		["list.ss", 2, "-tp om", 
			"create", "SUCCESS",
			"main", "SUCCESS"
		],
		["simple_built_from_end.ss", 2, "-tp om", 
			"create", "SUCCESS",
			"main", "SUCCESS"
		],
		["simple.ss", 2, "-tp om", 
			"create", "SUCCESS",
			"main", "SUCCESS"
		],
		["splice.ss", 3, "-tp om", 
			"create", "SUCCESS",
			"main", "SUCCESS",
			"part", "SUCCESS"
		]
	],
	"Hip" => [
		["avl.ss", 13, "",
			"build_avl1", "SUCCESS",
			"build_avl2", "SUCCESS",
			"get_max", "SUCCESS",
			"height", "SUCCESS",
			"rotate_double_left", "SUCCESS",
			"rotate_double_right", "SUCCESS",
			"rotate_left", "SUCCESS",
			"rotate_right", "SUCCESS",
			"insert", "SUCCESS",
			"insert_inline", "SUCCESS",
			"merge", "SUCCESS",
			"merge2", "SUCCESS",
			"remove_min", "SUCCESS"
		],
		["avl-orig.ss", 11, "",
			"build_avl1", "SUCCESS",
			"build_avl2", "SUCCESS",
			"get_max", "SUCCESS",
			"height", "SUCCESS",
			"rotate_double_left", "SUCCESS",
			"rotate_double_right", "SUCCESS",
			"rotate_left", "SUCCESS",
			"rotate_right", "SUCCESS",
			"insert", "SUCCESS",
			"insert_inline", "SUCCESS",
			"merge", "SUCCESS"
		],
		["ll.ss", 13, "",
			"append", "SUCCESS",
			"append2", "SUCCESS",
			"append3", "SUCCESS",
			"create_list", "SUCCESS",
			"delete", "SUCCESS",
			"get_next", "SUCCESS",
			"get_next_next", "SUCCESS",
			"insert", "SUCCESS",
			"ret_first", "SUCCESS",
			"reverse", "SUCCESS",
			"set_next", "SUCCESS",
			"set_null", "SUCCESS",
			"set_null2", "SUCCESS"
		],
		["cll.ss", 4, "-tp om",
			"duplicate", "SUCCESS",
			"insert", "SUCCESS",
			"length", "SUCCESS",
			"remove", "SUCCESS"
		],
		["dll.ss", 11, "",
			"append", "SUCCESS",
			"append1", "SUCCESS",
			"append2", "SUCCESS",
			"delete", "SUCCESS",
			"delete1", "SUCCESS",
			"f1", "SUCCESS",
			"f2", "SUCCESS",
			"insert", "SUCCESS",
			"test_del", "SUCCESS",
			"test_del2", "SUCCESS",
			"test_fold", "SUCCESS"
		],
		["complete.ss", 6, "",
			"maxim", "SUCCESS",
			"height", "SUCCESS",
			"minim", "SUCCESS",
			"min_height", "SUCCESS",
			"insert", "SUCCESS",
			"is_perfect", "SUCCESS"
		],
		["heaps.ss", 5, "",
			"deleteoneel", "SUCCESS",
			"deleteone", "SUCCESS",
			"ripple", "SUCCESS",
			"deletemax", "SUCCESS",
			"insert", "SUCCESS"
		],
		["bst.ss", 6, "",
			"append", "SUCCESS",
			"count", "SUCCESS",
			"remove_min", "SUCCESS",
			"delete", "SUCCESS",
			"flatten", "SUCCESS",
			"insert", "SUCCESS"
		],
		["perfect.ss", 5, "",
			"create", "SUCCESS",
			"maxim", "SUCCESS",
			"height", "SUCCESS",
			"simple_insert", "SUCCESS",
			"insert", "SUCCESS"
		],
		["rb.ss", 19, "",
			"rotate_case_3", "SUCCESS",
			"case_2", "SUCCESS",
			"rotate_case_3r", "SUCCESS",
			"case_2r", "SUCCESS",
			"del_4", "SUCCESS",
			"del_6", "SUCCESS",
			"del_5", "SUCCESS",
			"is_black", "SUCCESS",
			"del_2", "SUCCESS",
			"del_4r", "SUCCESS",
			"del_6r", "SUCCESS",
			"del_5r", "SUCCESS",
			"del_2r", "SUCCESS",
			"del_3", "SUCCESS",
			"del_3r", "SUCCESS",
			"is_red", "SUCCESS",
			"remove_min", "SUCCESS",
			"del", "SUCCESS",
			"insert", "SUCCESS"
		],
		["bignat.ss", 18, "-tp redlog",
			"clone", "SUCCESS",
			"add_one_digit", "SUCCESS",
			"add_c", "SUCCESS",
			"add", "SUCCESS",
			"div_with_remainder", "SUCCESS",
			"bigint_of", "SUCCESS",
			"compare_int", "SUCCESS",
			"compare_n", "SUCCESS",
			"int_value", "SUCCESS",
			"is_equal", "SUCCESS",
			"is_zero", "SUCCESS",
			"mult_c", "SUCCESS",
			"shift_left", "SUCCESS",
			"mult", "SUCCESS",
			"sub_one_digit", "SUCCESS",
			"sub_c", "SUCCESS",
			"sub", "SUCCESS",
			"karatsuba_mult", "SUCCESS"
		],
		["bignat-n.ss", 18, "-tp redlog",
			"clone", "SUCCESS",
			"add_one_digit", "SUCCESS",
			"add_c", "SUCCESS",
			"add", "SUCCESS",
			"div_with_remainder", "SUCCESS",
			"bigint_of", "SUCCESS",
			"compare_int", "SUCCESS",
			"compare_n", "SUCCESS",
			"int_value", "SUCCESS",
			"is_equal", "SUCCESS",
			"is_zero", "SUCCESS",
			"mult_c", "SUCCESS",
			"shift_left", "SUCCESS",
			"mult", "SUCCESS",
			"sub_one_digit", "SUCCESS",
			"sub_c", "SUCCESS",
			"sub", "SUCCESS",
			"karatsuba_mult", "SUCCESS"
		]

	]
);

# if($timings){
    $mainSum = 0.0;
    $childSum = 0.0;
    $totalSum = 0.0;
    $prooflogSum = 0.0;
    $falseContextSum = 0;
# }

open(LOGFILE, "> $output_file") || die ("Could not open $output_file.\n");
hip_process_file();
close(LOGFILE);

if ($error_count > 0) {
  print "Total number of errors: $error_count in files:\n $error_files.\n";
}
else
	{print "All test results were as expected.\n";}
if($home21){
	chdir("/home") or die "Can't chdir to $target_dir $!";
	rmtree(["$target_dir"]) or die ("Could not delete folder: $target_dir $!");
}

printf "Total verification time: %.2f second\n", $totalSum;
printf "\tTime spent in main process: %.2f second\n", $mainSum;
printf "\tTime spent in child processes: %.2f second\n", $childSum;
printf "\tNumber of false contexts: %d\n", $falseContextSum; 
 

sub sum_of_timings {
 my $outp = $_[0];
 if($outp =~ m/Total verification time: (.*?) second/){
     $totalSum = $totalSum + $1;
 }
 if($outp =~ m/Time spent in main process: (.*?) second/){
     $mainSum = $mainSum + $1;
 }
 if($outp =~ m/Time spent in child processes: (.*?) second/){
     $childSum = $childSum + $1;
 }
 if($outp =~ m/	Time for logging: (.*?) second/){
     $prooflogSum = $prooflogSum + $1;
 }
 if($outp =~ m/\b(\w+) false contexts/){
     $falseContextSum = $falseContextSum + $1;
 }
}

# string-pattern for collecting hip answer after the verification of a procedure:
#   "Procedure proc_name$ignored_string RESULT", where proc_name is the name of the procedure to be 
#   verified, and RESULT can be either SUCCESS or FAIL
sub hip_process_file {
	foreach $param (@param_list)
  {
		my $procedure = "Procedure"; # assume the lemma checking is disabled by default; 
    $exempl_path_full = "$exempl_path/examples/$param";
    print "Starting $param tests:\n";
		$t_list = $hip_files{$param};
		foreach $test (@{$t_list})
		{
			$extra_options = $test->[2];
      if ("$extra_options" eq "") {
				print "Checking $test->[0]\n";
      } else {
      	print "Checking $test->[0] (runs with extra options: $extra_options)\n";
      }
			#print "$hip $script_arguments $extra_options $exempl_path_full/$test->[0] 2>&1 \n";
			$output = `$hip $script_arguments $extra_options $exempl_path_full/$test->[0] 2>&1`;
			print LOGFILE "\n======================================\n";
			print LOGFILE "$output";
			$limit = $test->[1]*2+2;

			for($i = 3; $i<$limit;$i+=2)
			{
				if($output !~ /$procedure $test->[$i]\$.* $test->[$i+1]/)
				{
			 		$error_count++;
					$error_files=$error_files."error at: $test->[0] $test->[$i]\n";
					print "error at: $test->[0] $test->[$i]\n";
				}
			}
			#Termination checking result
      if ($output !~ "ERR:") {}
			else {
				$error_count++;
				$error_files=$error_files."term error at: $test->[0] $test->[$i]\n";
				print "term error at: $test->[0] $test->[$i]\n";
			}
      if($timings) {
        log_one_line_of_timings ($test->[0],$output);
      }
      sum_of_timings ($output);
    }
  }
}

