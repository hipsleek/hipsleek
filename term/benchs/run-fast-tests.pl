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
  "log-timings" => \$timings,
  "log-string=s" => \$str_log,
  "bags" => \$bags,
  "lists" => \$lists
);

@param_list = @ARGV;
if(($help) || (@param_list == ""))
{
	print "./run-fast-tests.pl [-help] [-root path_to_sleek] [-tp name_of_prover] [-log-timings] [-log-string string_to_be_added_to_the_log] [-copy-to-home21] hip_tr|hip|imm|sleek [-flags \"arguments to be transmited to hip/sleek \"]\n";
	exit(0);
}

if($root) {
	$exempl_path = "$root/examples/working";
	$exec_path = "$root";
}
else {
	$exempl_path = ".";
	$exec_path = '../..';
}

if($prover) {
	%provers = ('cvcl' => 'cvcl', 'cvc3' => 'cvc3', 'oc' => 'oc','oc-2.1.6' => 'oc-2.1.6', 
		'co' => 'co', 'isabelle' => 'isabelle', 'coq' => 'coq', 'mona' => 'mona', 'om' => 'om', 
		'oi' => 'oi', 'set' => 'set', 'cm' => 'cm', 'redlog' => 'redlog', 'rm' => 'rm', 'prm' => 'prm', 
		'z3' => 'z3', 'z3-2.19' => 'z3-2.19', 'zm' => 'zm');
	if (!exists($provers{$prover})) {
		print "./run-fast-tests.pl [-help] [-root path_to_sleek] [-tp name_of_prover] [-log-timings]  [-log-string string_to_be_added_to_the_log] [-copy-to-home21] hip_tr|hip sleek [-flags \"arguments to be transmited to hip/sleek \"]\n";
		print "\twhere name_of_prover should be one of the followings: 'cvcl', 'cvc3', 'omega', 'co', 'isabelle', 'coq', 'mona', 'om', 'oi', 'set', 'cm', 'redlog', 'rm', 'prm', 'z3' or 'zm'\n";
		exit(0);
	}
}
else {
	if("$flags" =~ m/-tp (\w+)\b/ ) {
		$prover = "$1";
  } else {
		$prover = "oc";
  }
}

if("$flags") {
	$script_arguments = "$flags";
	if (!($script_arguments =~ "-tp ")){
		$script_arguments = $script_arguments." -tp ".$prover;
	}
}
else {
	$script_arguments = " -tp ".$prover;
}

if($home21){
	$current_dir = getcwd();
	$current_hostname = hostname;
	#if ($current_hostname eq "loris-21"){
	#	print "The current host is already loris-21";
	#	exit(0);
	#}
	$target_dir = "/home21/".getlogin()."/sleek_tmp_".getppid();
	mkdir $target_dir or die "\nerror: Could not create directory $target_dir\n";
	my $cp = File::NCopy->new(recursive => 1);
    $cp->copy("$exec_path/*", $target_dir) or die "Could not perform rcopy of $source_dir to $target_dir: $!";
	$exec_path = "$target_dir";
	$exempl_path = "$target_dir/examples/working";
	if($root) {
		chdir("$root") or die "Can't chdir to $root $!";
	} else {
		chdir("$target_dir") or die "Can't chdir to $target_dir $!"; 
	}	
}

if($timings){
    my $parser = new Spreadsheet::ParseExcel::SaveParser;
    $timings_logfile = "timings_log.xls";
    if(-e "$timings_logfile") {#check for file existance
        $book = $parser->Parse("$timings_logfile") #open file for appending
            or die "File $timings_logfile was not found";
        my $count = $book->{SheetCount};#total number of worksheets of teh workbook
        my $provers_sheet_no = 0;
        for(my $i=0; $i < $count ; $i++){#iterate through all the worksheets 
            if ($book->{Worksheet}[$i]->{Name} =~ "$prover") {#check if a profiling worksheet of the selected prover already exists
                if($book->{Worksheet}[$i]->{Name} =~ m/_(\d+)/) {#find the no. of the newest worksheet of this prover
                    if($provers_sheet_no < int($1)){
                        $provers_sheet_no = int($1);
                    }
                }
            }
        }
        $provers_sheet_no = $provers_sheet_no + 1;
        my $new_worksheet_name = "$prover"."_".$provers_sheet_no;#compute the name of the new worksheet: prover_maxno
        $book->AddWorksheet($new_worksheet_name);
        local $^W = 0;
        $workbook = $book->SaveAs("temp_"."$timings_logfile");
        $worksheet = $workbook->sheets($count);
    }else{
        #create a new file
        $workbook = Spreadsheet::WriteExcel->new("temp_"."$timings_logfile")
            or die "Could not create file $timings_logfile"; 
        my $new_worksheet_name = "$prover"."_1";
        $workbook->add_worksheet($new_worksheet_name);
        $worksheet = $workbook->sheets(0);
    }

    $row = 3;
    (my $Second, my $Minute, $Hour, $Day, $Month, $Year, $WeekDay, $DayOfYear, $IsDST) = localtime(time);
    $Year += 1900;
    $Month++;
    $date = "$Day/$Month/$Year  $Hour:$Minute";
    $worksheet->set_column(0, 0, 10);
    $worksheet->write($row, 3, "Time:");
    $worksheet->write($row, 4, $date);
    $row++;
    $worksheet->write($row, 3, "Prover:");
    $worksheet->write($row, 4, "$prover");
    $row++;
    if("$flags"){
        $worksheet->write($row, 3, "Call args:");
        $worksheet->write($row, 4, "$flags");
    }
    $row++;
    if("$str_log"){
        $worksheet->write($row, 3, "Comments:");
        $worksheet->write($row, 4, "$str_log");
    }
    $row = $row + 2;
    $programCol = 1;
    $mainCol = 2;
    $childCol = 3;
    $totalCol = 4;
    $falseContextCol = 5;
    my $format = $workbook->add_format();
    $format->set_bold();
    $format->set_align('center');
    $worksheet->write($row, $programCol, "Program", $format);
    $worksheet->set_column($programCol, 0, 15);
    $worksheet->set_column($mainCol,$falseContextCol, 10);
    $worksheet->write($row, $mainCol, "Main", $format);
    $worksheet->write($row, $childCol, "Child", $format);
    $worksheet->write($row, $totalCol, "Total time", $format);
    $worksheet->write($row, $falseContextCol, "No. false ctx", $format);

}

@excl_files = ();
$error_count = 0;
$error_files = "";
$hip = "$exec_path/hip ";
# TODO : check if hip is n-hip, as b-hip is too slow
# please use make native
$sleek = "$exec_path/sleek ";
$output_file = "log";
# list of file, nr of functions, function name, output, function name, output......
# files are searched in the subdirectory with the same name as the list name, in examples/working/hip directory (ex. hip/array for "array" list)
%hip_files=(
	"term"=>[
		###############################################
		["lit/cav08-1.ss", 1, "", "loop", "SUCCESS"],
		["lit/cav08-2.ss", 1, "", "loop", "SUCCESS"],
		["lit/cav08-3.ss", 1, "", "loop", "SUCCESS"],
		["lit/cav08-4.ss", 1, "", "loop", "SUCCESS"],
		["lit/cav08-5.ss", 2, "", "loop", "SUCCESS", "f", "SUCCESS"],
		["lit/cav08-6.ss", 1, "", "gcd", "SUCCESS"],
		["lit/dijkstra76-1.ss", 1, "", "loop", "SUCCESS"],
		["lit/dijkstra76-2.ss", 1, "", "loop", "SUCCESS"],
		["lit/dijkstra76-3.ss", 1, "", "loop", "SUCCESS"],
		["lit/leaf-year-bug-zune.ss", 2, "", "ConvertDays", "SUCCESS", "loop", "SUCCESS"],
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
		###############################################
		["key/AlternatingIncr.ss", 1, "", "increase", "SUCCESS"],
		["key/AlternDiv-invalid-1.ss", 1, "-tp redlog", "loop", "SUCCESS"],
		["key/AlternDiv.ss", 1, "-tp redlog", "loop", "SUCCESS"],
		["key/AlternDivWidening.ss", 2, "-tp redlog", "loop", "SUCCESS", "loop_aux", "SUCCESS"],
		["key/AlternDivWide.ss", 2, "", "loop", "SUCCESS", "loop_aux", "SUCCESS"],
		["key/AlternKonv.ss", 1, "", "loop", "SUCCESS"],
		["key/Collatz.ss", 1, "", "collatz", "SUCCESS"],
		["key/ComplInterv2.ss", 1, "", "loop", "SUCCESS"],
		["key/ComplInterv3.ss", 1, "", "loop", "SUCCESS"],
		["key/ComplInterv.ss", 1, "-tp redlog", "loop", "SUCCESS"],
		["key/ConvLower.ss", 1, "", "loop", "SUCCESS"],
		["key/Cousot.ss", 1, "", "loop", "SUCCESS"],
		["key/DoubleNeg.ss", 1, "-tp redlog", "loop", "SUCCESS"],
		["key/Even.ss", 2, "", "even", "SUCCESS", "loop", "SUCCESS"],
		["key/Ex01.ss", 1, "", "loop", "SUCCESS"],
		["key/Ex02.ss", 1, "", "loop", "SUCCESS"],
		["key/Ex03.ss", 1, "", "loop", "SUCCESS"],
		["key/Ex04.ss", 1, "", "loop", "SUCCESS"],
		["key/Ex05.ss", 1, "", "loop", "SUCCESS"],
		["key/Ex06.ss", 1, "", "loop", "SUCCESS"],
		["key/Ex07.ss", 1, "", "loop", "SUCCESS"],
		["key/Ex08.ss", 2, "", "main", "SUCCESS", "loop", "SUCCESS"],
		["key/Ex09.ss", 2, "", "half", "SUCCESS", "loop", "SUCCESS"],
		["key/Fibonacci.ss", 2, "", "fib", "SUCCESS", "loop", "SUCCESS"],
		["key/Flip2.ss", 1, "", "flip", "SUCCESS"],
		["key/Flip3.ss", 1, "", "flip", "SUCCESS"],
		["key/Flip.ss", 1, "", "flip", "SUCCESS"],
		["key/Gauss.ss", 2, "", "sum", "SUCCESS", "loop", "SUCCESS"],
		#["key/Gcd.ss", 2, "", "gcd", "SUCCESS", "loop", "SUCCESS"],
		["key/Lcm.ss", 2, "", "lcm", "SUCCESS", "loop", "SUCCESS"],
		["key/Marbie1.ss", 1, "", "loop", "SUCCESS"],
		["key/Marbie2.ss", 1, "", "loop", "SUCCESS"],
		["key/Middle.ss", 1, "", "middle", "SUCCESS"],
		["key/MirrorIntervSim.ss", 1, "", "loop", "SUCCESS"],
		["key/MirrorInterv.ss", 2, "", "mirrorInterv", "SUCCESS", "loop", "SUCCESS"],
		["key/ModuloLower.ss", 1, "", "loop", "SUCCESS"],
		["key/ModuloUp.ss", 2, "-tp redlog", "up", "SUCCESS", "loop", "SUCCESS"],
		["key/Narrowing.ss", 2, "", "narrowing", "SUCCESS", "loop", "SUCCESS"],
		["key/NarrowKonv.ss", 2, "", "narrowKonv", "SUCCESS", "loop", "SUCCESS"],
		["key/NegPos.ss", 1, "-tp redlog", "loop", "SUCCESS"],
		#["key/Plait.ss", 2, "", "plait", "SUCCESS", "loop", "SUCCESS"],
		["key/Sunset.ss", 1, "", "loop", "SUCCESS"],
		["key/TrueDiv.ss", 1, "", "loop", "SUCCESS"],
		["key/TwoFloatInterv.ss", 1, "", "loop", "SUCCESS"],
		["key/UpAndDownIneq.ss", 2, "", "upAndDown", "SUCCESS", "loop", "SUCCESS"],
		["key/UpAndDown.ss", 2, "", "upAndDown", "SUCCESS", "loop", "SUCCESS"],
		["key/WhileBreak.ss", 1, "", "loop", "SUCCESS"],
		["key/WhileDecr.ss", 1, "", "decrease", "SUCCESS"],
		["key/WhileIncrPart.ss", 1, "", "increase", "SUCCESS"],
		["key/WhileIncr.ss", 1, "", "increase", "SUCCESS"],
		["key/WhileNestedOffset.ss", 3, "", "increase", "SUCCESS", "loop_1", "SUCCESS", "loop_2", "SUCCESS"],
		["key/WhileNested.ss", 3, "", "increase", "SUCCESS", "loop_1", "SUCCESS", "loop_2", "SUCCESS"],
		["key/WhilePart.ss", 1, "", "increase", "SUCCESS"],
		["key/WhileSingle.ss", 1, "", "increase", "SUCCESS"],
		["key/WhileSum.ss", 1, "", "increase", "SUCCESS"],
		["key/WhileTrue.ss", 1, "", "endless", "SUCCESS"],
		###############################################
		["aprove/Aprove_09/GCD5.ss", 2, "-tp redlog", "main", "SUCCESS", "gcd", "SUCCESS"],
		["aprove/Aprove_09/GCD.ss", 2, "-tp redlog", "main", "SUCCESS", "gcd", "SUCCESS"],
		#["aprove/Aprove_09/McCarthyIterative.ss", 2, "", "mcCarthy", "SUCCESS", "loop", "SUCCESS"],
		["aprove/Aprove_09/McCarthyRec.ss", 1, "", "mcCarthy", "SUCCESS"],
		["aprove/Aprove_09/PastaA10.ss", 2, "", "main", "SUCCESS", "loop", "SUCCESS"],
		["aprove/Aprove_09/PastaA1.ss", 3, "", "main", "SUCCESS", "loop_1", "SUCCESS", "loop_2", "SUCCESS"],
		["aprove/Aprove_09/PastaA8.ss", 2, "", "main", "SUCCESS", "loop", "SUCCESS"],
		["aprove/Aprove_09/PastaA9.ss", 2, "", "main", "SUCCESS", "loop", "SUCCESS"],
		["aprove/Aprove_09/PastaB10.ss", 2, "", "main", "SUCCESS", "loop", "SUCCESS"],
		["aprove/Aprove_09/PastaB11.ss", 2, "", "main", "SUCCESS", "loop", "SUCCESS"],
		["aprove/Aprove_09/PastaB12.ss", 2, "", "main", "SUCCESS", "loop", "SUCCESS"],
		["aprove/Aprove_09/PastaB13.ss", 2, "", "main", "SUCCESS", "loop", "SUCCESS"],
		["aprove/Aprove_09/PastaB14.ss", 3, "", "main", "SUCCESS", "loop_1", "SUCCESS", "loop_2", "SUCCESS"],
		["aprove/Aprove_09/PastaB15.ss", 3, "", "main", "SUCCESS", "loop_1", "SUCCESS", "loop_2", "SUCCESS"],
		["aprove/Aprove_09/PastaB16-loop.ss", 3, "", "main", "SUCCESS", "loop_1", "SUCCESS", "loop_2", "SUCCESS"],
		["aprove/Aprove_09/PastaB16.ss", 3, "", "main", "SUCCESS", "loop_1", "SUCCESS", "loop_2", "SUCCESS"],
		["aprove/Aprove_09/PastaB17.ss", 3, "", "main", "SUCCESS", "loop_1", "SUCCESS", "loop_2", "SUCCESS"],
		["aprove/Aprove_09/PastaB18.ss", 3, "", "main", "SUCCESS", "loop", "SUCCESS", "decrease", "SUCCESS"],
		["aprove/Aprove_09/PastaC10-while.ss", 1, "", "main", "SUCCESS"],
		["aprove/Aprove_09/PastaC11.ss", 2, "", "main", "SUCCESS", "loop", "SUCCESS"],
		["aprove/Aprove_09/PastaC11-while.ss", 1, "", "main", "SUCCESS"],
		["aprove/Aprove_09/PastaC1.ss", 3, "", "main", "SUCCESS", "loop_1", "SUCCESS", "loop_2", "SUCCESS"],
		["aprove/Aprove_09/PastaC1-while.ss", 1, "", "main", "SUCCESS"],
		["aprove/Aprove_09/PastaC2-while.ss", 1, "", "main", "SUCCESS"],
		["aprove/Aprove_09/PastaC3.ss", 2, "", "main", "SUCCESS", "loop", "SUCCESS"],
		["aprove/Aprove_09/PastaC3-while.ss", 1, "", "main", "SUCCESS"],
		["aprove/Aprove_09/PastaC4-while.ss", 1, "", "main", "SUCCESS"],
		["aprove/Aprove_09/PastaC5-while.ss", 1, "", "main", "SUCCESS"],
		["aprove/Aprove_09/PastaC7-simpl-1.ss", 1, "", "loop", "SUCCESS"],
		["aprove/Aprove_09/PastaC7-simpl-2.ss", 1, "", "loop", "SUCCESS"],
		["aprove/Aprove_09/PastaC7-simpl.ss", 1, "", "loop", "SUCCESS"],
		["aprove/Aprove_09/PastaC7.ss", 2, "", "main", "SUCCESS", "loop", "SUCCESS"],
		["aprove/Aprove_09/PastaC7-while.ss", 1, "", "main", "SUCCESS"],
		["aprove/Aprove_09/PastaC8-while.ss", 1, "", "main", "SUCCESS"],
		["aprove/Aprove_09/PastaC9-while.ss", 1, "", "main", "SUCCESS"],
		["aprove/Aprove_09/PlusSwap.ss", 2, "", "main", "SUCCESS", "loop", "SUCCESS"],
		###############################################
		["/aprove/AProVE11NO/LoopingNonTerm.ss", 2, "", "main", "SUCCESS", "loop", "SUCCESS"],
		["/aprove/AProVE11NO/NonPeriodicNonTerm2.ss", 2, "", "main", "SUCCESS", "loop", "SUCCESS"],
		###############################################
		["/aprove/BOG_RTA_11/TerminatiorRec01.ss", 3, "", "main", "SUCCESS", "f", "SUCCESS", "loop", "SUCCESS"],
		["/aprove/BOG_RTA_11/TerminatiorRec02.ss", 1, "-tp redlog", "fact", "SUCCESS"],
		["/aprove/BOG_RTA_11/TerminatiorRec03.ss", 1, "", "f", "SUCCESS"],
		["/aprove/BOG_RTA_11/TerminatiorRec04-modified.ss", 3, "", "main", "SUCCESS", "f", "SUCCESS", "loop", "SUCCESS"],
		["/aprove/BOG_RTA_11/TerminatiorRec04.ss", 3, "", "main", "SUCCESS", "f", "SUCCESS", "loop", "SUCCESS"],
		###############################################
		["/aprove/Costa_Julia_09/Exc4.ss", 2, "", "main", "SUCCESS", "loop", "SUCCESS"],
		###############################################
		["/aprove/Julia_11_iterative/ChooseLife.ss", 2, "", "main", "SUCCESS", "loop", "SUCCESS"],
		["/aprove/Julia_11_iterative/Choose.ss", 2, "", "main", "SUCCESS", "loop", "SUCCESS"],
		["/aprove/Julia_11_iterative/Continue.ss", 2, "", "main", "SUCCESS", "loop", "SUCCESS"],
		["/aprove/Julia_11_iterative/NO_24.ss", 1, "", "main", "SUCCESS"],
		["/aprove/Julia_11_iterative/Parts.ss", 3, "", "parts", "SUCCESS", "main", "SUCCESS", "for_1", "SUCCESS",
				"loop_1", "SUCCESS", "for_2", "SUCCESS", "loop_2", "SUCCESS"],
		["/aprove/Julia_11_iterative/Swingers.ss", 2, "", "main", "SUCCESS", "loop", "SUCCESS"], 
		###############################################
		["hip/clist.ss", 4, "-tp om", 
			"length", "SUCCESS", "duplicate", "SUCCESS",
			"remove", "SUCCESS", "insert", "SUCCESS"],
		["hip/avl.ss", 13, "",  
			"height", "SUCCESS", "rotate_left", "SUCCESS",
			"rotate_right", "SUCCESS", "get_max", "SUCCESS",
			"rotate_double_left", "SUCCESS",
			"rotate_double_right", "SUCCESS",
			"build_avl1", "SUCCESS", "build_avl2", "SUCCESS",
			"insert", "SUCCESS", "insert_inline", "SUCCESS",
			"merge", "SUCCESS", "merge2", "SUCCESS",
			"remove_min","SUCCESS"
		]

	]        
);

# list of file, string with result of each entailment&lemma....
# the pattern to add a new program below: ["program_name", "default options", "lemma validity check results", "checkentail results"]
%sleek_files=();

if($timings){
    $mainSum = 0.0;
    $childSum = 0.0;
    $totalSum = 0.0;
    $falseContextSum = 0;
}

open(LOGFILE, "> $output_file") || die ("Could not open $output_file.\n");
sleek_process_file();
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

if($timings){
    #do the last computations and close the timings log worksheet
    #compute the total times*
    $row = $row + 2;
    my $format = $workbook->add_format();
    $format->set_bold();
    $format->set_num_format('0.00');
    $format->set_align('right');
    $worksheet->write($row, $programCol, "Totals:", $format);
    $worksheet->write($row, $mainCol, "$mainSum", $format);
    $worksheet->write($row, $childCol, "$childSum", $format);
    $worksheet->write($row, $totalCol, $totalSum, $format);
    $worksheet->write($row, $falseContextCol, $falseContextSum, $format);
    $workbook->close();
    my $parser = new Spreadsheet::ParseExcel::SaveParser;
    $book = $parser->Parse("temp_"."$timings_logfile") #open file for appending
            or die "File $timings_logfile was not found";
    local $^W = 0;
    $workbook = $book->SaveAs("$timings_logfile");
    $workbook->close();
    unlink("temp_"."$timings_logfile");
}
exit(0);

sub log_one_line_of_timings{
 my ($prog_name, $outp) = @_;
 $row++;
 $worksheet->write($row, $programCol, "$prog_name");
 my $format = $workbook->add_format();
 # $format->set_num_format('0.00');
 $format->set_align('right');
 if($outp =~ m/Total verification time: (.*?) second/){
     my $formatted_no = sprintf "%.2f", "$1";
     $worksheet->write_number($row, $totalCol, $formatted_no, $format);
     $totalSum = $totalSum + $1;
 }
 if($outp =~ m/Time spent in main process: (.*?) second/){
     my $formatted_no = sprintf "%.2f", "$1";
     $worksheet->write($row, $mainCol, $formatted_no, $format);
     $mainSum = $mainSum + $1;
 }
 if($outp =~ m/Time spent in child processes: (.*?) second/){
     my $formatted_no = sprintf "%.2f", "$1";
     $worksheet->write($row, $childCol, $formatted_no, $format);
     $childSum = $childSum + $1;
 }
 if($outp =~ m/\b(\w+) false contexts/){
     $format->set_num_format('0');
     $worksheet->write($row, $falseContextCol, "$1", $format);
     $falseContextSum = $falseContextSum + $1;
 }
}

sub hip_process_file {
    foreach $param (@param_list)
    {
        my $procedure = "Procedure"; # assume the lemma checking is disabled by default; 
        if ("$param" =~ "lemmas") { $procedure = "Entailing lemma"; }
        if ("$param" =~ "hip") {
            $exempl_path_full = "$exempl_path/hip";
            print "Starting hip tests:\n";
        } else {
            $exempl_path_full = "$exempl_path";
            print "Starting hip-$param tests:\n";
        }
		$t_list = $hip_files{$param};
		foreach $test (@{$t_list})
		{
            $extra_options = $test->[2];
            if ("$extra_options" eq "") {
                print "Checking $test->[0]\n";
            } else {
                print "Checking $test->[0] (runs with extra options: $extra_options)\n";
            }
			#print "$hip $script_arguments $extra_options $exempl_path/hip/$test->[0] 2>&1 \n";
			$output = `$hip $script_arguments $extra_options $exempl_path_full/$test->[0] 2>&1`;
			print LOGFILE "\n======================================\n";
			print LOGFILE "$output";
			$limit = $test->[1]*2+2;
			#print "\nbegin"."$output"."end\n";
			for($i = 3; $i<$limit;$i+=2)
			{
				if($output !~ /$procedure $test->[$i].* $test->[$i+1]/)
				{
			 		$error_count++;
					$error_files=$error_files."error at: $test->[0] $test->[$i]\n";
					print "error at: $test->[0] $test->[$i]\n";
				}
			}
            if($timings) {
                log_one_line_of_timings ($test->[0],$output);
            }
        }
    }
}

sub sleek_process_file  {
  foreach $param (@param_list)
  {
      my $lem = 0; # assume the lemma checking is disabled by default; make $lem=1 if lemma checking will be enabled by default and uncomment elsif
      my $err = 0;
      if ("$param" =~ "errors") {
          print "Starting sleek must/may errors tests:\n";
          $exempl_path_full = "$exec_path/errors";
          $err = 1;
      }
      if (("$param" =~ "lemmas") ||  ($script_arguments=~"--elp")) {  $lem = 1; }
#      elsif ($script_arguments=~"--dlp"){ $lem = 0; }
      
      if ("$param" =~ "sleek") {
          print "Starting sleek tests:\n";
          $exempl_path_full = "$exempl_path/sleek";
      }else {
          $exempl_path_full = "$exempl_path_full/$param";
          print "Starting sleek-$param tests:\n";
      }
      $t_list = $sleek_files{$param};
      foreach $test (@{$t_list})
			{
            my $extra_options = $test->[1];
            if ("$extra_options" eq "") {
                print "Checking $test->[0]\n";
            } else {
                print "Checking $test->[0] (runs with extra options: $extra_options)\n";
            }
            $script_args = $script_arguments.$extra_options;
			$output = `$sleek $script_args $exempl_path_full/$test->[0] 2>&1`;
			print LOGFILE "\n======================================\n";
	        print LOGFILE "$output";
            my $lemmas_results = "";
            my $entail_results = "";
            my @lines = split /\n/, $output; 
            foreach my $line (@lines) { 
                if($line =~ m/Entailing lemma/){
                    if($line =~ m/Valid/) { $lemmas_results = $lemmas_results ."Valid."; }
                    elsif($line =~ m/Fail/)  { $lemmas_results = $lemmas_results ."Fail.";}
                }elsif($line =~ m/Entail/){
                    if( $err == 1) {
                        $i = index($line, "Valid. (bot)",0);
                        $h = index($line, "Valid.",0);
                        $j = index($line, "Fail.(must)",0);
                        $k = index($line, "Fail.(may)",0);
                        #  print "i=".$i ." h=". $h . " j=" .$j . " k=".$k ."\n";
                        if($i >= 0) { $r = $r ."bot."; }
                        elsif($h >= 0) { $r = $r ."Valid."; }
                        elsif($j >= 0)  { $r = $r ."must.";} #$line =~ m/Fail.(must)/
                        elsif($k >= 0)  { $r = $r ."may.";}
                    }
                    else {
                        if($line =~ m/Valid/) { $entail_results = $entail_results ."Valid."; }
                        elsif($line =~ m/Fail/)  { $entail_results = $entail_results ."Fail.";}
                    }
                }
            }
			if (($entail_results !~ /^$test->[3]$/) || ( ($lem == 1)  && ($lemmas_results !~ /^$test->[2]$/)))
			{
				print "Unexpected result with : $test->[0]\n";
				$error_count++;
				$error_files = $error_files . " " . $test->[0];
			}
            if($timings) {
               # log_one_line_of_timings ($test->[0],$output);
            }
		}
	}
}

