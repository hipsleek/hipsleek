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

GetOptions( "stop"  => \$stop,
			"help" => \$help,
			"root=s" => \$root,
			"tp=s" => \$prover,
			"flags=s" => \$flags,
			"copy-to-home21" => \$home21,
            "log-timings" => \$timings,
            "log-string=s" => \$str_log,
            "bags" => \$bags,
            "term" => \$term,
            "lists" => \$lists
			);
@param_list = @ARGV;
if(($help) || (@param_list == ""))
{
	print "./run-fast-tests.pl [-help] [-root path_to_sleek] [-tp name_of_prover] [-log-timings] [-log-string string_to_be_added_to_the_log] [-copy-to-home21] spring-if|spring-else|spring [-flags \"arguments to be transmited to hip/sleek \"]\n";
	exit(0);
}

if($root){
	$exempl_path = "$root/test_proof/spring";
	$exec_path = "$root";
}
else
	{
		$exempl_path = ".";
		$exec_path = '..';
	}

if($prover){
	%provers = ('cvcl' => 'cvcl', 'cvc3' => 'cvc3', 'oc' => 'oc','oc-2.1.6' => 'oc-2.1.6', 
		'co' => 'co', 'isabelle' => 'isabelle', 'coq' => 'coq', 'mona' => 'mona', 'om' => 'om', 
		'oi' => 'oi', 'set' => 'set', 'cm' => 'cm', 'redlog' => 'redlog', 'rm' => 'rm', 'prm' => 'prm', 'z3' => 'z3', 'z3-2.19' => 'z3-2.19', 'zm' => 'zm', 'log' => 'log');
	if (!exists($provers{$prover})){
        print "./run-fast-tests.pl [-help] [-root path_to_sleek] [-tp name_of_prover] [-log-timings]  [-log-string string_to_be_added_to_the_log] [-copy-to-home21] hip_tr|hip|sleek|hip_vperm|sleek_vperm [-flags \"arguments to be transmited to hip/sleek \"]\n";
		print "\twhere name_of_prover should be one of the followings: 'cvcl', 'cvc3', 'omega', 'co', 'isabelle', 'coq', 'mona', 'om', 'oi', 'set', 'cm', 'redlog', 'rm', 'prm', 'z3' or 'zm'\n";
		exit(0);
	}
}
else{
    if("$flags" =~ m/-tp (\w+)\b/ ){
        $prover = "$1";
    }
    else{
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
    $invocationCol = 2;
    $proverCol =3;
    $mainCol = 4;
    $childCol = 5;
    $cl = $childCol;
    if("$flags" =~ m/--enable-logging-txt\b/ ){
     $cl=$childCol+1;
     $prooflogCol = $cl;	
    }
    $totalCol = $cl+1;
    $falseContextCol = $cl+2;
    my $format = $workbook->add_format();
    $format->set_bold();
    $format->set_align('center');
    $worksheet->write($row, $programCol, "Program", $format);
    $worksheet->write($row, $invocationCol, "Invocations", $format);
    $worksheet->write($row, $proverCol, "Prover Time", $format);
    $worksheet->set_column($programCol, 0, 15);
    $worksheet->set_column($invocationCol, 0, 13);
    $worksheet->set_column($proverCol, 0, 13);
    $worksheet->set_column($mainCol,$falseContextCol, 10);
    $worksheet->write($row, $mainCol, "Main", $format);
    $worksheet->write($row, $childCol, "Child", $format);
    if("$flags" =~ m/--enable-logging-txt\b/ ){
       $worksheet->write($row, $prooflogCol, "Proof log", $format);
    }
    $worksheet->write($row, $totalCol, "Total time", $format);
    $worksheet->write($row, $falseContextCol, "No. false ctx", $format);

}

@excl_files = ();
$error_count = 0;
$error_files = "";
$hip = "$exec_path/hip ";
# TODO : check if hip is n-hip, as b-hip is too slow
# please use make native
$output_file = "log";
# list of file, nr of functions, function name, output, function name, output......
# files are searched in the subdirectory with the same name as the list name, in examples/working/hip directory (ex. hip/array for "array" list)
%hip_files=(
	# AN HOA : ADDED ARRAY TESTING EXAMPLES
	"if"=>[["spring-if-10.ss",1,"","spring","SUCCESS"]],
        "if-else"=>[["spring-if-else-5.ss",1,"","spring","SUCCESS"],
                    ["spring-if-else-10.ss",1,"","spring","SUCCESS"],
                    ["spring-if-else-15.ss",1,"","spring","SUCCESS"],
                    ["spring-if-else-20.ss",1,"","spring","SUCCESS"] 
         ]
	# END OF ARRAY TESTING EXAMPLE
    );

if($timings){
    $mainSum = 0.0;
    $childSum = 0.0;
    $totalSum = 0.0;
    $prooflogSum =0.0;
    $invocationSum = 0.0;
    $proverSum = 0.0;
    $falseContextSum = 0;
}

open(LOGFILE, "> $output_file") || die ("Could not open $output_file.\n");
hip_process_file();
close(LOGFILE);

if ($error_count > 0) {
  print "Total number of errors: $error_count in files:\n $error_files.\n";
}
else
	{print "All test results were as expected.\n";}

if($timings){
    #do the last computations and close the timings log worksheet
    #compute the total times*
    $row = $row + 2;
    my $format = $workbook->add_format();
    $format->set_bold();
    $format->set_num_format('0.00');
    $format->set_align('right');
    $worksheet->write($row, $programCol, "Totals:", $format);
    $worksheet->write($row, $invocationCol, "$invocationSum", $format);
    $worksheet->write($row, $proverCol, "$proverSum", $format);
    $worksheet->write($row, $mainCol, "$mainSum", $format);
    $worksheet->write($row, $childCol, "$childSum", $format);
    if("$flags" =~ m/--enable-logging-txt\b/ ){
      $worksheet->write($row, $prooflogCol, "$prooflogSum", $format);	
    }
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
 
 if($outp =~ m/Stop z3... (.*?) invocations/){
     my $formatted_no = sprintf "%.2f", "$1";
     $worksheet->write_number($row, $invocationCol, $formatted_no, $format);
     $invocationSum = $invocationSum + $1;
 }
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
 if($outp =~ m/	Time for logging: (.*?) second/){
     my $formatted_no = sprintf "%.2f", "$1";
     $worksheet->write($row, $prooflogCol, $formatted_no, $format);
     $prooflogSum = $prooflogSum + $1;
 }
 if($outp =~ m/	Z3 Prover Time: (.*?) second/){
     my $formatted_no = sprintf "%.2f", "$1";
     $worksheet->write($row, $proverCol, $formatted_no, $format);
     $proverSum = $proverSum + $1;
 }
 if($outp =~ m/\b(\w+) false contexts/){
     $format->set_num_format('0');
     $worksheet->write($row, $falseContextCol, "$1", $format);
     $falseContextSum = $falseContextSum + $1;
 }
}

# string-pattern for collecting hip answer after the verification of a procedure:
#   "Procedure proc_name$ignored_string RESULT", where proc_name is the name of the procedure to be 
#                                                  verified, and RESULT can be either SUCCESS or FAIL
sub hip_process_file {
    foreach $param (@param_list)
    {    

        my $procedure = "Procedure"; # assume the lemma checking is disabled by default; 
        if ("$param" =~ "lemmas") { $procedure = "Entailing lemma"; }
        if ("$param" =~ "spring-if") {
            $exempl_path_full = "$exempl_path/spring/if";
            $hashkey="if";
            print "Starting hip tests:$exempl_path_full \n";
        } 
        elsif ("$param" =~ "spring-else"){
            $exempl_path_full = "$exempl_path/spring/if-else";
            $hashkey="if-else";
            print "Starting hip tests:$exempl_path_full \n"; 
        } else {
         $exempl_path_full = "$exempl_path/spring/$param";
         print "Starting hip-$param tests:\n"; 
        }
         
        $t_list = $hip_files{$hashkey};	
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
                        #print "limit=$limit\n";
                        #print "$output"; 
			for($i = 3; $i<$limit;$i+=2)
			{
				if($output !~ /$procedure $test->[$i]\$.* $test->[$i+1]/)
				{
                                        #print "$output";                
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
        }
    }
}




