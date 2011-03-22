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
            "log-string=s" => \$str_log
			);

@param_list = @ARGV;
if(($help) || (@param_list == ""))
{
	print "./run-fast-tests.pl [-help] [-root path_to_sleek] [-tp name_of_prover] [-log-timings] [-log-string string_to_be_added_to_the_log] [-copy-to-home21] hip_tr|hip|hip_imm|sleek [-flags \"arguments to be transmited to hip/sleek \"]\n";
	exit(0);
}
if($root){
	$exempl_path = "$root/examples/working";
	$exec_path = "$root";
}
	else
	{
		$exempl_path = ".";
		$exec_path = '../..';
	}

if($prover){
	%provers = ('cvcl' => 'cvcl', 'cvc3' => 'cvc3', 'omega' => 'omega', 
		'co' => 'co', 'isabelle' => 'isabelle', 'coq' => 'coq', 'mona' => 'mona', 'om' => 'om', 
		'oi' => 'oi', 'set' => 'set', 'cm' => 'cm', 'redlog' => 'redlog', 'rm' => 'rm', 'prm' => 'prm');
	if (!exists($provers{$prover})){		
        print "./run-fast-tests.pl [-help] [-root path_to_sleek] [-tp name_of_prover] [-log-timings]  [-log-string string_to_be_added_to_the_log] [-copy-to-home21] hip_tr|hip sleek [-flags \"arguments to be transmited to hip/sleek \"]\n";
		print "\twhere name_of_prover should be one of the followings: 'cvcl', 'cvc3', 'omega', 'co', 'isabelle', 'coq', 'mona', 'om', 'oi', 'set', 'cm', 'redlog', 'rm' or 'prm' \n";
		exit(0);
	}
}
else
{
    if("$flags" =~ m/-tp (\w+)\b/ ){
        $prover = "$1";
    }
    else{
	$prover = "omega";
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
	if($root){
		chdir("$root") or die "Can't chdir to $root $!";
	}else{
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
    (my $Second,my $Minute, $Hour, $Day, $Month, $Year, $WeekDay, $DayOfYear, $IsDST) = localtime(time);
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
$fails_count = 0;
$success_count = 0;
$fatal_errors = 0;
$fail_files = "";
$fatal_error_files = "";
$hip = "$exec_path/hip ";
$sleek = "$exec_path/sleek ";
$output_file = "log";
# list of file, nr of functions, function name, output, function name, output......
%hip_files=(
	"hip" =>[
        ["avl-all-1.ss", ""],
        ["avl-all.ss", "--eps --eap"],
        ["avl-modular-2.ss", ""],
        ["avl-modular-3.ss", ""],
        ["avl-modular-hei.ss", ""],
        ["avl-modular-new3.ss", ""],
        ["avl-modular-set.ss", ""],
        ["avl-modular-siz.ss", ""],
        ["avl-modular.ss", ""],
        ["avl.scp.ss", ""],
        ["avl.ss", ""],
        ["bubble.ss", ""],
        ["cll.ss", ""],
        ["dll.ss", ""],
        ["insertion.ss", ""],
        ["ll.ss", ""],
        ["merge-modular.ss", ""],
        ["merge.ss", ""],
        ["qsort.ss", ""],
        ["rb_bags.ss", ""],
        ["rb.scp.ss", ""],
        ["selection.ss", ""],
        ["trees.ss", ""]]
  );
# list of file, string with result of each entailment....
%sleek_files=(
		"sleek"=>[["sleek.slk","Valid.Valid.Valid.Fail."],
					["sleek1.slk","Fail."],
					["sleek10.slk","Valid.Fail."],
					["sleek2.slk","Fail.Valid.Fail.Fail.Valid.Valid.Valid.Fail."],
					["sleek3.slk","Valid.Fail.Valid."],
					["sleek4.slk","Valid.Valid."],
					["sleek6.slk","Valid.Valid."],
					["sleek7.slk","Valid.Valid.Valid.Fail.Valid.Valid.Valid.Valid.Fail.Valid."],
					["sleek8.slk","Valid.Fail.Valid.Valid.Valid.Valid.Valid.Valid.Valid.Fail.Valid.Valid.Valid.Valid.Fail.Valid.Fail."],
					["sleek9.slk","Valid."]]				
			);

if($timings){
    $mainSum = 0.0;
    $childSum = 0.0;
    $totalSum = 0.0;
    $falseContextSum = 0;
}

open(LOGFILE, "> $output_file") || die ("Could not open $output_file.\n");
print "Starting hip tests:\n";
hip_process_file();
close(LOGFILE);

if ($fails_count > 0) {
    print "\nProcedure verification failures: $fails_count \n$fail_files\n";
}
if ($fatal_errors > 0){
    print "\nProgram fatal errors: $fatal_errors:\n$fatal_error_files\n";
}
if (($fails_count > 0 || $fatal_errors > 0) && $success_count > 0) {
    print "Total number of procedures verified with success: $success_count\n\n";
}
elsif ($sunccess_count > 0) {print "All test results were as expected.\n";}

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
		$t_list = $hip_files{$param};	
		foreach $test (@{$t_list})
		{
			print "Checking $test->[0]\n";
            if($timings) {
                @output = `$hip $script_arguments $exempl_path/$test->[0] | grep -e "Proc" -e "time" -e "Time" -e "false contexts" 2>&1`;}
            else{
                @output = `$hip $script_arguments $exempl_path/$test->[0] | grep -e "Proc" 2>&1`;    
            }
            my $fails = 0;
            my $successes = 0;
            my $output_str = "";
            if (@output){
                foreach $line (@output)
                {
                    if($line =~ m/FAIL/){
                        $fails++;
                        # chomp $line;
                        # print $line;
                        $line =~ m/Procedure(.*)\$/; 
                        # my $proc = '$1';
                        $fail_files=$fail_files." fail: $test->[0]: $1\n";
                        print "  error at: $test->[0] $1\n";
                    }
                    elsif($line =~ m/SUCCESS/){
                        $successes++;
                    }
                    $output_str = $output_str.$line;
                }
            }
            $fails_count = $fails_count + $fails;
            $success_count = $success_count + $successes;
            if ($fails == 0 && $successes == 0){
                    $fatal_errors++;
                    $fatal_error_files=$fatal_error_files."  $test->[0] \n";
                }
            if($timings) {
                log_one_line_of_timings ($test->[0], $output_str);
            }
		}
    }
}
