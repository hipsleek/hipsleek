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
        ["avl-all-1.ss", 8, "remove_min", "SUCCESS", "rotate_double_right", "SUCCESS", "rotate_double_left", "SUCCESS", 
         "get_max", "SUCCESS", "rotate_right", "SUCCESS", "rotate_left", "SUCCESS", "height", "SUCCESS"],
        ["avl-all.ss", 11, "delete", "SUCCESS", "delete_top", "SUCCESS", "remove_min", "SUCCESS","remove_max_add", "SUCCESS", ,"remove_min_add","SUCCESS",
         "insert", "SUCCESS", "rotate_double_left",  "SUCCESS", "get_max", "SUCCESS", "rotate_right", "SUCCESS", "rotate_left", "SUCCESS", "height", "SUCCESS"],
        ["avl-modular-2.ss", 16, "delete", "SUCCESS", "delete_top", "SUCCESS", "remove_min", "SUCCESS", "remove_max_add", "SUCCESS", "remove_min_add", "SUCCESS", 
         "insert", "SUCCESS", "rotate_double_right", "SUCCESS", "rotate_double_left", "SUCCESS", "get_max", "SUCCESS", "rotate_right", "SUCCESS", 
         "rotate_left", "SUCCESS", "diff_h_by_2", "SUCCESS", "diff_h_by_1", "SUCCESS", "eq_h", "SUCCESS", "less_h", "SUCCESS", "get_max_height_add1", "SUCCESS",
         "height","SUCCESS"],
        ["avl-modular-3.ss", 11, "delete", "SUCCESS", "delete_top", "SUCCESS", "remove_min", "SUCCESS","remove_max_add", "SUCCESS", ,"remove_min_add","SUCCESS",
         "insert", "SUCCESS", "rotate_double_left",  "SUCCESS", "get_max", "SUCCESS", "rotate_right", "SUCCESS", "rotate_left", "SUCCESS", "height", "SUCCESS"],
        ["avl-modular-2.ss", 17, "delete", "SUCCESS", "delete_top", "SUCCESS", "remove_min", "SUCCESS", "remove_max_add", "SUCCESS", "remove_min_add", "SUCCESS", 
         "insert", "SUCCESS", "rotate_double_right", "SUCCESS", "rotate_double_left", "SUCCESS", "get_max", "SUCCESS", "rotate_right", "SUCCESS", 
         "rotate_left", "SUCCESS", "diff_h_by_2", "SUCCESS", "diff_h_by_1", "SUCCESS", "eq_h", "SUCCESS", "less_h", "SUCCESS", "get_max_height_add1", "SUCCESS",
         "height","SUCCESS"],
        ["avl-modular-hei.ss", 14, "delete", "SUCCESS", "delete_top", "SUCCESS", "remove_min", "SUCCESS", "remove_max_add", "SUCCESS", "remove_min_add", "SUCCESS", 
         "insert", "SUCCESS", "rotate_double_right", "SUCCESS", "rotate_double_left", "SUCCESS", "get_max", "SUCCESS", "rotate_right", "SUCCESS", 
         "rotate_left", "SUCCESS", "rotate_right2", "SUCCESS", "rotate_left2", "SUCCESS", "height","SUCCESS"],
        ["avl-modular-new3.ss", 18, "delete", "SUCCESS", "delete_top", "SUCCESS", "remove_min", "SUCCESS", "remove_max_add", "SUCCESS", "remove_min_add", "SUCCESS", 
         "insert", "SUCCESS", "is_mem", "SUCCESS","rotate_double_right", "SUCCESS", "rotate_double_left", "SUCCESS", "get_max", "SUCCESS", "rotate_right", "SUCCESS", 
         "rotate_left", "SUCCESS", "diff_h_by_2", "SUCCESS", "diff_h_by_1", "SUCCESS", "eq_h", "SUCCESS", "less_h", "SUCCESS", "get_max_height_add1", "SUCCESS",
         "height","SUCCESS"],
        ["avl-modular-set.ss", 3 ,"delete", "SUCCESS", "delete_top", "SUCCESS", "remove_min", "SUCCESS"],
        ["avl-modular-siz.ss", 3 ,"delete", "SUCCESS", "delete_top", "SUCCESS", "remove_min", "SUCCESS"],
        ["avl-modular.ss", 12, "delete", "SUCCESS", "delete_top", "SUCCESS", "remove_min", "SUCCESS", "remove_max_add", "SUCCESS", "remove_min_add", "SUCCESS", 
         "insert", "SUCCESS", "rotate_double_right", "SUCCESS", "rotate_double_left", "SUCCESS", "get_max", "SUCCESS", "rotate_right", "SUCCESS", 
         "rotate_left", "SUCCESS", "height","SUCCESS"],
        ["avl.scp.ss", 19 ,"delete", "SUCCESS", "remove_min", "SUCCESS", "insert_inline1", "SUCCESS", "insert_inline", "SUCCESS", "insert1", "SUCCESS", "insert", "SUCCESS",
         "build_avl2", "SUCCESS", "build_avl1", "SUCCESS", "rotate_double_right1", "SUCCESS", "rotate_double_right", "SUCCESS", "rotate_double_left1", "SUCCESS",
         "rotate_double_left", "SUCCESS", "get_max", "SUCCESS", "rotate_right1", "SUCCESS", "rotate_right", "SUCCESS", "rotate_left1", "SUCCESS", "rotate_left", "SUCCESS",
         "height1", "SUCCESS", "height", "SUCCESS"],
        ["avl.ss",  8,"insert_inline", "SUCCESS",  "insert", "SUCCESS", "rotate_double_right", "SUCCESS", "rotate_double_left", "SUCCESS", "get_max", "SUCCESS", 
         "rotate_right", "SUCCESS", "rotate_left", "SUCCESS","height", "SUCCESS"],
        ["bubble.ss", 3, "bsort1", "SUCCESS", "bubble1", "SUCCESS", "id1", "SUCCESS"],
        ["cll.ss", 4, "delete2", "SUCCESS", "delete", "SUCCESS", "count", "SUCCESS", "count_rest", "SUCCESS"],
        ["dll.ss", 2, "append", "SUCCESS", "insert", "SUCCESS"],
        ["insertion.ss", 3, "insertion_sort", "SUCCESS", "delete", "SUCCESS", "insert", "SUCCESS"],
        ["ll.ss", 4, "reverse1", "SUCCESS", "delete1", "SUCCESS", "insert", "SUCCESS", "append", "SUCCESS"],
        ["merge-modular.ss", 5, "insert1", "SUCCESS", "merge1", "SUCCESS", "merge_sort1", "SUCCESS", "split1", "SUCCESS", "count1", "SUCCESS"],
        ["merge.ss", 5, "insert1", "SUCCESS", "merge1", "SUCCESS", "merge_sort1", "SUCCESS", "split1", "SUCCESS", "count1", "SUCCESS"],
        ["qsort.ss", 3, "qsort1", "SUCCESS", "append_bll1", "SUCCESS", "partition1", "SUCCESS"],
        ["rb_bags.ss", 19, "insert_1", "SUCCESS", "del_1", "SUCCESS", "remove_min_1", "SUCCESS", "del_2r_1", "SUCCESS", "del_2_1", "SUCCESS", "del_3r_1", "SUCCESS",
         "del_3_1", "SUCCESS", "del_4r_1", "SUCCESS", "del_4_1", "SUCCESS", "del_5r_1", "SUCCESS", "del_5_1", "SUCCESS", "del_6r_1", "SUCCESS", "del_6_1", "SUCCESS",
         "is_black_1", "SUCCESS", "is_red_1", "SUCCESS", "case_2r_1", "SUCCESS", "rotate_case_3r_1", "SUCCESS", "case_2_1", "SUCCESS", "rotate_case_3_1", "SUCCESS"],
        ["rb.scp.ss", 38, "insert_1", "SUCCESS", "insert", "SUCCESS", "del_1", "SUCCESS", "del", "SUCCESS", "remove_min_1", "SUCCESS", "remove_min", "SUCCESS", 
         "del_2r_1", "SUCCESS", "del_2r", "SUCCESS", "del_2_1", "SUCCESS", "del_2", "SUCCESS", "del_3r_1", "SUCCESS", "del_3r", "SUCCESS", "del_3_1", "SUCCESS", 
         "del_3", "SUCCESS", "del_4r_1", "SUCCESS", "del_4r", "SUCCESS", "del_4_1", "SUCCESS", "del_4", "SUCCESS", "del_5r_1", "SUCCESS", "del_5r", "SUCCESS", 
         "del_5_1", "SUCCESS", "del_5", "SUCCESS", "del_6r_1", "SUCCESS", "del_6r", "SUCCESS", "del_6_1", "SUCCESS", "del_6", "SUCCESS", "is_black_1", "SUCCESS", 
         "is_black", "SUCCESS", "is_red_1", "SUCCESS", "is_red", "SUCCESS", "case_2r_1", "SUCCESS", "case_2r", "SUCCESS", "rotate_case_3r_1", "SUCCESS", 
         "rotate_case_3r", "SUCCESS", "case_2_1", "SUCCESS", "case_2", "SUCCESS", "rotate_case_3_1", "SUCCESS", "rotate_case_3", "SUCCESS"],
        ["selection.ss", 3, "selection_sort", "SUCCESS", "delete_min", "SUCCESS", "find_min", "SUCCESS"],
        ["trees.ss", 5, "delete1", "SUCCESS", "remove_min1", "SUCCESS", "insert1", "SUCCESS", "flatten1", "SUCCESS", "append1", "SUCCESS"]]
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
