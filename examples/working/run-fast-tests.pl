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
else{
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

    $row = 1;
    (my $Second,my $Minute, $Hour, $Day, $Month, $Year, $WeekDay, $DayOfYear, $IsDST) = localtime(time);
    $Year += 1900;
    $Month++;
    $date = "$Day/$Month/$Year  $Hour:$Minute";
    $worksheet->set_column(0, 0, 10);
    $worksheet->write($row, 0, "Time:");
    $worksheet->write($row, 1, $date);
    $row++;
    $worksheet->write($row, 0, "Prover:");
    $worksheet->write($row, 1, "$prover");
    $row++;
    if("$flags"){
        $worksheet->write($row, 0, "Call args:");
        $worksheet->write($row, 1, "$flags");
    }
    $row++;
    if("$str_log"){
        $worksheet->write($row, 0, "Comments:");
        $worksheet->write($row, 1, "$str_log");
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
$hip = "$exec_path/hip.opt ";
$sleek = "$exec_path/sleek.opt ";
$output_file = "log";
# list of file, nr of functions, function name, output, function name, output......
%hip_files=(
	"hip_tr"=>[["trees.ss",1,"insert"]],
        "hip_imm" =>[ 
         ["imm/bigint_imm.ss",18,
		 "clone", "SUCCESS",
		 "int_value", "SUCCESS",
		 "bigint_of", "SUCCESS",
		 "add_one_digit", "SUCCESS",
		 "test", "SUCCESS", 
		 "add_c", "SUCCESS",
		 "add", "SUCCESS",
		 "sub_one_digit", "SUCCESS",
		 "sub_c", "SUCCESS",
		 "sub", "SUCCESS",
		 "mult_c", "SUCCESS",
		 "shift_left", "SUCCESS",
		 "mult", "SUCCESS",
#		 "karatsuba_mult", "SUCCESS",
		 "is_zero", "SUCCESS",
		 "is_equal", "SUCCESS",
		 "compare", "SUCCESS",
		 "compare_int", "SUCCESS",
		 "div_with_remainder", "SUCCESS"],
         ["imm/bigint.ss",18,
		 "clone", "SUCCESS",
		 "int_value", "SUCCESS",
		 "bigint_of", "SUCCESS",
		 "add_one_digit", "SUCCESS",
		 "test", "SUCCESS", 
		 "add_c", "SUCCESS",
		 "add", "SUCCESS",
		 "sub_one_digit", "SUCCESS",
		 "sub_c", "SUCCESS",
		 "sub", "SUCCESS",
		 "mult_c", "SUCCESS",
		 "shift_left", "SUCCESS",
		 "mult", "SUCCESS",
#		 "karatsuba_mult", "SUCCESS",
		 "is_zero", "SUCCESS",
		 "is_equal", "SUCCESS",
		 "compare", "SUCCESS",
		 "compare_int", "SUCCESS",
		 "div_with_remainder", "SUCCESS"],
                ["imm/append_imm.ss", 1, "append", "SUCCESS"],
                ["imm/kara.ss",1,"karatsuba_mult","SUCCESS"],
                ["imm/kara-imm.ss",1,"karatsuba_mult","SUCCESS"],
                ["imm/kara-tight.ss",1,"karatsuba_mult","SUCCESS"],
                ["imm/kara-tight-imm.ss",1,"karatsuba_mult","SUCCESS"],
                ["imm/ll_imm.ss", 6, "length", "SUCCESS",
		 "append", "SUCCESS",
		 "get_next", "SUCCESS",
		 "set_next", "SUCCESS",
		 "get_next_next", "SUCCESS",
		 "sumN", "SUCCESS"]],
	"hip" =>[
#	["2-3trees.ss",4,"make_node","SUCCESS","insert_left","SUCCESS","insert_middle","SUCCESS","insert_right","SUCCESS","insert","SUCCESS"],
				["append.ss",1,"append","SUCCESS"],
#				["append-tail.ss --combined-lemma-heuristic",1,"append","SUCCESS"],
				["avl-bind.ss",9,"height","SUCCESS", "rotate_left","SUCCESS", "rotate_right","SUCCESS", "get_max","SUCCESS", "rotate_double_left","SUCCESS",
					"rotate_double_right","SUCCESS","build_avl1","SUCCESS","build_avl2","SUCCESS","insert","SUCCESS",
					#"insert_inline","SUCCESS","remove_min","SUCCESS","delete","SUCCESS"
					],
				["avl.ss",10,	 "height","SUCCESS","rotate_left","SUCCESS","rotate_right","SUCCESS",
								 "get_max","SUCCESS","rotate_double_left","SUCCESS","rotate_double_right","SUCCESS",
								 "build_avl1","SUCCESS","build_avl2","SUCCESS",
								 "insert","SUCCESS","insert_inline","SUCCESS",
								 #"remove_min","SUCCESS","delete","SUCCESS"
								 ],
				["avl-orig-2.ss",7,"height","SUCCESS","get_max","SUCCESS","insert","SUCCESS",
								 "double_left_child","SUCCESS","double_right_child","SUCCESS",
								 "rotate_left_child","SUCCESS", "rotate_right_child","SUCCESS",
								 #"f","SUCCESS","g","SUCCESS","h","SUCCESS","k","SUCCESS","test","SUCCESS",  "rotate_left_child_2","SUCCESS"
								 ],
				["avl-orig3.ss",7,"height","SUCCESS","get_max","SUCCESS",
				"insert","SUCCESS",	"double_left_child","SUCCESS",
				"double_right_child","SUCCESS",	"rotate_left_child","SUCCESS",
				"rotate_right_child","SUCCESS"],
			    ["bll.ss",2,"insert","SUCCESS",
							"delete","SUCCESS"],
				["bubble.ss",4, "id2","SUCCESS",
								"id3","SUCCESS",
								"bubble","SUCCESS",
								"bsort","SUCCESS",
								#"skip","SUCCESS"
								],
				["cll.ss",5,"test","SUCCESS",
						 "insert","SUCCESS",
						 "count_rest","SUCCESS",
						 "count","SUCCESS",
						 "delete","SUCCESS"],
				["complete.ss",5,"maxim","SUCCESS",
								 "minim","SUCCESS",
								 "height","SUCCESS",
								 "min_height","SUCCESS",
								 "insert","SUCCESS"],
				["dll.ss",10,"insert","SUCCESS",
							 "delete","SUCCESS",
							 "delete1","SUCCESS",
							 "test_del","SUCCESS",
							 "test_del2","SUCCESS",
							 "test_fold","SUCCESS",
							 "append","SUCCESS",
							 "append1","SUCCESS",
							 "f1","SUCCESS",
							 "f2","SUCCESS",
							 #"append3","SUCCESS",
							 #"find_last","SUCCESS",
							 #"id1","SUCCESS"	
							 ],
				["heaps.ss",5,"insert","SUCCESS",
								#"insert1","SUCCESS",
								"deleteoneel","SUCCESS",
								#"deleteoneel1","SUCCESS",
								"deleteone","SUCCESS",
								#"deleteone1","SUCCESS",
								"ripple","SUCCESS",
								#"ripple1","SUCCESS",
								"deletemax","SUCCESS",
								#"deletemax1","SUCCESS"
								],
				["insertion.ss",2,"insert","SUCCESS",
								  "insertion_sort","SUCCESS"],
				["ll.ss",10,"append","SUCCESS",
						  "ret_first","SUCCESS",
						  "get_next","SUCCESS",
						  "set_next","SUCCESS",
						  "set_null","SUCCESS",
						  "get_next_next","SUCCESS",
						  "insert","SUCCESS",
						  "delete","SUCCESS",
						  #"delete1","SUCCESS",
						  "create_list","SUCCESS",
						  "rev","SUCCESS",
						  #"reverse1","SUCCESS",
						  #"test","SUCCESS"
						  ],
				["merge.ss",5,"count","SUCCESS",
							  "split_func","SUCCESS",
							  #"div2","SUCCESS",
							  "merge_sort","SUCCESS",
							  "merge","SUCCESS",
							  "insert","SUCCESS",
							  #"merge_sort_1","SUCCESS"
							  ],
				["perfect.ss",5,"simple_insert","SUCCESS",
								"create","SUCCESS",
								"maxim","SUCCESS",
								"height","SUCCESS",
								"insert","SUCCESS"],
				["qsort.ss",3,	"partition","SUCCESS",
								"append_bll","SUCCESS",
								"qsort","SUCCESS"],
#				["qsort-tail.ss --combined-lemma-heuristic",2,"qsort","SUCCESS","partition1","SUCCESS"],
				["rb.ss",18,"rotate_case_3","SUCCESS",
							"case_2","SUCCESS",
							"rotate_case_3r","SUCCESS",
							"case_2r","SUCCESS",
							"is_red","SUCCESS",
							"is_black","SUCCESS",
							"del_6","SUCCESS",
							"del_6r","SUCCESS",
							"del_5","SUCCESS",
							"del_5r","SUCCESS",
							"del_4","SUCCESS",
							"del_4r","SUCCESS",
							"del_3","SUCCESS",
							"del_3r","SUCCESS",
							"del_2","SUCCESS",
							#"del_2r","SUCCESS",
							#"bh","SUCCESS",
							"remove_min","SUCCESS",
							"del","SUCCESS",
							#"test_insert","SUCCESS",
							#"node_error","SUCCESS",
							"insert","SUCCESS"],
				["selection.ss",3,"find_min","SUCCESS",
								"delete_min","SUCCESS",
								"selection_sort","SUCCESS"],
				["sll.ss",6,"insert","SUCCESS",
							"insert2","SUCCESS",
							"delete","SUCCESS",
							"get_tail","SUCCESS",
							"insertion_sort","SUCCESS",
							"id","SUCCESS"],
				["trees.ss",6,"append","SUCCESS",
								#"append1","SUCCESS",
								"count","SUCCESS",
								"flatten","SUCCESS",
								#"flatten1","SUCCESS",
								"insert","SUCCESS",
								#"insert1","SUCCESS",
								"remove_min","SUCCESS",
								#"remove_min1","SUCCESS",
								"delete","SUCCESS",
								#"delete1","SUCCESS"
								],
		        ["global1.ss",1,"increase","SUCCESS"],
                ["global2.ss",1,"increase","SUCCESS"],
                ["global3.ss",2,"increase","SUCCESS",
                                "increase_n","SUCCESS"],
                ["global4.ss",2,"increase_n","SUCCESS",
                                "main", "SUCCESS"],
                ["global5.ss",2,"increase","SUCCESS",
                                "decrease","SUCCESS"],
		        ["global-ll.ss",5,"insert_rec","SUCCESS",
                                  "delete_last_rec","SUCCESS",
                                  "insert","SUCCESS",
                                  "delete_last","SUCCESS",
                                  "main","SUCCESS"],
		        ["global-mutual-rec.ss",3,"decrease1","SUCCESS",
                                          "decrease2","SUCCESS",
										  "main","SUCCESS"]
				]

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
				        #["sleek8.slk","Valid.Fail.Valid.Valid.Valid.Valid.Valid.Valid.Valid.Fail.Valid.Valid.Valid.Valid.Fail.Valid.Fail."],
					["sleek9.slk","Valid."],
                                        ["imm/imm1.slk","Fail.Valid.Valid.Valid.Valid.Valid.Valid."],
			                ["imm/imm2.slk","Valid.Fail.Valid.Valid.Valid.Fail.Valid.Fail."],
			                ["imm/imm3.slk","Fail.Fail.Valid.Valid.Valid.Valid."],
			                ["imm/imm4.slk","Valid.Fail."]]				
			);
if($timings){
    $mainSum = 0.0;
    $childSum = 0.0;
    $totalSum = 0.0;
    $falseContextSum = 0;
}

open(LOGFILE, "> $output_file") || die ("Could not open $output_file.\n");
print "Starting sleek tests:\n";
	sleek_process_file();
print "Starting hip tests:\n";
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
 $format->set_num_format('0.00');
 $format->set_align('right');
 if($outp =~ m/Total verification time: (.*?) second/){
     $worksheet->write_number($row, $totalCol,"$1", $format);
     $totalSum = $totalSum + $1;
 }
 if($outp =~ m/Time spent in main process: (.*?) second/){
     $worksheet->write($row, $mainCol, "$1", $format);
     $mainSum = $mainSum + $1;
 }
 if($outp =~ m/Time spent in child processes: (.*?) second/){
     $worksheet->write($row, $childCol, "$1", $format);
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
			#print "$hip $script_arguments $exempl_path/hip/$test->[0] 2>&1 \n";
			$output = `$hip $script_arguments $exempl_path/hip/$test->[0] 2>&1`;
			print LOGFILE "\n======================================\n";
			print LOGFILE "$output";
			$limit = $test->[1]*2+2;
			#print "\nbegin"."$output"."end\n";
			for($i = 2; $i<$limit;$i+=2)
			{
				if($output !~ /Procedure $test->[$i].* $test->[$i+1]/)
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
		$t_list = $sleek_files{$param};	
		foreach $test (@{$t_list})
			{
			print "Checking $test->[0]\n";
			$output = `$sleek $script_arguments $exempl_path/sleek/$test->[0] 2>&1`;
			print LOGFILE "\n======================================\n";
	        print LOGFILE "$output";
			$pos = 0;
			$r = "";
			while($pos >= 0)
			{
				$i = index($output, "Valid",$pos);
				$j = index($output, "Fail",$pos);
				if ($i==-1 && $j == -1)
					{$pos = -1;}
				else
				{
					if(($i<$j || $j==-1)&& ($i>=0))
					{
						$pos=$i+3;
						$r = $r ."Valid.";
					}
					else
					{
						$pos=$j+3;
						$r = $r ."Fail.";
					}
				}
				if ($pos >=length($output)) 
				{$pos = -1;}
			}
			if($r !~ /^$test->[1]$/)
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
