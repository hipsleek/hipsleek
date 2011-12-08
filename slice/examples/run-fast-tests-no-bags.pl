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
            "lists" => \$lists,
			"slicing" => \$slicing,
			"small" => \$small
			);
@param_list = @ARGV;
if(($help) || (@param_list == ""))
{
	print "./run-fast-tests.pl [-help] [-root path_to_sleek] [-tp name_of_prover] [-log-timings] [-log-string string_to_be_added_to_the_log] [-copy-to-home21] hip_tr|hip|hip_imm|sleek [-flags \"arguments to be transmited to hip/sleek \"]\n";
	exit(0);
}

if($root){
	$exempl_path = "$root/slice/examples";
	$exec_path = "$root";
}
else
	{
		$exempl_path = ".";
		$exec_path = '../..';
	}

if($prover){
	%provers = ('cvcl' => 'cvcl', 'cvc3' => 'cvc3', 'omega' => 'omega', 'z3' => 'z3', 'zm' => 'zm', 
		'co' => 'co', 'isabelle' => 'isabelle', 'coq' => 'coq', 'mona' => 'mona', 'om' => 'om', 
		'oi' => 'oi', 'set' => 'set', 'cm' => 'cm', 'redlog' => 'redlog', 'rm' => 'rm', 'prm' => 'prm');
	if (!exists($provers{$prover})){
        print "./run-fast-tests.pl [-help] [-root path_to_sleek] [-tp name_of_prover] [-log-timings]  [-log-string string_to_be_added_to_the_log] [-copy-to-home21] hip_tr|hip sleek [-flags \"arguments to be transmited to hip/sleek \"]\n";
		print "\twhere name_of_prover should be one of the followings: 'cvcl', 'cvc3', 'omega', 'co', 'isabelle', 'coq', 'mona', 'om', 'oi', 'set', 'cm', 'redlog', 'z3', 'zm', 'rm' or 'prm' \n";
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
$error_count = 0;
$error_files = "";
$hip = "$exec_path/hip ";
$sleek = "$exec_path/sleek ";
$output_file = "log";
# list of file, nr of functions, function name, output, function name, output......
%hip_files=(
	"hip_tr"=>[["trees.ss",1,"insert"]],
    "hip_imm" =>[ 
        ["imm/bigint.ss",17, "",
		 "clone", "SUCCESS",
		 "int_value", "SUCCESS",
		 "bigint_of", "SUCCESS",
         "add_one_digit", "SUCCESS",
#		 "test", "SUCCESS", 
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
         "compare", "SUCCESS", #loop?
         "compare_int", "SUCCESS",
         "div_with_remainder", "SUCCESS"],
        ["imm/bigint_imm.ss",18, "",
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
        ["imm/bigint_imm-star.ss",17, "",
         "clone", "SUCCESS",
         "int_value", "SUCCESS",
         "bigint_of", "SUCCESS",
         "add_one_digit", "SUCCESS",
#		 "test", "SUCCESS", 
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
        ["imm/bigint-tight.ss",17, "",
         "clone", "SUCCESS",
         "int_value", "SUCCESS",
         "bigint_of", "SUCCESS",
         "add_one_digit", "SUCCESS",
#		 "test", "SUCCESS", 
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
        ["imm/bigint-tight-imm.ss",18, "",
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
        ["imm/bigint-tight-imm-star.ss",17, "",
         "clone", "SUCCESS",
         "int_value", "SUCCESS",
         "bigint_of", "SUCCESS",
         "add_one_digit", "SUCCESS",
#		 "test", "SUCCESS", 
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
        ["imm/append_imm.ss", 1, "", "append", "SUCCESS"],
        ["imm/kara.ss",1, "", "karatsuba_mult","SUCCESS"],
        ["imm/kara-imm.ss",1,  "", "karatsuba_mult","SUCCESS"],
        ["imm/kara-imm-star.ss",1,  "", "karatsuba_mult","SUCCESS"],
        ["imm/kara-tight.ss",1,  "", "karatsuba_mult","SUCCESS"],
        ["imm/kara-tight-imm.ss",1, "", "karatsuba_mult","SUCCESS"],
        ["imm/kara-tight-imm-star.ss",1,  "", "karatsuba_mult","SUCCESS"],
        ["imm/ll_imm.ss", 6, "", "length", "SUCCESS",
         "append", "SUCCESS",
         "get_next", "SUCCESS",
         "set_next", "SUCCESS",
         "get_next_next", "SUCCESS",
         "sumN", "SUCCESS"]],
	"hip" =>[
#	["2-3trees.ss",4,"make_node","SUCCESS","insert_left","SUCCESS","insert_middle","SUCCESS","insert_right","SUCCESS","insert","SUCCESS"],
				["append.ss",1,  "", "append","SUCCESS"],
				["append-tail.ss",1,  "","append","SUCCESS"],
				["avl-bind.ss",9,  "", "height","SUCCESS", "rotate_left","SUCCESS", "rotate_right","SUCCESS", "get_max","SUCCESS", "rotate_double_left","SUCCESS",
					"rotate_double_right","SUCCESS","build_avl1","SUCCESS","build_avl2","SUCCESS","insert","SUCCESS",
					#"insert_inline","SUCCESS","remove_min","SUCCESS","delete","SUCCESS"
					],
				["avl.ss",10,	 "",  "height","SUCCESS","rotate_left","SUCCESS","rotate_right","SUCCESS",
								 "get_max","SUCCESS","rotate_double_left","SUCCESS","rotate_double_right","SUCCESS",
								 "build_avl1","SUCCESS","build_avl2","SUCCESS",
								 "insert","SUCCESS","insert_inline","SUCCESS",
								 #"remove_min","SUCCESS","delete","SUCCESS"
								 ],
				["avl-orig-2.ss",7,  "","height","SUCCESS","get_max","SUCCESS","insert","SUCCESS",
								 "double_left_child","SUCCESS","double_right_child","SUCCESS",
								 "rotate_left_child","SUCCESS", "rotate_right_child","SUCCESS",
								 #"f","SUCCESS","g","SUCCESS","h","SUCCESS","k","SUCCESS","test","SUCCESS",  "rotate_left_child_2","SUCCESS"
								 ],
				["avl-orig3.ss",7, "", "height","SUCCESS","get_max","SUCCESS",
				"insert","SUCCESS",	"double_left_child","SUCCESS",
				"double_right_child","SUCCESS",	"rotate_left_child","SUCCESS",
				"rotate_right_child","SUCCESS"],
			    ["bll.ss",2,  "", "insert","SUCCESS",
							"delete","SUCCESS"],
				["bubble.ss",4,  "", "id2","SUCCESS",
								"id3","SUCCESS",
								"bubble","SUCCESS",
								"bsort","SUCCESS",
								#"skip","SUCCESS"
								],
				["cll.ss",5,  "", "test","SUCCESS",
						 "insert","SUCCESS",
						 "count_rest","SUCCESS",
						 "count","SUCCESS",
						 "delete","SUCCESS"],
				["complete.ss",5, "", "maxim","SUCCESS",
								 "minim","SUCCESS",
								 "height","SUCCESS",
								 "min_height","SUCCESS",
								 "insert","SUCCESS"],
				["dll.ss",10, "", "insert","SUCCESS",
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
				["heaps.ss",5, "", "insert","SUCCESS",
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
				["insertion.ss",2, "", "insert","SUCCESS",
								  "insertion_sort","SUCCESS"],
				["ll.ss",10, "", "append","SUCCESS",
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
				["merge.ss",5, "", "count","SUCCESS",
							  "split_func","SUCCESS",
							  #"div2","SUCCESS",
							  "merge_sort","SUCCESS",
							  "merge","SUCCESS",
							  "insert","SUCCESS",
							  #"merge_sort_1","SUCCESS"
							  ],
				["perfect.ss",5, "", "simple_insert","SUCCESS",
								"create","SUCCESS",
								"maxim","SUCCESS",
								"height","SUCCESS",
								"insert","SUCCESS"],
				["qsort.ss",3, "", "partition","SUCCESS",
								"append_bll","SUCCESS",
								"qsort","SUCCESS"],
        # goes into a loop with combined-lemma-heuristics still
				["qsort-tail.ss",2, "", "qsort","SUCCESS","partition1","SUCCESS"],
				["selection.ss",3, "", "find_min","SUCCESS",
								"delete_min","SUCCESS",
								"selection_sort","SUCCESS"],
				["sll.ss",6, "", "insert","SUCCESS",
							"insert2","SUCCESS",
							"delete","SUCCESS",
							"get_tail","SUCCESS",
							"insertion_sort","SUCCESS",
							"id","SUCCESS"],
				["trees.ss",6, "", "append","SUCCESS",
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
				["rb.ss",18, "", "rotate_case_3","SUCCESS",
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
							"remove_min","SUCCESS", #fixed duplicated false
							"del","SUCCESS",
							#"test_insert","SUCCESS",
							#"node_error","SUCCESS",
							"insert","SUCCESS"],
		        ["global1.ss",1, "", "increase","SUCCESS"],
                ["global2.ss",1, "", "increase","SUCCESS"],
                ["global3.ss",2, "", "increase","SUCCESS",
                                "increase_n","SUCCESS"],
                ["global4.ss",2, "", "increase_n","SUCCESS",
                                "main", "SUCCESS"],
                ["global5.ss",2, "", "increase","SUCCESS",
                                "decrease","SUCCESS"],
		        ["global-ll.ss",5, "", "insert_rec","SUCCESS",
                                  "delete_last_rec","SUCCESS",
                                  "insert","SUCCESS",
                                  "delete_last","SUCCESS",
                                  "main","SUCCESS"],
		        ["global-mutual-rec.ss",3, "", "decrease1","SUCCESS",
                                          "decrease2","SUCCESS",
										  "main","SUCCESS"]
				],
	"bags" =>[
        ["avl-all-1.ss", 8, "", "remove_min", "SUCCESS", "rotate_double_right", "SUCCESS", "rotate_double_left", "SUCCESS", 
         "get_max", "SUCCESS", "rotate_right", "SUCCESS", "rotate_left", "SUCCESS", "height", "SUCCESS"],
        ["avl-all.ss", 11, "", "delete", "SUCCESS", "delete_top", "SUCCESS", "remove_min", "SUCCESS","remove_max_add", "SUCCESS", ,"remove_min_add","SUCCESS",
         "insert", "SUCCESS", "rotate_double_left",  "SUCCESS", "get_max", "SUCCESS", "rotate_right", "SUCCESS", "rotate_left", "SUCCESS", "height", "SUCCESS"],
        ["avl-modular-2.ss", 16, "", "delete", "SUCCESS", "delete_top", "SUCCESS", "remove_min", "SUCCESS", "remove_max_add", "SUCCESS", "remove_min_add", "SUCCESS", 
         "insert", "SUCCESS", "rotate_double_right", "SUCCESS", "rotate_double_left", "SUCCESS", "get_max", "SUCCESS", "rotate_right", "SUCCESS", 
         "rotateleft", "SUCCESS", "diff_h_by_2", "SUCCESS", "diff_h_by_1", "SUCCESS", "eq_h", "SUCCESS", "less_h", "SUCCESS", "get_max_height_add1", "SUCCESS",
         "height","SUCCESS"],
        ["avl-modular-3.ss", 11, "", "delete", "SUCCESS", "delete_top", "SUCCESS", "remove_min", "SUCCESS","remove_max_add", "SUCCESS", ,"remove_min_add","SUCCESS",
         "insert", "SUCCESS", "rotate_double_left",  "SUCCESS", "get_max", "SUCCESS", "rotate_right", "SUCCESS", "rotate_left", "SUCCESS", "height", "SUCCESS"],
        ["avl-modular-2.ss", 17, "", "delete", "SUCCESS", "delete_top", "SUCCESS", "remove_min", "SUCCESS", "remove_max_add", "SUCCESS", "remove_min_add", "SUCCESS", 
         "insert", "SUCCESS", "rotate_double_right", "SUCCESS", "rotate_double_left", "SUCCESS", "get_max", "SUCCESS", "rotate_right", "SUCCESS", 
         "rotate_left", "SUCCESS", "diff_h_by_2", "SUCCESS", "diff_h_by_1", "SUCCESS", "eq_h", "SUCCESS", "less_h", "SUCCESS", "get_max_height_add1", "SUCCESS",
         "height","SUCCESS"],
        ["avl-modular-hei.ss", 14, "", "delete", "SUCCESS", "delete_top", "SUCCESS", "remove_min", "SUCCESS", "remove_max_add", "SUCCESS", "remove_min_add", "SUCCESS", 
         "insert", "SUCCESS", "rotate_double_right", "SUCCESS", "rotate_double_left", "SUCCESS", "get_max", "SUCCESS", "rotate_right", "SUCCESS", 
         "rotate_left", "SUCCESS", "rotate_right2", "SUCCESS", "rotate_left2", "SUCCESS", "height","SUCCESS"],
        ["avl-modular-new3.ss", 18, "", "delete", "SUCCESS", "delete_top", "SUCCESS", "remove_min", "SUCCESS", "remove_max_add", "SUCCESS", "remove_min_add", "SUCCESS", 
         "insert", "SUCCESS", "is_mem", "SUCCESS","rotate_double_right", "SUCCESS", "rotate_double_left", "SUCCESS", "get_max", "SUCCESS", "rotate_right", "SUCCESS", 
         "rotate_left", "SUCCESS", "diff_h_by_2", "SUCCESS", "diff_h_by_1", "SUCCESS", "eq_h", "SUCCESS", "less_h", "SUCCESS", "get_max_height_add1", "SUCCESS",
         "height","SUCCESS"],
        ["avl-modular-set.ss", 3 ,"", "delete", "SUCCESS", "delete_top", "SUCCESS", "remove_min", "SUCCESS"],
        ["avl-modular-siz.ss", 3 , "", "delete", "SUCCESS", "delete_top", "SUCCESS", "remove_min", "SUCCESS"],
        ["avl-modular.ss", 12, "", "delete", "SUCCESS", "delete_top", "SUCCESS", "remove_min", "SUCCESS", "remove_max_add", "SUCCESS", "remove_min_add", "SUCCESS", 
         "insert", "SUCCESS", "rotate_double_right", "SUCCESS", "rotate_double_left", "SUCCESS", "get_max", "SUCCESS", "rotate_right", "SUCCESS", 
         "rotate_left", "SUCCESS", "height","SUCCESS"],
        ["avl.scp.ss", 19 ,"", "delete", "SUCCESS", "remove_min", "SUCCESS", "insert_inline1", "SUCCESS", "insert_inline", "SUCCESS", "insert1", "SUCCESS", "insert", "SUCCESS",
         "build_avl2", "SUCCESS", "build_avl1", "SUCCESS", "rotate_double_right1", "SUCCESS", "rotate_double_right", "SUCCESS", "rotate_double_left1", "SUCCESS",
         "rotate_double_left", "SUCCESS", "get_max", "SUCCESS", "rotate_right1", "SUCCESS", "rotate_right", "SUCCESS", "rotate_left1", "SUCCESS", "rotate_left", "SUCCESS",
         "height1", "SUCCESS", "height", "SUCCESS"],
        ["avl.ss",  8, "", "insert_inline", "SUCCESS",  "insert", "SUCCESS", "rotate_double_right", "SUCCESS", "rotate_double_left", "SUCCESS", "get_max", "SUCCESS", 
         "rotate_right", "SUCCESS", "rotate_left", "SUCCESS","height", "SUCCESS"],
        ["bubble.ss", 3, "", "bsort1", "SUCCESS", "bubble1", "SUCCESS", "id1", "SUCCESS"],
        ["cll.ss", 4, "", "delete2", "SUCCESS", "delete", "SUCCESS", "count", "SUCCESS", "count_rest", "SUCCESS"],
        ["dll.ss", 2, "", "append", "SUCCESS", "insert", "SUCCESS"],
        ["insertion.ss", 3, "", "insertion_sort", "SUCCESS", "delete", "SUCCESS", "insert", "SUCCESS"],
        ["ll.ss", 4, "reverse1", "SUCCESS", "delete1", "SUCCESS", "insert", "SUCCESS", "append", "SUCCESS"],
        ["merge-modular.ss", 5, "", "insert1", "SUCCESS", "merge1", "SUCCESS", "merge_sort1", "SUCCESS", "split1", "SUCCESS", "count1", "SUCCESS"],
        ["merge.ss", 5, "", "insert1", "SUCCESS", "merge1", "SUCCESS", "merge_sort1", "SUCCESS", "split1", "SUCCESS", "count1", "SUCCESS"],
        ["qsort.ss", 3, "", "qsort1", "SUCCESS", "append_bll1", "SUCCESS", "partition1", "SUCCESS"],
        ["rb_bags.ss", 19, "", "insert_1", "SUCCESS", "del_1", "SUCCESS", "remove_min_1", "SUCCESS", "del_2r_1", "SUCCESS", "del_2_1", "SUCCESS", "del_3r_1", "SUCCESS",
         "del_3_1", "SUCCESS", "del_4r_1", "SUCCESS", "del_4_1", "SUCCESS", "del_5r_1", "SUCCESS", "del_5_1", "SUCCESS", "del_6r_1", "SUCCESS", "del_6_1", "SUCCESS",
         "is_black_1", "SUCCESS", "is_red_1", "SUCCESS", "case_2r_1", "SUCCESS", "rotate_case_3r_1", "SUCCESS", "case_2_1", "SUCCESS", "rotate_case_3_1", "SUCCESS"],
        ["rb.scp.ss", 38, "", "insert_1", "SUCCESS", "insert", "SUCCESS", "del_1", "SUCCESS", "del", "SUCCESS", "remove_min_1", "SUCCESS", "remove_min", "SUCCESS", 
         "del_2r_1", "SUCCESS", "del_2r", "SUCCESS", "del_2_1", "SUCCESS", "del_2", "SUCCESS", "del_3r_1", "SUCCESS", "del_3r", "SUCCESS", "del_3_1", "SUCCESS", 
         "del_3", "SUCCESS", "del_4r_1", "SUCCESS", "del_4r", "SUCCESS", "del_4_1", "SUCCESS", "del_4", "SUCCESS", "del_5r_1", "SUCCESS", "del_5r", "SUCCESS", 
         "del_5_1", "SUCCESS", "del_5", "SUCCESS", "del_6r_1", "SUCCESS", "del_6r", "SUCCESS", "del_6_1", "SUCCESS", "del_6", "SUCCESS", "is_black_1", "SUCCESS", 
         "is_black", "SUCCESS", "is_red_1", "SUCCESS", "is_red", "SUCCESS", "case_2r_1", "SUCCESS", "case_2r", "SUCCESS", "rotate_case_3r_1", "SUCCESS", 
         "rotate_case_3r", "SUCCESS", "case_2_1", "SUCCESS", "case_2", "SUCCESS", "rotate_case_3_1", "SUCCESS", "rotate_case_3", "SUCCESS"],
        ["selection.ss", 3, "", "selection_sort", "SUCCESS", "delete_min", "SUCCESS", "find_min", "SUCCESS"],
        ["trees.ss", 5, "", "delete1", "SUCCESS", "remove_min1", "SUCCESS", "insert1", "SUCCESS", "flatten1", "SUCCESS", "append1", "SUCCESS"]],
    "term" => [
        ["e1.ss", 1, "", "loop", "SUCCESS"],
        ["ex1.ss", 2, "", "length", "SUCCESS", "app2", "SUCCESS"],
        ["ex10.ss", 1, "", "loop", "SUCCESS"],
        ["ex11.ss", 1, "", "bsearch", "SUCCESS"],
        ["ex12.ss", 1, "", "loop", "SUCCESS"],
        ["ex12a.ss", 1, "", "loop", "SUCCESS"],
        ["ex12b.ss", 1, "", "loop", "SUCCESS"],
        ["ex12c.ss", 1, "", "loop", "SUCCESS"],
        ["ex13.ss", 1, "", "loop", "SUCCESS"],
        ["ex14.ss", 1, "", "loop", "SUCCESS"],
        ["ex14a.ss", 1, "", "loop", "SUCCESS"],
        ["ex15.ss", 2, "", "loop", "SUCCESS", "f", "SUCCESS"],
        ["ex16.ss", 1, "", "loop", "SUCCESS"],
        ["ex2.ss", 1, "", "loop", "SUCCESS"],
        ["ex3.ss", 1, "", "loop", "SUCCESS"],
        ["ex4.ss", 1, "", "inc_loop", "SUCCESS"],
        ["ex5.ss", 1, "", "foo", "SUCCESS"],
        ["ex6.ss", 1, "", "Ack", "SUCCESS"],
        ["ex7.ss", 3, "", "loop_aux1", "SUCCESS", "loop_aux", "SUCCESS", "loop", "SUCCESS"],
        ["ex7a.ss", 1, "", "loop", "SUCCESS"],
        ["ex8.ss", 2, "", "loop2", "SUCCESS", "loop", "SUCCESS"],
        ["ex9.ss", 1, "", "loop", "SUCCESS"],
        ["ex9a.ss", 1, "", "loop", "SUCCESS"],
        ["mutual.ss", 2, "", "g", "SUCCESS", "f", "SUCCESS"]
    ],
    "lists" => [
        # ["allz1.ss", 0, ""],
        # ["allz2.ss", 0, ""],
        # ["allz3.ss", 0, ""],
        # ["allz4.ss", 0, ""],
        ["demo.ss", 11, "",, "reverse", "SUCCESS", "create_list", "SUCCESS", "delete_val", "SUCCESS", "delete", "SUCCESS", "insert", "SUCCESS", "get_next_next", "SUCCESS", "set_null", "SUCCESS", "set_next", "SUCCESS", "get_next", "SUCCESS", "ret_first", "SUCCESS", "append", "SUCCESS"],
        ["demo2.ss", 3, "", "app_rev", "SUCCESS", "reverse", "SUCCESS", "append", "SUCCESS"],
        ["err-coq.ss", 2, "", "ret_first2", "SUCCESS", "ret_first", "SUCCESS"],
        ["ll.ss", 11, "", "reverse", "SUCCESS", "create_list", "SUCCESS", "delete_val", "SUCCESS", "delete", "SUCCESS", "insert", "SUCCESS", "get_next_next", "SUCCESS", "set_null", "SUCCESS", "set_next", "SUCCESS", "get_next", "SUCCESS", "ret_first", "SUCCESS", "append", "SUCCESS"],
        ["ll_bak.ss", 11, "", "reverse", "SUCCESS", "create_list", "SUCCESS", "delete_val", "SUCCESS", "delete", "SUCCESS", "insert", "SUCCESS", "get_next_next", "SUCCESS", "set_null", "SUCCESS", "set_next", "SUCCESS", "get_next", "SUCCESS", "ret_first", "SUCCESS", "append", "SUCCESS"],
        ["ll_bak2.ss", 11, "", "reverse", "SUCCESS", "create_list", "SUCCESS", "delete_val", "SUCCESS", "delete", "SUCCESS", "insert", "SUCCESS", "get_next_next", "SUCCESS", "set_null", "SUCCESS", "set_next", "SUCCESS", "get_next", "SUCCESS", "ret_first", "SUCCESS", "append", "SUCCESS"],
        ["ll_bak3.ss", 11, "", "reverse", "SUCCESS", "create_list", "SUCCESS", "delete_val", "SUCCESS", "delete", "SUCCESS", "insert", "SUCCESS", "get_next_next", "SUCCESS", "set_null", "SUCCESS", "set_next", "SUCCESS", "get_next", "SUCCESS", "ret_first", "SUCCESS", "append", "SUCCESS"],
        ["ll_nolists.ss", 11, "", "reverse", "SUCCESS", "create_list", "SUCCESS", "delete_val", "SUCCESS", "delete", "SUCCESS", "insert", "SUCCESS", "get_next_next", "SUCCESS", "set_null", "SUCCESS", "set_next", "SUCCESS", "get_next", "SUCCESS", "ret_first", "SUCCESS", "append", "SUCCESS"],
        ["ll_test1.ss", 1, "", "reverse", "SUCCESS"],
        ["ll_test2.ss", 1, "", "delete", "SUCCESS"],
        # ["ll_test3.ss", , "", ],
        ["ll_test4.ss", 1, "", "test", "SUCCESS"],
        ["ll_test5.ss", 1, "", "delete_val", "SUCCESS"],
        ["lr.ss", 2, "", "my_rev", "SUCCESS", "reverse", "SUCCESS"],
        ["lrev-bug.ss", 1, "", "lrev", "SUCCESS"],
        ["lrev.ss", 1, "", "lrev", "SUCCESS"],
        # ["lz_bak.ss", 0, ""],
        # ["lz_bak2.ss", 0, ""],
        ["merge.ss", 1, "", "merge", "SUCCESS"],
        ["merge1.ss", 1, "", "merge", "SUCCESS"],
        ["merge2.ss", 1, "", "merge", "SUCCESS"],
        ["merge3.ss", 1, "", "merge", "SUCCESS"],
        ["mk_zero.ss", 1, "", "mk_zero", "SUCCESS"],
        ["perm.ss", 1, "", "append", "SUCCESS"]
    ],
	"slicing" => [
		["avl_size_height_0_link.ss", 11, "",  
			"height", "SUCCESS",
			"rotate_left", "SUCCESS",
			"rotate_right", "SUCCESS",
			"get_max", "SUCCESS",
			"rotate_double_left", "SUCCESS",
			"rotate_double_right", "SUCCESS",
			"build_avl1", "SUCCESS",
			"build_avl2", "SUCCESS",
			"insert", "SUCCESS",
			"insert_inline", "SUCCESS",
			"merge", "SUCCESS"
			#"remove_min","SUCCESS",
			#"delete","SUCCESS"
		],
		["avl_size_height_1_link.ss", 11, "",  
			"height", "SUCCESS",
			"rotate_left", "SUCCESS",
			"rotate_right", "SUCCESS",
			"get_max", "SUCCESS",
			"rotate_double_left", "SUCCESS",
			"rotate_double_right", "SUCCESS",
			"build_avl1", "SUCCESS",
			"build_avl2", "SUCCESS",
			"insert", "SUCCESS",
			"insert_inline", "SUCCESS",
			"merge", "SUCCESS"
			#"remove_min","SUCCESS",
			#"delete","SUCCESS"
		],
		["avl_size_height_bal_1_link.ss", 7, "",  
			"height", "SUCCESS",
			"get_max", "SUCCESS",
			"insert", "SUCCESS",
			"double_left_child", "SUCCESS",
			"double_right_child", "SUCCESS",
			"rotate_left_child", "SUCCESS",
			"rotate_right_child", "SUCCESS"
		],
		["avl_size_height_bal_2_links.ss", 7, "",  
			"height", "SUCCESS",
			"get_max", "SUCCESS",
			"insert", "SUCCESS",
			"double_left_child", "SUCCESS",
			"double_right_child", "SUCCESS",
			"rotate_left_child", "SUCCESS",
			"rotate_right_child", "SUCCESS"
		],
		["avl_size_height_bal_5_links.ss", 7, "",  
			"height", "SUCCESS",
			"get_max", "SUCCESS",
			"insert", "SUCCESS",
			"double_left_child", "SUCCESS",
			"double_right_child", "SUCCESS",
			"rotate_left_child", "SUCCESS",
			"rotate_right_child", "SUCCESS"
		],
		["avl_size_height_bal_6_links.ss", 7, "",  
			"height", "SUCCESS",
			"get_max", "SUCCESS",
			"insert", "SUCCESS",
			"double_left_child", "SUCCESS",
			"double_right_child", "SUCCESS",
			"rotate_left_child", "SUCCESS",
			"rotate_right_child", "SUCCESS"
		],
		["bubble_size_bags_0_link.ss", 2, "",  
			"bsort", "SUCCESS",
			"bubble", "SUCCESS"
		],
		["qsort_size_bags_0_link.ss", 3, "",  
			"qsort1", "SUCCESS",
			"append_bll1", "SUCCESS",
		    "partition1", "SUCCESS"
		],
		["msort_size_bags_0_link.ss", 5, "",  
			"insert1", "SUCCESS",
			"merge1", "SUCCESS",
		    "merge_sort1", "SUCCESS",
		    "split1", "SUCCESS",
		    "count1", "SUCCESS"
		],
		["complete_size_minheight_1_link.ss", 5, "",  
			"insert", "SUCCESS",
			"min_height", "SUCCESS",
		    "height", "SUCCESS",
		    "minim", "SUCCESS",
		    "maxim", "SUCCESS"
		],
		["heaps_size_maxelem_0_link.ss", 5, "",  
			"deletemax", "SUCCESS",
			"ripple", "SUCCESS",
		    "deleteone", "SUCCESS",
		    "deleteoneel", "SUCCESS",
		    "insert", "SUCCESS"
		],
	],
	"small" => [
		["append.ss", 1,  "",
		 "append", "SUCCESS"
		],
		["append-tail.ss", 1,  "",
		 "append", "SUCCESS"
		],
		["bll.ss", 2,  "",
		 "insert", "SUCCESS",
		 "delete", "SUCCESS"
		],
		["cll.ss", 5,  "",
		 "test", "SUCCESS",
		 "insert", "SUCCESS",
		 "count_rest", "SUCCESS",
		 "count", "SUCCESS",
		 "delete", "SUCCESS"
		],
		["dll.ss", 10, "",
		 "insert","SUCCESS",
		 "delete","SUCCESS",
		 "delete1","SUCCESS",
		 "test_del","SUCCESS",
		 "test_del2","SUCCESS",
		 "test_fold","SUCCESS",
		 "append","SUCCESS",
		 "append1","SUCCESS",
		 "f1","SUCCESS",
		 "f2","SUCCESS",
		],
		["insertion.ss", 2, "",
		 "insert","SUCCESS",
		 "insertion_sort","SUCCESS"
		],
		["ll.ss", 10, "",
		 "append","SUCCESS",
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
		["perfect.ss", 5, "",
		 "simple_insert","SUCCESS",
		 "create","SUCCESS",
		 "maxim","SUCCESS",
		 "height","SUCCESS",
		 "insert","SUCCESS"
		],
		["selection.ss", 3, "",
		 "find_min","SUCCESS",
		 "delete_min","SUCCESS",
		 "selection_sort","SUCCESS"
		],
		["sll.ss", 6, "",
		 "insert","SUCCESS",
		 "insert2","SUCCESS",
		 "delete","SUCCESS",
		 "get_tail","SUCCESS",
		 "insertion_sort","SUCCESS",
		 "id","SUCCESS"
		],
		["trees.ss", 6, "",
		 "append","SUCCESS",
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
		 ["global1.ss", 1, "",
		  "increase","SUCCESS"
		 ],
         ["global2.ss", 1, "", "increase","SUCCESS"],
         ["global3.ss", 2, "",
		  "increase","SUCCESS",
          "increase_n","SUCCESS"
		 ],
         ["global4.ss", 2, "",
		  "increase_n","SUCCESS",
          "main", "SUCCESS"
		 ],
         ["global5.ss", 2, "",
		  "increase","SUCCESS",
          "decrease","SUCCESS"],
		 ["global-ll.ss", 5, "",
		  "insert_rec","SUCCESS",
          "delete_last_rec","SUCCESS",
          "insert","SUCCESS",
          "delete_last","SUCCESS",
          "main","SUCCESS"
		 ],
		 ["global-mutual-rec.ss", 3, "",
		  "decrease1","SUCCESS",
          "decrease2","SUCCESS",
		  "main","SUCCESS"
		 ]
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
                  # slow in sleek8.slk due to search
				  ["sleek8.slk","Valid.Valid.Valid.Valid.Valid.Valid.Valid.Valid.Valid.Fail.Valid.Valid.Valid.Valid.Fail.Valid.Fail."],
					["sleek9.slk","Valid.Fail.Valid.Valid."],
                                        ["imm/imm1.slk","Fail.Valid.Valid.Valid.Valid.Valid."],
			                #["imm/imm2.slk","Valid.Fail.Valid.Valid.Valid.Fail.Valid.Fail."],
			                ["imm/imm2.slk","Fail.Valid.Fail.Valid.Fail."],
			                ["imm/imm3.slk","Fail.Fail.Valid.Valid.Valid.Valid."],
			                ["imm/imm4.slk","Valid.Fail."],
			                ["imm/imm-hard.slk","Valid.Valid.Valid.Valid.Valid.Valid.Valid.Valid.Valid.Valid.Valid."]]				
			);

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
        if ("$param" =~ "hip") {
            $exempl_path_full = "$exempl_path/hip";
            print "Starting hip tests:\n";
        }elsif("$param" =~ "bags") {
            $exempl_path_full = "$exempl_path/bags";
            print "Starting bags tests:\n";
        }elsif ("$param" =~ "term") {
            $exempl_path_full = "$exempl_path/term";
            print "Starting term tests:\n";
        }elsif ("$param" =~ "lists") {
            $exempl_path_full = "$exempl_path/list_examples";
            print "Starting term tests:\n";
        }elsif ("$param" =~ "slicing") {
            $exempl_path_full = "$exempl_path/slicing_examples";
            print "Starting slicing tests:\n";
        }elsif ("$param" =~ "small") {
            $exempl_path_full = "$exempl_path/slicing_small_examples";
            print "Starting slicing tests for small examples:\n";
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
      if ("$param" =~ "sleek") {
          print "Starting sleek tests:\n";
          $exempl_path_full = "$exempl_path/sleek";
      }
      $t_list = $sleek_files{$param};	
      foreach $test (@{$t_list})
			{
			print "Checking $test->[0]\n";
			$output = `$sleek $script_arguments $exempl_path_full/$test->[0] 2>&1`;
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
