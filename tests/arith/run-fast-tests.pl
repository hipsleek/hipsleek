#!/usr/bin/perl

use File::Find;
use File::Basename;
use Getopt::Long;
use Sys::Hostname;
use File::NCopy;
use File::Path 'rmtree';
use Cwd;

GetOptions( "stop"  => \$stop,
			"help" => \$help,
			"root=s" => \$root,
			"tp=s" => \$prover,
			"flags=s" => \$flags,
			"copy-to-home21" => \$home21 
			);
@param_list = @ARGV;
if(($help) || (@param_list == ""))
{
	print "./run-fast-tests.pl [-help] [-root path_to_sleek] [-tp name_of_prover] hip_tr|hip sleek [-flags \"arguments to be transmited to hip/sleek \"]  [-copy-to-home21]\n";
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
		print "./run-fast-tests.pl [-help] [-root path_to_sleek] [-tp name_of_prover] hip_tr|hip sleek [-flags \"arguments to be transmited to hip/sleek \"]  [-copy-to-home21]\n";
		print "\twhere name_of_prover should be one of the followings: 'cvcl', 'cvc3', 'omega', 'co', 'isabelle', 'coq', 'mona', 'om', 'oi', 'set', 'cm', 'redlog', 'rm' or 'prm' \n";
		exit(0);
	}
}else{
	$prover = "omega";
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

@excl_files = ();
$error_count = 0;
$error_files = "";
$hip = "$exec_path/hip.opt ";
$sleek = "$exec_path/sleek.opt ";
$output_file = "log";
# list of file, nr of functions, function name, output, function name, output......
%hip_files=(
	"hip_tr"=>[["trees.ss",1,"insert"]],
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
				]);
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
exit(0);


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
			#print "$output";
			for($i = 2; $i<$limit;$i+=2)
			{
				if($output !~ /Procedure $test->[$i].* $test->[$i+1]/)
				{
			 		$error_count++;
					$error_files=$error_files."error at: $test->[0] $test->[$i]\n";
					print "error at: $test->[0] $test->[$i]\n";
				}
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
		}
	}
}
