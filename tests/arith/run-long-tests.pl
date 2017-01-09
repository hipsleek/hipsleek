#!/usr/bin/perl

use File::Find;
use File::Basename;
use Getopt::Long;
$module = "sleekex";
$cvs_module_rep = "/home/nguyenh2/cvs-repo";
$log_file = "long_test_result";
$proof_dump = "last_proof_dump";
$output_file = $log_file;
$temp_output_dir = ".";
$crt = system "pwd";
$hip = '';
$sleek = '';
$examples_path_working = "sleekex/examples/working";
$examples_path_working_bags = "sleekex/examples/working_bags";
$examples_path_working_mult_specs = "sleekex/examples/working_mult_specs";
# list of file, nr of functions, function name, output, function name, output......
%hip_files=(
		"append.ss"=>["",1,"append","SUCCESS"],
		"append-tail.ss"=>["--combined-lemma-heuristic",1,"append","SUCCESS"],#
		"bll.ss"=>["",2,"insert","SUCCESS","delete","SUCCESS"],
		"bubble.ss"=>["",4,		"id2","SUCCESS",
								"id3","SUCCESS",
								"bubble","SUCCESS",
								"bsort","SUCCESS",
								#"skip","SUCCESS"
								],
		"cll.ss"=>["",5, "test","SUCCESS",
						 "insert","SUCCESS",
						 "count_rest","SUCCESS",
						 "count","SUCCESS",
						 "delete","SUCCESS"],
		"complete.ss"=>["",5,"maxim","SUCCESS",
								 "minim","SUCCESS",
								 "height","SUCCESS",
								 "min_height","SUCCESS",
								 "insert","SUCCESS"],
		"dll.ss"=>["",10,"insert","SUCCESS",
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
		"heaps.ss"=>["",5,"insert","SUCCESS",
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
		"insertion.ss"=>["",2,"insert","SUCCESS",
								  "insertion_sort","SUCCESS"],
		"ll.ss"=>["",10,"append","SUCCESS",
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
		"merge.ss"=>["",5,"count","SUCCESS",
							  "split_func","SUCCESS",
							  #"div2","SUCCESS",
							  "merge_sort","SUCCESS",
							  "merge","SUCCESS",
							  "insert","SUCCESS",
							  #"merge_sort_1","SUCCESS"
							  ],
		"perfect.ss"=>["",5,"simple_insert","SUCCESS",
								"create","SUCCESS",
								"maxim","SUCCESS",
								"height","SUCCESS",
								"insert","SUCCESS"],
		
		"qsort.ss"=>["",3,	"partition","SUCCESS",
								"append_bll","SUCCESS",
								"qsort","SUCCESS"],
		"qsort-tail.ss"=>["--combined-lemma-heuristic",2,"qsort","SUCCESS",
									"partition1","SUCCESS"],
		"rb.ss"=>["",18,"rotate_case_3","SUCCESS",
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
		"selection.ss"=>["",3,"find_min","SUCCESS",
								"delete_min","SUCCESS",
								"selection_sort","SUCCESS"],
		"sll.ss"=>["",6,"insert","SUCCESS",
							"insert2","SUCCESS",
							"delete","SUCCESS",
							"get_tail","SUCCESS",
							"insertion_sort","SUCCESS",
							"id","SUCCESS"],
		"trees.ss"=>["",6,"append","SUCCESS",
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
		"avl-bind.ss"=>["",9,"height","SUCCESS", 
							  "rotate_left","SUCCESS", 
							  "rotate_right","SUCCESS", 
							  "get_max","SUCCESS", 
							  "rotate_double_left","SUCCESS",
							  "rotate_double_right","SUCCESS",
							  "build_avl1","SUCCESS",
							  "build_avl2","SUCCESS",
							  "insert","SUCCESS",
							  #"node_error","SUCCESS",
							  #"insert_inline","SUCCESS",
							  #"remove_min","SUCCESS",
							  #"delete","SUCCESS"
							  ],							
								);
			#	["2-3trees.ss",4,"make_node","SUCCESS","insert_left","SUCCESS","insert_middle","SUCCESS","insert_right","SUCCESS","insert","SUCCESS"],
	
				
			
			#	["avl.ss",13,	 "height","SUCCESS","rotate_left","SUCCESS","rotate_right","SUCCESS",
			#					 "get_max","SUCCESS","rotate_double_left","SUCCESS","rotate_double_right","SUCCESS",
			#					 "build_avl1","SUCCESS","build_avl2","SUCCESS","node_error","SUCCESS",
			#					 "insert","SUCCESS","insert_inline","SUCCESS","remove_min","SUCCESS","delete","SUCCESS"],
			#	["avl-orig-2.ss",8,"height","SUCCESS","get_max","SUCCESS","insert","SUCCESS",
			#					 "double_left_child","SUCCESS","double_right_child","SUCCESS",
			#					 "rotate_left_child","SUCCESS", "rotate_right_child","SUCCESS",
			#					 "f","SUCCESS","g","SUCCESS","h","SUCCESS","k","SUCCESS","test",
			#					 "SUCCESS","rotate_left_child_2","SUCCESS"],
			 
%sleek_files=(
		"sleek.slk"=>[["Valid.Valid.Valid.Fail.Valid."],["omega"],[""]],
		"sleek1.slk"=>[["Valid."],["omega","mona"],[""]],
		"sleek10.slk"=>[["Valid.Fail."],["omega","mona"],[""]],
		"sleek2.slk"=>[["Fail.Valid.Fail.Fail.Valid.Valid.Valid.Fail."],["omega"],[""]],
		"sleek3.slk"=>[["Fail.Fail.Fail."],["omega"],[""]],
		"sleek4.slk"=>[["Valid.Valid."],["omega"],[""]],
		"sleek6.slk"=>[["Valid.Valid."],["omega","mona"],[""]],
		"sleek7.slk"=>[["Valid.Valid.Valid.Fail.Valid.Valid.Valid.Valid.Fail.Valid."],["omega","mona"],[""]],
		"sleek8.slk"=>[["Valid.Fail.Valid.Valid.Valid.Valid.Valid.Valid.Valid.Fail.Valid.Valid.Valid.Valid.Fail.Valid.Fail."],["omega","mona"],[""]],
		"sleek9.slk"=>[["Valid."],["omega"],[""]]);

		
open(LOGFILE, ">> $log_file") || die ("Could not open $log_file.\n");
open(PROOFLOGFILE, "> $proof_dump") || die ("Could not open $proof_dump.\n");

$aux = `export PATH=$PATH:/usr/local/bin`;
$aux = `date`;
print LOGFILE "-----------------\n $aux \n";

$aux = `pwd`;
print LOGFILE "$aux";


@yest = `date +"%Y/%m/%d" -d "yesterday"`;$yest  = pop(@yest);$yest  = substr($yest, 0, 10);

@tomorrow = `date +"%Y/%m/%d" -d "tomorrow"`;$tomorrow = pop (@tomorrow);$tomorrow  = substr($tomorrow, 0, 10);

@today =`date +"%Y/%m/%d"`;$today = pop (@today);$today  = substr($today, 0, 10);

$aux = join "", 'cvs -d ',$cvs_module_rep,' rlog -S -d"', $yest, ' < ', $tomorrow, '" ',$module,' | grep "', $yest, '" | wc -l';
@wc = `$aux`;$wc = pop(@wc);

#if(not($wc>0)) {
#		print LOGFILE "$yest no changes\n";
#		print LOGFILE "----------\n";
#		close(LOGFILE);
#		exit(0);
#	}
	
print LOGFILE "$yest found changes $wc  deleting subdir: $temp_output_dir/$module\n";
$aux ="rm -r $temp_output_dir/$module";
$aux = system $aux;
$aux = system "cvs -d $cvs_module_rep checkout sleekex";
if ($aux!=0){
		print LOGFILE "error checkingout module $module\n";
		cleanup();
		print LOGFILE "----------\n";
		close(LOGFILE);
		exit(0);		
	}
print LOGFILE "cvs checked out $module\n";

$aux = system "cd $module/xml; make";
if ($aux!=0){
		print LOGFILE "error making the xml\n";
		cleanup();
		print LOGFILE "----------\n";	
		close(LOGFILE);
		exit(0);		
	}
$aux =system "cd $module; make hip.opt;make sleek.opt";
if ($aux!=0){
		print LOGFILE "error making sleekex\n";
		cleanup();
		print LOGFILE "----------\n";	
		close(LOGFILE);
		exit(0);		
	}
	
#if ($optimized) {
$hip = "$hip".'.opt';
$sleek ="$sleek".'.opt -ee -filter';
#}

$error_count = 0;
$error_files = "";

print LOGFILE "Making... OK\n Starting sleek tests:\n";
$sleek = "../../../sleek.opt";
$pth = "$examples_path_working/sleek";
call_find_s();

print LOGFILE "Starting hip tests:\n";
$hip = "../../../hip.opt";
$tp = "omega";$pth = "$examples_path_working/hip";
call_find_h();
$tp = "mona"; $pth = "$examples_path_working/hip";
call_find_h();

$hip = "../../hip.opt";
$tp = "mona";$pth = "$examples_path_working_bags";
call_find_h();
$tp = "isabelle";$pth = "$examples_path_working_bags";
call_find_h();

$tp = "mona";$pth = "$examples_path_working_mult_specs";
call_find_h();
$tp = "isabelle";$pth = "$examples_path_working_mult_specs";
call_find_h();

if ($error_count > 0) {
 print LOGFILE "Total number of errors: $error_count in files: $error_files.\n";
}
else {
 print LOGFILE "No errors, all is fine.\n";
}


cleanup();
print LOGFILE "----------\n";	
close(LOGFILE);
exit(0);


sub call_find_s
{
print LOGFILE "using $tp\n";
find(\&sleek_process_file, "$pth");
}

sub call_find_h
{
print LOGFILE "using $tp\n";
find(\&hip_process_file, "$pth");
}

sub cleanup
{
	print LOGFILE "cleanup: removing checkedout dir: $temp_output_dir/$module\n";
	$aux ="rm -r $temp_output_dir/$module";
	$aux = system $aux;
}

sub hip_process_file {
  $file = $_;

  my $ext = (fileparse($file,'\..*'))[2];

  if ($ext eq ".ss") {
	print LOGFILE "Checking $file\n";
	$parameters = "";
	if($hip_files{$file}) {$parameters = $hip_files{$file}->[0];}
	print PROOFLOGFILE "\n$hip -tp $tp $file $parameters\n\n";
    my $output = "";
	eval {
        local $SIG{ALRM} = sub { `pkill hip;pkill mona;pkill poly;pkill hip`;die "alarm clock restart" };
        alarm 1800;
		$output = `$hip -tp $tp $file $parameters 2>&1`;
        alarm 0;
    };
    if ($@ and $@ =~ /alarm clock restart/) {  $error_count++;$error_files = $error_files . "\n " . $file . " timed out ";print LOGFILE "!!!!!!!timed out\n"; print "!!!!!!!timed out"; }
	else {
		print PROOFLOGFILE "$output";
		#print LOGFILE "\n======================================\n";
		#print LOGFILE "$output";

		if($hip_files{$file}) {
			$count = 0;
			$count++ while $output =~ /Procedure/g;
			if ($count == $hip_files{$file}->[1])
			{
				$limit = $hip_files{$file}->[1]*2+2;
				#print "$output";
				for($i = 2; $i<$limit;$i+=2)
				{
					if($output !~ /Procedure $hip_files{$file}->[$i].* $hip_files{$file}->[$i+1]/)
					{
						print LOGFILE "Error found in $file $hip_files{$file}->[$i]\n";
				 		$error_count++;
						$error_files=$error_files."error at: $hip_files{$file}->[0] $hip_files{$file}->[$i]\n";
					}
				}
			}else{
				print LOGFILE "Error found in $file, the procedure count has changed, expected $hip_files{$file}->[1], got $count \n";
				$error_count++;
				$error_files=$error_files."the procedure count has changed\n";}
		}
		else{
		if (($output =~ m/.*error.*/i)||($output =~ m/.*fail.*/i)) {
		  print LOGFILE "Error found in the newly added file $file\n";
		  $error_count++;
		  $error_files = $error_files . " " . $file;
		  if ($stop) {
			exit(0);
		  }
		}
		}
	}
  }
}

sub sleek_process_file  {
  $file = $_;

  my $ext = (fileparse($file,'\..*'))[2];

  if ($ext eq ".slk") {
      my $output = "";
	  if($sleek_files{$file}) {$tp_list = $sleek_files{$file}->[1]}
	  else {$tp_list = ["omega","mona"];}
	  foreach $tp (@$tp_list)
	 {
	  print LOGFILE "Checking $file with $tp\n";
      eval {
          local $SIG{ALRM} = sub { `pkill sleek;pkill mona;pkill poly`;die "alarm clock restart" };
          alarm 1800;
          $output = `$sleek -tp $tp $file 2>&1`;
          alarm 0;
      };
      if ($@ and $@ =~ /alarm clock restart/) {  $error_count++;$error_files = $error_files . " " . $file;print "!!!!!!!timed out\n"; }
      else {
          print PROOFLOGFILE "$output";
          #print LOGFILE "\n======================================\n";
          #print LOGFILE "$output";
		  if($sleek_files{$file}) 
			{
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
						if(($r !~ /^$sleek_files{$file}->[0]->[0]$/)||($output =~ m/.*failure.*/i))
						{
							print LOGFILE "Unexpected result with : $file got: $r expected $sleek_files{$file}->[0]->[0]\n";
							$error_count++;
							$error_files = $error_files . " " . $file;
						} 
			}
		  else{
          if (($output =~ m/.*error.*/i)||($output =~ m/.*fail.*/i)) {
	          print LOGFILE "Error found in the newly added file $file\n";
	          $error_count++;
	          $error_files = $error_files . " " . $file;
	          if ($stop) {
                  exit(0);
	          }
          }
		}
      }
	}
  }
}
