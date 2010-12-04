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
$hip = "$exec_path/hip.opt -tp om --eps";
$sleek = "$exec_path/sleek.opt -tp om --eps";
$output_file = "log";
# list of file, nr of functions, function name, output, function name, output......
%hip_files=(
	"hip" =>["selection.ss", "trees.ss",
  "cll.ss",
  "bubble.ss",
  "dll.ss",
  "merge.ss",
  "ll.ss",
  "merge-modular.ss",
  "qsort.ss"],
  "hip-l" =>["rb.scp.ss","avl-modular-2.ss"]
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

open(LOGFILE, "> $output_file") || die ("Could not open $output_file.\n");
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
			print "Checking $test\n";
			print "$hip $exempl_path/$test \n";
			$output = `$hip $exempl_path/$test | grep Proce`;
      print $output;
		}
  }
}