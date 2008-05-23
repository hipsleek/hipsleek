#!/usr/bin/perl

use File::Find;
use File::Basename;
use Getopt::Long;

GetOptions( "stop"  => \$stop,
			"sleek"  => \$run_sleek,
			"hip"  => \$run_hip			);
$exempl_path = ".";
$exec_path = '../..';
@excl_files = ();
$error_count = 0;
$error_files = "";
$hip = "$exec_path/hip";
$sleek = "$exec_path/sleek";
$output_file = "log";
# list of file, nr of functions, function name, output, function name, output......
@hip_files=(["append.ss",1,"append","ERROR"]);
# list of file, string with result of each entailment....
@sleek_files=(
			["sleek1.slk","Valid.Fail."],
			["sleek2.slk","Valid.Fail."]);

open(LOGFILE, "> $output_file") || die ("Could not open $output_file.\n");
if ($run_hip)
{
	print "Starting hip tests:\n";
	hip_process_file();
}
if($run_sleek)
{
	print "Starting sleek tests:\n";
	sleek_process_file();
}
close(LOGFILE);

if ($error_count > 0) {
  print "Total number of errors: $error_count in files: $error_files.\n";
}

exit(0);


sub hip_process_file {
  foreach $test (@hip_files)
	{
		print "Checking $test->[0]\n";

		$output = `$hip $exempl_path/hip/$test->[0] 2>&1`;
		print LOGFILE "\n======================================\n";
		print LOGFILE "$output";
		$limit = $test->[1]*2+2;
		for($i = 2; $i<$limit;$i+=2)
		{
			if($output !~ /Checking procedure $test->[$i].*$test->[$i+1]/)
			{
				$error_count++;
				$error_files=$error_files."error at: $test->[0] $test->[$i]\n";
			}
		}
	}
}

sub sleek_process_file  {
	foreach $test (@sleek_files)
	{
		print "Checking $test->[0]\n";
		$output = `$sleek $exempl_path/sleek/$test->[0] 2>&1`;
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
			$s = length($output);
			print "\nl$s\n";
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