#!/usr/bin/perl

use File::Find;
use File::Basename;
use Getopt::Long;

GetOptions( "stop"  => \$stop,
			"sleek"  => \$run_sleek,
			"hip"  => \$run_hip			);
$exempl_path = ".";
$exec_path = '../../..';
@excl_files = ("avl","heaps","avl-orig-2");
$error_count = 0;
$error_files = "";
$hip = "$exec_path/hip";
$sleek = "$exec_path/sleek";
$output_file = "log";
@hip_fail=("pepm08/bsearch","POSSIBLE","+infer +check -o:con1 PostStrong -m:1");
@sleek_fail=("pepm08/bubblesort","SAFETY","+infer +check -o:con1 PostStrong -m:1");

open(LOGFILE, "> $output_file") || die ("Could not open $output_file.\n");
if ($run_hip)
{
	print "Starting hip tests:\n";
	find(\&hip_process_file, "$exempl_path/hip");
}
if($run_sleek)
{
	print "Starting sleek tests:\n";
	find(\&sleek_process_file, "$exempl_path/sleek");
}
close(LOGFILE);

if ($error_count > 0) {
  print "Total number of errors: $error_count in files: $error_files.\n";
}

exit(0);


sub hip_process_file {
  $file = $_;
	@file_part = (fileparse($file,'\..*'));
  my $ext = (@file_part)[2];

  if ($ext eq ".ss" && not(grep(/^($file_part[0])$/,@excl_files))) {
	print "Checking $file\n";
	my $output = `$hip $file 2>&1`;
	
	print LOGFILE "\n======================================\n";
	print LOGFILE "$output";

	if (($output =~ /.*(e|E)rror.*/ && not(grep(/^($file_part[0])$/,@hip_fail)))||
		($output !~ /.*(e|E)rror.*/ &&    (grep(/^($file_part[0])$/,@hip_fail)))){
	  print "Unexpected result with : $file\n";
	  $error_count++;
	  $error_files = $error_files . " " . $file;
	  if ($stop) {
		exit(0);
	  }
	}
  }
}
sub sleek_process_file  {
  $file = $_;
  @file_part = (fileparse($file,'\..*'));
  my $ext = (@file_part)[2];
  my $ext = (fileparse($file,'\..*'))[2];

	if ($ext eq ".slk" && not(grep(/^($file_part[0])$/,@excl_files))) {
		print "Checking $file\n";
       my $output = `$sleek $file 2>&1`;

        print LOGFILE "\n======================================\n";
        print LOGFILE "$output";

	if (($output =~ /.*(e|E)rror.*/ && not(grep(/^($file_part[0])$/,@sleek_fail)))||
		($output !~ /.*(e|E)rror.*/ &&    (grep(/^($file_part[0])$/,@sleek_fail)))){
	  print "Unexpected result with : $file\n";
          $error_count++;
          $error_files = $error_files . " " . $file;
          if ($stop) {
                exit(0);
          }
        }
  }
}
