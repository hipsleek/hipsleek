#!/usr/bin/perl

use File::Find;
use File::Basename;
use Getopt::Long;

GetOptions( "stop"  => \$stop,
			"opt" => \$optimized,
            "output=s" => \$output_file );

$ss = '../../ss';
if ($optimized) {
  $ss = '../../ss.opt -ee -filter ';
}

$error_count = 0;
$error_files = "";

if ($output_file) {}
else { $output_file = "log"; }

open(LOGFILE, "> $output_file") || die ("Could not open $output_file.\n");

find(\&process_file, ".");

close(LOGFILE);

if ($error_count > 0) {
  print "Total number of errors: $error_count in files: $error_files.\n";
}

exit(0);


sub process_file {
  $file = $_;

  my $ext = (fileparse($file,'\..*'))[2];

  if ($ext eq ".ss") {
	print "Checking $file\n";

	my $output = `$ss $file 2>&1`;
	
	print LOGFILE "\n======================================\n";
	print LOGFILE "$output";

	if ($output =~ /.*(e|E)rror.*/) {
	  print "Error found\n";
	  $error_count++;
	  $error_files = $error_files . " " . $file;
	  if ($stop) {
		exit(0);
	  }
	}
  }

}
