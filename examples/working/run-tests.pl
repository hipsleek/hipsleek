#!/usr/bin/perl

use File::Find;
use File::Basename;
use Getopt::Long;

GetOptions( "stop"  => \$stop,
			"opt" => \$optimized,
            "output=s" => \$output_file );

$hip = '../../../hip --no-LHS-wrap-exist';
$sleek = '../../../sleek';

if ($optimized) {
  $hip = '../../hip.opt';
  $sleek = '../../sleek.opt -ee -filter';
}

$error_count = 0;
$error_files = "";

if ($output_file) {}
else { $output_file = "log"; }

open(LOGFILE, "> $output_file") || die ("Could not open $output_file.\n");

print "Starting hip tests:\n";

find(\&hip_process_file, "./hip");
print "Starting sleek tests:\n";
find(\&sleek_process_file, "./sleek");

close(LOGFILE);

if ($error_count > 0) {
  print "Total number of errors: $error_count in files: $error_files.\n";
}

exit(0);


sub hip_process_file {
  $file = $_;

  my $ext = (fileparse($file,'\..*'))[2];

  if ($ext eq ".ss") {
	print "Checking $file\n";
	my $output = `$hip $file 2>&1`;
	
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

sub sleek_process_file  {
  $file = $_;

  my $ext = (fileparse($file,'\..*'))[2];

  if ($ext eq ".slk") {
        print "Checking $file\n";

        my $output = `$sleek <$file 2>&1`;

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
