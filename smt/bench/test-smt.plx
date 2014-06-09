#!/usr/bin/perl
use strict;
use warnings;

use File::Basename;
use File::Path qw(make_path);
use File::Path;
use File::Copy;
use File::Find::Rule;
use File::Find;
use File::Spec;
use Cwd qw();

my $cwd = Cwd::cwd();
my $test_path = $cwd . "/latest";
my $final_path = $cwd . "/final";
my $sleek = "../../sleek ";

my $error_count = 0;
my $error_files = "";
my $not_found_count = 0;
my $not_found_files = "";

my @test_files = (
  "dll-vc01.smt2", "dll-vc02.smt2", "dll-vc03.smt2", "dll-vc04.smt2", "dll-vc05.smt2", 
  "dll-vc06.smt2", "dll-vc07.smt2", "dll-vc08.smt2", "dll-vc09.smt2", "dll-vc10.smt2", 
  "dll-vc11.smt2", "dll-vc12.smt2", "dll-vc13.smt2",
  
  "nll-vc01.smt2", "nll-vc02.smt2", "nll-vc03.smt2", "nll-vc04.smt2", "nll-vc05.smt2", 
  "nll-vc06.smt2", "nll-vc07.smt2", "nll-vc08.smt2", "nll-vc09.smt2", "nll-vc10.smt2",
  "nll-vc11.smt2", "nll-vc12.smt2", "nll-vc13.smt2", "nll-vc14.smt2", "nll-vc15.smt2",
  "nll-vc16.smt2",
  
  "skl2-vc01.smt2", "skl2-vc02.smt2", "skl2-vc03.smt2", "skl2-vc04.smt2",
  "skl3-vc01.smt2", "skl3-vc02.smt2", #"skl3-vc03.smt2", "skl3-vc04.smt2", "skl3-vc05.smt2",
  #"skl3-vc06.smt2", "skl3-vc07.smt2", "skl3-vc08.smt2", "skl3-vc09.smt2", "skl3-vc10.smt2"
);

my $tmp_dir = $cwd . "/tmp";

if (-d $tmp_dir) {
  rmtree $tmp_dir;
}
make_path $tmp_dir or die "Failed to create temp folder";

foreach my $test_file (@test_files) {
  my @abs_paths;
  print "\n" . $test_file;
  find({
    wanted   => sub { push @abs_paths, $_ if -f and -r and basename($_, "") eq $test_file},
    no_chdir => 1,
  }, $test_path);
  
  if (@abs_paths) {
    print "\n";
    foreach my $smt2_file (@abs_paths) {
      my $rel_path = " latest/" . File::Spec->abs2rel($smt2_file, $test_path);
      my $slk_file = $smt2_file . ".slk";
      system("smt2slk " . $smt2_file);
      move ($slk_file, $tmp_dir) or die "The move operation failed: $!";
      
      my $smt2_name = basename($slk_file, ".slk");
      my $output = `$sleek $tmp_dir/$smt2_name.slk --smt-compete-test 2>&1`;
      if ($output =~ "Unexpected") {
        print " $rel_path: Fail\n";
        
        $error_count++;
        $error_files = $error_files . $rel_path . "\n";
      } else {
        print " $rel_path: OK\n";
      }
    }
  } else {
    print ": Not found.\n";
    
    $not_found_count++;
    $not_found_files = $not_found_files . " " . $test_file . "\n";
  }
}

if ($error_count > 0) {
  print "\nTotal number of errors: $error_count in files:\n$error_files\n";
} else {
  print "\n All test results were as expected.\n";
}

if ($not_found_count > 0) {
  print "\nNot found files:\n$not_found_files\n";
}
