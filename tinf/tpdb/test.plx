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
use Try::Tiny;
use Getopt::Long;
use POSIX qw(:sys_wait_h);
use Time::HiRes qw(gettimeofday);

my $cwd = Cwd::cwd();
my $test_path = $cwd . "/Java_Bytecode/";
my $hip = "../../hip";

my $test_bench = "";

GetOptions (
  "test=s" => \$test_bench,
) or die("Error in command line arguments\n");

my @benchs;
if ($test_bench ne "") {
  @benchs = ($test_path . $test_bench . "/");
} else {
  @benchs = File::Find::Rule->new
    ->mindepth(1)->maxdepth(1)->directory->in($test_path);
}
  
foreach my $bench (@benchs) {
  my $bench_name = basename($bench, "");
  print "Testing " . $bench_name . " ...\n";
  
  my @tests = File::Find::Rule->new
  ->mindepth(1)->maxdepth(1)->directory->in($bench);
  foreach my $test (@tests) {
    my $test_name = basename($test, "");
    print "  Parsing " . $test_name . " ...\n";
    
    my $output = `$hip $test/*.java`;
    print $output;
  }
}

