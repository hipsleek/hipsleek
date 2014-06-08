#!/usr/bin/perl
use strict;
use warnings;

use File::Basename;
use File::Path qw(make_path);
use File::Copy;
use File::Find::Rule;
use Cwd qw();

my $path = Cwd::cwd();

my @benchs = File::Find::Rule->new
  ->mindepth(1)->maxdepth(1)->directory->in($path);

foreach my $bench (@benchs) {
  my $bench_name = basename($bench, "");
  print "Translating " . $bench_name . " ...\n";
  
  my @smt2_files = <$bench/*.smt2>;
  my $slk_dir = $bench . "/sleek";

  if (!-d $slk_dir) {
    make_path $slk_dir or die "Failed to create folder $slk_dir";
  }

  foreach my $smt2_file (@smt2_files) {
    my $slk_file = $smt2_file . ".slk";
    system("smt2slk " . $smt2_file);
    move ($slk_file, $slk_dir) or die "The move operation failed: $!";
  }
}
