#!/usr/bin/perl

use File::Basename;
use File::Copy;
use File::Find::Rule;
use Cwd qw();

my $path = Cwd::cwd();

my @benchs = File::Find::Rule->new
  ->mindepth(1)->maxdepth(1)->directory->in($path);

foreach my $bench (@benchs) {
	my $bench_name = basename($bench, "");
  print "Translating " . $bench_name . " ...\n";
  
  my @bench_sets = File::Find::Rule->new
    ->mindepth(1)->maxdepth(1)->directory->in($bench);
  foreach my $bench_set (@bench_sets) {
    my @smt2_files = <$bench_set/*.smt2>;
    my $slk_dir = $bench_set . "/sleek";
    foreach my $smt2_file (@smt2_files) {
      my $slk_file = $smt2_file . ".slk";
      system("smt2slk " . $smt2_file);
      move ($slk_file, $slk_dir) or die "The move operation failed: $!";
    }
  }
}
