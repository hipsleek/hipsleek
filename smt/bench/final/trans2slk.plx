#!/usr/bin/perl

use File::Basename;
use File::Copy;
use File::Find::Rule;
use Cwd qw();
use Path::Tiny qw(path);

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
			my $filename = basename($smt2_file, ".smt2"); 
			my $old_slk_file = $slk_dir . "/" . $filename . ".smt2.slk";
      if (-e $old_slk_file) {
				my $slk_file = path($old_slk_file);
				my $data = $slk_file->slurp_utf8;
				$data =~ s/checkentail /checkentail_exact /g;
				$slk_file->spew_utf8($data);
      } else {
				my $new_slk_file = $smt2_file . ".slk";
        system("smt2slk " . $smt2_file);
        move ($new_slk_file, $slk_dir) or die "The move operation failed: $!";
      }
    }
  }
}
