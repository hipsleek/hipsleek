#!/usr/bin/perl
use File::Basename;

$asterix_path = "/home/locle/tools/pldi11";

use Env qw(LD_LIBRARY_PATH);
BEGIN
{
    $LD_LIBRARY_PATH .= ":/home/locle/tools/pldi11";
}

$num_args = $#ARGV + 1;

if ($num_args == 0) {
  print "\nUsage: add-validate.plx [bolognesa | clones | smallfoot | spaguetti]\n";
  exit;
}

@slk_files = <$ARGV[0]*.slk>; 

@sl_files = <$asterix_path/benchmarks/benchs/sl/$ARGV[0]*.sl>;

foreach $sl_file (@sl_files) {
  print $sl_file . "\n";

  #system($asterix_path . "/asterix < " . $sl_file);
  $asterix_cmd = $asterix_path . "/asterix < " . $sl_file;
  $output = `$asterix_cmd 2>&1`;
  
  @lines = split /\n/, $output; 
  
  $prefix = basename($sl_file, ".sl");
  
  for ($i = 1; $i <= 10; $i++) {
    if ($i < 10) {
      $index = "0" . $i;
    } else {
      $index = $i;
    }
    $slk_file = $prefix . "-e" . $index . ".tptp.smt2.slk";
    open(my $fh, '>>', $slk_file) or die "Could not open file '$slk_file' $!";
    print $slk_file;
    if ($lines[$i-1] =~ /invalid/) {
      print ": Invalid\n"; 
      $expect = "\nexpect Fail.";
    } else {
      print ": Valid\n";
      $expect = "\nexpect Valid.";
    }
    say $fh $expect;
    close $fh;
  }
}

