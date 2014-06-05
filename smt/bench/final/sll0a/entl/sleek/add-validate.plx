#!/usr/bin/perl
use File::Basename;
use Tie::File;

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

$bench_name = $ARGV[0]; 

@sl_files = <$asterix_path/benchmarks/benchs/sl/$bench_name*.sl>;

foreach $sl_file (@sl_files) {
  print $sl_file . "\n";

  #system($asterix_path . "/asterix < " . $sl_file);
  $asterix_cmd = $asterix_path . "/asterix < " . $sl_file;
  $output = `$asterix_cmd 2>&1`;
  
  @lines = split /\n/, $output; 
  
  $prefix = basename($sl_file, ".sl");
  
  if ($ARGV[0] =~ /smallfoot/) {
    $max_index = 77;
  } else {
    $max_index = 10;
    $prefix = $prefix . "-e";
  }
  
  for ($i = 1; $i <= $max_index; $i++) {
    if ($i < 10) {
      $index = "0" . $i;
    } else {
      $index = $i;
    }
    $slk_file = $prefix . $index . ".tptp.smt2.slk";
    print $slk_file;
    
    #open(my $fh, '>>', $slk_file) or die "Could not open file '$slk_file' $!";
    tie my @slk_lines, 'Tie::File', $slk_file or die "Could not open file '$slk_file' $!";
    
    # Remove expect command, if any
    #@slk_lines = grep(!/expect/, @slk_lines);
    @slk_lines = grep {$_ !~ /expect/} @slk_lines;
    
    if ($lines[$i-1] =~ /invalid/) {
      print ": Invalid\n"; 
      $expect = "expect Fail.";
    } else {
      print ": Valid\n";
      $expect = "expect Valid.";
    }
    #say $fh $expect;
    #close $fh;
    push (@slk_lines, $expect);
    untie @slk_lines;
  }
}

