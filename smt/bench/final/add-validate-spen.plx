#!/usr/bin/perl
use File::Basename;
use Tie::File;
use Cwd qw();

$spen_path = "/home/chanhle/tools/spen/spen";
$spen_samples_path = $spen_path . "/samples";

$cwd_path = Cwd::cwd();

$num_args = $#ARGV + 1;

if ($num_args == 0) {
  print "\nUsage: add-validate-spen.plx [nll0a | skl3]\n";
  exit;
}

$bench_name = $ARGV[0]; 

@slk_files = <$cwd_path/$bench_name/entl/sleek/*.smt2.slk>;

foreach $slk_file (@slk_files) {
  $prefix = basename($slk_file, ".smt2.slk");
  print $prefix;
  
  if ($bench_name eq "nll0a") {
    $spen_samples = $spen_samples_path . "/nll";
  } else {
    if ($prefix =~ /skl3/) {
      $spen_samples = $spen_samples_path . "/skl3";
    } else {
      $spen_samples = $spen_samples_path . "/skl2";
    }
  }
  my $spen_expect_file = $spen_samples . "/" . $prefix . ".smt.exp";
  print $spen_expect_file;
  
  open (my $spen_file, '<', $spen_expect_file) or die "Could not open file '$spen_expect_file' $!";
  my $result = <$spen_file>; 
  if ($result =~ /unsat/) {
      print ": Valid\n"; 
      $expect = "expect Valid.";
    } else {
      print ": Fail\n";
      $expect = "expect Fail.";
    }
  close $spen_file;
  
  tie my @slk_lines, 'Tie::File', $slk_file or die "Could not open file '$slk_file' $!";
    
  # Remove expect command, if any
  @slk_lines = grep {$_ !~ /expect/} @slk_lines;  
  push (@slk_lines, $expect);
  untie @slk_lines;
}

