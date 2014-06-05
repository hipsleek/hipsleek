#!/usr/bin/perl

$num_args = $#ARGV + 1;

if ($num_args == 0) {
  @files = <*.slk>;
} else {
  @files = <$ARGV[0]*.slk>;
}

foreach $file (@files) {
  print $file . "\n";

  system("sleek " . $file ." --smt-compete-test");
}

