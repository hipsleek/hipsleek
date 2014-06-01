#!/usr/bin/perl

@files = <*.slk>;

foreach $file (@files) {
    print $file . "\n";

    system("sleek --gen-smt " . $file);
}
system("mkdir -f smt");
system("mv *.smt2 smt");






