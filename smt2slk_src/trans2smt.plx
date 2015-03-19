#!/usr/bin/perl

@files = <*.slk>;

foreach $file (@files) {
    print $file . "\n";

    system("sleek --gen-smt " . $file);
}
system("mkdir smt");
system("mv *.smt2 smt");






