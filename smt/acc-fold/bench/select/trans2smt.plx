#!/usr/bin/perl

@files = <*.slk>;

foreach $file (@files) {
    print $file . "\n";

    system("../../../../sleek --gen-smt " . $file);
}
system("mkdir -p smt");
system("mv *.smt2 smt");






