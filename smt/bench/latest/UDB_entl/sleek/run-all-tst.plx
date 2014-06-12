#!/usr/bin/perl

@files = <*.tst.*.slk>;

foreach $file (@files) {
    print $file . "\n";

    system("../../../../../sleek " . $file ." --smt-compete-test");
}

