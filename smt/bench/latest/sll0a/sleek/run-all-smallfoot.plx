#!/usr/bin/perl

@files = <smallfoot*.slk>;

foreach $file (@files) {
    print $file . "\n";

    system("../../../../../sleek " . $file ." --smt-compete-test");
}

