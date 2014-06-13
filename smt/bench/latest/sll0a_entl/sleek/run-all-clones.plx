#!/usr/bin/perl

@files = <clones*.slk>;

foreach $file (@files) {
    print $file . "\n";

    system("../../../../../sleek " . $file ." --smt-compete-test");
}

