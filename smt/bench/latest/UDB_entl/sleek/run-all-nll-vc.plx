#!/usr/bin/perl

@files = <nll-vc*.slk>;

foreach $file (@files) {
    print $file . "\n";

    system("../../../../../sleek " . $file ." --smt-compete-test");
}

