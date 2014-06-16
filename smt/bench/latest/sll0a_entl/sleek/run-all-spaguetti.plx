#!/usr/bin/perl

@files = <spaguetti*.slk>;

foreach $file (@files) {
    print $file . "\n";

    system("../../../../../sleek " . $file ." --smt-compete-test");
}

