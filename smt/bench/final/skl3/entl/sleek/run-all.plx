#!/usr/bin/perl

@files = <*.slk>;

foreach $file (@files) {
    print $file . "\n";

    system("sleek " . $file ." --smt-compete-test");
}

