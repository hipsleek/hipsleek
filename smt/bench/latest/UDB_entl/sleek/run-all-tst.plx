#!/usr/bin/perl

@files = <append_*.slk>;

foreach $file (@files) {
    print $file . "\n";

    system("../../../../../sleek " . $file ." --smt-test");
}

