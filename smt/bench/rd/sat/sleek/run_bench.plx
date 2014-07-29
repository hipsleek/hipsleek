#!/usr/bin/perl

@files = <*.slk>;

foreach $file (@files) {
    print $file . "\n";

    system("timeout 10s ../../../../../sleek " . $file . " --smt-compete --elg");
}






