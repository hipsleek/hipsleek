#!/usr/bin/perl

@files = <*.smt2>;

foreach $file (@files) {
    print $file . "\n";

    system("smt2slk " . $file);
}







