#!/usr/bin/perl

@files = <comp/*.c>;

my $s2 = "./hip";
my $timeout = 3600;


foreach $file (@files) {
    print $file . "\n";

    system("./hip " . $file ." --svcomp-compete");

}

