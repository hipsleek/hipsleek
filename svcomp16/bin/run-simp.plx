#!/usr/bin/perl

@files = <simpl/*.c>;

my $s2 = "./hip";
my $timeout = 3600;


foreach $file (@files) {
    print $file . "\n";

    system("./hiprec " . $file);

}

