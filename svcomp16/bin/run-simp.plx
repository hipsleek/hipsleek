#!/usr/bin/perl

@files = <simpl/*.c>;


foreach $file (@files) {
    print $file . "\n";

    system("./hiprec_run.sh " . $file);

}

