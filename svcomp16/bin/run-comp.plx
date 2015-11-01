#!/usr/bin/perl

@files = <comp/*.c>;



foreach $file (@files) {
    print $file . "\n";

    system("./hiprec_run.sh " . $file );

}

