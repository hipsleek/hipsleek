#!/usr/bin/perl

use File::Find;
use File::Basename;
use Getopt::Long;
use Sys::Hostname;
use File::NCopy;
use File::Path 'rmtree';
use Cwd;
use lib '/usr/local/share/perl/5.10.0';
use Spreadsheet::ParseExcel;
use Spreadsheet::ParseExcel::SaveParser;


#my @dirs=("termination-crafted-lit","termination-memory-alloca");
#my @dirs=("termination-memory-alloca");
# my @dirs=("test");
my @dirs=("termination-crafted-lit");
my $exec_path = '..';
my $hip  = "$exec_path/hip ";
my $args = '-infer "\@term"';
my $result_file = "SV-COMP 2015.xls";

#my $root_dir = getcwd();
my $first_row = 2;
my $col = 0;
my $filename_col = $col++;
my $res_col = $col++;
$col++;
my $bench_col = $col++;

my $parser = new Spreadsheet::ParseExcel::SaveParser;

if(-e "$result_file")  {#check for file existance

    my $workbook = $parser->Parse("$result_file") #open file for modifying
        or die "File $result_file was not found";
    my $row = $first_row;
    foreach $dir (@dirs) {
        $worksheet = $workbook->worksheet("$dir");
        my $current_dir = "$dir/";
        #print "$current_dir"."*.c";
        print "\n";
        my @files = <$current_dir*.c>;
        #my @files = <termination-crafted-lit/*.c>;
        foreach $file (@files) {
            #print $file . "\n";
            $filename = basename($file);
            print  "\n\n\n$filename" . "\n";
            #$1="";$2=""; #reset the output channels
            my $output = `$hip $file $args 2>&1`;
            # print  "\n $hip $file $args  2>&1 \n";
            # print " ------------- \n$output \n -------------\n";
            # print "#################\n$1 \n #################";
            my $res_cell = "ERR";
            if ($output =~ m/(Checking procedure main.*)/s){
                my $res = $1;
                #print "$res \n";
                my $loop = "";
                my $mayloop = "";
                my $term = "";
                if ($res =~ m/(Temporal Assumptions:.*)Termination Inference Result:/s){
                    my $res_assump = $1;
                    # print "\n\n ---------------------";
                    # print "$res_assump";
                    # print "\n\n ---------------------\n\n";
                    my @lines = split /\n/, $res_assump; 
                    foreach my $line (@lines) { 
                        if($line =~ m/Term/i)       { $term = "Term"; }
                        elsif($line =~ m/MayLoop/i) { $mayloop = "MayLoop"; }
                        elsif($line =~ m/Loop/i)    { $loop = "Loop"; }
                    }
                }
                if ($res =~ m/(Termination Inference Result:.*)/s){
                    my $res_inf = $1;
                    # print "$res_inf \n";

                    my @lines = split /\n/, $res_inf; 
                    
                    foreach my $line (@lines) { 
                        if($line =~ m/.*requires.*/){
                            if($line =~ m/Term/i # && $term =~ m/Term/i
                                )       { $res_cell = "OK - Term"; }
                            elsif($line =~ m/MayLoop/i && $loop =~ m/Loop/i) { $res_cell = "OK - MayLoop"; }
                            elsif($line =~ m/MayLoop/i && $mayloop =~ m/MayLoop/i) { $res_cell = "Check MayLoop"; }
                            # elsif($line =~ m/Loop/i)    { $res_cell = "Loop"; }
                        }
                    }
                    print "$res_cell \n";
                }
            }
            $worksheet->AddCell($row++, $res_col, $res_cell);
            
        }
    }
    $workbook->SaveAs("$result_file");
} else {
    print "\n Oops, file $result_file was not found";
}

