#!/usr/bin/perl

use Try::Tiny;
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


GetOptions( "infer-lex"       => \$lex,          #register - update the xml
            "revid=s"         => \$revid,        #revision id
    );


#my @dirs=("termination-crafted-lit","termination-memory-alloca");
#my @dirs=("termination-memory-alloca");
#my @dirs=("test");
my @dirs=("termination-crafted-lit", "termination-crafted","termination-numeric","termination-memory-alloca");
#my @dirs=("termination-memory-alloca");
#my @dirs=("termination-numeric");
#my @dirs=("termination-crafted");
#my @dirs=("termination-crafted");
my $exec_path = '..';
my $hip  = "$exec_path/hip ";
my $args = '-infer "\@post_n\@term"';
my $result_file = "SV-COMP 2015.xls";
my $summary_file = "SV-COMP 2015 - SUM.xls";
my $timeout = 60;

#my $root_dir = getcwd();
my $first_row = 2;
my $col = 0;
my $filename_col = $col++;
my $res_col = $col++;
$col++; #empty col
my $bench_col = $col++;
$col++;#empty col
$col++;
$col++;
my $lex_col = $col++;

my $working_col =  $res_col;

my $row_sum_old     =  8;
my $row_sum_new     =  9;
my $row_sum_lex     =  10;
my $col_sum_term    = 14;
my $col_sum_mayloop = 15;
my $col_sum_fail    = 16;
my $col_sum_timeout = 17;
my $col_sum_err     = 18;

my $sum_row = $row_sum_new;
if($lex) {$working_col =  $lex_col;  $sum_row = $row_sum_lex; }

my $parser = new Spreadsheet::ParseExcel::SaveParser;
#my $parser_sum = new Spreadsheet::ParseExcel::SaveParser;

if(-e "$result_file")  {#check for file existance

    my $workbook = $parser->Parse("$result_file") #open file for modifying
        or die "File $result_file was not found";
    # my $workbook_sum = $parser->Parse("$summary_file") #open file for modifying
    #     or die "File $summary_file was not found";
    my $row = $first_row;
    foreach $dir (@dirs) {
        #if ($dir  =~ m/termination-memory-alloca/){
            $hip = "C_INCLUDE_PATH=termination-memory-alloca/ ".$hip;
            $args = '-infer "\@shape\@term"';
        #}
        if($lex) {
         $args = $args.' --infer-lex '; 
        }
        $worksheet = $workbook->worksheet("$dir");
        my $current_dir = "$dir/";
        $row = $first_row;
        #print "$current_dir"."*.c";
        print "\n";

        my $term_cnt = 0;
        my $mayloop_cnt = 0;
        my $fail_cnt = 0;
        my $err_cnt = 0;
        my $timeout_cnt = 0;

        my $lex_term_cnt = 0;
        my $lex_mayloop_cnt = 0;
        my $lex_fail_cnt = 0;
        my $lex_err_cnt = 0;
        my $lex_timeout_cnt = 0;

        my @files = <$current_dir*.c>;
        #my @files = <termination-crafted-lit/*.c>;
        foreach $file (@files) {
            #print $file . "\n";
            $filename = basename($file);
            print  "\n\n\n$filename" . "\n";
            #$1="";$2=""; #reset the output channels

            my $res_cell = "ERR";
            my $output = " ";

            try {
                local $SIG{ALRM} = sub { die "alarm\n" };
                alarm $timeout;
                $output = `$hip $file $args 2>&1`;
                alarm 0;
            } catch {
                die $_ unless $_ eq "alarm\n";
                #print "timed out\n";
                $res_cell = "TIMEOUT";
            };

            # print  "\n $hip $file $args  2>&1 \n";
            # print " ------------- \n$output \n -------------\n";
            # print "#################\n$1 \n #################";
            
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
                            #print "REQUIRES: \n";
                            if($line =~ m/Term/i # && $term =~ m/Term/i
                                )       { $res_cell = "OK - Term"; $term_cnt++;  last; }
                            elsif($line =~ m/MayLoop/i && $loop =~ m/Loop/i) { $res_cell = "OK - MayLoop"; $mayloop_cnt++; last; }
                            elsif($line =~ m/MayLoop\{.*\}/i) { $res_cell = "OK - MayLoop"; $mayloop_cnt++; last; }
                            elsif($line =~ m/MayLoop/i && $mayloop =~ m/MayLoop/i) { $res_cell = "Check MayLoop"; $fail_cnt++; last; }
                            # else { $err_cnt++; }
                            elsif($line =~ m/Loop/i)    { $res_cell = "Loop";  $mayloop_cnt++;}
                        }
                    }
                }
            }
            print "$res_cell \n";
            if ($res_cell =~ m/ERR/i) {$err_cnt++;}
            elsif ($res_cell =~ m/TIMEOUT/i) {$timeout_cnt++;}
            $worksheet->AddCell($row++, $working_col, $res_cell);
        }
        
        $worksheet->AddCell($sum_row, $col_sum_term, $term_cnt);
        $worksheet->AddCell($sum_row, $col_sum_mayloop, $mayloop_cnt);
        $worksheet->AddCell($sum_row, $col_sum_fail, $fail_cnt);
        $worksheet->AddCell($sum_row, $col_sum_timeout, $timeout_cnt);
        $worksheet->AddCell($sum_row, $col_sum_err, $err_cnt);
        #$workbook_sum->AddWorksheet("$revid-$dir");
        
        
    }
    $workbook->SaveAs("$result_file");
    #$workbook_sum->SaveAs("$summary_file");
} else {
    print "\n Oops, file $result_file was not found";
}

