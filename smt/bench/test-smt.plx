#!/usr/bin/perl
use strict;
use warnings;

use File::Basename;
use File::Path qw(make_path);
use File::Path;
use File::Copy;
use File::Find::Rule;
use File::Find;
use File::Spec;
use Cwd qw();
use Try::Tiny;
use Getopt::Long;
use POSIX qw(:sys_wait_h);
use Time::HiRes qw(gettimeofday);

my $cwd = Cwd::cwd();
my $test_path = $cwd . "/latest";
my $final_path = $cwd . "/final";
my $sleek = "../../sleek";
my $smt2slk = "smt2slk"; #"$cwd/bin/smt2slk"; #"../smt2slk/bin/smt2slk";

my $unexpected_count = 0;
my $unexpected_files = "";
my $unsound_count = 0;
my $unsound_files = "";
my $unknown_count = 0;
my $unknown_files = "";
my $error_count = 0;
my $error_files = "";
my $not_found_count = 0;
my $not_found_files = "";
my $timeout_count = 0;
my $timeout_files = "";

my $timeout = 0;
my $total_time = 0;
my $print_short;
my $print_time;

my $test_all;
my $test_10s;
my $test_fail;
my $test_bench = "";
my $test_name = "";
my $test_opt = "";

sub println {
  print $_[0];
  if ($print_time) {
    print " ($_[1] seconds)";
  }
  print "\n";
}
  
GetOptions (
  "all" => \$test_all,
  "flags=s" => \$test_opt,
  "fail" => \$test_fail,
  "over10" => \$test_10s,
  "bench=s" => \$test_bench,
  "test=s" => \$test_name,
  "tidy" => \$print_short,
  "time" => \$print_time,
  "timeout=i"  => \$timeout)
or die("Error in command line arguments\n");

my @options = ("--smt-compete-test");
if ($test_opt ne "") {
  my @test_opts =  split(/ /, $test_opt);
  push (@options, @test_opts); 
}

my @smt2_files;

if ($test_all) {
  my @benchs = File::Find::Rule->new->
    mindepth(1)->maxdepth(1)->directory->in($test_path);

  foreach my $bench (@benchs) {
    my @bench_files = <$bench/*.smt2>;
    push (@smt2_files, @bench_files);
  }
} elsif ($test_bench ne "") {
  if (-d "$test_path/$test_bench") {
    my @bench_files = <$test_path/$test_bench/*.smt2>;
    push (@smt2_files, @bench_files);
  } else {
    print "Benchmark $test_bench is not found.\n";
  }
} elsif ($test_name ne "") {
  my @bench_files = <$test_path/*/*$test_name*.smt2>;
  push (@smt2_files, @bench_files);
} else {  
  my @test_files;
  if ($test_fail) {
    @test_files = (
    # Unexpected
"11.tst.smt2",
"dll-spaghetti-existential.smt2",
"nlcl-vc05.smt2",
"tll-ravioli-existential.smt2"
    # "08.tst.smt2",
    # "10.tst.smt2",
    # "11.tst.smt2","12.tst.smt2","16.tst.smt2","21.tst.smt2",
    # "dll-entails-dll0+.smt2",
    #  "dll-rev-entails-dll.smt2",
    # "dll-entails-dll-rev.smt2",
    # "dll-mid-entails-dll-rev.smt2",
    # "dll-rev-entails-dll-mid.smt2",
    # "dll-spaghetti-existential.smt2",
    # "dll2-entails-dll2-rev.smt2",
    # "dll2-rev-entails-dll2.smt2",
    # "dll2-spaghetti-existential.smt2",
    # "dll2-spaghetti.smt2",
    # "nlcl-vc05.smt2",
    # "node-dll-rev-dll-entails-dll.smt2",
    # "tll-pp-entails-tll-pp-rev.smt2",
    # "tll-pp-rev-entails-tll-pp.smt2",
    # "tll-ravioli-existential.smt2",
    # "tree-pp-entails-tree-pp-rev.smt2",
    # "tree-pp-rev-entails-tree-pp.smt2",
    # "dll-vc07.smt2",
    # "dll-vc08.smt2","dll-vc10.smt2",
    # "nlcl-vc05.smt2",
    # Exception
    );
  } elsif ($test_10s) {
    @test_files = (
    #"clones-02-e08.tptp.smt2",
    "dll-spaghetti.smt2",
    #"skl2-vc03.smt2",
    #"skl3-vc04.smt2",
    "skl3-vc05.smt2",
    "skl3-vc06.smt2",
    "skl3-vc07.smt2",
    "skl3-vc08.smt2",
    "skl3-vc09.smt2",
    #"tll-ravioli.smt2",
    #"tll_slk-13.smt2",
    #"skl2-vc03.smt2",
    #"skl3-vc04.smt2",
    "skl3-vc05.smt2",
    "skl3-vc06.smt2",
    "skl3-vc07.smt2",
    "skl3-vc08.smt2",
    "skl3-vc09.smt2",
    );
  } else {
    @test_files = (
    "dll-vc01.smt2", "dll-vc02.smt2","dll-vc03.smt2",
     "dll-vc04.smt2", "dll-vc05.smt2","dll-vc06.smt2",
      "dll-vc09.smt2", "dll-vc10.smt2", 
     "dll-vc11.smt2","dll-vc12.smt2", "dll-vc13.smt2",
    
    "nll-vc01.smt2", "nll-vc02.smt2", "nll-vc03.smt2", "nll-vc04.smt2", "nll-vc05.smt2", 
    "nll-vc06.smt2", "nll-vc07.smt2", "nll-vc08.smt2", "nll-vc09.smt2", "nll-vc10.smt2",
    "nll-vc11.smt2", "nll-vc12.smt2", "nll-vc13.smt2", "nll-vc14.smt2", "nll-vc15.smt2",
    "nll-vc16.smt2",
    "elseg4_slk-6.smt2", "elseg4_slk-7.smt2","lsegex4_slk-1.smt2","odd-lseg3_slk-5.smt2",
    "skl2-vc01.smt2", "skl2-vc02.smt2", "skl2-vc03.smt2", "skl2-vc04.smt2",
    "skl3-vc01.smt2", "skl3-vc02.smt2", "skl3-vc03.smt2", #"skl3-vc04.smt2", "skl3-vc05.smt2",
    #"skl3-vc06.smt2", "skl3-vc07.smt2", "skl3-vc08.smt2", "skl3-vc09.smt2", "skl3-vc10.smt2"
    "spaguetti-10-e01.tptp.smt2", "spaguetti-10-e02.tptp.smt2", "spaguetti-10-e03.tptp.smt2",
    "spaguetti-11-e01.tptp.smt2", "spaguetti-11-e02.tptp.smt2", "spaguetti-20-e01.tptp.smt2",
    "bolognesa-10-e01.tptp.smt2", "bolognesa-10-e02.tptp.smt2", "bolognesa-10-e03.tptp.smt2",
    "bolognesa-11-e01.tptp.smt2", "bolognesa-12-e01.tptp.smt2", "bolognesa-15-e01.tptp.smt2", 
    "bolognesa-20-e01.tptp.smt2","bolognesa-15-e02.tptp.smt2","spaguetti-13-e03.tptp.smt2",
    "bolognesa-16-e04.tptp.smt2",
    "bolognesa-17-e02.tptp.smt2",
    "bolognesa-18-e02.tptp.smt2",
    "bolognesa-18-e03.tptp.smt2",
    "bolognesa-18-e08.tptp.smt2",
    "bolognesa-20-e03.tptp.smt2",
    "clones-01-e07.tptp.smt2",
    "clones-01-e08.tptp.smt2",
    "clones-01-e09.tptp.smt2",
    "clones-01-e10.tptp.smt2",
    "clones-02-e07.tptp.smt2",
    "clones-02-e08.tptp.smt2",
    "clones-02-e09.tptp.smt2",
    "clones-02-e10.tptp.smt2",
    "clones-03-e07.tptp.smt2",
    "clones-03-e08.tptp.smt2",
    "clones-03-e09.tptp.smt2",
    "clones-03-e10.tptp.smt2",
    "smallfoot-vc29.tptp.smt2",
    "smallfoot-vc30.tptp.smt2",
    "smallfoot-vc32.tptp.smt2",
    "smallfoot-vc33.tptp.smt2",
    "smallfoot-vc35.tptp.smt2",
    "smallfoot-vc37.tptp.smt2",
    "abduced02.defs.smt2",
    "abduced03.defs.smt2",
    "abduced04.defs.smt2",
    "abduced07.defs.smt2",
    "abduced08.defs.smt2",
    "abduced10.defs.smt2",
    "abduced14.defs.smt2",
    "abduced15.defs.smt2",
    "abduced16.defs.smt2",
    "abduced17.defs.smt2",
    "abduced18.defs.smt2",
    "inconsistent-ls-of-ls.defs.smt2",
     "succ-circuit03.defs.smt2",
    "succ-circuit04.defs.smt2",
    "succ-circuit05.defs.smt2",
    "succ-circuit06.defs.smt2",
    "succ-circuit07.defs.smt2",
    "succ-circuit08.defs.smt2",
    "succ-circuit09.defs.smt2",
    "succ-circuit10.defs.smt2",
    "succ-circuit11.defs.smt2",
    "succ-circuit12.defs.smt2",
    "succ-circuit13.defs.smt2",
    "succ-circuit14.defs.smt2",
    "succ-circuit15.defs.smt2",
    "succ-circuit16.defs.smt2",
    "succ-circuit17.defs.smt2",
    "succ-circuit18.defs.smt2",
    "succ-circuit19.defs.smt2",
    "succ-circuit20.defs.smt2",
    "succ-rec05.defs.smt2",
    "succ-rec06.defs.smt2",
    "succ-rec07.defs.smt2",
    "succ-rec08.defs.smt2",
    "succ-rec09.defs.smt2",
    "succ-rec10.defs.smt2",
    "succ-rec11.defs.smt2",
    "succ-rec12.defs.smt2",
    "succ-rec13.defs.smt2",
    "succ-rec14.defs.smt2",
    "succ-rec15.defs.smt2",
    "succ-rec16.defs.smt2",
    "succ-rec17.defs.smt2",
    "succ-rec18.defs.smt2",
    "succ-rec19.defs.smt2",
    "succ-rec20.defs.smt2",
    "succ-circuit01.defs.smt2",
    "succ-circuit02.defs.smt2",
    "succ-rec01.defs.smt2",
    "succ-rec02.defs.smt2",
    "succ-rec03.defs.smt2",
    "clones-04-e07.tptp.smt2",
    "clones-04-e09.tptp.smt2",
    "clones-04-e10.tptp.smt2",
    "clones-05-e07.tptp.smt2",
    "clones-05-e09.tptp.smt2",
    "clones-05-e10.tptp.smt2",
    "clones-06-e07.tptp.smt2",
    "clones-06-e09.tptp.smt2",
    "clones-06-e10.tptp.smt2",
    "clones-07-e07.tptp.smt2",
    "clones-07-e09.tptp.smt2",
    "clones-07-e10.tptp.smt2",
    "clones-08-e07.tptp.smt2",
    "clones-08-e09.tptp.smt2",
    "clones-08-e10.tptp.smt2",
    "clones-09-e07.tptp.smt2",
    "clones-09-e09.tptp.smt2",
    "clones-09-e10.tptp.smt2",
    "clones-10-e07.tptp.smt2",
    "clones-10-e09.tptp.smt2",
    "clones-10-e10.tptp.smt2",
    "smallfoot-vc04.tptp.smt2",
    "smallfoot-vc05.tptp.smt2",
    "smallfoot-vc10.tptp.smt2",
    "smallfoot-vc11.tptp.smt2",
    "smallfoot-vc24.tptp.smt2",
    "smallfoot-vc28.tptp.smt2",
    "smallfoot-vc31.tptp.smt2",
    "smallfoot-vc41.tptp.smt2",
    "smallfoot-vc42.tptp.smt2",
    "01.tst.smt2",
    "07.tst.smt2",
    #"10.tst.smt2",
    #"12.tst.smt2",
    "13.tst.smt2",
    "14.tst.smt2",
    "15.tst.smt2",
    #"16.tst.smt2",
    "17.tst.smt2",
    "18.tst.smt2",
    #"21.tst.smt2",
    "20.tst.smt2",
     "22.tst.smt2",
    );
  }
  foreach my $test_file (@test_files) {
    my @abs_paths;
    find({
      wanted   => sub { push @abs_paths, $_ if -f and -r and basename($_, "") eq $test_file },
      no_chdir => 1,
    }, $test_path);
    if (@abs_paths) {
      push (@smt2_files, @abs_paths);
    } else {
      print " $test_file: Not found.\n";
    
      $not_found_count++;
      $not_found_files = $not_found_files . " " . $test_file . "\n";
    }
  }
}

my $tmp_dir = $cwd . "/tmp";

if (-d $tmp_dir) {
  rmtree $tmp_dir;
}
make_path $tmp_dir or die "Failed to create temp folder";

foreach my $smt2_file (@smt2_files) {
  my $rel_path = "";
  if ($print_short) {
    $rel_path = basename($smt2_file, "");
  } else {
    $rel_path = " latest/" . File::Spec->abs2rel($smt2_file, $test_path);
  }
  my $slk_file = $smt2_file . ".slk";
  system($smt2slk . " " . $smt2_file);
  move ($slk_file, $tmp_dir) or die "The move operation failed: $!";
  
  my $smt2_name = basename($slk_file, ".slk");
  my $output = "";
  print " $rel_path: ";
  my $start_time;
  my $end_time;
  if ($timeout > 0) {
    #try {
    #  local $SIG{ALRM} = sub { die "alarm\n" };
    #  alarm $timeout;
    #  $output = `$sleek $tmp_dir/$smt2_name.slk --smt-compete-test 2>&1`;
    #  alarm 0;
    #} catch {
    #  die $_ unless $_ eq "alarm\n";
    #  $output = "timeout";
    #};
    pipe(README, WRITEME);
    if (my $pid = fork) { # Parent
      try {
        local $SIG{ALRM} = sub {kill 9, -$pid; die "TIMEOUT!\n"};
        alarm($timeout);
        $start_time = gettimeofday();
        waitpid($pid, 0);
        $end_time = gettimeofday();
        alarm(0);
        close(WRITEME);
        while (<README>) {
          $output .= $_;
        }
        close(README);
      } catch {
        die $_ unless $_ eq "TIMEOUT!\n";
        $end_time = gettimeofday();
        $output = "timeout";
      }
    } else { # Child
      die "cannot fork: $!" unless defined $pid;
      setpgrp(0,0);
      open(STDOUT, ">&=WRITEME") or die "Couldn't redirect STDOUT: $!";
      open(STDERR, ">&=WRITEME") or die "Couldn't redirect STDERR: $!";
      close(README);
      exec($sleek, @options, "$tmp_dir/$smt2_name.slk") or die "Couldn't run $sleek: $!\n";
      exit(0);
    }
  } else { # No timeout setting
    $start_time = gettimeofday();
    $output = `$sleek $tmp_dir/$smt2_name.slk --smt-compete-test 2>&1`;
    $end_time = gettimeofday();
  }
  
  my $diff = $end_time - $start_time;
  $total_time += $diff;
  if ($output =~ "UNKNOWN") {
    println("UNK", $diff);
    $unknown_count++;
    $unknown_files = $unknown_files . $rel_path . "\n";
  } elsif ($output =~ "Unexpected") {
    if ($output =~ "UNSAT") {
      println("Unexpected: UNSOUND", $diff);
      $unsound_count++;
      $unsound_files = $unsound_files . $rel_path . "\n";
    } else {
      if ($output =~ "may") {
        println("Unexpected (may)", $diff);
      } else {
        println("Unexpected", $diff);
      }
    }
    
    $unexpected_count++;
    $unexpected_files = $unexpected_files . $rel_path . "\n";
  } elsif ($output eq "timeout") {
    println("Timeout", $diff);
      
    $timeout_count++;
    $timeout_files = $timeout_files . $rel_path . "\n";
  } elsif ($output =~ "exception") {
    my @lines = split /\n/, $output;
    my $error = "";
    foreach my $line (@lines) {
      if ($line =~ "exception") {
        $error .= $line;
      }
    }
  
    print "$error\n";
      
    $error_count++;
    $error_files = $error_files . "$rel_path: $error\n";
  } else {
    if ($output =~ "may") {
      println("OK (may)", $diff);
    } else {
      println("OK", $diff);
    }
  }
}

if ($unexpected_count + $not_found_count + $timeout_count + $error_count + $unknown_count) {
  if ($not_found_count > 0) {
    print "\nTotal number of not found files: $not_found_count in:\n$not_found_files\n";
  }
  
  if ($unexpected_count > 0) {
    print "\nTotal number of unexpected results: $unexpected_count in files:\n$unexpected_files\n";
  }
  
  if ($unsound_count > 0) {
    print "\nTotal number of unsound results: $unsound_count in files:\n$unsound_files\n";
  }
  
  if ($error_count > 0) {
    print "\nTotal number of errors: $error_count in files:\n$error_files\n";
  }

  if ($timeout_count > 0) {
    print "\nTotal number of timeout files: $timeout_count in:\n$timeout_files\n";
  }
  
  if ($unknown_count > 0) {
    print "\nTotal number of unknown results: $unknown_count in files:\n$unknown_files\n";
  }
} else {
  print "\nAll test results were as expected.\n";
}

if ($print_time) {
  print "Total: $total_time (s).\n";
}
