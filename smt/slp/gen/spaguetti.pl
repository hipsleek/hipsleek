#!/usr/bin/perl -w

use strict;
use Math::Random qw/:all/;
use Getopt::Long qw/:config no_ignore_case/;

my $N = 10;
my $n = 10;
my $lsegp = 0.2;
my $neqsp = 0.1;
my $fmt = 'sf';
my %fmt = map { $_ => 1 } qw/sf js sl slk/;
my $seed;
my $help;
my $opts = join(" ", @ARGV);

GetOptions(
   'samples|N=i'    => \$N,
   'nodes|n=i'      => \$n,
   'lsegp|lp=f'     => \$lsegp,
   'neqsp|np=f'     => \$neqsp,
   'format|fmt|f=s' => \$fmt,
   'seed|s=s'       => \$seed,
   'help|h'         => \$help
);

if ($help) {
  print <<'USAGE';
Usage: ./spaguetti.pl [options]

Available options include:

  -N NUM, --samples=NUM
        Number of sample instances to generate. Default: 10.
        
  -n NUM, --nodes=NUM
        Number of nodes (variables) per instance. Default: 10.
        
  -lp PROB, --lsegp=PROB
        Probability of any list segment to appear in the spatial part of the
        formula. Default: 0.2.
        
  -np PROB, --neqsp=PROB
        Probability of any inequality X ~= Y to appear in the pure part of the
        formula. Default: 0.1.
        
  -f FORMAT, --format=FORMAT
        Format to use when writing the formulas. The available formats are 'sf'
        for Smallfoot, 'js' for jStar, and 'sl' for SLP, and 'slk for Sleek (Asankhaya). Default: 'sf'.
        
  -s SEED, --seed=SEED
        Any string to be used as seed for the pseudo-random number generator.
        You need to specify this if you want reproducible generation of
        formulas.
USAGE

  exit 1;
}

die "Unknown format: $fmt\n" unless $fmt{$fmt};

random_set_seed_from_phrase($seed) if defined $seed;
print "% $opts\n\n" if $fmt eq 'sl';
print "tl;\n\n" if $fmt eq 'sf';
print "data node { int val ; node next }.\n 
pred lseg<p> == self = p 
or self::node<_,r> * r::lseg<p> & self!=p inv true.\n\n" if $fmt eq 'slk';

my $vars = join(",", map { "x$_" } (1..$n));

for my $i (1..$N) {
  my $fma = make_formula($n, $lsegp, $neqsp, $fmt);
  if ($fmt eq 'sf') {
    print "ex$i($vars) [$fma] { } [ x1 != x1 ]\n\n";
  } elsif ($fmt eq 'js') {
    print "Implication:\n   $fma |- x1 != x1\n\n";
  } elsif($fmt eq 'slk') {
    print "//Entail($i)\n";
    print "checkentail $fma |- false.\n\n";
  } else {
    print "ex$i :: $fma ==> x1 ~= x1, emp.\n\n";
  }
}

sub make_formula {
  my ($n, $edgep, $diffp, $fmt) = @_;
  
  my $edges = $n * ($n - 1); # edges in complete graph (directed & no self-loops).
  my $k = random_binomial(1, $edges, $edgep); # edges selected

  my %lseg;
  my %neqs;
  while ($k > 0) {
    my ($x, $y) = random_uniform_integer(2, 1, $n);
    next if $x == $y;
    next if exists $lseg{$x}{$y};
    $lseg{$x}{$y} = 1;
    $neqs{$x}{$y} = 1;
    $k -= 1;
  }

#  $edges = $n * ($n - 1) / 2; # edges in complete graph (symmetric & no self-loops).
#  $k = random_binomial(1, $edges, $diffp); # edges selected

#  my %neqs;
#  while ($k > 0) {
#    my ($x, $y) = random_uniform_integer(2, 1, $n);
#    next if $x == $y;
#    ($x, $y) = ($y, $x) if $x > $y;
#    next if exists $neqs{$x}{$y};
#    $neqs{$x}{$y} = 1;
#    $k -= 1;
#  }

  my @lseg;
  my $r;
  while (my ($x, $ys) = each %lseg) {
    for my $y (keys %$ys) {
      if($fmt eq 'js'){
        $r = "lspe(x$x, x$y)";
     }elsif ($fmt eq 'slk') {
        $r = "x$x\:\:lseg<x$y>";
     }else {
        $r = "lseg(x$x, x$y)";
     }
      push @lseg, ($r);
    }
  }
  push @lseg, "emp" unless @lseg > 0;

  my @neqs;
  while (my ($x, $ys) = each %neqs) {
    for my $y (keys %$ys) {
      my $lit = ($fmt eq 'sl' ? "x$x ~= x$y" : "x$x != x$y");
      push @neqs, "$lit";
    }
  }
  
  return join(" * ", @neqs, @lseg) if $fmt eq 'js' || $fmt eq 'sf' ;
  
  push @neqs, (join " * ", @lseg);

  return join(", ", @neqs) if $fmt eq 'sl';
  return join(" & ", reverse(@neqs)) if $fmt eq 'slk';
}
