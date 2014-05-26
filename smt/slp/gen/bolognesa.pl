#!/usr/bin/perl -w

use strict;
use Math::Random qw/:all/;
use Getopt::Long qw/:config no_ignore_case/;

my $N = 10;
my $n = 10;
my $d = 10;
my $p = 0.3;
my $fmt = 'sf';
my $seed;
my $help;
my $opts = join(" ", @ARGV);
my %format = (
  'sl' => [\&sl_atom, \&sl_entail],
  'sf' => [\&sf_atom, \&sf_entail],
  'js' => [\&js_atom, \&js_entail],
  'slk' => [\&sk_atom, \&sk_entail]
);

GetOptions(
   'samples|N=i'    => \$N,
   'nodes|n=i'      => \$n,
   'domain|d=i'     => \$d,
   'nextp|p=f'      => \$p,
   'format|fmt|f=s' => \$fmt,
   'seed|s=s'       => \$seed,
   'help|h'         => \$help
);

if ($help) {
  print <<'USAGE';
Usage: ./bolognesa.pl [options]

Available options include:

  -N NUM, --samples=NUM
        Number of sample instances to generate. Default: 10.
        
  -n NUM, --nodes=NUM
        Number of nodes (variables) per instance. Default: 10.
        
  -d NUM, --domain=NUM
        Number of edges to generate in the "unfolded" spatial term.
        Default: 10.
        
  -p PROB, --nextp=PROB
        Probability of any edge to appear as a "next" pointer. 1 - PROB is the
        probability of an edge to appear as a list segment. Default: 0.3.
        
  -f FORMAT, --format=FORMAT
        Format to use when writing the formulas. The available formats are 'sf'
        for Smallfoot, 'js' for jStar, and 'sl' for SLP and 'slk' for Sleek (Asankhaya). Default: 'sf'.
        
  -s SEED, --seed=SEED
        Any string to be used as seed for the pseudo-random number generator.
        You need to specify this if you want reproducible generation of
        formulas.
USAGE

  exit 1;
}

die "Unknown format: $fmt\n" unless defined $format{$fmt};

random_set_seed_from_phrase($seed) if defined $seed;
print "% $opts\n\n" if $fmt eq 'sl';
print "tl;\n\n" if $fmt eq 'sf';
print "data node { int val ; node next }.\n 
pred lseg<p> == self = p 
or self::node<_,r> * r::lseg<p> & self!=p inv true.\n\n" if $fmt eq 'slk';

my ($atom, $entail) = @{ $format{$fmt} };
my $vars = join(", ", map { "x$_" } (1..$n));

for my $i (1..$N) {
  if($fmt eq 'slk') {
    print "//Entail($i)\n";
  }
  print make_formula("ex$i", $n, $d, $p), "\n\n";
}

sub make_formula {
  my ($label, $n, $d, $p) = @_;
  my %heap;
  my @A;
  my @B;
  
  while ($d) {
    my ($x, $y) = random_uniform_integer(2, 1, $n);
    my $to = random_binomial(1, 1, $p) ? "next" : "lseg";
    next if $x == $y;
    next if exists $heap{$x};
    $heap{$x} = $y;
    push @A, $atom->($to, $x, $y);
    $d--;
  }
  
  my @dom = random_permutation(keys %heap);
  while (@dom) {
    my $x = shift @dom;
    next unless exists $heap{$x};
    
    my %seen = ( $x => 1 );
    my $z = $x;
    while (exists $heap{$z} && !$seen{$heap{$z}}) {
      $z = delete $heap{$z};
      $seen{$z} = 1;
    }
    push @B, $atom->('lseg', $x, $z);
  }
  
  return $entail->($label, \@A, \@B);
}

sub sl_atom {
  my ($to, $x, $y) = @_;
  return "$to(x$x, x$y)";
}

sub sl_entail {
  my ($ex, $A, $B) = @_;
  return "$ex :: ", join(" * ", @$A), " ==> ", join(" * ", @$B), ".";
}

sub sf_atom {
  my ($to, $x, $y) = @_;
  return "x$x |-> x$y" if $to eq 'next';
  return "$to(x$x, x$y)";
}

sub sf_entail {
  my ($ex, $A, $B) = @_;
  return "$ex($vars) [", join(" * ", @$A), "] { } [", join(" * ", @$B), "]";
}

sub js_atom {
  my ($to, $x, $y) = @_;
  return "NodeLL(x$x, x$y)" if $to eq 'next';
  return "lspe(x$x, x$y)";
#  return "field($x,\"<NodeLL: NodeLL $to>\", $y)";
}

sub js_entail {
  my ($ex, $A, $B) = @_;
  return "Implication:\n  ", join(" * ", @$A), " |- ", join(" * ", @$B);
}

sub sk_atom {
  my ($to, $x, $y) = @_;
  return "x$x\:\:node<_,x$y>" if $to eq 'next';
  return "x$x\:\:lseg<x$y>";
#  return "field($x,\"<NodeLL: NodeLL $to>\", $y)";
}

sub sk_entail {
  my ($ex, $A, $B) = @_;
  return "checkentail ", join(" * ", @$A), " |- ", join(" * ", @$B), ".";
}
