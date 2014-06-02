#!/usr/bin/perl -w

use strict;
use Getopt::Long qw/:config no_ignore_case/;
use Data::Dumper;
$Data::Dumper::Deepcopy = 1;

my $fmt = 'sf';
my $clone = 1;
my $help;

GetOptions(
   'clone|n=i'      => \$clone,
   'format|fmt|f=s' => \$fmt,
   'help|h'         => \$help
);

if ($help) {
  print <<'USAGE';
Usage: ./sl2clone.pl [options] [files]

Available options include:

  -n NUM, --clone=NUM
        Number of clones made for each instance. Default: 1.
        
  -f FORMAT, --format=FORMAT
        Format to use when writing the formulas. The available formats are 'sf'
        for Smallfoot, 'js' for jStar, and 'sl' for SLP and 'slk' for Sleek (Asankhaya). Default: 'sf'.
USAGE

  exit 1;
}

print "hd,tl;\n\n" if $fmt eq 'sf';
print "data node { int val ; node next }.\n 
pred lseg<p> == self = p 
or self::node<_,r> * r::lseg<p> & self!=p inv true.\n\n" if $fmt eq 'slk';

my $i = 0;
my @error;
my $skip = 0;
my $ex;

while (<>) {
  next unless s/^%  //;
  my $data = parse_entail($_);
  if (exists $data->{'ERROR'}) {
    $skip++;
    push @error, @{ $data->{'ERROR'} };
  } else {
    $i++;
    print entail_str($i, $data, $clone), "\n\n";
  }
}

# exit 0 unless $skip;
# warn "$skip instances skipped\nOffending terms:\n";
# for my $term (@error) { warn "  $term\n" };

sub entail_str {
  my ($num, $data, $clone) = @_;
  my $nvars = (scalar keys %{ $data->{'VARS'} });
  my $pre = conj_str($data->{'PRE'}, $clone, $nvars);
  my $pos = conj_str($data->{'POS'}, $clone, $nvars);
  return "fun$num :: $pre ==> $pos."    if $fmt eq 'sl';
  return "Implication: /* $num */\n  $pre |- $pos" if $fmt eq 'js';
  return "checkentail $pre |- $pos." if $fmt eq 'slk';
  my $vars = join(", ", map { "x$_" } (1..($nvars * $clone)));
  return "fun$num ($vars) [ $pre ] { } [ $pos ]";
}

sub conj_str {
  my ($conj, $clone, $nvars) = @_;
  my @pure;
  my @heap;
  my $offset = 0;
  while ($clone > 0) {
    push @pure, map { term_str($_, $offset) } @{ $conj->{'PURE'} };
    push @heap, map { term_str($_, $offset) } @{ $conj->{'HEAP'} };
    $offset += $nvars;
    $clone--;
  }
  push @heap, emp_str() unless @heap;
  return join(' * ', @pure, @heap) if ($fmt ne 'sl' && $fmt ne "slk");
  push @pure, join(" * ", @heap);
  return join(', ', @pure) if $fmt eq 'sl';
  return join(' & ', reverse(@pure)) if $fmt eq 'slk';
}

sub emp_str {
  if ($fmt eq "slk") {
  return "x1 = x1"
  }
  return $fmt eq "js" ? "x1==x1" : "emp";
}

sub term_str {
  my ($term, $offset) = @_;
  my @args = @$term;
  my $fun = shift @args;
  
  if ($fun eq '==') {
    my ($x, $y) = map { expr_str($_, $offset) } @args;
    return ($fmt eq 'sl' || $fmt eq 'slk') ? "$x = $y" : "$x==$y";
  } elsif ($fun eq '!=') {
    my ($x, $y) = map { expr_str($_, $offset) } @args;
    return $fmt eq 'sl' ? "$x ~= $y" : "$x!=$y";
  } elsif ($fun eq 'LSEG') {
    my ($x, $y) = map { expr_str($_, $offset) } @args;
    if ($fmt eq 'slk') {
    return $x eq 'null' ? "z::lseg<z>" :"$x\:\:lseg<$y>";
    }
    return $fmt eq 'js' ? "lspe($x, $y)" : "lseg($x, $y)";
  } elsif ($fun eq 'PTR') {
    my $to = shift @args;
    my ($x, $y) = map { expr_str($_, $offset) } @args;
    return "$x |-> $to:$y" if $fmt eq 'sf';
    return $fmt eq 'slk' ? "$x\:\:node<_,$y>" : $fmt eq 'sl' ? "next($x, $y)" : "NodeLL($x, $y)" if $to eq 'tl';
    return $fmt eq 'slk' ? $y eq 'null' ? "$x\:\:node<_,_>" : "$x\:\:node<$y,_>" : $fmt eq 'sl' ? "data($x, [$to-$y])" : "field($x,$to,$y)";
  } elsif ($fun eq 'DOM') {
    my $x = expr_str($args[0], $offset);
    return "$x |->"       if $fmt eq 'sf';
    return "data($x, [])" if $fmt eq 'sl';
    return "$x\:\:node<>" if $fmt eq 'slk';
    $ex++;
    return "field($x, _f$ex, _e$ex)";
  } else {
    die "Malformed term:\n" . Dumper($term) . "\n";
  }
}

sub expr_str {
  my ($expr, $offset) = @_;
  if (ref $expr eq '') {
    return 'nil'   if $expr eq '0' && $fmt eq 'sl';
    return 'null'  if $expr eq '0' && $fmt eq 'slk';
    return 'nil()' if $expr eq '0' && $fmt eq 'js';
    return $expr;
  }
  $offset = 0 unless defined $offset;
  return 'x' . ($expr->[1] + $offset);
}

sub parse_entail {
  my $entail = shift @_;
  my $data = { 'VARS' => { } };
  
  $entail =~ s/\s+$//;
  my ($pre, $pos) = split ' \|- ', $entail;
  parse_terms($data, 'PRE', $pre);
  parse_terms($data, 'POS', $pos);
  return $data;
}

sub parse_terms {
  my ($data, $sign, $terms) = @_;
  $data->{$sign} = { 'PURE' => [], 'HEAP' => [ ] };
  for my $term (split ' \* ', $terms) {
    parse_term($data, $data->{$sign}, $term)
  }
}

sub parse_term {
  my ($data, $lits, $term) = @_;
  
  $term =~ s/^\s+//;
  $term =~ s/\s+$//;
  if ($term eq 'emp') {
    # do nothing
  } elsif ($term =~ m/^(\w+)([!=]=)(\w+)$/) {
    push @{ $lits->{'PURE'} }, [$2, fetch_vars($data, $1, $3)];
  } elsif ($term =~ m/^listseg\(tl; (\w+), (\w+)\)$/) {
    push @{ $lits->{'HEAP'} }, ['LSEG', fetch_vars($data, $1, $2)];
  } elsif ($term =~ m/^(\w+) \|-> (\w+):(\w+)$/) {
    push @{ $lits->{'HEAP'} }, ['PTR', $2, fetch_vars($data, $1, $3)];
  } elsif ($term =~ m/^(\w+) \|->$/) {
    push @{ $lits->{'HEAP'} }, ['DOM', fetch_vars($data, $1)];
  } else {
    push @{ $data->{'ERROR'} }, $term;
  }
}

sub fetch_vars {
  my $data = shift @_;
  return map { fetch_var($data, $_) } @_;
}

sub fetch_var {
  my ($data, $v) = @_;
  die "Strange variable: $v" unless $v =~ /^\w+$/;
  return $v if $v =~ /^\d+$/;
  
  my $vars = $data->{'VARS'};
  $vars->{$v} = ['VAR', (scalar keys %$vars) + 1, $v] unless (exists $vars->{$v});
  return $vars->{$v};
}

