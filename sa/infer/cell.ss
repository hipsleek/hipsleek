data cell {
  int val;
}

void main(cell x, cell y)
  infer[@shape,@post_n,@term]
  requires x::cell<_> * y::cell<_>
  ensures x::cell<_> * y::cell<_>;
{
  while (y.val<x.val) 
    infer[@shape,@post_n,@term]
      requires x::cell<_> * y::cell<_>
      ensures x::cell<_> * y::cell<_>;
  {
    x.val = x.val-1;
  }
}
/*
# cell.ss -pcp

  while (y.val<x.val) 
    infer[@shape]
      requires true
      ensures true;

Why bind-error?
Using --pcp, I noted the following:

while-loop uses infer[@shape], but main uses 
infer[H,G]. I guess the translation of @shape
occurred before loop removal. I think this situation
corrected.

void f_r_1200_while_10_2$cell~cell(  cell x,  cell y)
@ref x, y
 rec
static  EInfer @shape[]
   EBase emp&{FLOW,(4,5)=__norm}[]
           EBase emp&MayLoop[]&{FLOW,(4,5)=__norm}[]
                   EAssume ref [x;y]
                     emp&{FLOW,(4,5)=__norm}[]

void main$cell~cell(  cell x,  cell y)
static  EInfer [HP_11,GP_12]
   EBase HP_11(x,y)&{FLOW,(4,5)=__norm}[]
           EBase emp&MayLoop[]&{FLOW,(4,5)=__norm}[]
                   EAssume 
                     GP_12(x,y)&{FLOW,(4,5)=__norm}[]


Checking procedure f_r_1200_while_10_2$cell~cell... Proving binding in method f_
r_1200_while_10_2$cell~cell for spec  EAssume ref [x;y]
   emp&{FLOW,(4,5)=__norm}[]
   , Line 0

( []) bind: node  y'::cell<val_10_1205'>@L cannot be derived from context
cell.ss_10:9_10:14

===


*/
