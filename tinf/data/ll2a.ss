data node { int val; node next }

ll<n> == 
	self = null & n = 0 or 
	self::node<v, p> * p::ll<n1> & n = n1 + 1
	inv n >= 0;

int length (node x)
  infer [@term]
	requires x::ll<n>
        ensures x::ll<n> & res=n;
{
	if (x == null) return 0;
	else return 1 + length(x.next);
}
/*
# ll2a.ss --imm

-- below pick implicit and expilict
   parameters from spec
   that are of int/bool type
-- Did we miss something?

      let params = imp_spec_vars @params  in
      let params = List.filter 
        (fun sv -> match sv with
          | CP.SpecVar(t,_,_) -> 
                (match t with
                  | Int | Bool -> true
                  | _ -> false)) params in


Questions: 
 (1) what if there are redundant integer parameters
 (2) what if some non-int/non-bool parameters are critical?
 (3) Can case-spec presentation be improved?

Termination Inference Result:
length:  
requires x::ll<n> & true
    case {
       1<=n -> requires emp & Term[62,3,0+(1*n)]
               ensures x::ll<n_41> & n_41=n & res=n; 
       n=0 -> requires emp & Term[62,1]
              ensures x::ll<n_41> & n_41=n & 
                          res=n; 
                          }

int length (node x)
	infer[@term]
	requires x::ll<n>@L
        ensures res=n;


!!! params2:[]
!!! imp_spec_vars:[]
!!! specs: EInfer @post []
   EBase exists (Expl)[](Impl)[n](ex)[]x::ll{}<n>&{FLOW,(24,25)=__norm}[]
           EAssume 
             (exists n1: x::ll{}<n1>&n1=n&{FLOW,(24,25)=__norm})[]


Checking procedure length$node... Proving binding in method length$node for spec  EAssume 
   emp&{FLOW,(24,25)=__norm}[]
   , Line 10

( [(,1 ); (,2 )]) bind: node  x'::node<val_13_1183',next_13_1184'> cannot be derived from context
ll2a.ss_13:24_13:30



*/
