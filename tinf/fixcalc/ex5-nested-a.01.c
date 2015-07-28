extern int __VERIFIER_nondet_int(void);
/*@ relation nondet_int__(int x). */

int test_fun(int x, int y)
{
    int c = 0;
    while (x > 0) {
        y = 0;
        while (y < x) {
            y = y + 1;
            c = c + 1;
        }
        x = x - 1;
    }
    return c;
}

int main() {
    return test_fun(__VERIFIER_nondet_int(), __VERIFIER_nondet_int());
}

/*
typechecker.ml
    (* QUICK FIX : why did we remove pre/post? *)
    (* let () = prog.prog_rel_decls # reset in *)
    (* let () = prog.prog_rel_decls # push_list rem_pure_inf_prog_rel_decls in *)

@post_n
=======
!!! **infer.ml#2149:RelInferred (simplified):[RELDEFN post_1489: ( y<x & post_1489(1+c,x,1+y,c',y',flow)) -->  post_1489(c,x,y,c',y',flow)]
!!! **infer.ml#2149:RelInferred (simplified):[RELDEFN post_1489: ( c'=c & y'=y & x<=y) -->  post_1489(c,x,y,c',y',flow)]

[RELDEFN post_1489: ( y<x & post_1489(1+c,x,1+y,c',y',flow)) -->  post_1489(c,x,y,c',y',flow),
RELDEFN post_1489: ( c'=c & y'=y & x<=y) -->  post_1489(c,x,y,c',y',flow)]

!!! **fixcalc.ml#1027:Input of fixcalc: :post_1489:={[c,x,y] -> [PRIc,PRIy,flow] -> []: (PRIc=c && PRIy=y && x<=y ||  (exists (fc_1519: (exists (fc_1518:post_1489(fc_1518,x,fc_1519,PRIc,PRIy,flow) && fc_1518=1+c))  && fc_1519=1+y))  && y<x)
};
bottomupgen([post_1489], [2], SimHeur);
!!! **fixcalc.ml#390:svls (orig):[post_1489,c',y',flow,c,y,x]
!!! **fixcalc.ml#391:svls (from parse_fix):[x,y,y',c,c']
!!! **fixcalc.ml#1055:Result of fixcalc (parsed): :[ ((x>=(1+y) & x=y' & y+c'=c+x) | (y>=x & y=y' & c=c'))]
!!! **pi.ml#762:pre_rel_fmls:[]
!!! **pi.ml#763:pre_fmls:[ true, MayLoop[]]
!!! **pi.ml#773:>>>>>>>>>>> (bef postprocess): <<<<<<<<<
!!! **pi.ml#774:>>REL POST:  post_1489(c,x,y,c',y',flow)
!!! **pi.ml#775:>>POST:  ((x>=(1+y) & x=y' & y+c'=c+x) | (y>=x & y=y' & c=c'))
!!! **pi.ml#776:>>REL PRE :  true
!!! **pi.ml#777:>>PRE :  true

Post Inference result:
while_8_8$int~int~int
 EBase 
   emp&MayLoop[]&{FLOW,(4,5)=__norm#E}[]
   EAssume 
     ref [c;y]
     emp&((y>=x & y=y' & c=c') | (x>=(1+y) & x=y' & y+c'=c+x))&
     {FLOW,(4,5)=__norm#E}[]


!!! **infer.ml#2149:RelInferred (simplified):[RELDEFN post_1521: ( x=c_1554-c & y_1556=c_1554-c & x_1555=(c_1554-c)-1 & c<c_1554 & 
 post_1521(c_1554,x_1555,y_1556,c',x',y',flow)) -->  post_1521(c,x,y,c',x',y',flow)]
!!! **infer.ml#2149:RelInferred (simplified):[RELDEFN post_1521: ( c'=c & y'=y & x'=x & x<=0) -->  post_1521(c,x,y,c',x',y',flow)]

[RELDEFN post_1521: ( x=c_1554-c & y_1556=c_1554-c & x_1555=(c_1554-c)-1 & c<c_1554 & 
 post_1521(c_1554,x_1555,y_1556,c',x',y',flow)) -->  post_1521(c,x,y,c',x',y',flow),
RELDEFN post_1521: ( c'=c & y'=y & x'=x & x<=0) -->  post_1521(c,x,y,c',x',y',flow)]

!!! **fixcalc.ml#1027:Input of fixcalc: :post_1521:={[c,x,y] -> [PRIc,PRIx,PRIy,flow] -> []: (PRIc=c && PRIy=y && PRIx=x && x<=0 ||  (exists (y_1556: (exists (x_1555: (exists (c_1554:c=c_1554-(y_1556) && post_1521(c_1554,x_1555,y_1556,PRIc,PRIx,PRIy,flow)))  && x_1555=y_1556-(1)))  && x=y_1556 && 1<=y_1556)) )
};
bottomupgen([post_1521], [2], SimHeur);
!!! **fixcalc.ml#390:svls (orig):[y,c,post_1521,c',x',y',flow,x]
!!! **fixcalc.ml#391:svls (from parse_fix):[c,c',x',x,y,y']
!!! **fixcalc.ml#1055:Result of fixcalc (parsed): :
[ (((3+c')>=(c+(3*x)) & c'>=(c+x) & x>=0 & 0=x' & 1=y') | 

while_6_4$int~int~int
 EBase 
   emp&MayLoop[]&{FLOW,(4,5)=__norm#E}[]
   EAssume 
     ref [c;x;y]
     emp&
     ((0>=x' & c=c' & x'=x & y=y') | 
      ((3+c')>=(c+(3*x)) & c'>=(c+x) & x>=0 & 0=x' & 1=y'))&
     {FLOW,(4,5)=__norm#E}[]

========================================================
@term
======
!!! **pi.ml#745:sp:compute_fixpoint:[( c'=c & y'=y & x'=x & x<=0, post_1558(c,x,y,c',x',y',flow)),( x=c_1591-c & y_1593=c_1591-c & x_1592=(c_1591-c)-1 & c<c_1591 & 
 post_1558(c_1591,x_1592,y_1593,c',x',y',flow), post_1558(c,x,y,c',x',y',flow))]
!!! **pi.ml#746: post_1558(c,x,y,c',x',y',flow) = ( c'=c & y'=y & x'=x & x<=0) \/ ( x=c_1591-c & y_1593=c_1591-c & x_1592=(c_1591-c)-1 & c<c_1591 & 
 post_1558(c_1591,x_1592,y_1593,c',x',y',flow))
!!! PROBLEM with fix-point calculation
ExceptionNot_foundOccurred!

Error1(s) detected at main 

=====================================================

!!! **pi.ml#745:sp:compute_fixpoint:[( c'=c & y'=y & x'=x & x<=0, post_1521(c,x,y,c',x',y',flow)),( x=c_1554-c & y_1556=c_1554-c & x_1555=(c_1554-c)-1 & c<c_1554 & 
 post_1521(c_1554,x_1555,y_1556,c',x',y',flow), post_1521(c,x,y,c',x',y',flow))]
!!! **pi.ml#746: post_1521(c,x,y,c',x',y',flow) = ( c'=c & y'=y & x'=x & x<=0) \/ ( x=c_1554-c & y_1556=c_1554-c & x_1555=(c_1554-c)-1 & c<c_1554 & 
 post_1521(c_1554,x_1555,y_1556,c',x',y',flow))
*************************************
****** Before putting into fixcalc*******
pre_vars: c,x,y
post_vars: c',x',y',flow
*************************************
formula:  ((c'=c & y'=y & x'=x & x<=0) | 
  exists(y_1556:exists(x_1555:exists(c_1554:c=c_1554-y_1556 & 
                                            post_1521(c_1554,x_1555,y_1556,c',x',y',flow)) & 
                              x_1555=y_1556-1) & 
                x=y_1556 & 1<=y_1556))
*************************************

Using @post_n
=============
(==fixcalc.ml#848==)
look_up_rel_args_type_from_prog@2
look_up_rel_args_type_from_prog inp1 :post_1521
look_up_rel_args_type_from_prog@2 EXIT:[int,int,int,int,int,int,int]

Using @term
============
(==fixcalc.ml#848==)
look_up_rel_args_type_from_prog@2
look_up_rel_args_type_from_prog inp1 :post_1558
look_up_rel_args_type_from_prog@2 EXIT ExceptionNot_foundOccurred!

Exception(substitute_args):Not_found
Exception(extract_inv_helper):Not_found
Exception(compute_fixpoint_xx):Not_found
Exception(compute_fixpoint_x2):Not_found
Exception(compute_fixpoint_2):Not_found
*/
