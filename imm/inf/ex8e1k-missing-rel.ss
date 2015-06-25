data cell{
 int fst;
}

relation P1(ann v1).
relation P2(ann v1, ann v2).
relation Q(ann v1).
//relation P3(ann v1, int v,int r, int s).

int foo(cell c)
  infer [QQ]
  requires c::cell<v>@a & a=@L //a=@L
  ensures c::cell<_>@b & QQ(b); //c::cell<w>@b & b=@L  ;
/*
  requires c::cell<v>@a & a=@L
  ensures emp; //c::cell<w>@b & b=@L  ;
*/
{
 int x = c.fst;
 if (x!=1) {
   //c.fst =c.fst-1;
   int tmp=2+foo(c);
   dprint;
   return tmp;
 } else return 0;
}

/*
# ex8e1g.ss

# why exists(QQ:QQ(..))

(==#0==)
pure_mkExists@1014
pure_mkExists inp1 :[imm_1499,QQ,a_1492]
pure_mkExists inp2 : imm_1499=@L & a_1492=@L & c=c' & a=@L & x'=v & QQ(@A) & v!=1
pure_mkExists@1014 EXIT: exists(a_1492:a_1492=@L) & exists(QQ:QQ(@A)) & 
exists(imm_1499:imm_1499=@L) & c=c' & a=@L & x'=v & v!=1

Successful States:
[
 Label: [(,0 ); (,1 )]
 State:c::cell<v>@L&exists(QQ:QQ(@A)) & c=c' & a=@L & x'=v & v!=1&
         {FLOW,(4,5)=__norm#E}[]
       es_pure: @L<:a_1492 & a_1492=@L
       es_cond_path: [1; 0]
       es_var_measures 1: Some(MayLoop[]{})
       es_infer_vars_rel: [QQ]
 Exc:None

 GOT:
===
!!! **infer.ml#2139:RelInferred (simplified):[RELDEFN Q: ( @L<:b_1463) -->  Q(b_1463)]push_list:[RELDEFN Q: ( @L<:b_1463) -->  Q(b_1463)]

!!! **infer.ml#2139:RelInferred (simplified):[RELDEFN Q: ( @L<:b_1463) -->  Q(b_1463)]push_list:[RELDEFN Q: ( @L<:b_1463) -->  Q(b_1463)]


# Could we organize your simplification as a separate step
so that we can later explore other alternative;
and it is clearer that how some simplification has taken place?

I am particularly worried that recursive call has disappeared;
and would like to see when it disappeared.

=====

c::cell<..>@L |- c::cell<..>@L (bind)
c::cell<..>@L * c::cell<..>@b1 & Q(b1) (pre-cond proving)
c::cell<..>@I & I=@L-@b1 & Q(b1) |- c::cell<..>@b & Q(b)  (post-cond)

Thus far when proving the recursive post-cond, we got the
following:

 I=@L-@b1 & Q(b1) & I<:@b --> Q(b)

which is equivalent to:

[RELDEFN Q: ( Q(b_1507) & (b_1507+@L)<:b_1463) -->  Q(b_1463),

The point here is what is permitted for
 I=@L-b1
where @b1 is the annotation in the post-condition.

Now b1 can either be @A, @M and @L. 

It cannot be @M since @L-@M is invalid. 

It cannot be @L since @L is not allowed in
post-condition.

Hence, it can only be @A. Using this instantiation,
we would now obtain:

 I=@L-@b1 & b1=@A & Q(b1) & I<:@b --> Q(b)
 I<:@b --> Q(b)

 With this we only have:
   @L<:b  --> Q(b)

 Doing a post-condition processing, we get:
  Q(b) = b=@A

We can check if this idea applies to loop-write..

*/
