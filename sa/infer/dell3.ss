data cell {
  int val;
}

/*
void main(cell x, cell y)
  infer[@shape,@post_n,@term]
  requires true
  ensures true;
{
  while (y.val<x.val) 
    infer[@shape,@post_n,@term]
      requires true
      ensures true;
  {
    x.val = x.val-1;
  }
}
*/

void loop(cell x,cell y)
  infer [@shape
         ,@post_n,@term
  ]
  requires true
  ensures true;
{
  if (y.val<x.val) {
    //dprint;
    x.val = x.val-1;
    // dprint;
    loop(x,y);
  }
}

/*
# dell3.ss 

void loop(cell x,cell y)
  infer [@shape
         ,@post_n
  ]


Why post did not have base-case branch?
                     ]
*************************************
******pure relation assumption*******
*************************************
[RELDEFN post_1541: ( val_28_1514=val_28_1509 & val_28_1513=val_28_1510 & val_28_1509<=val_28_1510) -->  post_1541(val_28_1513,val_28_1514,val_28_1509,val_28_1510)]
*************************************

*************************************
*******fixcalc of pure relation *******
*************************************
[( post_1541(val_28_1509,val_28_1510,val_28_1513,val_28_1514), val_28_1509=val_28_1514 & val_28_1510=val_28_1513 & val_28_1514<=val_28_1513, true, true)]
*************************************

!!! REL POST :  post_1541(val_28_1509,val_28_1510,val_28_1513,val_28_1514)
!!! POST:  val_28_1509=val_28_1514 & val_28_1510=val_28_1513 & val_28_1514<=val_28_1513
!!! REL PRE :  true
!!! PRE :  true

void loop(cell x,cell y)
  infer [@post_n
  ]

Why does the above different from dell3a.ss woeka...

[RELDEFN post_1460: ( post_1460(d_1442,e_1443,a_1488,b) & a=1+a_1488 & b<=a_1488) -->  post_1460(d_1442,e_1443,a,b),
RELDEFN post_1460: ( d_1442=a & e_1443=b & a<=b) -->  post_1460(d_1442,e_1443,a,b)]
*************************************

!!! >>>>>> compute_fixpoint <<<<<<
!!! Input of fixcalc: post_1460:={[a,b] -> [d_1442,e_1443] -> []: (((d_1442=a && e_1443=b) && a<=b) || ( (exists (a_1488:(a_1488+1=a && post_1460(a_1488,b,d_1442,e_1443))))  && b<a))
};
bottomupgen([post_1460], [2], SimHeur);
*************************************
*******fixcalc of pure relation *******
*************************************
[( post_1460(a,b,d_1442,e_1443), ((e_1443=d_1442 & b=d_1442 & d_1442<a) | (a=d_1442 & b=e_1443 & 
d_1442<=e_1443)), true, true)]
*************************************
*/
