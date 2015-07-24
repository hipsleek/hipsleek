bool rand()
  requires Term
  ensures true;

relation P(int i, int j).
  relation Q(int i, int j,int r).


int bsearch(int i, int j)
  infer[P,Q]
  requires P(i,j)
  ensures Q(i,j,res);
{
  if (i>=j) return i;
  int mid = (i+j)/2;
  if (rand()) return bsearch(i,mid);
  return bsearch(mid+1,j);
}

/*
# i-ex7a.ss

Below is present in default but not in ann_2 branch. 

!!! **fixcalc.ml#908:No of disjs:1
!!! **fixcalc.ml#913:bottom up
!!! fixcalc file name: logs/fixcalc.inf
(==fixcalc.ml#1337==)
compute_fixpoint_aux@5@4
compute_fixpoint_aux inp1 :[( Q(i,j,res), ((i=res & j<=res) | 
exists(mid_1490:exists(fc_mid_1493:Q(fc_mid_1493,j,res) & fc_mid_1493=1+
mid_1490) & 0<=mid_1490 & mid_1490<j & (i+j)<=(1+(2*mid_1490)) & (2*
mid_1490)<=(i+j)) | exists(mid':0<=mid' & mid'<j & (i+j)<=(1+(2*mid')) & (2*
mid')<=(i+j) & Q(i,mid',res))),1)]
compute_fixpoint_aux inp2 :[P,i,j]
compute_fixpoint_aux@5 EXIT:[( Q(i,j,res), res>=i)]

(==pi.ml#617==)
compute_fixpoint#2@4
compute_fixpoint#2 inp1 :[( 0<=mid_1490 & mid_1490<j & (j+i)<=(1+(2*mid_1490)) & (2*mid_1490)<=(j+i) & 
Q(1+mid_1490,j,res), Q(i,j,res)),
( i=res & j<=res, Q(i,j,res)),
( 0<=mid' & mid'<j & (j+i)<=(1+(2*mid')) & (2*mid')<=(j+i) & Q(i,mid',res), Q(i,j,res))]
compute_fixpoint#2 inp2 :[P,i,j]
compute_fixpoint#2@4 EXIT:[( Q(i,j,res), res>=i)]

!!! **pi.ml#619:bottom_up_fp0:[( Q(i,j,res), res>=i)]
!!! **pi.ml#636:fixpoint:[( Q(i,j,res), res>=i, P(i,j), true)]
!!! **pi.ml#650:>>REL POST :  Q(i,j,res)
!!! **pi.ml#651:>>POST:  res>=i
!!! **pi.ml#652:>>REL PRE :  P(i,j)
!!! **pi.ml#653:>>PRE :  true

*/
