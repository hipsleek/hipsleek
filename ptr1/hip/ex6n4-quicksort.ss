data arrI {
  int val;
}

// Predicates
arr_seg<i,n> == i=n & i>=0
  or x::arrI<_>*self::arr_seg<i+1,n> & x=self+i & i>=0
  inv n>=i & i>=0;

arr_seg_sorted<i,n,ma,mi> == x::arrI<v> & x=self+i & i=n-1 & i>=0
  or x::arrI<mi> * self::arr_seg_sorted<i+1,n,ma,mi1> & x=self+i & mi<=mi1 & i<n-1 & i>=0
  or self::arr_seg_sorted<i,n-1,ma1,mi> * x::arrI<ma> & x+1=self+n & ma>=ma1 & i<n-1 & i>=0
  inv n>i & i>=0;

arr_seg_max_min<i,n,ma,mi> == i=n & i>=0
  or x::arrI<cur> * self::arr_seg_max_min<i+1,n,ma,mi> & x=self+i & i>=0 & i<n & cur<=ma & cur>mi &((!(i=n-1))|(cur=ma & cur=mi))
  inv n>=i & i>=0;

// Primitive operations
void merge_sort(arrI base, int i, int k, int n)
  requires base::arr_seg_sorted<i,k,ma,mi> * base::arr_seg_sorted<k,n,ma1,mi1> & ma<=mi1
  ensures base::arr_seg_sorted<i,n,ma1,mi>;

void unfold_tail_2(arrI base, int i, int n)
  requires base::arr_seg_max_min<i,n,ma,mi> & i<n
  ensures base::arr_seg_max_min<i,n-1,ma,mi> * x::arrI<v> & x+1= base+n & v<=ma & v>=mi; 

void reverse_unfold_2(arrI base, int i,int n)
  requires x::arrI<v>*base::arr_seg_max_min<i+1,n,ma,mi> & x=base+i
  ensures base::arr_seg_max_min<i,n,max(v,ma),min(v,mi)>;

void reverse_unfold_tail_2(arrI base, int i,int n)
 case{
  i<n -> requires x::arrI<v>*base::arr_seg_max_min<i,n-1,ma,mi> & x+1=base+n
    ensures base::arr_seg_max_min<i,n,max(v,ma),min(v,mi)>;
  i>=n -> requires true
    ensures true;
}

void reverse_unfold_sort(arrI base, int i, int n)
  requires x::arrI<v> * base::arr_seg_sorted<i+1,n,ma,mi> & x=base+i & v<=mi
  ensures base::arr_seg_sorted<i,n,ma,v>;

void upd_arr(arrI base, int i, int v)
  requires a::arrI<_> & a=base+i & i>=0
  ensures a::arrI<v> & a=base+i;

arrI arr_inc(arrI a)
  requires true //a::arrI<_>@L
  ensures res=a+1;

int get_arr(arrI base, int i)
  requires a::arrI<v>@L & a=base+i
  ensures res=v;

// Verification with a better specification
int partition(arrI base, int i, int m, int pivot)
  requires base::arr_seg_max_min<i,m,ma,mi>
  ensures base::arr_seg_max_min<i,res,pivot1,mi> * base::arr_seg_max_min<res,m,ma,pivot2> & pivot1<=pivot & pivot2>=pivot;
{
  if(i==m){
    return i;
  }
  else{

    if(i<m-1){

      unfold_tail_2(base,i,m);
      int tmpi=get_arr(base,i);
      int tmpm=get_arr(base,m-1);

      if(tmpi>pivot){
        if(tmpm<=pivot){
          upd_arr(base,i,tmpm);
          upd_arr(base,m-1,tmpi);
        }
        else{
          reverse_unfold_2(base,i,m-1);
          int tmp1 = partition(base,i,m-1,pivot);
          reverse_unfold_tail_2(base,tmp1,m);
          return tmp1;
        }
      }

      reverse_unfold_tail_2(base,i+1,m);
      int tmp2=partition(base,i+1,m,pivot);
      reverse_unfold_2(base,i,tmp2);
      return tmp2;
    }
    else{

      // i == m-1
      int tmpi=get_arr(base,i);
      if(tmpi>pivot){
        return i;
      }
      else{
        return m;
      }
    }
  }
}


// void quicksort(arrI base, int i, int m)
//   requires base::arr_seg_max_min<i,m,ma,mi> & i<m
//   ensures base::arr_seg_sorted<i,m,ma1,mi1> & ma1<=ma & mi1>=mi;
// {
//   if(i>=m-1){
//     //    assume false;
//     get_arr(base,i); // Different predicate names
//     return;
//   }
//   else{
//     // i<m-1
//     // assume false;
//     int pivot = get_arr(base,i); // (i)[i+1...m)

//     int index = partition(base,i+1,m,pivot); // (i)[i+1...index)[index...m)
//     if(index>i+1 && index<m){
//       //      assume false;
//       unfold_tail_2(base,i+1,index); // (i)[i+1...index-1)(index-1)[index...m)
//       int tmp = get_arr(base,index-1); //
//       upd_arr(base,index-1,pivot);
//       upd_arr(base,i,tmp);
//       reverse_unfold_2(base,i,index-1);
//       quicksort(base,i,index-1);
//       quicksort(base,index,m);
//       //      dprint;
//       merge_sort(base,i,index-1,m);
//       //      dprint;
//       return;
//     }
//     else{
//       //assume false;
//       if(index==i+1){
//         //        assume false;
//         quicksort(base,index,m);// (base+index-1)::arrI<pivot> * base::arr_seg_sorted<index,m,ma,pivot2> & pivot2>=pivot
//         reverse_unfold_sort(base,i,m);
//         //dprint;
//         return;
//       }
//       else{
// 	   if(index==m){	       
// 	  unfold_tail_2(base,i+1,index); // (i)[i+1...index-1)(index-1)[index...m)
// 	  int tmp = get_arr(base,index-1);
//           upd_arr(base,index-1,pivot);
//           upd_arr(base,i,tmp);
//           reverse_unfold_2(base,i,index-1);
//           quicksort(base,i,index-1);
//           return;
//         }
//       }
//     }
//   }
// }

