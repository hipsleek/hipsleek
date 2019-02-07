hip_include 'scontracts/mapprimitives.ss'

data node{
   int val;
   node next;
}


// pred list<n> == self=null & n=0 or
//                 self::node<_,t> * t::list<n-1>
//                 inv n>=0;

// i - iterator
// m - length of proposals
// n - length of proposalNames
void for_loop(mapping(int => int) proposals, int i, int m, int n)
  case {
    i<0  -> requires true
            ensures  true;
    i>=n & i>=0 ->
            requires [ts0] proposals::Map<ts0> &
                      forall(j: !(m<=j & j<m+n) | ts0[j]=0)
            ensures  (exists ts1: proposals::Map<ts1> &
                      forall(j: !(m<=j & j<m+n) | ts1[j]=0));
    i<n  & i>=0 ->
            requires [ts0] proposals::Map<ts0> &
                      forall(j: !(m<=j & j<m+i) | ts0[j]=0)
            ensures  (exists ts1: proposals::Map<ts1> &
                      forall(j: !(m<=j & j<=m+i) | ts1[j]=0));
  }
{
 if(0<=i && i<n)
 {
   proposals[m+i] = 0;
   for_loop(proposals, i+1,m,n);
 }
}

// i - iterator
// m - length of proposals
// ll - length of proposalNames
void for_loop_ballot(mapping(int => int) proposals, int i, int ll, int m)
     case {
       i<0         ->
          requires true
          ensures  true;
       i>=ll & i>=0 ->
          requires [prps0] proposals::Map<prps0> * tmp1::Proposal<xxx,0>
                     & forall(j: !(m<=j & j<m+ll) | (prps0[j]=tmp1 & xxx=j))
          ensures  (exists prps1: proposals::Map<prps1> * tmp1::Proposal<xxx,0>
                     & forall(j: !(m<=j & j<m+ll) | prps1[j]=tmp1 & xxx=j));
       i<ll & i>=0  ->
          requires [prps0] proposals::Map<prps0> * tmp1::Proposal<yyy,0>
                     & forall(j: !(m<=j & j<m+i) | prps0[j]=tmp1 & yyy=j)
          ensures  (exists prps1: proposals::Map<prps1> * tmp1::Proposal<yyy,0>
                     & forall(j: !(m<=j & j<=m+i) | prps1[j]=tmp1 & yyy=j));
     //(exists prps1: proposals'::Map<prps1> * tmp1::Proposal<proNums[i],0> & prps1[i] = tmp1 & i' = i+1);
     }
{
     if(0<=i && i<ll){
         dprint;
         Proposal tmp = new_proposal();
         //int pronum = proNums[i];
         //tmp.num = pronum;
         // int nnnn = i + m;
         tmp.num = i+m;//proNums[i];
         tmp.voteCount = 0;
         proposals[i+m] = tmp;
         dprint;
         for_loop_ballot(proposals, i+1, ll, m);
     }
}

// int get_length(node x)
//    requires x::list<nnn>@L
//    ensures  res = nnn;
// {
//  if (x==null) return 0;
//  else return (1 + (get_length(x.next)));
// }

// assume that the length of proposals is m
void ballot(node proposalNames, mapping(int => int) proposals, int m)
  requires true//proposalNames::list<n> & m>=0
  ensures  true;
{
 int x;
 int i = 0;
 //int length = get_length(proposalNames);
 for_loop(proposals, i, m, 9);
}

/*
    /// Create a new ballot to choose one of `proposalNames`.
    function Ballot(bytes32[] proposalNames) public {
        chairperson = msg.sender;
        voters[chairperson].weight = 1;

        // For each of the provided proposal names,
        // create a new proposal object and add it
        // to the end of the array.
        for (uint i = 0; i < proposalNames.length; i++) {
            // `Proposal({...})` creates a temporary
            // Proposal object and `proposals.push(...)`
            // appends it to the end of `proposals`.
            proposals.push(Proposal({
                name: proposalNames[i],
                voteCount: 0
            }));
        }
    }
*/
