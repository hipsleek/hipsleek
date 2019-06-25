struct node {
int val;
struct node* next;
};


/*@
ll<n> == (self = null) & (n = 0)
 or self::node<Anon_11,r> * r::ll<n2> & n = 1+n2
;
*/
int length(struct node* x)
/*@
requires x::ll<n> & true
ensures x::ll<n> & res = n;
*/
{
int k;
int tmp;
if ((x) == (NULL)) {

} else {
tmp = length(x->next);
k = 1 + tmp;
return k;
}
}

