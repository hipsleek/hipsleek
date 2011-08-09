data cell {int val;}.

checkentail x::cell<n> & n > 3 |- x::cell<m> & m > 2.
checkentail x::cell<n> & n > 1 |- x::cell<m> & m > 2.

checkentail x::cell<_> |- x::cell<_>.

checkentail x::cell@[L,R]<_> |- x::cell<_>.
checkentail x::cell@[L,R]<_> |- x::cell@[L]<_>.
checkentail x::cell@[L]<_> |- x::cell@[R]<_>.
checkentail x::cell<_> |- x::cell@[R]<_>.
print residue.
checkentail x::cell<_> |- x::cell@[L]<_>.
print residue.


checkentail x::cell@[L,R]<_> |- x::cell<_>.
checkentail x::cell@[R,R]<_> |- x::cell[L,R]<_>.
checkentail x::cell@v<_> |- x::cell@v<_>.

checkentail x::cell@v1<_> |- x::cell@v<_>. //error

checkentail x::cell@[R]<_> |- x::cell@[R,L]<_>. //error
print residue.