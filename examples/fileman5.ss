/*
	File Manager:
	- tree of folders (left child/right sibling)
	- each folder holds a list of files and a list of folders

	Operations:
	- Create folder/file
	- Remove folder/file
	- Move/copy file/folder

	There is always a non-null root folder.

	Calling these operations: 
	simulating user inputs by using functions that ensures true/no size
*/

data str {
}

bool streq(str s1, str s2)
	requires true ensures true;

// path entry
data pentry {
	str ent;
	pentry next;
}

path<n> == self = null & n = 0
	or self::pentry<next = r> * r::path<n1> & n = n1 + 1
	inv n >= 0;

data file {
	str name;

	file next;
}

data folder {
	str name;
	
	file files;

	folder child;
	folder sib;
}

flist<n> == self = null & n = 0
	or self::file<name = fl, next = r> 
		* r::flist<n1> 
		& n = n1 + 1
	inv n >= 0;

// nf : total number of files
// nr : total number of folders
ftree<nf, nr> == self = null & nf = 0 & nr = 0
	or self::folder<name = fldr, files = fls, child = chd, sib = sb>
		* fls::flist<n1>
		* chd::ftree<nf1, nr1> * sb::ftree<nf2, nr2> 
		& nf = n1 + nf1 + nf2 & nr = 1 + nr1 + nr2
	inv nf >= 0 & nr >= 0;

fseg<p, nf, nr> == self = p & nf = 0 & nr = 0
	or self::folder<name = fldr, files = fls, child = chd, sib = sb>
		* fls::flist<n1>
		* chd::ftree<nf1, nr1> * sb::fseg<p, nf2, nr2>
		& nf = n1 + nf1 + nf2 & nr = 1 + nr1 + nr2
	inv nf >= 0 & nr >= 0;

lemma self::ftree<nf, nr> <- self::fseg<x, nf1, nr1> * x::ftree<nf2, nr2> & nf = nf1 + nf2 & nr = nr1 + nr2;

/*
	Search for a name in a folder list by following the sib link.
*/
folder search_name(str name, folder flist)
	requires flist::ftree<nf, nr>
	ensures flist::ftree<nf, nr> & res = null
		or flist::fseg<res, nf1, nr1> * res::ftree<nf2, nr2> & nf = nf1 + nf2 & nr = nr1 + nr2 & res != null;
{
	if (flist != null) {
		if (streq(flist.name, name)) {
			return flist;
		}
		else {
			folder tmp = search_name(name, flist.sib);
			return tmp;
		}
	}
	else
		return null;
}

/*
	Make a folder with path pa in the folder tree rooted at fldr.
*/
bool mkdir(folder fldr, pentry pa)
	requires fldr::ftree<nf, nr> * pa::path<> & fldr != null
	ensures fldr::ftree<nf1, nr1> * pa::path<> & nf1 = nf & nr1 >= nr;
{
	bool ok = false;

	if (pa != null) {
		folder tmp = search_name(pa.ent, fldr.child);
		if (tmp != null) {
			ok = mkdir(tmp, pa.next);
			return ok;
		}
		else {
			// make a sub-folder as the left-most child
			tmp = new folder(pa.ent, null, null, fldr.child);
			fldr.child = tmp;
			mkdir(tmp, pa.next);
			ok = true;
			return ok;
		}
	}
	else {
		return ok;
	}
}

/*
	Remove a folder.

	Returns true if folder is really removed.
*/
bool remove(folder fldr, pentry pa)
	requires fldr::ftree<nf, nr> * pa::path<> & fldr != null
	ensures fldr::ftree<nf1, nr1> * pa::path<> & nf1 <= nf & nr1 <= nr;
{
	bool deleted = false;

	if (pa != null) {
		folder tmp = search_name(pa.ent, fldr.child);
		if (tmp != null) {
			if (pa.next != null) {
				deleted = remove(tmp, pa.next);
				return deleted;
			}
			else {
				fldr.child = delete_entry(fldr.child, tmp);
				deleted = true;
				return deleted;
			}
		}
		else {
			return deleted; // not deleted
		}
	}
	else {
		return deleted;
	}
}

folder delete_entry(folder l, folder e)
	requires l::fseg<e, nf, nr> * e::ftree<nf1, nr1> & e != null
	ensures res::ftree<nf2, nr2> & nf2 <= nf + nf1 & nr2 < nr + nr1;
{
	if (l == null) {
		return l;
	}
	if (l == e) {
		return l.sib;
	}

	if (l.sib == e) {
		l.sib = e.sib;
		return l;
	}
	else {
		folder tmp = delete_entry(l.sib, e);
		l.sib = tmp;
		return l;
	}
}

/*
/*
	Find folder.
*/
folder find_folder(folder fldr, pentry pa)
	requires fldr::ftree<nf, nr> * pa::path<> & fldr != null
	ensures <needs to talk about tree with hole>
{
}
*/

/*
/*
	Copy folder.
*/
folder dup_folder(folder fldr)
	requires fldr::ftree<nf, nr>
	ensures fldr::ftree<nf, nr> * res::ftree<nf, nr>;
{
	if (fldr != null) {
		
	}
	else
		return null;
}
*/
