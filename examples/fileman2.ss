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

// only track number of files
// nf : total number of files
ftree<nf> == self = null & nf = 0
	or self::folder<name = fldr, files = fls, child = chd, sib = sb>
		* fls::flist<n1>
		* chd::ftree<nf1> * sb::ftree<nf2> 
		& nf = n1 + nf1 + nf2
	inv nf >= 0;

fseg<p, nf> == self = p & nf = 0
	or self::folder<name = fldr, files = fls, child = chd, sib = sb>
		* fls::flist<n1>
		* chd::ftree<nf1> * sb::fseg<p, nf2>
		& nf = n1 + nf1 + nf2
	inv nf >= 0;

lemma self::ftree<nf> <- self::fseg<x, nf1> * x::ftree<nf2> & nf = nf1 + nf2;

/*
	Search for a name in a folder list by following the sib link.
*/
folder search_name(str name, folder flist)
	requires flist::ftree<nf>
	ensures flist::ftree<nf> & res = null
		or flist::fseg<res, nf1> * res::ftree<nf2> & nf = nf1 + nf2 & res != null;
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
	else {
		return null;
	}
}

/*
	Make a folder with path pa in the folder tree rooted at fldr.
*/
bool mkdir(folder fldr, pentry pa)
	requires fldr::ftree<nf> * pa::path<> & fldr != null
	ensures fldr::ftree<nf1> * pa::path<> & nf1 = nf;
{
	bool ok = true;

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
			ok = mkdir(tmp, pa.next);
			return ok;
		}
	}
	else {
		return ok;
	}
}
