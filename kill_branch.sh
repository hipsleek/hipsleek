echo "this is to merge and kill an old branch"
# to merge but keep local copy
#hg --config ui.merge=internal:fail merge $1
#hg revert --all --rev .
# to mark the local files as resolved
#hg resolve --mark --all


# Occasionally you want to merge two heads, but you want to throw away all changes from one of the heads, a so-called dummy merge. You can override the merge by using the ui.merge configuration entry:

# $ hg --config ui.merge=internal:local merge  #keep my files
# $ hg --config ui.merge=internal:other merge  #keep their files
# Here local means parent of working directory, other is the head you want to merge with. This will leave out updates from the other head.

# To merge X into the current revision without letting any of the changes from X come through, do:

# hg --config ui.merge=internal:fail merge X
# hg revert --all --rev .
