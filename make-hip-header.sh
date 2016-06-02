# Script for converting a SLEEK header into a HIP header.
# Only converts type declarations and pred declarations now.
#
# Usage: ./make-hip-header <sleek_header.slk>



#! /bin/bash

hip_header_filename=$(sed 's/slk/ss/' <<< $1)

: > $hip_header_filename

pred=false

while IFS='' read -r line || [[ -n "$line" ]]; do
	printf "%s\n" "$line"
	# process includes
	hip_line="$line"
	if [[ "$line" == *"sleek_include"* ]]
	then
			hip_line=`sed 's/sleek_include/hip_include/' <<< $hip_line`
			hip_line=`sed 's/\.slk/\.ss/' <<< $hip_line`
			hip_line=`sed 's/\.$//' <<< $hip_line`
	# type declaration
	elif [[ "$line" == *"}."* ]]
	then
			hip_line=`sed 's/}\./}/' <<< $hip_line`
	elif [[ "$line" == *"pred"* || $pred = true ]]
	then
			hip_line=`sed '/pred/{s/pred//;q}; /pred/!{q100}' <<< $hip_line`
			if [ $? -eq 0 ]
			then
					pred=true
			fi
			hip_line=`sed '/\./{s/\.$/;/;q}; /\./!{q100}' <<< $hip_line`
			if [ $? -eq 0 ]
			then
					pred=false
			fi
	fi
	echo "$hip_line" >> $hip_header_filename
done < "$1"
